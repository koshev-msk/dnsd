/*
 * Copyright (C) 2016  Kamary

 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.

 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.

 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 */
#define _GNU_SOURCE
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <signal.h>
#include <getopt.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <curl/curl.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <poll.h>
#include <sys/stat.h>   // umask()
#include <errno.h>
#include <dnssec.h>
#include <log.h>


sig_atomic_t                        running = 0;
static int                          sock;
static int                          pidfp;
static unsigned char*               buffer;
static struct sockaddr_storage      peer_add;
static socklen_t                    peer_add_len;
static struct func_options          options;

static void __attribute__ ((unused)) start_daemon()
{
    pid_t process_id = 0;
    pid_t sid        = 0;
    process_id = fork();
    if (process_id < 0)
    {
        fprintf(stderr, "fork() failed.\n");
        exit(EXIT_FAILURE);
    }

    if (process_id > 0)
    {
        fprintf(stdout, "daemon process id is %d. \n", process_id);
        exit(EXIT_SUCCESS);
    }

    umask(0);
    sid = setsid();
    if(sid < 0)
    {
        fprintf(stderr, "setsid() failed.\n");
        exit(EXIT_FAILURE);
    }

    chdir("/");

    close(STDIN_FILENO);
    close(STDOUT_FILENO);
    close(STDERR_FILENO);

    if (open("/dev/null", O_RDONLY) == -1)
    {
        fprintf(stderr, "open(stdin)");
        exit(EXIT_FAILURE);
    }
    if (open("/dev/null", O_WRONLY) == -1)
    {
        fprintf(stderr, "open(stdout)");
        exit(EXIT_FAILURE);
    }
    if (open("/dev/null", O_RDWR) == -1)
    {
        fprintf(stderr, "open(stderr)");
        exit(EXIT_FAILURE);
    }
}

#if DEBUG_AUDIT_ENABLE
void audit_pid(const char* port)
{
    int   failed = 1;
    FILE* fp;
    char  buffer[2048];

    fp = popen("netstat -npau 2>&1", "r");
    if (fp == NULL)
    {
        LOG_DEBUG("failed to run 'netstat'");
        return;
    }


    while (fgets(buffer, sizeof(buffer), fp) != NULL)
    {
        char * curLine = buffer;
        while(curLine)
        {
            char * nextLine = strchr(curLine, '\n');
            if (nextLine) *nextLine = '\0';
            if (strstr(curLine, "udp") && strstr(curLine, port))
            {
                LOG_DEBUG("%s", curLine);
                failed = 0;
            }
            if (nextLine) *nextLine = '\n';
            curLine = nextLine ? (nextLine + 1) : NULL;
        }
    }

    if (failed) LOG_DEBUG("PID audit failed.");

    pclose(fp);
}
#endif

int ipoll()
{
    struct pollfd fds;
    fds.fd      = sock;
    fds.events  = POLLIN;

    return poll(&fds, 1, 1000);
}

struct dns_resp
{
    unsigned char*  buf;
    size_t          len;
    size_t          cap;
};

static CURL*                        curl;
static struct curl_slist*           headers;
static struct dns_resp              resp;

size_t body_callback (void* contents, size_t size, size_t nmemb, void* userp)
{
    struct dns_resp* r = (struct dns_resp*) userp;
    size_t chunk = size * nmemb;

    // the answer does not fit, abort the transfer
    if (chunk > r->cap - r->len) return 0;

    memcpy(r->buf + r->len, contents, chunk);
    r->len += chunk;

    return chunk;
}

static int curl_setup()
{
    curl = curl_easy_init();
    if (!curl)
    {
        LOG_ERROR("curl_easy_init() failed.");
        return EXIT_FAILURE;
    }

    headers = curl_slist_append(headers, "Content-Type: application/dns-message");
    headers = curl_slist_append(headers, "Accept: application/dns-message");

    curl_easy_setopt(curl, CURLOPT_URL, options.server_url);
    curl_easy_setopt(curl, CURLOPT_HTTPHEADER, headers);
    curl_easy_setopt(curl, CURLOPT_POST, 1L);
    curl_easy_setopt(curl, CURLOPT_HTTP_VERSION, CURL_HTTP_VERSION_2TLS);
    curl_easy_setopt(curl, CURLOPT_FAILONERROR, 1L);
    curl_easy_setopt(curl, CURLOPT_NOSIGNAL, 1L);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, (long) options.server_timeout);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, body_callback);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, (void *)&resp);

    if (options.https_proxy[0])
    {
        curl_easy_setopt(curl, CURLOPT_PROXY, options.https_proxy);
    }

    if (options.service_pub_key[0])
    {
        if (curl_easy_setopt(curl, CURLOPT_PINNEDPUBLICKEY, options.service_pub_key) != CURLE_OK)
        {
            LOG_ERROR("failed to load the pinned public key");
            return EXIT_FAILURE;
        }
    }

    return EXIT_SUCCESS;
}

// RFC 8484: the DNS message goes to the server as is, the answer comes back as is
static int https_query(const unsigned char* query, size_t length)
{
    resp.len = 0;

    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, (const char *)query);
    curl_easy_setopt(curl, CURLOPT_POSTFIELDSIZE, (long) length);

    CURLcode res = curl_easy_perform(curl);

    if (res != CURLE_OK)
    {
        LOG_ERROR("curl_easy_perform() failed: %s", curl_easy_strerror(res));
        return EXIT_FAILURE;
    }

    if (resp.len < sizeof(struct dns_header))
    {
        LOG_ERROR("short answer (%zu bytes).", resp.len);
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}

// offset of the first byte after the question section, 0 if malformed
static size_t question_end(const unsigned char* p, size_t length)
{
    size_t i = sizeof(struct dns_header);

    while (i < length && p[i])
    {
        if (p[i] & 0xC0) return 0;
        i += p[i] + 1;
    }

    i += 1 + 4;

    return i <= length ? i : 0;
}

int server()
{

    struct sockaddr_in        server_add;
    buffer        = malloc(BUFFER_SIZE);
    resp.buf      = malloc(BUFFER_SIZE);
    resp.cap      = BUFFER_SIZE;

    if (buffer == NULL || resp.buf == NULL) return EXIT_FAILURE;

    curl_global_init(CURL_GLOBAL_DEFAULT);
    if (curl_setup() == EXIT_FAILURE) return EXIT_FAILURE;

    server_add.sin_family      = AF_INET;
    server_add.sin_port        = htons(options.service_port);
    server_add.sin_addr.s_addr = htonl(INADDR_ANY);

    if (options.service_ip[0] != '\0')
    {
        if (inet_pton(AF_INET, options.service_ip, &(server_add.sin_addr)) == 1)
        {
            LOG_INFO("service ip (%s)", options.service_ip);
        }
        else
        {
            LOG_ERROR("invalid service ip (%s)", options.service_ip);
        }
    }

    LOG_DEBUG("service port (%d)", options.service_port);

    sock = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
    if (sock < 0)
    {

#if LOG_LEVEL == LEV_NO_DEV_LOG
        perror("socket()");
#endif
        LOG_ERROR("socket() %s", strerror(errno));
        return EXIT_FAILURE;
    }

    if (bind(sock, (struct sockaddr*) &server_add, sizeof(server_add)))
    {

#if LOG_LEVEL == LEV_NO_DEV_LOG
        perror("bind()");
#endif
        LOG_ERROR("bind() %s", strerror(errno));
        return EXIT_FAILURE;
    }


    while (running)
    {
        int rp    = ipoll();

        if (rp == 0) continue;
        else if (rp < 0)
        {
            if (running)
            {
                LOG_ERROR("socket poll failed.");
                running = 0;
            }
            break;
        }

        peer_add_len = sizeof(peer_add);
        ssize_t nread = recvfrom(sock, buffer, BUFFER_SIZE, 0, (struct sockaddr*)&peer_add, &peer_add_len);

        // too short for a header, or already a response (QR bit)
        if (nread < (ssize_t) sizeof(struct dns_header) || (buffer[2] & 0x80)) continue;

        if (https_query(buffer, nread) == EXIT_SUCCESS)
        {
            if (sendto(sock, resp.buf, resp.len, 0, (struct sockaddr *) &peer_add, peer_add_len) != (ssize_t) resp.len)
                LOG_ERROR("(%x) error sending response.", (buffer[0] << 8) | buffer[1]);
        }
        else
        {
            // answer the client with SERVFAIL instead of leaving it to time out
            size_t qlen = question_end(buffer, nread);

            if (qlen)
            {
                buffer[2] = 0x80 | (buffer[2] & 0x79);  // QR, keep opcode and RD
                buffer[3] = 0x80 | DNS_SERVER_FAILURE;  // RA, SERVFAIL
                memset(buffer + 6, 0x00, 6);            // no answer/authority/additional
                sendto(sock, buffer, qlen, 0, (struct sockaddr *) &peer_add, peer_add_len);
            }
        }
    }

    curl_easy_cleanup(curl);
    curl_slist_free_all(headers);
    curl_global_cleanup();

    free(buffer);
    free(resp.buf);
    close(sock);

    return EXIT_SUCCESS;
}

int main(int argc, char **argv)
{

    memset(&options, 0x00, sizeof(struct func_options));

    extern char* optarg;
    extern int   optind;
    int          c;


    static struct option long_options[] =
    {
        {"debug",      no_argument,             0, 'D'},
        {"help",       no_argument,             0, 'h'},
        {"config",     required_argument,       0, 'f'},
        {0, 0, 0, 0}
    };

    int option_index = 0;

    while ((c = getopt_long(argc, argv, "hDf:", long_options, &option_index)) != -1)
    {
        switch (c)
        {
        case 'f':
            strncpy(options.config_file, optarg, OPT_CONIG_FILE_LEN);
            break;
        case 'D':
            options.enable_debug = 0xFF;
            break;
        case 'h':
            usage(argv[0]);
            return EXIT_FAILURE;
        default:
            usage(argv[0]);
            return EXIT_FAILURE;
        }
    }

    if (options.config_file[0] != '\0' && parse_options() == EXIT_FAILURE)
    {
        LOG_ERROR("parsing the configuration file has been failed.");
    }

    if (options.server_url[0] == 0) strncpy(options.server_url, OPT_DEFAULT_URL, OPT_SERVER_URL_LEN - 1);
    if (options.service_port == 0) options.service_port = DNS_SERVER_PORT;
    if (options.server_timeout == 0) options.server_timeout = DNS_SERVER_TIMEOUT;

    peer_add_len  = sizeof(struct sockaddr_storage);
    running       = 1;

    // signal handler initialization
    sigset_t sigset;
    sigemptyset(&sigset);
    sigaddset(&sigset, SIGCHLD);
    sigaddset(&sigset, SIGTSTP);
    sigaddset(&sigset, SIGTTOU);
    sigaddset(&sigset, SIGTTIN);
    sigprocmask(SIG_BLOCK, &sigset, NULL);

    struct sigaction sa;
    memset (&sa, '\0', sizeof(sa));
    sa.sa_handler = handle_signal;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;

    sigaction(SIGHUP,   &sa, NULL);
    sigaction(SIGUSR1,  &sa, NULL);
    sigaction(SIGINT,   &sa, NULL);
    sigaction(SIGTERM,  &sa, NULL);
    signal(SIGPIPE, SIG_IGN);

    if (options.enable_debug != 0xFF)
    {
        start_daemon();
        if (create_pidfile() == EXIT_FAILURE) return EXIT_FAILURE;
    }

    if (server() == EXIT_FAILURE)
        LOG_ERROR ("udp server failed to start.");

    LOG_DEBUG ("Process Terminated.");

    return EXIT_SUCCESS;
}

void handle_signal(int signal)
{
    switch (signal)
    {
    case SIGHUP:
    case SIGTERM:
    case SIGUSR1:
    case SIGINT:
        close(pidfp);
        running = 0;
    default:
        return;
    }
}

void usage(char* exec_name)
{
    fprintf(stderr, "\n"LICENSE"\n\n");
    fprintf(stderr, "Usage : %s [-D] [-f CONFIG_FILE]\n", exec_name);
    fprintf(stderr, "        %s [-h|--help] Display this information.\n", exec_name);
}

int parse_options()
{
    FILE    *fp     = NULL;
    char    *line   = NULL;
    size_t  len     = 0;
    ssize_t read    = 0;

    options.https_proxy[0]      = 0;
    options.server_url[0]       = 0;
    options.server_ip_list[0]   = 0;
    options.service_ip[0]       = 0;

    fp = fopen(options.config_file, "r");
    if (fp == NULL) return EXIT_FAILURE;

    while ((read = getline(&line, &len, fp)) != -1)
    {

        // replace the trailing newline characters with the space character
        for (size_t indx = 0; indx < read; indx++)
        {
            if (line[indx] == '\n' || line[indx] == '\r') line[indx] = 0x20;
        }

        int shift = remove_spaces(line);
        read -= shift;

        // skip too short lines
        if (read < 3) continue;

        // skip comment lines
        if (line[0] == '#') continue;

        if (strstr(line, OPT_HTTPS_PROXY) != NULL)
        {
            strncpy(options.https_proxy, line + sizeof(OPT_HTTPS_PROXY), OPT_HTTPS_PROXY_LEN);
        }
        else if (strstr(line, OPT_SERVER_URL) != NULL)
        {
            if (line[read - 1] == '/') line[read - 1] = '\0';
            strncpy(options.server_url, line + sizeof(OPT_SERVER_URL), OPT_SERVER_URL_LEN - 1);
        }
        else if (strstr(line, OPT_SERVICE_PORT) != NULL)
        {
            options.service_port = atoi(line + sizeof(OPT_SERVICE_PORT));
        }
        else if (strstr(line, OPT_SERVICE_IP) != NULL)
        {
            strncpy(options.service_ip, line + sizeof(OPT_SERVICE_IP), OPT_SERVICE_IP_LEN);
        }
        else if (strstr(line, OPT_SERVICE_PUB_KEY) != NULL)
        {
            strncpy(options.service_pub_key, line + sizeof(OPT_SERVICE_PUB_KEY), OPT_CONIG_FILE_LEN);
        }
        else if (strstr(line, OPT_ENABLE_EDNS) != NULL)
        {
            if (strcasestr(line, OPT_ENABLE_TRUE) != NULL) options.enable_edns = 1;
        }
    }

    free(line);

    return EXIT_SUCCESS;
}


int create_pidfile()
{
    char str[10] = {0};

    pidfp        = open(PIDFILE, O_RDWR|O_CREAT, 0600);

    if (pidfp == -1) return EXIT_FAILURE;

    if (lockf(pidfp, F_TLOCK,0) == -1) return EXIT_FAILURE;

    sprintf(str,"%d\n", getpid());

    write(pidfp, str, strlen(str));

    return EXIT_SUCCESS;
}

int remove_spaces(char* str)
{
    if (str == NULL) return 0;

    char* stra = str;
    char* strb = str;
    int shift = 0;

    do
    {
        *stra = *strb;
        if(*stra != ' ') stra++;
        else shift++;
    } while(*strb++ != 0);

    return shift;
}
