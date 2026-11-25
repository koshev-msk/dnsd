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
#include <time.h>
#include <dnssec.h>
#include <log.h>


sig_atomic_t                        running = 0;
static int                          sock;
static int                          pidfp = -1;
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
static struct curl_slist*           resolve;
static struct dns_resp              resp;

static char                         url_host[256];
static char                         url_port[8];
static int                          url_is_ip;
static time_t                       bootstrap_time;

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

// offset after the (possibly compressed) name at i, 0 on error
static size_t skip_name(const unsigned char* p, size_t length, size_t i)
{
    while (i < length)
    {
        if (p[i] == 0) return i + 1;
        if ((p[i] & 0xC0) == 0xC0) return i + 2 <= length ? i + 2 : 0;
        if (p[i] & 0xC0) return 0;
        i += p[i] + 1;
    }

    return 0;
}

// offset of the first byte after the question section, 0 if malformed
static size_t question_end(const unsigned char* p, size_t length)
{
    size_t i = skip_name(p, length, sizeof(struct dns_header));

    if (i == 0) return 0;
    i += 4;

    return i <= length ? i : 0;
}

// split the URL: host and port are needed for the bootstrap lookup
static int url_parse()
{
    CURLU* u        = curl_url();
    char*  scheme   = NULL;
    char*  host     = NULL;
    char*  port     = NULL;
    int    ret      = EXIT_FAILURE;
    struct in_addr a4;

    if (u == NULL) return ret;

    if (curl_url_set(u, CURLUPART_URL, options.url, 0) == CURLUE_OK &&
        curl_url_get(u, CURLUPART_SCHEME, &scheme, 0) == CURLUE_OK &&
        curl_url_get(u, CURLUPART_HOST, &host, 0) == CURLUE_OK &&
        curl_url_get(u, CURLUPART_PORT, &port, CURLU_DEFAULT_PORT) == CURLUE_OK &&
        (!strcmp(scheme, "https") || !strcmp(scheme, "http")) &&
        strlen(host) < sizeof(url_host) && strlen(port) < sizeof(url_port))
    {
        strcpy(url_host, host);
        strcpy(url_port, port);
        url_is_ip = host[0] == '[' || inet_pton(AF_INET, host, &a4) == 1;
        ret = EXIT_SUCCESS;
    }

    curl_free(scheme);
    curl_free(host);
    curl_free(port);
    curl_url_cleanup(u);

    return ret;
}

// ask one DNS server for an A or AAAA record of host
static int bootstrap_query(const struct sockaddr* srv, socklen_t srvlen, const char* host,
                           uint16_t qtype, char* out, size_t outlen)
{
    unsigned char q[300], r[1500];
    size_t        n = sizeof(struct dns_header);
    const char*   p = host;
    uint16_t      id = (uint16_t) rand();

    memset(q, 0x00, n);
    q[0] = id >> 8;
    q[1] = id & 0xFF;
    q[2] = 0x01;                // RD
    q[5] = 1;                   // one question

    while (*p)
    {
        const char* dot = strchr(p, '.');
        size_t      l   = dot ? (size_t)(dot - p) : strlen(p);

        if (l == 0 || l > MAX_SUBDOMAIN_LENGTH || n + l + 1 + 5 > sizeof(q)) return EXIT_FAILURE;

        q[n++] = l;
        memcpy(q + n, p, l);
        n += l;
        p += l;
        if (*p == '.') p++;
    }

    q[n++] = 0;
    q[n++] = qtype >> 8;
    q[n++] = qtype & 0xFF;
    q[n++] = 0;
    q[n++] = DNS_INET_ADDR;     // class IN

    int s = socket(srv->sa_family, SOCK_DGRAM, 0);
    if (s < 0) return EXIT_FAILURE;

    struct timeval tv = { BOOTSTRAP_TIMEOUT, 0 };
    setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));

    // connected socket: only the bootstrap server can answer
    if (connect(s, srv, srvlen) != 0 || send(s, q, n, 0) != (ssize_t) n)
    {
        close(s);
        return EXIT_FAILURE;
    }

    ssize_t rn = recv(s, r, sizeof(r), 0);
    close(s);

    if (rn < (ssize_t) sizeof(struct dns_header) || r[0] != q[0] || r[1] != q[1] ||
        !(r[2] & 0x80) || (r[3] & 0x0F)) return EXIT_FAILURE;

    size_t qd = (r[4] << 8) | r[5];
    size_t an = (r[6] << 8) | r[7];
    size_t i  = sizeof(struct dns_header);

    for (size_t k = 0; k < qd; k++)
    {
        i = skip_name(r, rn, i);
        if (i == 0) return EXIT_FAILURE;
        i += 4;
    }

    for (size_t k = 0; k < an; k++)
    {
        i = skip_name(r, rn, i);
        if (i == 0 || i + 10 > (size_t) rn) return EXIT_FAILURE;

        uint16_t type  = (r[i] << 8) | r[i + 1];
        uint16_t class = (r[i + 2] << 8) | r[i + 3];
        size_t   rdlen = (r[i + 8] << 8) | r[i + 9];
        i += 10;

        if (i + rdlen > (size_t) rn) return EXIT_FAILURE;

        if (class == DNS_INET_ADDR && type == qtype)
        {
            if (qtype == DNS_A_RECORD && rdlen == 4)
                return inet_ntop(AF_INET, r + i, out, outlen) ? EXIT_SUCCESS : EXIT_FAILURE;
            if (qtype == DNS_AAAA_RECORD && rdlen == 16)
                return inet_ntop(AF_INET6, r + i, out, outlen) ? EXIT_SUCCESS : EXIT_FAILURE;
        }

        i += rdlen;
    }

    return EXIT_FAILURE;
}

// resolve the host of the URL through the bootstrap server(s) and give the address to curl
static int bootstrap_apply()
{
    char  list[256];
    char  addr[INET6_ADDRSTRLEN];
    char  entry[sizeof(url_host) + sizeof(url_port) + INET6_ADDRSTRLEN + 8];
    char* tok;
    int   found = 0;

    bootstrap_time = time(NULL);

    strncpy(list, options.bootstrap, sizeof(list) - 1);
    list[sizeof(list) - 1] = '\0';

    for (tok = strtok(list, ","); tok && !found; tok = strtok(NULL, ","))
    {
        struct addrinfo hints, *ai = NULL;

        memset(&hints, 0x00, sizeof(hints));
        hints.ai_family     = AF_UNSPEC;
        hints.ai_socktype   = SOCK_DGRAM;
        hints.ai_flags      = AI_NUMERICHOST | AI_NUMERICSERV;

        if (getaddrinfo(tok, "53", &hints, &ai) != 0)
        {
            LOG_ERROR("invalid bootstrap address (%s)", tok);
            continue;
        }

        // IPv4 first: a router without IPv6 uplink cannot use an AAAA answer
        found = bootstrap_query(ai->ai_addr, ai->ai_addrlen, url_host, DNS_A_RECORD, addr, sizeof(addr)) == EXIT_SUCCESS ||
                bootstrap_query(ai->ai_addr, ai->ai_addrlen, url_host, DNS_AAAA_RECORD, addr, sizeof(addr)) == EXIT_SUCCESS;
        freeaddrinfo(ai);

        if (!found) LOG_ERROR("bootstrap server %s did not resolve %s", tok, url_host);
    }

    if (!found) return EXIT_FAILURE;

    if (strchr(addr, ':'))
        snprintf(entry, sizeof(entry), "%s:%s:[%s]", url_host, url_port, addr);
    else
        snprintf(entry, sizeof(entry), "%s:%s:%s", url_host, url_port, addr);

    struct curl_slist* fresh = curl_slist_append(NULL, entry);
    if (fresh == NULL) return EXIT_FAILURE;

    if (curl) curl_easy_setopt(curl, CURLOPT_RESOLVE, fresh);
    curl_slist_free_all(resolve);
    resolve = fresh;

    if (options.debug) LOG_INFO("bootstrap: %s -> %s", url_host, addr);

    return EXIT_SUCCESS;
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

    curl_easy_setopt(curl, CURLOPT_URL, options.url);
    curl_easy_setopt(curl, CURLOPT_HTTPHEADER, headers);
    curl_easy_setopt(curl, CURLOPT_POST, 1L);
    curl_easy_setopt(curl, CURLOPT_HTTP_VERSION, CURL_HTTP_VERSION_2TLS);
    curl_easy_setopt(curl, CURLOPT_FAILONERROR, 1L);
    curl_easy_setopt(curl, CURLOPT_NOSIGNAL, 1L);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, (long) options.server_timeout);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, body_callback);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, (void *)&resp);

    if (resolve)
    {
        curl_easy_setopt(curl, CURLOPT_RESOLVE, resolve);
    }

    if (options.proxy)
    {
        curl_easy_setopt(curl, CURLOPT_PROXY, options.proxy);
    }

    if (options.pin)
    {
        if (curl_easy_setopt(curl, CURLOPT_PINNEDPUBLICKEY, options.pin) != CURLE_OK)
        {
            LOG_ERROR("failed to load the pinned public key");
            return EXIT_FAILURE;
        }
    }

    return EXIT_SUCCESS;
}

// one line per query: what was asked, which server answered, how
static void log_transfer(const unsigned char* query, size_t length, CURLcode res)
{
    char     name[MAX_DOMAIN_LENGTH + 1] = {0};
    char*    ip      = NULL;
    long     port    = 0;
    long     code    = 0;
    long     ver     = 0;
    double   sec     = 0;
    uint16_t qtype   = 0;
    size_t   i       = sizeof(struct dns_header);
    size_t   n       = 0;

    while (i < length && query[i] && !(query[i] & 0xC0) &&
           i + query[i] < length && n + query[i] + 1 < sizeof(name))
    {
        memcpy(name + n, query + i + 1, query[i]);
        n += query[i];
        name[n++] = '.';
        i += query[i] + 1;
    }

    if (n == 0) name[0] = '.';
    if (i + 2 < length) qtype = (query[i + 1] << 8) | query[i + 2];

    curl_easy_getinfo(curl, CURLINFO_PRIMARY_IP, &ip);
    curl_easy_getinfo(curl, CURLINFO_PRIMARY_PORT, &port);
    curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &code);
    curl_easy_getinfo(curl, CURLINFO_HTTP_VERSION, &ver);
    curl_easy_getinfo(curl, CURLINFO_TOTAL_TIME, &sec);

    LOG_INFO("%s type %u -> %s:%ld %s %ld, %zu bytes, %.0f ms%s", name, qtype,
             (ip && ip[0]) ? ip : "-", port,
             ver == CURL_HTTP_VERSION_2_0 ? "HTTP/2" : ver == CURL_HTTP_VERSION_1_1 ? "HTTP/1.1" : "HTTP/?",
             code, resp.len, sec * 1000, res == CURLE_OK ? "" : " (failed)");
}

// RFC 8484: the DNS message goes to the server as is, the answer comes back as is
static int https_query(const unsigned char* query, size_t length)
{
    resp.len = 0;

    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, (const char *)query);
    curl_easy_setopt(curl, CURLOPT_POSTFIELDSIZE, (long) length);

    CURLcode res = curl_easy_perform(curl);

    if (options.debug) log_transfer(query, length, res);

    if (res != CURLE_OK)
    {
        LOG_ERROR("curl_easy_perform() failed: %s", curl_easy_strerror(res));

        // the address of the server may have changed: ask the bootstrap server again
        if (options.bootstrap && !url_is_ip && time(NULL) - bootstrap_time >= BOOTSTRAP_RETRY)
            bootstrap_apply();

        return EXIT_FAILURE;
    }

    if (resp.len < sizeof(struct dns_header))
    {
        LOG_ERROR("short answer (%zu bytes).", resp.len);
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}

// open and bind the listening socket
static int server_init()
{
    struct addrinfo hints, *ai = NULL;
    char   port[8];

    memset(&hints, 0x00, sizeof(hints));
    hints.ai_family     = AF_UNSPEC;
    hints.ai_socktype   = SOCK_DGRAM;
    hints.ai_flags      = AI_NUMERICHOST | AI_NUMERICSERV | AI_PASSIVE;
    snprintf(port, sizeof(port), "%u", options.port);

    if (getaddrinfo(options.listen_ip, port, &hints, &ai) != 0)
    {
        LOG_ERROR("invalid listen address (%s)", options.listen_ip);
        return EXIT_FAILURE;
    }

    sock = socket(ai->ai_family, SOCK_DGRAM, IPPROTO_UDP);
    if (sock < 0)
    {
        LOG_ERROR("socket() %s", strerror(errno));
        freeaddrinfo(ai);
        return EXIT_FAILURE;
    }

    if (bind(sock, ai->ai_addr, ai->ai_addrlen))
    {
        LOG_ERROR("bind(%s:%u) %s", options.listen_ip, options.port, strerror(errno));
        freeaddrinfo(ai);
        return EXIT_FAILURE;
    }

    freeaddrinfo(ai);

    return EXIT_SUCCESS;
}

int server()
{
    buffer        = malloc(BUFFER_SIZE);
    resp.buf      = malloc(BUFFER_SIZE);
    resp.cap      = BUFFER_SIZE;

    if (buffer == NULL || resp.buf == NULL) return EXIT_FAILURE;

    if (curl_setup() == EXIT_FAILURE) return EXIT_FAILURE;

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
    curl_slist_free_all(resolve);

    free(buffer);
    free(resp.buf);
    close(sock);

    return EXIT_SUCCESS;
}

int main(int argc, char **argv)
{

    memset(&options, 0x00, sizeof(struct func_options));

    extern char* optarg;
    int          c;

    options.listen_ip       = "127.0.0.1";
    options.port            = DNS_SERVER_PORT;
    options.server_timeout  = DNS_SERVER_TIMEOUT;

    static struct option long_options[] =
    {
        {"url",        required_argument,       0, 'u'},
        {"bootstrap",  required_argument,       0, 'b'},
        {"listen",     required_argument,       0, 'l'},
        {"port",       required_argument,       0, 'p'},
        {"pid",        required_argument,       0, 'P'},
        {"proxy",      required_argument,       0, 'x'},
        {"pin",        required_argument,       0, 'k'},
        {"debug",      no_argument,             0, 'D'},
        {"help",       no_argument,             0, 'h'},
        {0, 0, 0, 0}
    };

    int option_index = 0;

    while ((c = getopt_long(argc, argv, "u:b:l:p:P:x:k:Dh", long_options, &option_index)) != -1)
    {
        switch (c)
        {
        case 'u':
            options.url = optarg;
            break;
        case 'b':
            options.bootstrap = optarg;
            break;
        case 'l':
            options.listen_ip = optarg;
            break;
        case 'p':
        {
            char* end = NULL;
            long  val = strtol(optarg, &end, 10);

            if (*optarg == '\0' || *end != '\0' || val < 1 || val > 65535)
            {
                fprintf(stderr, "invalid port (%s)\n", optarg);
                return EXIT_FAILURE;
            }
            options.port = (uint16_t) val;
            break;
        }
        case 'P':
            options.pid_file = optarg;
            break;
        case 'x':
            options.proxy = optarg;
            break;
        case 'k':
            options.pin = optarg;
            break;
        case 'D':
            options.debug = 1;
            break;
        case 'h':
            usage(argv[0]);
            return EXIT_SUCCESS;
        default:
            usage(argv[0]);
            return EXIT_FAILURE;
        }
    }

    if (options.url == NULL)
    {
        fprintf(stderr, "--url is required\n");
        usage(argv[0]);
        return EXIT_FAILURE;
    }

    srand((unsigned) (time(NULL) ^ getpid()));
    curl_global_init(CURL_GLOBAL_DEFAULT);

    if (url_parse() == EXIT_FAILURE)
    {
        fprintf(stderr, "invalid url (%s), only http:// and https:// are supported\n", options.url);
        return EXIT_FAILURE;
    }

    // bootstrap is needed only when the URL has a host name
    if (options.bootstrap && !url_is_ip && bootstrap_apply() == EXIT_FAILURE)
    {
        fprintf(stderr, "bootstrap failed: cannot resolve %s through %s\n", url_host, options.bootstrap);
        return EXIT_FAILURE;
    }

    if (server_init() == EXIT_FAILURE) return EXIT_FAILURE;

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

    if (!options.debug) start_daemon();

    if (options.pid_file && create_pidfile() == EXIT_FAILURE)
    {
        LOG_ERROR("cannot create the pid file (%s)", options.pid_file);
        return EXIT_FAILURE;
    }

    if (server() == EXIT_FAILURE)
        LOG_ERROR ("udp server failed to start.");

    if (options.pid_file) unlink(options.pid_file);

    curl_global_cleanup();

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
        running = 0;
    default:
        return;
    }
}

void usage(char* exec_name)
{
    fprintf(stderr, "\n"LICENSE"\n\n");
    fprintf(stderr, "Usage : %s --url URL [options]\n\n", exec_name);
    fprintf(stderr,
        "  -u, --url URL          DoH endpoint (RFC 8484), e.g. https://1.1.1.1/dns-query\n"
        "  -b, --bootstrap IP,..  DNS server(s) used only to resolve the host name of the URL\n"
        "  -l, --listen IP        address to listen on (default 127.0.0.1)\n"
        "  -p, --port PORT        UDP port to listen on (default 53)\n"
        "  -P, --pid FILE         write the PID file\n"
        "  -x, --proxy URL        use a proxy for the DoH connection\n"
        "  -k, --pin PIN          pin the server public key (sha256//base64)\n"
        "  -D, --debug            stay in the foreground and log every query to stderr\n"
        "  -h, --help             display this information\n");
}

int create_pidfile()
{
    char str[16] = {0};

    pidfp        = open(options.pid_file, O_RDWR|O_CREAT, 0644);

    if (pidfp == -1) return EXIT_FAILURE;

    if (lockf(pidfp, F_TLOCK,0) == -1) return EXIT_FAILURE;

    if (ftruncate(pidfp, 0) == -1) return EXIT_FAILURE;

    snprintf(str, sizeof(str), "%d\n", getpid());

    if (write(pidfp, str, strlen(str)) < 0) return EXIT_FAILURE;

    return EXIT_SUCCESS;
}
