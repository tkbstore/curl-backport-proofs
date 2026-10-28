/*
 * CVE-2026-8927（research/backport-proof-debian/cases/CVE-2026-8927.md）の Debian 側（D1・D0）の翻訳単位の前置き。
 * C1 の PROTOCOL §4 で許した「関数の外側の変更」だけを置く。
 *
 * 出典: curl tag curl-8_14_1（D0）と、それに Debian の CVE-2026-8927.patch の lib/url.c・lib/urldata.h を当てたもの（D1）
 * 構成: prelude_u.h と同じ（CURL_DISABLE_PROXY・CURL_DISABLE_HTTP・CURL_DISABLE_DIGEST_AUTH は定義しない。USE_UNIX_SOCKETS を定義する）
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl 8.14.1 の宣言順を保つ）
 *     struct hostname       lib/urldata.h:519   rawalloc, name
 *     struct Curl_handler   lib/urldata.h       protocol, flags
 *     struct proxy_info     lib/urldata.h:713   host, proxytype, user, passwd
 *     struct ConnectBits    lib/urldata.h       httpproxy, socksproxy, proxy_user_passwd, tunnel_proxy, proxy
 *     struct connectdata    lib/urldata.h       host, socks_proxy, http_proxy, bits, handler, unix_domain_socket
 *     struct digestdata     lib/vauth/vauth.h   nonce（Curl_auth_digest_cleanup の仕様を述べるためだけに残す）
 *     struct UserDefined    lib/urldata.h       str
 *     struct UrlState       lib/urldata.h       envproxy（D1 だけ。Debian のパッチが足す）, digest, proxydigest
 *     struct Curl_easy      lib/urldata.h:1801  set, state
 * - enum dupstring は 8.14.1 の lib/urldata.h:1322 から extract.py が切り出した（enum_d.h）
 * - マクロ: free・strdup は lib/curl_memory.h:141,149 の形（Curl_cfree・Curl_cstrdup）。Curl_safefree は lib/memdebug.h:208。
 *   infof・failf は lib/curl_trc.h:159 の `#define infof Curl_infof` の形
 * - 呼ばれる側の関数は extern の宣言にした。Curl_cfree・Curl_cstrdup は関数ポインタの変数だが関数として宣言した（Case 3 のバックポートと同じ）。
 *   detect_proxy・parse_proxy・parse_proxy_auth は lib/url.c の static 関数だが extern にした
 */
typedef unsigned long size_t;
typedef long curl_off_t;
typedef curl_off_t curl_prot_t;
typedef _Bool bool;
#define TRUE 1
#define FALSE 0
#define NULL ((void *)0)

typedef unsigned int curl_bit;
#define BIT(x) curl_bit x:1

#define USE_UNIX_SOCKETS 1

#define CURLPROTO_HTTP   (1L << 0)
#define CURLPROTO_HTTPS  (1L << 1)
#define CURLPROTO_WS     (1L << 30)
#define CURLPROTO_WSS    ((curl_prot_t)1 << 31)
#define PROTO_FAMILY_HTTP (CURLPROTO_HTTP|CURLPROTO_HTTPS|CURLPROTO_WS| \
                           CURLPROTO_WSS)
#define PROTOPT_NONETWORK (1<<4)
#define PROTOPT_PROXY_AS_HTTP (1<<11)

typedef enum {
  CURLE_OK = 0,
  CURLE_UNSUPPORTED_PROTOCOL = 1,
  CURLE_OUT_OF_MEMORY = 27
} CURLcode;

typedef enum {
  CURLPROXY_HTTP = 0,
  CURLPROXY_HTTP_1_0 = 1,
  CURLPROXY_HTTPS = 2,
  CURLPROXY_HTTPS2 = 3,
  CURLPROXY_SOCKS4 = 4,
  CURLPROXY_SOCKS5 = 5,
  CURLPROXY_SOCKS4A = 6,
  CURLPROXY_SOCKS5_HOSTNAME = 7
} curl_proxytype;

#include "enum_d.h"

struct hostname {
  char *rawalloc;
  char *name;
};

struct Curl_handler {
  curl_prot_t protocol;
  unsigned int flags;
};

struct proxy_info {
  struct hostname host;
  unsigned char proxytype;
  char *user;
  char *passwd;
};

struct ConnectBits {
  BIT(httpproxy);
  BIT(socksproxy);
  BIT(proxy_user_passwd);
  BIT(tunnel_proxy);
  BIT(proxy);
};

struct connectdata {
  struct hostname host;
  struct proxy_info socks_proxy;
  struct proxy_info http_proxy;
  struct ConnectBits bits;
  const struct Curl_handler *handler;
  char *unix_domain_socket;
};

struct digestdata {
  char *nonce;
};

struct UserDefined {
  char *str[STRING_LAST];
};

struct UrlState {
#ifdef DEB_D1
  char *envproxy;
#endif
  struct digestdata digest;
  struct digestdata proxydigest;
};

struct Curl_easy {
  struct UserDefined set;
  struct UrlState state;
};

extern const struct Curl_handler Curl_handler_http;

extern char *Curl_cstrdup(const char *s);
#define strdup(ptr) Curl_cstrdup(ptr)
extern void Curl_cfree(void *ptr);
#define free(ptr) Curl_cfree(ptr)
#define Curl_safefree(ptr) \
  do { free((ptr)); (ptr) = NULL;} while(0)
extern void Curl_failf(struct Curl_easy *data, const char *fmt, ...);
#define failf Curl_failf
extern void Curl_infof(struct Curl_easy *data, const char *fmt, ...);
#define infof Curl_infof
extern char *curl_getenv(const char *variable);
extern bool Curl_check_noproxy(const char *name, const char *no_proxy);
extern char *detect_proxy(struct Curl_easy *data, struct connectdata *conn);
extern CURLcode parse_proxy(struct Curl_easy *data, struct connectdata *conn,
                            char *proxy, curl_proxytype proxytype);
extern CURLcode parse_proxy_auth(struct Curl_easy *data,
                                 struct connectdata *conn);
extern bool Curl_safecmp(char *a, char *b);
extern void Curl_auth_digest_cleanup(struct digestdata *digest);
