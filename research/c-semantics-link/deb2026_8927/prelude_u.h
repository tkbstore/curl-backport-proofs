/*
 * CVE-2026-8927（research/backport-proof-debian/cases/CVE-2026-8927.md）の上流側（U1・U0）の翻訳単位の前置き。
 * C1 の PROTOCOL §4 で許した「関数の外側の変更」だけを置く。
 *
 * 出典: curl 5c225384b8d52c67ce8259c6e4203bc57aacb567（U1）と親 d99dcfb04a70fa0e49a7745de63ed6041e5b67f5（U0）
 * 構成: CURL_DISABLE_PROXY・CURL_DISABLE_HTTP・CURL_DISABLE_DIGEST_AUTH は定義しない。USE_UNIX_SOCKETS を定義する
 *       （enum dupstring の並びにだけ効く）。BUILDING_LIBCURL・非 CURL_MEMDEBUG
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl の宣言順を保つ）
 *     struct Curl_peer      lib/peer.h:34       hostname
 *     struct Curl_scheme    lib/protocol.h:242  protocol, flags
 *     struct proxy_info     lib/urldata.h:325   peer, proxytype
 *     struct ConnectBits    lib/urldata.h       httpproxy, socksproxy, tunnel_proxy, proxy
 *     struct connectdata    lib/urldata.h:335   origin, socks_proxy, http_proxy, bits, scheme
 *     struct digestdata     lib/vauth/vauth.h   nonce（Curl_auth_digest_cleanup の仕様を述べるためだけに残す）
 *     struct UserDefined    lib/urldata.h:981   str
 *     struct UrlState       lib/urldata.h:647   envproxy（U1 だけ。DEB_ENVPROXY）, digest, proxydigest
 *     struct Curl_easy      lib/urldata.h:1308  set, state
 * - enum dupstring は lib/urldata.h から extract.py が切り出した（enum_u1.h・enum_u0.h）
 * - CURLcode・curl_proxytype は使う値だけ（include/curl/curl.h と同じ値）
 * - マクロ: curlx_safefree は lib/curl_setup.h:1326 の形。infof・failf は lib/curl_trc.h の `#define infof Curl_infof` の形
 *   （C1 の Case 3 と同じ）。PROTOPT_* は lib/protocol.h:215,227、PROTO_FAMILY_HTTP は lib/protocol.h:84
 * - 呼ばれる側の関数は extern の宣言にした（仕様は Lean 側で定理の仮定として与える）。
 *   curlx_strdup・curlx_free は BUILDING_LIBCURL では関数ポインタの変数 Curl_cstrdup・Curl_cfree だが、関数として宣言した（Case 3 と同じ）。
 *   url_detect_proxy・parse_proxy は lib/url.c の static 関数だが extern にした
 */
typedef unsigned long size_t;
typedef long curl_off_t;
typedef curl_off_t curl_prot_t;
typedef unsigned char uint8_t;
typedef unsigned int uint32_t;
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
#define PROTO_FAMILY_HTTP (CURLPROTO_HTTP | CURLPROTO_HTTPS | CURLPROTO_WS | \
                           CURLPROTO_WSS)
#define PROTOPT_NONETWORK (1 << 4)
#define PROTOPT_PROXY_AS_HTTP (1 << 11)

typedef enum {
  CURLE_OK = 0,
  CURLE_UNSUPPORTED_PROTOCOL = 1,
  CURLE_COULDNT_RESOLVE_PROXY = 5,
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

#ifdef DEB_U1
#include "enum_u1.h"
#else
#include "enum_u0.h"
#endif

struct Curl_peer {
  char *hostname;
};

struct Curl_scheme {
  curl_prot_t protocol;
  uint32_t flags;
};

struct proxy_info {
  struct Curl_peer *peer;
  uint8_t proxytype;
};

struct ConnectBits {
  BIT(httpproxy);
  BIT(socksproxy);
  BIT(tunnel_proxy);
  BIT(proxy);
};

struct connectdata {
  struct Curl_peer *origin;
  struct proxy_info socks_proxy;
  struct proxy_info http_proxy;
  struct ConnectBits bits;
  const struct Curl_scheme *scheme;
};

struct digestdata {
  char *nonce;
};

struct UserDefined {
  char *str[STRING_LAST];
};

struct UrlState {
#ifdef DEB_U1
  char *envproxy;
#endif
  struct digestdata digest;
  struct digestdata proxydigest;
};

struct Curl_easy {
  struct UserDefined set;
  struct UrlState state;
};

extern const struct Curl_scheme Curl_scheme_http;

extern char *curlx_strdup(const char *s);
extern void curlx_free(void *ptr);
#define curlx_safefree(ptr) \
  do {                      \
    curlx_free(ptr);        \
    (ptr) = NULL;           \
  } while(0)
extern void Curl_failf(struct Curl_easy *data, const char *fmt, ...);
#define failf Curl_failf
extern void Curl_infof(struct Curl_easy *data, const char *fmt, ...);
#define infof Curl_infof
extern char *curl_getenv(const char *variable);
extern bool Curl_check_noproxy(const char *name, const char *no_proxy);
extern char *url_detect_proxy(struct Curl_easy *data, struct connectdata *conn);
extern CURLcode parse_proxy(struct Curl_easy *data, const char *proxy,
                            bool for_pre_proxy, struct proxy_info *proxyinfo);
extern bool Curl_safecmp(char *a, char *b);
extern void Curl_auth_digest_cleanup(struct digestdata *digest);
extern void *memset(void *s, int c, size_t n);
