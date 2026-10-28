/*
 * CVE-2026-7168（research/backport-proof-debian/cases/CVE-2026-7168.md）の Debian 側（D1・D0）の翻訳単位の前置き。
 * C1 の PROTOCOL §4 で許した「関数の外側の変更」だけを置く。
 *
 * 出典: curl tag curl-8_14_1（D0）と、それに Debian の CVE-2026-7168.patch の lib/setopt.c・lib/vauth/vauth.h を当てたもの（D1）
 * 構成: prelude_u.h と同じ
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl 8.14.1 の lib/urldata.h の宣言順を保つ）
 *     struct ssl_config_data  fsslctxp
 *     struct UserDefined      debugdata, errorbuffer, out, in_set, writeheader, postfields, postfieldsize,
 *                             sockopt_client, opensocket_client, closesocket_client, prereq_userp, seek_client,
 *                             progress_client, ioctl_client, ssl, private_data, str, allowed_protocols, redir_protocols,
 *                             resolver_start_client, uh, trailer_data, method, haproxyprotocol
 *     struct digestdata       nonce（Curl_auth_digest_cleanup の仕様を述べるためだけに残す）
 *     struct auth             lib/urldata.h:1027  picked
 *     struct UrlState         proxydigest, authproxy, url, referer, url_alloc, referer_alloc
 *     struct Curl_easy        set, state
 * - enum dupstring は lib/urldata.h:1322 から、CURLoption は include/curl/curl.h から extract.py が作った（enum_d.h・opt_d.h）
 * - Curl_HttpReq は lib/http.h:36、CURLPROTO_* は include/curl/curl.h・lib/urldata.h:81、SIZE_T_MAX は lib/curl_setup.h:635
 * - free は lib/curl_memory.h:149 の形（Curl_cfree を関数として宣言）。Curl_safefree は lib/memdebug.h:208
 * - setstropt_userpwd・setstropt_interface・protocol2num は lib/setopt.c の static 関数だが extern にした
 */
#define USE_SSL 1
#define CURL_DISABLE_FTP 1
#define CURL_DISABLE_SMTP 1
#define CURL_DISABLE_RTSP 1
#define CURL_DISABLE_NETRC 1
#define CURL_DISABLE_HSTS 1
#define CURL_DISABLE_DOH 1
#define CURL_DISABLE_ALTSVC 1
#define CURL_DISABLE_COOKIES 1
#define CURL_DISABLE_AWS 1
#define CURL_DISABLE_MIME 1
#define CURL_DISABLE_MQTT 1
#define SIZEOF_CURL_OFF_T 8
#define SIZEOF_SIZE_T 8

typedef unsigned long size_t;
typedef long curl_off_t;
typedef curl_off_t curl_prot_t;
typedef _Bool bool;
#define TRUE 1
#define FALSE 0
#define NULL ((void *)0)

typedef unsigned int curl_bit;
#define BIT(x) curl_bit x:1

#define SSLSUPP_CA_PATH      (1<<0)
#define SSLSUPP_PINNEDPUBKEY (1<<2)
#define SSLSUPP_SSL_CTX      (1<<3)
#define SSLSUPP_TLS13_CIPHERSUITES (1<<5)
#define SSLSUPP_CIPHER_LIST  (1<<9)
#define SSLSUPP_SIGNATURE_ALGORITHMS (1<<10)
#define REJECT_ZERO 4
#define SIZE_T_MAX 18446744073709551615U
#define CURLPROTO_HTTP   (1<<0)
#define CURLPROTO_HTTPS  (1<<1)
#define CURLPROTO_FTP    (1<<2)
#define CURLPROTO_FTPS   (1<<3)
#define CURLPROTO_ALL    (~0)
#define CURLPROTO_REDIR (CURLPROTO_HTTP | CURLPROTO_HTTPS | CURLPROTO_FTP | \
                         CURLPROTO_FTPS)

typedef enum {
  CURLE_OK = 0,
  CURLE_NOT_BUILT_IN = 4,
  CURLE_OUT_OF_MEMORY = 27,
  CURLE_BAD_FUNCTION_ARGUMENT = 43,
  CURLE_UNKNOWN_OPTION = 48
} CURLcode;

typedef enum {
  HTTPREQ_GET,
  HTTPREQ_POST,
  HTTPREQ_POST_FORM,
  HTTPREQ_POST_MIME,
  HTTPREQ_PUT,
  HTTPREQ_HEAD
} Curl_HttpReq;

#include "opt_d.h"
#include "enum_d.h"

typedef struct Curl_URL CURLU;

struct ssl_config_data {
  void *fsslctxp;
};

struct UserDefined {
  void *debugdata;
  char *errorbuffer;
  void *out;
  void *in_set;
  void *writeheader;
  void *postfields;
  curl_off_t postfieldsize;
  void *sockopt_client;
  void *opensocket_client;
  void *closesocket_client;
  void *prereq_userp;
  void *seek_client;
  void *progress_client;
  void *ioctl_client;
  struct ssl_config_data ssl;
  void *private_data;
  char *str[STRING_LAST];
  curl_prot_t allowed_protocols;
  curl_prot_t redir_protocols;
  void *resolver_start_client;
  CURLU *uh;
  void *trailer_data;
  unsigned char method;
  BIT(haproxyprotocol);
};

struct digestdata {
  char *nonce;
};

struct auth {
  unsigned long picked;
};

struct UrlState {
  struct digestdata proxydigest;
  struct auth authproxy;
  char *url;
  char *referer;
  BIT(url_alloc);
  BIT(referer_alloc);
};

struct Curl_easy {
  struct UserDefined set;
  struct UrlState state;
};

extern void Curl_cfree(void *ptr);
#define free(ptr) Curl_cfree(ptr)
#define Curl_safefree(ptr) \
  do { free((ptr)); (ptr) = NULL;} while(0)
extern CURLcode Curl_setstropt(char **charp, const char *s);
extern CURLcode setstropt_userpwd(char *option, char **userp, char **passwdp);
extern CURLcode setstropt_interface(char *option, char **devp,
                                    char **ifacep, char **hostp);
extern CURLcode protocol2num(const char *str, curl_prot_t *val);
extern CURLcode Curl_urldecode(const char *string, size_t length,
                               char **ostring, size_t *olen, int ctrl);
extern bool Curl_ssl_supports(struct Curl_easy *data, unsigned int ssl_option);
extern CURLcode Curl_ssl_set_engine(struct Curl_easy *data, const char *engine);
extern void *Curl_memdup0(const char *src, size_t length);
extern void Curl_all_content_encodings(char *buf, size_t blen);
extern int strcmp(const char *s1, const char *s2);
extern void *memset(void *s, int c, size_t n);
extern void Curl_auth_digest_cleanup(struct digestdata *digest);
