/*
 * CVE-2026-7168（research/backport-proof-debian/cases/CVE-2026-7168.md）の上流側（U1・U0）の翻訳単位の前置き。
 * C1 の PROTOCOL §4 で許した「関数の外側の変更」だけを置く。
 *
 * 出典: curl c1cfdf59acbaf9504c4578d4cf56cdd7c8594507（U1）と親 7586ca74558b7b0b21b2b8c83882172a6bc470eb（U0）
 * 構成: cases/CVE-2026-7168.md の「構成」（下の #define）
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl の宣言順を保つ）
 *     struct ssl_config_data  lib/urldata.h   custom_cafile, custom_capath
 *     struct UserDefined      lib/urldata.h   proxy_ssl, str, haproxyprotocol
 *     struct digestdata       lib/vauth/vauth.h  nonce（Curl_auth_digest_cleanup の仕様を述べるためだけに残す）
 *     struct auth             lib/urldata.h:597  picked（memset の対象。証明で見るフィールドだけに減らした）
 *     struct UrlState         lib/urldata.h   proxydigest, authproxy
 *     struct Curl_easy        lib/urldata.h   set, state
 * - enum dupstring は lib/urldata.h から、CURLoption は include/curl/curl.h から extract.py が作った（enum_u.h・opt_u.h）
 * - CURLcode は使う値だけ（include/curl/curl.h と同じ値）。SSLSUPP_* は lib/vtls/vtls.h、REJECT_ZERO は lib/escape.h
 * - curlx_safefree は lib/curl_setup.h の形。curlx_free は関数として宣言した（CVE-2026-8927 と同じ）
 * - setstropt_userpwd は lib/setopt.c の static 関数だが extern にした
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
typedef unsigned int uint32_t;
typedef _Bool bool;
#define TRUE 1
#define FALSE 0
#define NULL ((void *)0)

typedef unsigned int curl_bit;
#define BIT(x) curl_bit x:1

#define SSLSUPP_CA_PATH      (1 << 0)
#define SSLSUPP_PINNEDPUBKEY (1 << 2)
#define SSLSUPP_TLS13_CIPHERSUITES (1 << 5)
#define SSLSUPP_CIPHER_LIST  (1 << 9)
#define REJECT_ZERO 4

typedef enum {
  CURLE_OK = 0,
  CURLE_NOT_BUILT_IN = 4,
  CURLE_UNKNOWN_OPTION = 48
} CURLcode;

#include "opt_u.h"
#include "enum_u.h"

struct ssl_config_data {
  BIT(custom_cafile);
  BIT(custom_capath);
};

struct UserDefined {
  struct ssl_config_data proxy_ssl;
  char *str[STRING_LAST];
  BIT(haproxyprotocol);
};

struct digestdata {
  char *nonce;
};

struct auth {
  uint32_t picked;
};

struct UrlState {
  struct digestdata proxydigest;
  struct auth authproxy;
};

struct Curl_easy {
  struct UserDefined set;
  struct UrlState state;
};

extern void curlx_free(void *ptr);
#define curlx_safefree(ptr) \
  do {                      \
    curlx_free(ptr);        \
    (ptr) = NULL;           \
  } while(0)
extern CURLcode Curl_setstropt(char **charp, const char *s);
extern CURLcode setstropt_userpwd(const char *option, char **userp, char **passwdp);
extern CURLcode Curl_urldecode(const char *string, size_t length,
                               char **ostring, size_t *olen, int ctrl);
extern bool Curl_ssl_supports(struct Curl_easy *data, unsigned int ssl_option);
extern int strcmp(const char *s1, const char *s2);
extern void *memset(void *s, int c, size_t n);
extern void Curl_auth_digest_cleanup(struct digestdata *digest);
