/*
 * CVE-2026-3783（research/backport-proof-debian/cases/CVE-2026-3783.md）の翻訳単位の前置き。
 * U（上流 e3d7401a32・1495489c41）と D（curl 8.14.1）で共通。違うところは SIDE_U・SIDE_D で分けた。
 *
 * ビルドの構成: CURL_DISABLE_AWS・CURL_DISABLE_DIGEST_AUTH を定義し、USE_SPNEGO・USE_NTLM は定義しない。
 *   Basic・Bearer・プロキシは有効のまま。
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl の宣言順を保つ）
 *     struct auth                lib/urldata.h（全フィールド。U は uint32_t、D は unsigned long）
 *     struct ConnectBits         lib/urldata.h  proxy_user_passwd
 *     struct connectdata         lib/urldata.h  bits
 *     struct dynamically_allocated_data（UrlState の aptr）  user, proxyuser
 *     struct UrlState            lib/urldata.h  aptr
 *     struct UserDefined         lib/urldata.h  str
 *     struct Curl_easy           lib/urldata.h  set, state
 * - enum dupstring は各版の lib/urldata.h を extract.py が切り出した（enum_u.h・enum_d.h）
 * - CURLcode は使う値だけ（include/curl/curl.h と同じ値）
 * - CURLAUTH_BASIC・CURLAUTH_BEARER（include/curl/curl.h）、STRCONST（lib/curl_setup.h）、TRUE・FALSE
 * - infof は lib/curl_trc.h の C99 でない側の定義（#define infof Curl_infof）
 * - 呼ばれる側の関数は extern の宣言（仕様は Lean 側で定理の仮定として与える）
 *     Curl_checkProxyheaders    lib/http.h
 *     Curl_checkheaders         lib/transfer.h
 *     Curl_auth_allowed_to_host lib/vauth/vauth.h
 *     http_output_basic・http_output_bearer  lib/http.c（元は static）
 *     Curl_infof                lib/curl_trc.h
 */
#define CURL_DISABLE_AWS 1
#define CURL_DISABLE_DIGEST_AUTH 1

typedef _Bool bool;
#define NULL ((void *)0)
#define TRUE 1
#define FALSE 0
typedef unsigned long size_t;
typedef unsigned int uint32_t;

typedef unsigned int curl_bit;
#define BIT(x) curl_bit x:1

typedef enum {
  CURLE_OK = 0
} CURLcode;

#define CURLAUTH_BASIC        (((unsigned long)1)<<0)
#define CURLAUTH_BEARER       (((unsigned long)1)<<6)
#define STRCONST(x) x,sizeof(x)-1
#define infof Curl_infof

struct auth {
#ifdef SIDE_U
  uint32_t want;
  uint32_t picked;
  uint32_t avail;
#else
  unsigned long want;
  unsigned long picked;
  unsigned long avail;
#endif
  BIT(done);
  BIT(multipass);
  BIT(iestyle);
};

struct ConnectBits {
  BIT(proxy_user_passwd);
};

struct connectdata {
  struct ConnectBits bits;
};

struct dynamically_allocated_data {
  char *user;
  char *proxyuser;
};

struct UrlState {
  struct dynamically_allocated_data aptr;
};

struct UserDefined {
  char *str[STRING_LAST];
};

struct Curl_easy {
  struct UserDefined set;
  struct UrlState state;
};

extern char *Curl_checkProxyheaders(struct Curl_easy *data,
                                    const struct connectdata *conn,
                                    const char *thisheader,
                                    const size_t thislen);
extern char *Curl_checkheaders(const struct Curl_easy *data,
                               const char *thisheader,
                               const size_t thislen);
extern bool Curl_auth_allowed_to_host(struct Curl_easy *data);
extern CURLcode http_output_basic(struct Curl_easy *data, bool proxy);
extern CURLcode http_output_bearer(struct Curl_easy *data);
extern void Curl_infof(struct Curl_easy *data, const char *fmt, ...);
