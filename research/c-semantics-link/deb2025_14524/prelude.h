/*
 * CVE-2025-14524（research/backport-proof-debian/cases/CVE-2025-14524.md）の翻訳単位の前置き。
 * U（上流 1a822275d3・bb134bba29）と D（curl 8.14.1）で共通。違うところは SIDE_U・SIDE_D で分けた。
 *
 * ビルドの構成: CURL_DISABLE_DIGEST_AUTH を定義し、USE_KERBEROS5・USE_GSASL・USE_NTLM は定義しない。
 *   この構成で Curl_sasl_start が選びうるのは EXTERNAL・OAUTHBEARER・XOAUTH2・PLAIN・LOGIN の5つ。
 * - lib/curl_sasl.h の SASL_MECH_*・SASL_MECH_STRING_*・saslstate・saslprogress・struct SASLproto・struct SASL は
 *   そのまま写した（8.14.1 と上流で同じ）
 * - struct bufref は lib/bufref.h（DEBUGBUILD でない側）
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl の宣言順を保つ）
 *     struct connectdata        lib/urldata.h  user, passwd, sasl_authzid
 *     struct dynamically_allocated_data（UrlState の aptr）  user
 *     struct UrlState           lib/urldata.h  aptr, this_is_a_follow
 *     struct UserDefined        lib/urldata.h  str, allow_auth_to_other_hosts, sasl_ir
 *     struct Curl_easy          lib/urldata.h  conn, set, state
 * - enum dupstring は各版の lib/urldata.h を extract.py が切り出した（enum_u.h・enum_d.h）
 * - CURLcode は使う値だけ（include/curl/curl.h と同じ値）。FIRSTSOCKET は lib/urldata.h と同じ 0
 * - DEBUGASSERT は DEBUGBUILD でない側の定義（何もしない）
 * - 呼ばれる側の関数は extern の宣言（仕様は Lean 側で定理の仮定として与える）
 *     Curl_conn_get_host（D）・Curl_conn_get_current_host（U）  lib/connect.h・lib/cfilters.h
 *     Curl_bufref_init・Curl_bufref_ptr・Curl_bufref_len・Curl_bufref_free  lib/bufref.h
 *       （Curl_bufref_ptr の戻り値は 8.14.1 が const unsigned char *、上流が const char *）
 *     Curl_auth_create_external_message・_oauth_bearer_message・_xoauth_bearer_message・
 *       _plain_message・_login_message  lib/vauth/vauth.h
 *     build_message・sasl_state  lib/curl_sasl.c（元は static）
 *     memset・strlen
 */
#define CURL_DISABLE_DIGEST_AUTH 1

typedef _Bool bool;
#define NULL ((void *)0)
#define TRUE 1
#define FALSE 0
typedef unsigned long size_t;

typedef unsigned int curl_bit;
#define BIT(x) curl_bit x:1

#define DEBUGASSERT(x) do { } while(0)
#define FIRSTSOCKET 0

typedef enum {
  CURLE_OK = 0
} CURLcode;

#define SASL_MECH_LOGIN             (1 << 0)
#define SASL_MECH_PLAIN             (1 << 1)
#define SASL_MECH_CRAM_MD5          (1 << 2)
#define SASL_MECH_DIGEST_MD5        (1 << 3)
#define SASL_MECH_GSSAPI            (1 << 4)
#define SASL_MECH_EXTERNAL          (1 << 5)
#define SASL_MECH_NTLM              (1 << 6)
#define SASL_MECH_XOAUTH2           (1 << 7)
#define SASL_MECH_OAUTHBEARER       (1 << 8)
#define SASL_MECH_SCRAM_SHA_1       (1 << 9)
#define SASL_MECH_SCRAM_SHA_256     (1 << 10)

#define SASL_MECH_STRING_LOGIN          "LOGIN"
#define SASL_MECH_STRING_PLAIN          "PLAIN"
#define SASL_MECH_STRING_CRAM_MD5       "CRAM-MD5"
#define SASL_MECH_STRING_DIGEST_MD5     "DIGEST-MD5"
#define SASL_MECH_STRING_GSSAPI         "GSSAPI"
#define SASL_MECH_STRING_EXTERNAL       "EXTERNAL"
#define SASL_MECH_STRING_NTLM           "NTLM"
#define SASL_MECH_STRING_XOAUTH2        "XOAUTH2"
#define SASL_MECH_STRING_OAUTHBEARER    "OAUTHBEARER"
#define SASL_MECH_STRING_SCRAM_SHA_1    "SCRAM-SHA-1"
#define SASL_MECH_STRING_SCRAM_SHA_256  "SCRAM-SHA-256"

typedef enum {
  SASL_STOP,
  SASL_PLAIN,
  SASL_LOGIN,
  SASL_LOGIN_PASSWD,
  SASL_EXTERNAL,
  SASL_CRAMMD5,
  SASL_DIGESTMD5,
  SASL_DIGESTMD5_RESP,
  SASL_NTLM,
  SASL_NTLM_TYPE2MSG,
  SASL_GSSAPI,
  SASL_GSSAPI_TOKEN,
  SASL_GSSAPI_NO_DATA,
  SASL_OAUTH2,
  SASL_OAUTH2_RESP,
  SASL_GSASL,
  SASL_CANCEL,
  SASL_FINAL
} saslstate;

typedef enum {
  SASL_IDLE,
  SASL_INPROGRESS,
  SASL_DONE
} saslprogress;

struct Curl_easy;

struct bufref {
  void (*dtor)(void *);
  const unsigned char *ptr;
  size_t len;
};

struct SASLproto {
  const char *service;
  CURLcode (*sendauth)(struct Curl_easy *data, const char *mech,
                       const struct bufref *ir);
  CURLcode (*contauth)(struct Curl_easy *data, const char *mech,
                       const struct bufref *contauth);
  CURLcode (*cancelauth)(struct Curl_easy *data, const char *mech);
  CURLcode (*getmessage)(struct Curl_easy *data, struct bufref *out);
  size_t maxirlen;
  int contcode;
  int finalcode;
  unsigned short defmechs;
  unsigned short flags;
};

struct SASL {
  const struct SASLproto *params;
  saslstate state;
  const char *curmech;
  unsigned short authmechs;
  unsigned short prefmech;
  unsigned short authused;
  BIT(resetprefs);
  BIT(mutual_auth);
  BIT(force_ir);
};

struct connectdata {
  char *user;
  char *passwd;
  char *sasl_authzid;
};

struct dynamically_allocated_data {
  char *user;
};

struct UrlState {
  struct dynamically_allocated_data aptr;
  BIT(this_is_a_follow);
};

struct UserDefined {
  char *str[STRING_LAST];
  BIT(allow_auth_to_other_hosts);
  BIT(sasl_ir);
};

struct Curl_easy {
  struct connectdata *conn;
  struct UserDefined set;
  struct UrlState state;
};

extern void Curl_conn_get_host(struct Curl_easy *data, int sockindex,
                               const char **phost, const char **pdisplay_host,
                               int *pport);
extern void Curl_conn_get_current_host(struct Curl_easy *data, int sockindex,
                                       const char **phost, int *pport);
extern void Curl_bufref_init(struct bufref *br);
#ifdef SIDE_U
extern const char *Curl_bufref_ptr(const struct bufref *br);
#else
extern const unsigned char *Curl_bufref_ptr(const struct bufref *br);
#endif
extern size_t Curl_bufref_len(const struct bufref *br);
extern void Curl_bufref_free(struct bufref *br);
extern void Curl_auth_create_external_message(const char *user,
                                              struct bufref *out);
extern CURLcode Curl_auth_create_oauth_bearer_message(const char *user,
                                                      const char *host,
                                                      const long port,
                                                      const char *bearer,
                                                      struct bufref *out);
extern CURLcode Curl_auth_create_xoauth_bearer_message(const char *user,
                                                       const char *bearer,
                                                       struct bufref *out);
extern CURLcode Curl_auth_create_plain_message(const char *authzid,
                                               const char *authcid,
                                               const char *passwd,
                                               struct bufref *out);
extern void Curl_auth_create_login_message(const char *value,
                                           struct bufref *out);
extern CURLcode build_message(struct SASL *sasl, struct bufref *msg);
extern void sasl_state(struct SASL *sasl, struct Curl_easy *data,
                       saslstate newstate);
extern void *memset(void *s, int c, size_t n);
extern size_t strlen(const char *s);
