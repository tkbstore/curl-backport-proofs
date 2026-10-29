/*
 * Case 4 (CURL-CVE-2025-13034) の翻訳単位の前置き。PROTOCOL §4 で許した「関数の外側の変更」だけを置く。
 *
 * 出典: curl 3d91ca8cdb3b434226e743946d428b4dd3acf2c9（修正後）と親 dc34498d18d3303d67364423b4aa0daab4afb3ba（修正前）
 * ビルドの構成: TLS のバックエンドは GnuTLS（USE_GNUTLS）。USE_OPENSSL・USE_WOLFSSL は定義しない
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl の宣言順を保つ）
 *     struct gtls_ctx            lib/vtls/gtls.h:67        session
 *     struct curl_tls_ctx        lib/vquic/vquic-tls.h:42  gtls
 *     struct ssl_primary_config  lib/urldata.h:240         verifyhost（修正前の関数だけが読む）
 *     struct ssl_config_data     lib/urldata.h:267         primary（&data->set.ssl を取るため、型を完全にする最初のフィールド）
 *     struct UserDefined         lib/urldata.h:1318        ssl, str
 *     struct Curl_easy                                      set
 *     struct ssl_peer            lib/vtls/vtls.h:85        scache_key
 * - enum dupstring は lib/urldata.h:1170 をそのまま写した（下の enum.h）。STRING_SSL_PINNEDPUBLICKEY の添字を変えないため
 * - CURLcode は使う2つの値だけ（include/curl/curl.h と同じ値）
 * - 呼ばれる側の関数3つは extern の宣言（仕様は Lean 側で定理の仮定として与える）
 *     Curl_ssl_cf_get_primary_config  lib/vtls/vtls.h:243
 *     Curl_gtls_verifyserver          lib/vtls/gtls.h:103
 *     Curl_ssl_scache_remove_all      lib/vtls/vtls_scache.h:199
 */
#define USE_GNUTLS 1

typedef unsigned int curl_bit;
#define BIT(x) curl_bit x:1

typedef enum {
  CURLE_OK = 0,
  CURLE_FAILED_INIT = 2
} CURLcode;

#include "enum_u.h"

struct Curl_cfilter;
struct gnutls_session_int;
typedef struct gnutls_session_int *gnutls_session_t;

struct gtls_ctx {
  gnutls_session_t session;
};

struct curl_tls_ctx {
  struct gtls_ctx gtls;
};

struct ssl_primary_config {
  BIT(verifyhost);
};

struct ssl_config_data {
  struct ssl_primary_config primary;
};

struct UserDefined {
  struct ssl_config_data ssl;
  char *str[STRING_LAST];
};

struct Curl_easy {
  struct UserDefined set;
};

struct ssl_peer {
  char *scache_key;
};

extern struct ssl_primary_config *
  Curl_ssl_cf_get_primary_config(struct Curl_cfilter *cf);
extern CURLcode Curl_gtls_verifyserver(struct Curl_cfilter *cf,
                                       struct Curl_easy *data,
                                       gnutls_session_t session,
                                       struct ssl_primary_config *config,
                                       struct ssl_config_data *ssl_config,
                                       struct ssl_peer *peer,
                                       const char *pinned_key);
extern void Curl_ssl_scache_remove_all(struct Curl_cfilter *cf,
                                       struct Curl_easy *data,
                                       const char *ssl_peer_key);
