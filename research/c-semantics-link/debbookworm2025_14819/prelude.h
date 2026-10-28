/*
 * CVE-2025-14819 bookworm（research/backport-proof-debian/cases/bookworm/CVE-2025-14819.md）の翻訳単位の前置き。4つの翻訳単位で共通。
 *
 * 出典: input/（auto/build.py の出力）。U1 上流 cd046f6c93、U0 上流 be3c226bb0、D1 curl-7_88_1 に Debian の CVE-2025-14819.patch を当てたもの、D0 curl-7_88_1
 * ビルドの構成: USE_OPENSSL、HAVE_SSL_X509_STORE_SHARE。HAVE_STDINT_H を定義する
 * - 構造体は、対象の関数が触るフィールドだけに減らした
 *     struct ssl_primary_config      lib/urldata.h        CAfile
 *     struct ssl_config_data         lib/urldata.h        no_partialchain（ビット）
 *     struct ossl_x509_share         lib/vtls/openssl.c   CAfile、no_partialchain（ビット。修正後だけ）  U1・U0
 *     struct multi_ssl_backend_data  lib/vtls/openssl.c   CAfile、no_partialchain（ビット。修正後だけ）  D1・D0
 *   上流の ossl_x509_share の store_is_empty など、7.88.1 の multi_ssl_backend_data の store・time は、対象の関数が読まないので外した。
 *   キャッシュの構造体は、翻訳単位ごとにその版の名前のものだけを置く（DEBBW_UP・DEBBW_AFTER で選ぶ）
 * - マクロの展開: BIT(x) は `bit x:1`（lib/curl_setup_once.h、bit は unsigned int）、TRUE は 1（lib/curl_setup_once.h）、
 *   true は 1（stdbool.h）、CURL_UNCONST(p) は `((void *)(uintptr_t)(const void *)(p))`（上流の lib/curl_setup_once.h、HAVE_STDINT_H のとき）
 * - 呼ばれる側の関数3つは extern の宣言（仕様は Lean 側で定理の仮定として与える）
 *     Curl_ssl_cf_get_primary_config  lib/vtls/vtls.h
 *     Curl_ssl_cf_get_config          lib/vtls/vtls.h（修正後の関数だけが呼ぶ）
 *     strcmp
 */
#define USE_OPENSSL 1
#define HAVE_SSL_X509_STORE_SHARE 1
#define TRUE 1
#define FALSE 0
#define true 1
#define false 0

typedef _Bool bool;
typedef unsigned int bit;
typedef unsigned long uintptr_t;
#define BIT(x) bit x:1
#define CURL_UNCONST(p) ((void *)(uintptr_t)(const void *)(p))

struct Curl_cfilter;
struct Curl_easy;

struct ssl_primary_config {
  char *CAfile;
};

struct ssl_config_data {
  BIT(no_partialchain);
};

#ifdef DEBBW_UP
struct ossl_x509_share {
  char *CAfile;
#ifdef DEBBW_AFTER
  BIT(no_partialchain);
#endif
};
#else
struct multi_ssl_backend_data {
  char *CAfile;
#ifdef DEBBW_AFTER
  BIT(no_partialchain);
#endif
};
#endif

extern struct ssl_primary_config *
  Curl_ssl_cf_get_primary_config(struct Curl_cfilter *cf);
extern struct ssl_config_data *Curl_ssl_cf_get_config(struct Curl_cfilter *cf,
                                                      struct Curl_easy *data);
extern int strcmp(const char *s1, const char *s2);
