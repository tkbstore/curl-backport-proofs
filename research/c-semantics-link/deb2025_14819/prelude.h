/*
 * CVE-2025-14819（research/backport-proof-debian/cases/CVE-2025-14819.md）の翻訳単位の前置き。4つの翻訳単位で共通。
 *
 * 出典: 上流 cd046f6c93（修正後）・be3c226bb0（修正前）、curl 8.14.1（修正前）とそれに Debian の CVE-2025-14819.patch を当てたもの
 * ビルドの構成: USE_OPENSSL。HAVE_STDINT_H を定義する
 * - 構造体は、対象の関数が触るフィールドだけに減らした
 *     struct ssl_primary_config  lib/urldata.h        CAfile
 *     struct ssl_config_data     lib/urldata.h        no_partialchain（ビット）
 *     struct ossl_x509_share     lib/vtls/openssl.c   CAfile、no_partialchain（ビット。修正後だけにある）
 *   上流の修正後の ossl_x509_share には store_is_empty（ビット）もあるが、対象の関数は読まないので外した。
 *   このため4つの翻訳単位で構造体の形は同じになる（修正前は no_partialchain が無い）
 * - マクロの展開: BIT(x) は `bit x:1`（lib/curl_setup_once.h、bit は unsigned int）、TRUE は 1（lib/curl_setup_once.h）、
 *   CURL_UNCONST(p) は `((void *)(uintptr_t)(const void *)(p))`（lib/curl_setup_once.h、HAVE_STDINT_H のとき）
 * - 呼ばれる側の関数3つは extern の宣言（仕様は Lean 側で定理の仮定として与える）
 *     Curl_ssl_cf_get_primary_config  lib/vtls/vtls.h
 *     Curl_ssl_cf_get_config          lib/vtls/vtls.h（修正後の関数だけが呼ぶ）
 *     strcmp
 */
#define USE_OPENSSL 1
#define TRUE 1
#define FALSE 0

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

#ifdef DEB2025_14819_AFTER
struct ossl_x509_share {
  char *CAfile;
  BIT(no_partialchain);
};
#else
struct ossl_x509_share {
  char *CAfile;
};
#endif

extern struct ssl_primary_config *
  Curl_ssl_cf_get_primary_config(struct Curl_cfilter *cf);
extern struct ssl_config_data *Curl_ssl_cf_get_config(struct Curl_cfilter *cf,
                                                      struct Curl_easy *data);
extern int strcmp(const char *s1, const char *s2);
