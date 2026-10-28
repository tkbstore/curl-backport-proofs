/*
 * CVE-2026-8924（research/backport-proof-debian/cases/CVE-2026-8924.md）の翻訳単位の前置き。
 * U（上流 51beed175d・614b94eecc）と D（curl 8.14.1）で共通。違うところは SIDE_U・SIDE_D で分けた。
 *
 * ビルドの構成: USE_LIBPSL を定義する。DEBUGF は DEBUGBUILD でない側（lib/curl_setup_once.h、何もしない）。
 *   infof は CURL_DISABLE_VERBOSE_STRINGS の側（上流 lib/curl_trc.h の定義、何もしない）。P1・P0 の経路は infof に達しない
 * - struct Cookie は name・domain だけに減らした（lib/cookie.h、並びは宣言順）
 * - CERR_OK・CERR_PSL は lib/cookie.c の値（8.14.1）。TRUE・FALSE
 * - 呼ばれる側の関数は extern の宣言（仕様は Lean 側で定理の仮定として与える）
 *     strlen、Curl_host_is_ipnum（lib/curlx/inet_pton.h ほか）、Curl_psl_use・Curl_psl_release（lib/psl.h）、
 *     Curl_strntolower（lib/strcase.h）、psl_is_cookie_domain_acceptable（libpsl.h）
 */
#define USE_LIBPSL 1

typedef _Bool bool;
#define NULL ((void *)0)
#define TRUE 1
#define FALSE 0
typedef unsigned long size_t;

#define DEBUGF(x) do { } while(0)
#define infof(data, ...) do { (void)(data); } while(0)

#define CERR_OK            0
#define CERR_PSL          14

struct Curl_easy;
typedef struct psl_ctx_st psl_ctx_t;

struct Cookie {
  char *name;
  char *domain;
};

extern size_t strlen(const char *s);
extern bool Curl_host_is_ipnum(const char *hostname);
extern const psl_ctx_t *Curl_psl_use(struct Curl_easy *easy);
extern void Curl_psl_release(struct Curl_easy *easy);
extern void Curl_strntolower(char *dest, const char *src, size_t n);
extern int psl_is_cookie_domain_acceptable(const psl_ctx_t *psl, const char *hostname,
                                           const char *cookie_domain);
