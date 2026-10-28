/*
 * CVE-2026-3805（research/backport-proof-debian/cases/CVE-2026-3805.md）の翻訳単位の前置き。4つの翻訳単位で共通。
 *
 * 出典: 上流 e090be9f73（修正後）・22b0cbe65f（修正前）、curl 8.14.1（修正前）とそれに Debian の CVE-2026-3805.patch を当てたもの
 * ビルドの構成: CURL_DISABLE_SMB を定義しない、USE_CURL_NTLM_CORE を定義する。CURL_MEMDEBUG は定義しない、BUILDING_LIBCURL を定義する
 * - 構造体は、対象の関数が触るフィールドだけに減らした
 *     struct urlpieces   lib/urldata.h   path
 *     struct UrlState    lib/urldata.h   up
 *     struct Curl_easy   lib/urldata.h   state
 *     struct smb_conn    lib/smb.c       share
 *     struct smb_request lib/smb.c       path
 * - CURLcode は使う3つの値だけ（include/curl/curl.h と同じ値）。enum urlreject は lib/escape.h と同じ値
 * - マクロの展開（curl の定義どおり）
 *     curlx_strdup → Curl_cstrdup、curlx_free → Curl_cfree   上流 lib/curl_setup.h（!CURL_MEMDEBUG かつ BUILDING_LIBCURL）
 *     strdup(p) → Curl_cstrdup(p)、free(p) → Curl_cfree(p)     8.14.1 lib/curl_memory.h
 *     Curl_safefree(p)                                        8.14.1 lib/memdebug.h の定義。上流 lib/curl_setup.h の定義は
 *                                                             `do { curlx_free(ptr); (ptr) = NULL; } while(0)` で、展開後は括弧の数だけが違う
 *     failf → Curl_failf                                      lib/curl_trc.h
 * - 呼ばれる側の関数は extern の宣言（仕様は Lean 側で定理の仮定として与える）
 *     Curl_cstrdup・Curl_cfree は curl では大域の関数ポインタ（curl_strdup_callback・curl_free_callback）だが、関数として宣言した。
 *     本体のトークン（`Curl_cstrdup(x)`）は同じで、呼ばれる関数の仕様を仮定する点も同じ
 */
#define USE_CURL_NTLM_CORE 1
#define NULL ((void *)0)

typedef unsigned long size_t;

typedef enum {
  CURLE_OK = 0,
  CURLE_URL_MALFORMAT = 3,
  CURLE_OUT_OF_MEMORY = 27
} CURLcode;

enum urlreject {
  REJECT_NADA = 2,
  REJECT_CTRL,
  REJECT_ZERO
};

struct urlpieces {
  char *path;
};

struct UrlState {
  struct urlpieces up;
};

struct Curl_easy {
  struct UrlState state;
};

struct smb_conn {
  char *share;
};

struct smb_request {
  char *path;
};

#define curlx_strdup Curl_cstrdup
#define curlx_free Curl_cfree
#define strdup(ptr) Curl_cstrdup(ptr)
#define free(ptr) Curl_cfree(ptr)
#define Curl_safefree(ptr) \
  do { free((ptr)); (ptr) = NULL;} while(0)
#define failf Curl_failf

extern CURLcode Curl_urldecode(const char *string, size_t length,
                               char **ostring, size_t *olen,
                               enum urlreject ctrl);
extern char *Curl_cstrdup(const char *str);
extern void Curl_cfree(void *ptr);
extern char *strchr(const char *s, int c);
extern void Curl_failf(struct Curl_easy *data, const char *fmt, ...);
