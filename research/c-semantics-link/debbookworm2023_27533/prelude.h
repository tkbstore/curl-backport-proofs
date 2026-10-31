/*
 * CVE-2023-27533 bookworm（research/backport-proof-debian/cases/bookworm/CVE-2023-27533.md）の翻訳単位の前置き。4つの翻訳単位で共通。
 *
 * 出典: input/（auto/build.py の出力）。U1 上流 538b1e79a6、U0 上流 674a0662cf、D1 curl-7_88_1 に Debian の CVE-2023-27533.patch を当てたもの、D0 curl-7_88_1
 * ビルドの構成: telnet を無効にしない（CURL_DISABLE_TELNET を定義しない）
 * - 構造体は、対象の関数が触るフィールドだけに減らした
 *     struct curl_slist                include/curl/curl.h  data、next
 *     struct TELNET                    lib/telnet.c         us_preferred、him_preferred、subopt_ttype、subopt_xdisploc、
 *                                                           subopt_wsx、subopt_wsy、telnet_vars
 *     struct connectdata               lib/urldata.h        user
 *     struct Curl_easy                 lib/urldata.h        conn、req.p.telnet、state.aptr.user、set.telnet_options
 *   req.p は lib/urldata.h では union（各プロトコルの状態へのポインタ）。メンバを telnet の1つに減らしたので、
 *   同じ配置の struct にした（オフセットは 0 で変わらない）
 * - マクロの展開: NULL は ((void *)0)、TRUE は 1、FALSE は 0（lib/curl_setup_once.h）、CURL_NO は 0、CURL_YES は 1（lib/telnet.c）、
 *   CURL_TELOPT_* は lib/arpa_telnet.h の値、msnprintf は curl_msnprintf（lib/curl_printf.h）、
 *   strcasecompare・strncasecompare は Curl_strcasecompare・Curl_strncasecompare（lib/strcase.h）、failf は Curl_failf（lib/sendf.h）
 * - CURLcode は include/curl/curl.h（curl-7_88_1）の値のうち、対象の関数が使う5つだけを並べた
 * - 呼ばれる側の関数は extern の宣言（仕様は Lean 側で定理の仮定として与える）
 * - 逸脱: curl_msnprintf の宣言を、可変長でなく4つの固定の引数にした（宣言の前の注を見よ）
 */
#define NULL ((void *)0)
#define TRUE 1
#define FALSE 0
#define CURL_NO 0
#define CURL_YES 1
#define CURL_TELOPT_BINARY 0
#define CURL_TELOPT_TTYPE 24
#define CURL_TELOPT_NAWS 31
#define CURL_TELOPT_XDISPLOC 35
#define CURL_TELOPT_NEW_ENVIRON 39

typedef _Bool bool;
typedef unsigned long size_t;

typedef enum {
  CURLE_OK = 0,
  CURLE_OUT_OF_MEMORY = 27,
  CURLE_BAD_FUNCTION_ARGUMENT = 43,
  CURLE_UNKNOWN_OPTION = 48,
  CURLE_SETOPT_OPTION_SYNTAX = 49
} CURLcode;

struct curl_slist {
  char *data;
  struct curl_slist *next;
};

struct TELNET {
  int us_preferred[256];
  int him_preferred[256];
  char subopt_ttype[32];
  char subopt_xdisploc[128];
  unsigned short subopt_wsx;
  unsigned short subopt_wsy;
  struct curl_slist *telnet_vars;
};

struct connectdata {
  char *user;
};

struct dynamically_allocated_data {
  char *user;
};

struct UrlState {
  struct dynamically_allocated_data aptr;
};

struct UserDefined {
  struct curl_slist *telnet_options;
};

struct SingleRequest {
  struct {
    struct TELNET *telnet;
  } p;
};

struct Curl_easy {
  struct connectdata *conn;
  struct SingleRequest req;
  struct UrlState state;
  struct UserDefined set;
};

#define msnprintf curl_msnprintf
#define strcasecompare(a, b) Curl_strcasecompare(a, b)
#define strncasecompare(a, b, c) Curl_strncasecompare(a, b, c)
#define failf Curl_failf

extern size_t strlen(const char *s);
/* 逸脱: curl_msnprintf は可変長引数（include/curl/mprintf.h）。Clight の呼び出しの規則は宣言の型の並びと引数の数が合わないと
 * 進めない（research/c-semantics-link/RESULTS.md の Case 3 の記録）。この関数での呼び出しは4つの引数の1か所だけなので、
 * その4つを並べた固定の引数の宣言にした。仕様は Lean 側で仮定する。sscanf・Curl_failf は性質の経路に無いので可変長のまま */
extern int curl_msnprintf(char *buffer, size_t maxlength, const char *format, const char *arg);
extern struct curl_slist *curl_slist_append(struct curl_slist *list, const char *data);
extern void curl_slist_free_all(struct curl_slist *list);
extern void Curl_failf(struct Curl_easy *data, const char *fmt, ...);
extern int Curl_strcasecompare(const char *first, const char *second);
extern int Curl_strncasecompare(const char *first, const char *second, size_t max);
extern char *strchr(const char *s, int c);
extern char *strncpy(char *dest, const char *src, size_t n);
extern unsigned long strtoul(const char *nptr, char **endptr, int base);
extern int atoi(const char *nptr);
extern int sscanf(const char *str, const char *format, ...);
extern char Curl_raw_tolower(char in);
