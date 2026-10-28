/*
 * CVE-2026-3784（research/backport-proof-debian/cases/CVE-2026-3784.md）の翻訳単位の前置き。
 * C1 の PROTOCOL §4 で許した「関数の外側の変更」だけを置く。
 *
 * 出典: curl 5f13a7645e（U1）と親 e47b6e657a（U0）
 * 構成: CURL_DISABLE_PROXY を定義しない
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl の lib/urldata.h の宣言順を保つ）
 *     struct hostname    name
 *     struct proxy_info  host, port, proxytype, user, passwd
 * - strcasecompare は 8.14.1 の lib/strcase.h:38 の形（D 側だけが使う）
 * - curl_strequal（include/curl/curl.h）・Curl_timestrcmp（lib/strcase.h）は extern の宣言（仕様は Lean 側で定理の仮定として与える）
 */
typedef unsigned short uint16_t;
typedef unsigned char uint8_t;
typedef _Bool bool;
#define TRUE 1
#define FALSE 0

struct hostname {
  char *name;
};

struct proxy_info {
  struct hostname host;
  uint16_t port;
  uint8_t proxytype;
  char *user;
  char *passwd;
};

extern int curl_strequal(const char *s1, const char *s2);
extern int Curl_timestrcmp(const char *first, const char *second);

