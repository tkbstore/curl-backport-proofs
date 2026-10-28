/*
 * CVE-2026-8286 の翻訳単位（D1・D0）の前置き。PROTOCOL §4 で許した「関数の外側の変更」だけを置く。
 * 出典: curl 8.14.1: struct Curl_handler（lib/urldata.h:574）、connectdata の handler（lib/urldata.h:800）
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは宣言順を保つ）
 *     struct Curl_handler    protocol, family, flags
 *     struct connectdata   handler
 *     struct url_conn_match（lib/url.c）  data, needle, may_tls, require_tls, req_tls
 *       修正後（U1・D1）は may_tls・require_tls を、修正前（U0・D0）は req_tls を読む。修正で req_tls が
 *       may_tls・require_tls に置き換わったので、減らした構造体には3つとも置いた（読まないものは関数に影響しない）
 * - マクロは curl の非デバッグビルドの定義をそのまま写した（BIT・TRUE・FALSE・DEBUGASSERT・DEBUGF、PROTOPT_SSL、PROTOPT_SSL_REUSE、FIRSTSOCKET）
 * - extern の宣言: Curl_conn_is_ssl（lib/cfilters.h）、Curl_ssl_conn_config_match（lib/vtls/vtls_config.h）。
 *   get_protocol_family は同じ翻訳単位の static 関数なので本体ごと入れる
 */
#include <stdbool.h>
#include <stdint.h>

typedef long curl_off_t;
typedef curl_off_t curl_prot_t;
typedef unsigned int curl_bit;

#define BIT(x) curl_bit x:1
#define TRUE true
#define FALSE false
#define DEBUGF(x) do {} while(0)
#define DEBUGASSERT(x) do {} while(0)

#define PROTOPT_SSL (1<<0)
#define PROTOPT_SSL_REUSE (1<<15)
#define FIRSTSOCKET 0

struct Curl_easy;

struct Curl_handler {
  curl_prot_t protocol;
  curl_prot_t family;
  unsigned int flags;
};

struct connectdata {
  const struct Curl_handler *handler;
};

struct url_conn_match {
  struct Curl_easy *data;
  struct connectdata *needle;
  BIT(may_tls);
  BIT(require_tls);
  BIT(req_tls);
};

extern bool Curl_conn_is_ssl(struct connectdata *conn, int8_t sockindex);
extern bool Curl_ssl_conn_config_match(struct Curl_easy *data,
                                       struct connectdata *candidate,
                                       bool proxy);
