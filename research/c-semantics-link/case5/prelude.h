/*
 * Case 5 (CURL-CVE-2026-86411) の翻訳単位の前置き。PROTOCOL §4 で許した「関数の外側の変更」だけを置く。
 *
 * 出典: curl 72352daba01ba8072b6c1c0254cb77860ed1ab06（修正後）と親 bdda3a268f0fd1a1bb4b16b9322aa6bc055b8e76（修正前）
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl の宣言順を保つ）
 *     struct Curl_scheme      lib/protocol.h:243  protocol, family, flags
 *     struct connectdata      lib/urldata.h:262   scheme
 *     struct url_conn_match   lib/url.c:581       data, needle, may_tls, require_tls
 * - マクロは curl の非デバッグビルド（DEBUGBUILD 未定義）の定義をそのまま写した
 *     BIT / TRUE / FALSE / DEBUGF / DEBUGASSERT  lib/curl_setup.h:1011,1049,1052,1067,1082
 *     PROTOPT_SSL / PROTOPT_SSL_REUSE           lib/protocol.h:207,234
 *     FIRSTSOCKET                               lib/urldata.h:234
 *     curl_off_t は LP64 の GCC/clang の定義（long）include/curl/system.h:335-340
 * - 呼ばれる側の関数のうち、別の翻訳単位にある2つは extern の宣言にした。仕様は Lean 側で公理として与える
 *     Curl_conn_is_ssl            lib/cfilters.h:391
 *     Curl_ssl_conn_config_match  lib/vtls/vtls_config.h:112
 *   get_protocol_family（lib/url.c:141）は同じ翻訳単位の static 関数なので、本体ごと入れる
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

#define PROTOPT_SSL (1 << 0)
#define PROTOPT_SSL_REUSE (1 << 15)
#define FIRSTSOCKET 0

struct Curl_easy;

struct Curl_scheme {
  curl_prot_t protocol;
  curl_prot_t family;
  uint32_t flags;
};

struct connectdata {
  const struct Curl_scheme *scheme;
};

struct url_conn_match {
  struct Curl_easy *data;
  struct connectdata *needle;
  BIT(may_tls);
  BIT(require_tls);
};

extern bool Curl_conn_is_ssl(struct connectdata *conn, int8_t sockindex);
extern bool Curl_ssl_conn_config_match(struct Curl_easy *data,
                                       struct connectdata *candidate,
                                       bool proxy);
