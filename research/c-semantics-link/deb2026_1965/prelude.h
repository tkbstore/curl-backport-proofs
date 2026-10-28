/*
 * CVE-2026-1965（_2 のパッチ）の4つの翻訳単位（U1・U0・D1・D0）に共通の前置き。
 * PROTOCOL（research/c-semantics-link/PROTOCOL.md §4）で許した「関数の外側の変更」だけを置く。
 *
 * ビルドの構成: USE_SPNEGO・USE_NTLM を定義（url_match_auth_nego が存在し、want_ntlm_* のビットがある構成）。
 *   CURL_DISABLE_PROXY を定義（プロキシの Negotiate の照合はプリプロセスで消える。Case 2 と同じ選び方）
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl 8.14.1 の宣言順を保つ）
 *     struct connectdata     lib/urldata.h  user, passwd, http_negotiate_state, proxy_negotiate_state
 *     struct url_conn_match  lib/url.c      found, needle と、触るビットフィールド5つ
 *       （want_ntlm_http, want_proxy_ntlm_http, want_nego_http, want_proxy_nego_http, force_reuse）
 *   U と D で触るフィールドは同じなので、前置きも同じものを使う
 * - マクロ・型は curl の非デバッグビルドの定義をそのまま写した（BIT・TRUE・FALSE、curlnegotiate）
 * - 呼ばれる側の関数は extern の宣言（仕様は Lean 側で定理の仮定として与える）
 *     Curl_timestrcmp  lib/strcase.h
 */
#define USE_SPNEGO 1
#define USE_NTLM 1
#define CURL_DISABLE_PROXY 1

#include <stdbool.h>

typedef unsigned int curl_bit;

#define BIT(x) curl_bit x:1
#define TRUE true
#define FALSE false

typedef enum {
  GSS_AUTHNONE,
  GSS_AUTHRECV,
  GSS_AUTHSENT,
  GSS_AUTHDONE,
  GSS_AUTHSUCC
} curlnegotiate;

struct connectdata {
  char *user;
  char *passwd;
  curlnegotiate http_negotiate_state;
  curlnegotiate proxy_negotiate_state;
};

struct url_conn_match {
  struct connectdata *found;
  struct connectdata *needle;
  BIT(want_ntlm_http);
  BIT(want_proxy_ntlm_http);
  BIT(want_nego_http);
  BIT(want_proxy_nego_http);
  BIT(force_reuse);
};

extern int Curl_timestrcmp(const char *first, const char *second);
