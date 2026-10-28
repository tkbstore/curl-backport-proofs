/*
 * CVE-2026-5545 の4つの翻訳単位（U1・U0・D1・D0）に共通の前置き。PROTOCOL §4 で許した「関数の外側の変更」だけを置く。
 *
 * ビルドの構成: USE_NTLM・USE_SPNEGO を定義（url_match_auth_ntlm が存在し、修正の `#ifdef USE_SPNEGO` の側が使われる構成）。
 *   CURL_DISABLE_PROXY を定義（プロキシの NTLM の照合はプリプロセスで消える。CVE-2026-1965 と同じ選び方）
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl 8.14.1 の宣言順を保つ）
 *     struct connectdata     lib/urldata.h  user, passwd, http_ntlm_state, proxy_ntlm_state, http_negotiate_state
 *     struct url_conn_match  lib/url.c      found, needle と、触るビットフィールド3つ（want_ntlm_http, want_proxy_ntlm_http, force_reuse）
 *   U と D で触るフィールドは同じなので、前置きも同じものを使う
 * - マクロ・型は curl の非デバッグビルドの定義をそのまま写した（BIT・TRUE・FALSE、curlntlm、curlnegotiate）
 * - 呼ばれる側の関数は extern の宣言: Curl_timestrcmp（lib/strcase.h）
 */
#define USE_NTLM 1
#define USE_SPNEGO 1
#define CURL_DISABLE_PROXY 1

#include <stdbool.h>

typedef unsigned int curl_bit;

#define BIT(x) curl_bit x:1
#define TRUE true
#define FALSE false

typedef enum {
  NTLMSTATE_NONE,
  NTLMSTATE_TYPE1,
  NTLMSTATE_TYPE2,
  NTLMSTATE_TYPE3,
  NTLMSTATE_LAST
} curlntlm;

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
  curlntlm http_ntlm_state;
  curlntlm proxy_ntlm_state;
  curlnegotiate http_negotiate_state;
};

struct url_conn_match {
  struct connectdata *found;
  struct connectdata *needle;
  BIT(want_ntlm_http);
  BIT(want_proxy_ntlm_http);
  BIT(force_reuse);
};

extern int Curl_timestrcmp(const char *first, const char *second);
