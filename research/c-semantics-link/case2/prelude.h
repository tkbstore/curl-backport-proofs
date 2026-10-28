/*
 * Case 2 (CURL-CVE-2026-86413) の翻訳単位の前置き。PROTOCOL §4 で許した「関数の外側の変更」だけを置く。
 *
 * 出典: curl 43029e2ec37eba2354ced199ccd8898de695858e（修正後）と親 9572e7914a4566e5356a096cd7df2d2634417eab（修正前）
 * ビルドの構成: USE_SPNEGO を定義（HTTP の Negotiate を使う）。USE_NTLM は定義しない。CURL_DISABLE_PROXY を定義
 *   （プロキシの Negotiate は H5 のモデルでも省いた。プロキシ無効の構成ではプリプロセスで消える）
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl の宣言順を保つ）
 *     struct Curl_scheme     lib/protocol.h   protocol
 *     struct connectdata     lib/urldata.h    creds, creds_origin, scheme, destination,
 *                                             http_negotiate_state, proxy_negotiate_state
 *     struct auth            lib/urldata.h:477 want
 *     struct UrlState        lib/urldata.h    origin, authhost, creds
 *     struct UserDefined     lib/urldata.h    use_ssl
 *     struct Curl_easy       lib/urldata.h    set, state
 *     struct curltime        lib/curlx/timeval.h:30（そのまま）
 *     struct url_conn_match  lib/url.c        found, data, needle, now と、触るビットフィールド7つ
 * - マクロ・型は curl の非デバッグビルドの定義をそのまま写した
 * - 呼ばれる側の関数は extern の宣言（仕様は Lean 側で定理の仮定として与える）。
 *   xfer_may_multiplex・url_match_conn・url_match_result は lib/url.c の static 関数だが、
 *   本体を入れずに extern の宣言にした（§4「関数が呼ぶ他の関数は extern の宣言にし」）
 */
#define USE_SPNEGO 1
#define CURL_DISABLE_PROXY 1

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

typedef long curl_off_t;
typedef curl_off_t curl_prot_t;
typedef long time_t;
typedef unsigned int curl_bit;

#define BIT(x) curl_bit x:1
#define TRUE true
#define FALSE false
#define DEBUGF(x) do {} while(0)
#define DEBUGASSERT(x) do {} while(0)

#define CURLAUTH_NEGOTIATE    (((unsigned long)1) << 2)
#define CURLPROTO_HTTP    (1L << 0)
#define CURLPROTO_HTTPS   (1L << 1)
#define CURLPROTO_WS     (1L << 30)
#define CURLPROTO_WSS    ((curl_prot_t)1 << 31)
#define PROTO_FAMILY_HTTP (CURLPROTO_HTTP | CURLPROTO_HTTPS | CURLPROTO_WS | \
                           CURLPROTO_WSS)
#define CURLUSESSL_NONE    0L
#define CURLUSESSL_CONTROL 2L

typedef enum {
  GSS_AUTHNONE,
  GSS_AUTHRECV,
  GSS_AUTHSENT,
  GSS_AUTHDONE,
  GSS_AUTHSUCC
} curlnegotiate;

struct Curl_creds;
struct Curl_peer;
struct cpool;

struct Curl_scheme {
  curl_prot_t protocol;
};

struct connectdata {
  struct Curl_creds *creds;
  struct Curl_peer *creds_origin;
  const struct Curl_scheme *scheme;
  char *destination;
  curlnegotiate http_negotiate_state;
  curlnegotiate proxy_negotiate_state;
};

struct auth {
  uint32_t want;
};

struct UrlState {
  struct Curl_peer *origin;
  struct auth authhost;
  struct Curl_creds *creds;
};

struct UserDefined {
  uint8_t use_ssl;
};

struct Curl_easy {
  struct UserDefined set;
  struct UrlState state;
};

struct curltime {
  time_t tv_sec; /* seconds */
  int tv_usec;   /* microseconds */
};

struct url_conn_match {
  struct connectdata *found;
  struct Curl_easy *data;
  struct connectdata *needle;
  struct curltime now;
  BIT(may_multiplex);
  BIT(want_nego_http);
  BIT(want_proxy_nego_http);
  BIT(may_tls);
  BIT(require_tls);
  BIT(wait_pipe);
  BIT(force_reuse);
};

typedef bool Curl_cpool_conn_match_cb(struct connectdata *conn,
                                      void *userdata);
typedef bool Curl_cpool_done_match_cb(void *userdata);

extern void *memset(void *s, int c, size_t n);
extern bool Curl_creds_same(struct Curl_creds *c1, struct Curl_creds *c2);
extern bool Curl_peer_equal(struct Curl_peer *p1, struct Curl_peer *p2);
extern bool Curl_auth_allowed_to_host(struct Curl_easy *data);
extern struct cpool *Curl_cpool_get_instance(struct Curl_easy *data);
extern const struct curltime *Curl_pgrs_now(struct Curl_easy *data);
extern void Curl_cpool_prune_dead(struct cpool *cpool, struct Curl_easy *data);
extern bool Curl_cpool_find(struct Curl_easy *data,
                            const char *destination,
                            Curl_cpool_conn_match_cb *conn_cb,
                            Curl_cpool_done_match_cb *done_cb,
                            void *userdata);
extern bool xfer_may_multiplex(const struct Curl_easy *data,
                               const struct connectdata *conn);
extern bool url_match_conn(struct connectdata *conn, void *userdata);
extern bool url_match_result(void *userdata);
