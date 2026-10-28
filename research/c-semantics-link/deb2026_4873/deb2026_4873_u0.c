/* curl lib/url.c @ 62d77b12fce55d3481bb0b2e70e0f921c8cbfe5e（上流の修正前 U0）
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude_u.h"

static curl_prot_t get_protocol_family(const struct Curl_scheme *s)
{
  DEBUGASSERT(s);
  DEBUGASSERT(s->family);
  return s->family;
}
static bool url_match_ssl_use(struct connectdata *conn,
                              struct url_conn_match *m)
{
  if(m->needle->scheme->flags & PROTOPT_SSL) {
    /* We are looking for SSL, if `conn` does not do it, not a match. */
    if(!Curl_conn_is_ssl(conn, FIRSTSOCKET))
      return FALSE;
  }
  else if(Curl_conn_is_ssl(conn, FIRSTSOCKET)) {
    /* If the protocol does not allow reuse of SSL connections OR
       is of another protocol family, not a match. */
    if(!(m->needle->scheme->flags & PROTOPT_SSL_REUSE) ||
       (get_protocol_family(conn->scheme) != m->needle->scheme->protocol))
      return FALSE;
  }
  return TRUE;
}
#include "epilogue.h"
