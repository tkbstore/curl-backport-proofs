/* curl lib/url.c @ a86efdd7ca5433de9231e650f18247de8319ad16（上流の修正後 U1）
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
  else if(m->require_tls)
    /* a clear-text STARTTLS protocol with required TLS */
    return FALSE;
  return TRUE;
}
static bool url_match_ssl_config(struct connectdata *conn,
                                 struct url_conn_match *m)
{
  /* If talking/upgrading to TLS, conn needs to use the same SSL options. */
  if(((m->needle->scheme->flags & PROTOPT_SSL) || m->may_tls) &&
     !Curl_ssl_conn_config_match(m->data, conn, FALSE)) {
    DEBUGF(infof(m->data, "Connection #%" FMT_OFF_T
                 " has different SSL parameters, cannot reuse",
                 conn->connection_id));
    return FALSE;
  }
  return TRUE;
}
#include "epilogue.h"
