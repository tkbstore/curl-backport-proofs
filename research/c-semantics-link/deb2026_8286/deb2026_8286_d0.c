/* curl lib/url.c @ curl-8_14_1 + Debian CVE-2026-1965_1, CVE-2026-1965_2, CVE-2026-3784, CVE-2026-4873, CVE-2026-5545, CVE-2026-6276（D0）
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude_d.h"

static curl_prot_t get_protocol_family(const struct Curl_handler *h)
{
  DEBUGASSERT(h);
  DEBUGASSERT(h->family);
  return h->family;
}
static bool url_match_ssl_use(struct connectdata *conn,
                              struct url_conn_match *m)
{
  if(m->needle->handler->flags&PROTOPT_SSL) {
    /* We are looking for SSL, if `conn` does not do it, not a match. */
    if(!Curl_conn_is_ssl(conn, FIRSTSOCKET))
      return FALSE;
  }
  else if(Curl_conn_is_ssl(conn, FIRSTSOCKET)) {
    /* We are not *requiring* SSL, however `conn` has it. If the
     * protocol *family* is not the same, not a match. */
    if(get_protocol_family(conn->handler) != m->needle->handler->protocol)
      return FALSE;
  }
  else if(m->req_tls)
    /* a clear-text STARTTLS protocol with required TLS */
    return FALSE;
  return TRUE;
}
static bool url_match_ssl_config(struct connectdata *conn,
                                 struct url_conn_match *m)
{
  /* If talking TLS, conn needs to use the same SSL options. */
  if((m->needle->handler->flags & PROTOPT_SSL) &&
     !Curl_ssl_conn_config_match(m->data, conn, FALSE)) {
    DEBUGF(infof(m->data,
                 "Connection #%" FMT_OFF_T
                 " has different SSL parameters, cannot reuse",
                 conn->connection_id));
    return FALSE;
  }
  return TRUE;
}
#include "epilogue.h"
