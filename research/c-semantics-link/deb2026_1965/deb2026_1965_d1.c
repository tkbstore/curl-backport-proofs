/* curl lib/url.c @ curl-8_14_1 + Debian CVE-2026-1965_1, CVE-2026-1965_2（D1）
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude.h"

static bool url_match_auth_nego(struct connectdata *conn,
                                struct url_conn_match *m)
{
  /* If we are looking for an HTTP+Negotiate connection, check if this is
     already authenticating with the right credentials. If not, keep looking
     so that we can reuse Negotiate connections if possible. */
  if(m->want_nego_http) {
    if(Curl_timestrcmp(m->needle->user, conn->user) ||
       Curl_timestrcmp(m->needle->passwd, conn->passwd))
      return FALSE;
  }
  else if(conn->http_negotiate_state != GSS_AUTHNONE) {
    /* Connection is using Negotiate auth but we do not want Negotiate */
    return FALSE;
  }

#ifndef CURL_DISABLE_PROXY
  /* Same for Proxy Negotiate authentication */
  if(m->want_proxy_nego_http) {
    /* Both conn->http_proxy.user and conn->http_proxy.passwd can be
     * NULL */
    if(!conn->http_proxy.user || !conn->http_proxy.passwd)
      return FALSE;

    if(Curl_timestrcmp(m->needle->http_proxy.user,
                       conn->http_proxy.user) ||
       Curl_timestrcmp(m->needle->http_proxy.passwd,
                       conn->http_proxy.passwd))
      return FALSE;
  }
  else if(conn->proxy_negotiate_state != GSS_AUTHNONE) {
    /* Proxy connection is using Negotiate auth but we do not want Negotiate */
    return FALSE;
  }
#endif
  if(m->want_nego_http || m->want_proxy_nego_http) {
    /* Credentials are already checked, we may use this connection. We MUST
     * use a connection where it has already been fully negotiated. If it has
     * not, we keep on looking for a better one. */
    m->found = conn;
    if((m->want_nego_http &&
        (conn->http_negotiate_state != GSS_AUTHNONE)) ||
       (m->want_proxy_nego_http &&
        (conn->proxy_negotiate_state != GSS_AUTHNONE))) {
      /* We must use this connection, no other */
      m->force_reuse = TRUE;
      return TRUE;
    }
    return FALSE; /* get another */
  }
  return TRUE;
}
#include "epilogue.h"
