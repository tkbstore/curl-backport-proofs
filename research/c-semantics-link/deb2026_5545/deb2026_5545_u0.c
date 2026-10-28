/* curl lib/url.c @ b27e828b938777b75cf627093e1c9c9d4af2cbd2（上流の修正前 U0）
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude.h"

static bool url_match_auth_ntlm(struct connectdata *conn,
                                struct url_conn_match *m)
{
  /* If we are looking for an HTTP+NTLM connection, check if this is
     already authenticating with the right credentials. If not, keep
     looking so that we can reuse NTLM connections if
     possible. (Especially we must not reuse the same connection if
     partway through a handshake!) */
  if(m->want_ntlm_http) {
    if(Curl_timestrcmp(m->needle->user, conn->user) ||
       Curl_timestrcmp(m->needle->passwd, conn->passwd)) {

      /* we prefer a credential match, but this is at least a connection
         that can be reused and "upgraded" to NTLM */
      if(conn->http_ntlm_state == NTLMSTATE_NONE)
        m->found = conn;
      return FALSE;
    }
  }
  else if(conn->http_ntlm_state != NTLMSTATE_NONE) {
    /* Connection is using NTLM auth but we do not want NTLM */
    return FALSE;
  }

#ifndef CURL_DISABLE_PROXY
  /* Same for Proxy NTLM authentication */
  if(m->want_proxy_ntlm_http) {
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
  else if(conn->proxy_ntlm_state != NTLMSTATE_NONE) {
    /* Proxy connection is using NTLM auth but we do not want NTLM */
    return FALSE;
  }
#endif
  if(m->want_ntlm_http || m->want_proxy_ntlm_http) {
    /* Credentials are already checked, we may use this connection.
     * With NTLM being weird as it is, we MUST use a
     * connection where it has already been fully negotiated.
     * If it has not, we keep on looking for a better one. */
    m->found = conn;

    if((m->want_ntlm_http &&
       (conn->http_ntlm_state != NTLMSTATE_NONE)) ||
        (m->want_proxy_ntlm_http &&
         (conn->proxy_ntlm_state != NTLMSTATE_NONE))) {
      /* We must use this connection, no other */
      m->force_reuse = TRUE;
      return TRUE;
    }
    /* Continue look up for a better connection */
    return FALSE;
  }
  return TRUE;
}
#include "epilogue.h"
