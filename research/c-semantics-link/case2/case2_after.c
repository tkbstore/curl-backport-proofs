/* curl lib/url.c @ 43029e2ec37eba2354ced199ccd8898de695858e (修正後)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude.h"

static bool url_match_auth_nego(struct connectdata *conn,
                                struct url_conn_match *m)
{
  if(conn->http_negotiate_state != GSS_AUTHNONE) {
    /* Connection is using Negotiate. We cannot reuse if transfer
     * has different Auth input parameters. */
    if(!m->want_nego_http ||
       !Curl_creds_same(conn->creds, m->data->state.creds) ||
       !Curl_peer_equal(conn->creds_origin, m->data->state.origin))
      return FALSE;
  }
  else if(m->want_nego_http) {
    /* Transfer wants Negotiate, connection is not using it.
     * Do not reuse when connection has credentials and they differ. */
    if(conn->creds &&
       (!Curl_creds_same(conn->creds, m->data->state.creds) ||
        !Curl_peer_equal(conn->creds_origin, m->data->state.origin)))
      return FALSE;
  }

#ifndef CURL_DISABLE_PROXY
  /* Same for Proxy Negotiate authentication */
  if(conn->proxy_negotiate_state != GSS_AUTHNONE) {
    if(!m->want_proxy_nego_http ||
       !Curl_creds_same(m->needle->http_proxy.creds, conn->http_proxy.creds))
      return FALSE;
  }
  else if(m->want_proxy_nego_http) {
    if(conn->http_proxy.creds &&
       !Curl_creds_same(m->needle->http_proxy.creds, conn->http_proxy.creds))
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
static bool url_attach_existing(struct Curl_easy *data,
                                struct connectdata *needle,
                                bool *waitpipe)
{
  struct cpool *cpool = Curl_cpool_get_instance(data);
  struct url_conn_match match;
  bool success;

  DEBUGASSERT(!data->conn);

  memset(&match, 0, sizeof(match));
  match.data = data;
  match.needle = needle;
  match.now = *Curl_pgrs_now(data);
  match.may_multiplex = xfer_may_multiplex(data, needle);

  Curl_cpool_prune_dead(cpool, data);

#ifdef USE_NTLM
  match.want_ntlm_http =
    (data->state.authhost.want & CURLAUTH_NTLM) &&
    (needle->scheme->protocol & PROTO_FAMILY_HTTP) &&
    Curl_auth_allowed_to_host(data);
#ifndef CURL_DISABLE_PROXY
  match.want_proxy_ntlm_http =
    needle->http_proxy.creds &&
    (data->state.authproxy.want & CURLAUTH_NTLM) &&
    (needle->scheme->protocol & PROTO_FAMILY_HTTP);
#endif
#endif

#if !defined(CURL_DISABLE_HTTP) && defined(USE_SPNEGO)
  match.want_nego_http =
    (data->state.authhost.want & CURLAUTH_NEGOTIATE) &&
    (needle->scheme->protocol & PROTO_FAMILY_HTTP) &&
    Curl_auth_allowed_to_host(data);
#ifndef CURL_DISABLE_PROXY
  match.want_proxy_nego_http =
    needle->http_proxy.creds &&
    (data->state.authproxy.want & CURLAUTH_NEGOTIATE) &&
    (needle->scheme->protocol & PROTO_FAMILY_HTTP);
#endif
#endif
  match.require_tls = data->set.use_ssl >= CURLUSESSL_CONTROL;
  match.may_tls = data->set.use_ssl > CURLUSESSL_NONE;

  /* Find a connection in the pool that matches what "data + needle"
   * requires. If a suitable candidate is found, it is attached to "data". */
  success = Curl_cpool_find(data, needle->destination,
                            url_match_conn, url_match_result, &match);

  /* wait_pipe is TRUE if we encounter a bundle that is undecided. There
   * is no matching connection then, yet. */
  *waitpipe = (bool)match.wait_pipe;
  return success;
}
#include "epilogue.h"
