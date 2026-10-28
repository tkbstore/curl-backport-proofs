/* curl lib/url.c @ curl-8_14_1（D0）
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude_d.h"

static CURLcode create_conn_helper_init_proxy(struct Curl_easy *data,
                                              struct connectdata *conn)
{
  char *proxy = NULL;
  char *socksproxy = NULL;
  char *no_proxy = NULL;
  CURLcode result = CURLE_OK;

  /*************************************************************
   * Extract the user and password from the authentication string
   *************************************************************/
  if(conn->bits.proxy_user_passwd) {
    result = parse_proxy_auth(data, conn);
    if(result)
      goto out;
  }

  /*************************************************************
   * Detect what (if any) proxy to use
   *************************************************************/
  if(data->set.str[STRING_PROXY]) {
    proxy = strdup(data->set.str[STRING_PROXY]);
    /* if global proxy is set, this is it */
    if(!proxy) {
      failf(data, "memory shortage");
      result = CURLE_OUT_OF_MEMORY;
      goto out;
    }
  }

  if(data->set.str[STRING_PRE_PROXY]) {
    socksproxy = strdup(data->set.str[STRING_PRE_PROXY]);
    /* if global socks proxy is set, this is it */
    if(!socksproxy) {
      failf(data, "memory shortage");
      result = CURLE_OUT_OF_MEMORY;
      goto out;
    }
  }

  if(!data->set.str[STRING_NOPROXY]) {
    const char *p = "no_proxy";
    no_proxy = curl_getenv(p);
    if(!no_proxy) {
      p = "NO_PROXY";
      no_proxy = curl_getenv(p);
    }
    if(no_proxy) {
      infof(data, "Uses proxy env variable %s == '%s'", p, no_proxy);
    }
  }

  if(Curl_check_noproxy(conn->host.name, data->set.str[STRING_NOPROXY] ?
                        data->set.str[STRING_NOPROXY] : no_proxy)) {
    Curl_safefree(proxy);
    Curl_safefree(socksproxy);
  }
#ifndef CURL_DISABLE_HTTP
  else if(!proxy && !socksproxy)
    /* if the host is not in the noproxy list, detect proxy. */
    proxy = detect_proxy(data, conn);
#endif /* CURL_DISABLE_HTTP */
  Curl_safefree(no_proxy);

#ifdef USE_UNIX_SOCKETS
  /* For the time being do not mix proxy and Unix domain sockets. See #1274 */
  if(proxy && conn->unix_domain_socket) {
    free(proxy);
    proxy = NULL;
  }
#endif

  if(proxy && (!*proxy || (conn->handler->flags & PROTOPT_NONETWORK))) {
    free(proxy);  /* Do not bother with an empty proxy string or if the
                     protocol does not work with network */
    proxy = NULL;
  }
  if(socksproxy && (!*socksproxy ||
                    (conn->handler->flags & PROTOPT_NONETWORK))) {
    free(socksproxy);  /* Do not bother with an empty socks proxy string or if
                          the protocol does not work with network */
    socksproxy = NULL;
  }

  /***********************************************************************
   * If this is supposed to use a proxy, we need to figure out the proxy host
   * name, proxy type and port number, so that we can reuse an existing
   * connection that may exist registered to the same proxy host.
   ***********************************************************************/
  if(proxy || socksproxy) {
    curl_proxytype ptype = (curl_proxytype)conn->http_proxy.proxytype;
    if(proxy) {
      result = parse_proxy(data, conn, proxy, ptype);
      Curl_safefree(proxy); /* parse_proxy copies the proxy string */
      if(result)
        goto out;
    }

    if(socksproxy) {
      result = parse_proxy(data, conn, socksproxy, ptype);
      /* parse_proxy copies the socks proxy string */
      Curl_safefree(socksproxy);
      if(result)
        goto out;
    }

    if(conn->http_proxy.host.rawalloc) {
#ifdef CURL_DISABLE_HTTP
      /* asking for an HTTP proxy is a bit funny when HTTP is disabled... */
      result = CURLE_UNSUPPORTED_PROTOCOL;
      goto out;
#else
      /* force this connection's protocol to become HTTP if compatible */
      if(!(conn->handler->protocol & PROTO_FAMILY_HTTP)) {
        if((conn->handler->flags & PROTOPT_PROXY_AS_HTTP) &&
           !conn->bits.tunnel_proxy)
          conn->handler = &Curl_handler_http;
        else
          /* if not converting to HTTP over the proxy, enforce tunneling */
          conn->bits.tunnel_proxy = TRUE;
      }
      conn->bits.httpproxy = TRUE;
#endif
    }
    else {
      conn->bits.httpproxy = FALSE; /* not an HTTP proxy */
      conn->bits.tunnel_proxy = FALSE; /* no tunneling if not HTTP */
    }

    if(conn->socks_proxy.host.rawalloc) {
      if(!conn->http_proxy.host.rawalloc) {
        /* once a socks proxy */
        if(!conn->socks_proxy.user) {
          conn->socks_proxy.user = conn->http_proxy.user;
          conn->http_proxy.user = NULL;
          free(conn->socks_proxy.passwd);
          conn->socks_proxy.passwd = conn->http_proxy.passwd;
          conn->http_proxy.passwd = NULL;
        }
      }
      conn->bits.socksproxy = TRUE;
    }
    else
      conn->bits.socksproxy = FALSE; /* not a socks proxy */
  }
  else {
    conn->bits.socksproxy = FALSE;
    conn->bits.httpproxy = FALSE;
  }
  conn->bits.proxy = conn->bits.httpproxy || conn->bits.socksproxy;

  if(!conn->bits.proxy) {
    /* we are not using the proxy after all... */
    conn->bits.proxy = FALSE;
    conn->bits.httpproxy = FALSE;
    conn->bits.socksproxy = FALSE;
    conn->bits.proxy_user_passwd = FALSE;
    conn->bits.tunnel_proxy = FALSE;
    /* CURLPROXY_HTTPS does not have its own flag in conn->bits, yet we need
       to signal that CURLPROXY_HTTPS is not used for this connection */
    conn->http_proxy.proxytype = CURLPROXY_HTTP;
  }

out:

  free(socksproxy);
  free(proxy);
  return result;
}
#define DEB_KEEP create_conn_helper_init_proxy
#include "epilogue.h"
