/* curl lib/url.c @ d99dcfb04a70fa0e49a7745de63ed6041e5b67f5（U0: 上流の修正前）
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude_u.h"

static CURLcode url_set_conn_proxies(struct Curl_easy *data,
                                     struct connectdata *conn)
{
  char *proxy = NULL;
  char *pre_proxy = NULL;
  char *no_proxy = NULL;
  CURLcode result = CURLE_OK;

  /*************************************************************
   * Detect what (if any) proxy to use
   *************************************************************/
  if(data->set.str[STRING_PROXY]) {
    proxy = curlx_strdup(data->set.str[STRING_PROXY]);
    /* if global proxy is set, this is it */
    if(!proxy) {
      failf(data, "memory shortage");
      result = CURLE_OUT_OF_MEMORY;
      goto out;
    }
  }

  if(data->set.str[STRING_PRE_PROXY]) {
    pre_proxy = curlx_strdup(data->set.str[STRING_PRE_PROXY]);
    /* if global socks proxy is set, this is it */
    if(!pre_proxy) {
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

  if(Curl_check_noproxy(conn->origin->hostname, data->set.str[STRING_NOPROXY] ?
                        data->set.str[STRING_NOPROXY] : no_proxy)) {
    curlx_safefree(proxy);
    curlx_safefree(pre_proxy);
  }
#ifndef CURL_DISABLE_HTTP
  else if(!proxy && !pre_proxy)
    /* if the host is not in the noproxy list, detect proxy. */
    proxy = url_detect_proxy(data, conn);
#endif /* CURL_DISABLE_HTTP */
  curlx_safefree(no_proxy);

  if(proxy && (!*proxy || (conn->scheme->flags & PROTOPT_NONETWORK))) {
    curlx_free(proxy);  /* Do not bother with an empty proxy string
                           or if the protocol does not work with network */
    proxy = NULL;
  }
  if(pre_proxy && (!*pre_proxy ||
                    (conn->scheme->flags & PROTOPT_NONETWORK))) {
    curlx_free(pre_proxy);  /* Do not bother with an empty socks proxy string
                               or if the protocol does not work with
                               network */
    pre_proxy = NULL;
  }

  /***********************************************************************
   * If this is supposed to use a proxy, we need to figure out the proxy host
   * name, proxy type and port number, so that we can reuse an existing
   * connection that may exist registered to the same proxy host.
   ***********************************************************************/
  if(proxy || pre_proxy) {
    if(pre_proxy) {
      result = parse_proxy(data, pre_proxy, TRUE, &conn->socks_proxy);
      if(result)
        goto out;
    }

    if(proxy) {
      result = parse_proxy(data, proxy, FALSE, &conn->http_proxy);
      if(result)
        goto out;
      switch(conn->http_proxy.proxytype) {
      case CURLPROXY_SOCKS4:
      case CURLPROXY_SOCKS4A:
      case CURLPROXY_SOCKS5:
      case CURLPROXY_SOCKS5_HOSTNAME:
        /* Whoops, it's not a HTTP proxy */
        if(conn->socks_proxy.peer) {
          /* and we already have a SOCKS pre-proxy. Cannot have both */
          failf(data, "Having a SOCKS pre-proxy and proxy is not "
                "supported with \'%s\'", proxy);
          result = CURLE_COULDNT_RESOLVE_PROXY;
          goto out;
        }
        /* switch */
        conn->socks_proxy = conn->http_proxy;
        memset(&conn->http_proxy, 0, sizeof(conn->http_proxy));
        break;
      default:
        break;
      }
    }

    if(conn->http_proxy.peer) {
#ifdef CURL_DISABLE_HTTP
      /* asking for an HTTP proxy is a bit funny when HTTP is disabled... */
      result = CURLE_UNSUPPORTED_PROTOCOL;
      goto out;
#else
      /* force this connection's protocol to become HTTP if compatible */
      if(!(conn->scheme->protocol & PROTO_FAMILY_HTTP)) {
        if((conn->scheme->flags & PROTOPT_PROXY_AS_HTTP) &&
           !conn->bits.tunnel_proxy)
          conn->scheme = &Curl_scheme_http;
        else
          /* if not converting to HTTP over the proxy, enforce tunneling */
          conn->bits.tunnel_proxy = TRUE;
      }
#endif
    }
    else
      conn->bits.tunnel_proxy = FALSE; /* no tunneling if not HTTP */
  }

  conn->bits.socksproxy = !!conn->socks_proxy.peer;
  conn->bits.httpproxy = !!conn->http_proxy.peer;
  conn->bits.proxy = conn->bits.httpproxy || conn->bits.socksproxy;

  if(!conn->bits.proxy) {
    /* we are not using the proxy after all... */
    conn->bits.proxy = FALSE;
    conn->bits.httpproxy = FALSE;
    conn->bits.socksproxy = FALSE;
    conn->bits.tunnel_proxy = FALSE;
    /* CURLPROXY_HTTPS does not have its own flag in conn->bits, yet we need
       to signal that CURLPROXY_HTTPS is not used for this connection */
    conn->http_proxy.proxytype = CURLPROXY_HTTP;
  }

out:

  curlx_free(pre_proxy);
  curlx_free(proxy);
  return result;
}
#define DEB_KEEP url_set_conn_proxies
#include "epilogue.h"
