/* curl lib/setopt.c @ 7586ca74558b7b0b21b2b8c83882172a6bc470eb（U0: 上流の修正前）
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#define DEB_U 1
#include "prelude_u.h"

static CURLcode setopt_cptr_proxy(struct Curl_easy *data, CURLoption option,
                                  const char *ptr)
{
  CURLcode result = CURLE_OK;
  struct UserDefined *s = &data->set;
  switch(option) {
  case CURLOPT_PROXYUSERPWD: {
    /*
     * user:password needed to use the proxy
     */
    char *u = NULL;
    char *p = NULL;
    result = setstropt_userpwd(ptr, &u, &p);

    /* URL decode the components */
    if(!result && u) {
      curlx_safefree(s->str[STRING_PROXYUSERNAME]);
      result = Curl_urldecode(u, 0, &s->str[STRING_PROXYUSERNAME], NULL,
                              REJECT_ZERO);
    }
    if(!result && p) {
      curlx_safefree(s->str[STRING_PROXYPASSWORD]);
      result = Curl_urldecode(p, 0, &s->str[STRING_PROXYPASSWORD], NULL,
                              REJECT_ZERO);
    }
    curlx_free(u);
    curlx_free(p);
    break;
  }
  case CURLOPT_PROXYUSERNAME:
    /*
     * authentication username to use in the operation
     */
    return Curl_setstropt(&s->str[STRING_PROXYUSERNAME], ptr);

  case CURLOPT_PROXYPASSWORD:
    /*
     * authentication password to use in the operation
     */
    return Curl_setstropt(&s->str[STRING_PROXYPASSWORD], ptr);

  case CURLOPT_NOPROXY:
    /*
     * proxy exception list
     */
    return Curl_setstropt(&s->str[STRING_NOPROXY], ptr);
  case CURLOPT_PROXY_SSLCERT:
    /*
     * String that holds filename of the SSL certificate to use for proxy
     */
    return Curl_setstropt(&s->str[STRING_CERT_PROXY], ptr);
  case CURLOPT_PROXY_SSLCERTTYPE:
    /*
     * String that holds file type of the SSL certificate to use for proxy
     */
    return Curl_setstropt(&s->str[STRING_CERT_TYPE_PROXY], ptr);
  case CURLOPT_PROXY_SSLKEY:
    /*
     * String that holds filename of the SSL key to use for proxy
     */
    return Curl_setstropt(&s->str[STRING_KEY_PROXY], ptr);
  case CURLOPT_PROXY_KEYPASSWD:
    /*
     * String that holds the SSL private key password for proxy.
     */
    return Curl_setstropt(&s->str[STRING_KEY_PASSWD_PROXY], ptr);
  case CURLOPT_PROXY_SSLKEYTYPE:
    /*
     * String that holds file type of the SSL key to use for proxy
     */
    return Curl_setstropt(&s->str[STRING_KEY_TYPE_PROXY], ptr);
  case CURLOPT_PROXY_SSL_CIPHER_LIST:
    if(Curl_ssl_supports(data, SSLSUPP_CIPHER_LIST)) {
      /* set a list of cipher we want to use in the SSL connection for proxy */
      return Curl_setstropt(&s->str[STRING_SSL_CIPHER_LIST_PROXY], ptr);
    }
    else
      return CURLE_NOT_BUILT_IN;
  case CURLOPT_PROXY_TLS13_CIPHERS:
    if(Curl_ssl_supports(data, SSLSUPP_TLS13_CIPHERSUITES))
      /* set preferred list of TLS 1.3 cipher suites for proxy */
      return Curl_setstropt(&s->str[STRING_SSL_CIPHER13_LIST_PROXY], ptr);
    else
      return CURLE_NOT_BUILT_IN;
  case CURLOPT_PROXY:
    /*
     * Set proxy server:port to use as proxy.
     *
     * If the proxy is set to "" (and CURLOPT_PRE_PROXY is set to "" or NULL)
     * we explicitly say that we do not want to use a proxy (even though there
     * might be environment variables saying so).
     *
     * Setting it to NULL, means no proxy but allows the environment variables
     * to decide for us (if CURLOPT_PRE_PROXY setting it to NULL).
     */
    return Curl_setstropt(&s->str[STRING_PROXY], ptr);
  case CURLOPT_PRE_PROXY:
    /*
     * Set proxy server:port to use as SOCKS proxy.
     *
     * If the proxy is set to "" or NULL we explicitly say that we do not want
     * to use the socks proxy.
     */
    return Curl_setstropt(&s->str[STRING_PRE_PROXY], ptr);
  case CURLOPT_SOCKS5_GSSAPI_SERVICE:
  case CURLOPT_PROXY_SERVICE_NAME:
    /*
     * Set proxy authentication service name for Kerberos 5 and SPNEGO
     */
    return Curl_setstropt(&s->str[STRING_PROXY_SERVICE_NAME], ptr);
  case CURLOPT_PROXY_PINNEDPUBLICKEY:
    /*
     * Set pinned public key for SSL connection.
     * Specify filename of the public key in DER format.
     */
#ifdef USE_SSL
    if(Curl_ssl_supports(data, SSLSUPP_PINNEDPUBKEY))
      return Curl_setstropt(&s->str[STRING_SSL_PINNEDPUBLICKEY_PROXY], ptr);
#endif
    return CURLE_NOT_BUILT_IN;

  case CURLOPT_HAPROXY_CLIENT_IP:
    /*
     * Set the client IP to send through HAProxy PROXY protocol
     */
    result = Curl_setstropt(&s->str[STRING_HAPROXY_CLIENT_IP], ptr);

    /* enable the HAProxy protocol if an IP is provided */
    s->haproxyprotocol = !!s->str[STRING_HAPROXY_CLIENT_IP];
    break;
  case CURLOPT_PROXY_CAINFO:
    /*
     * Set CA info SSL connection for proxy. Specify filename of the
     * CA certificate
     */
    s->proxy_ssl.custom_cafile = TRUE;
    return Curl_setstropt(&s->str[STRING_SSL_CAFILE_PROXY], ptr);
  case CURLOPT_PROXY_CRLFILE:
    /*
     * Set CRL file info for SSL connection for proxy. Specify filename of the
     * CRL to check certificates revocation
     */
    return Curl_setstropt(&s->str[STRING_SSL_CRLFILE_PROXY], ptr);
  case CURLOPT_PROXY_ISSUERCERT:
    /*
     * Set Issuer certificate file
     * to check certificates issuer
     */
    return Curl_setstropt(&s->str[STRING_SSL_ISSUERCERT_PROXY], ptr);
  case CURLOPT_PROXY_CAPATH:
    /*
     * Set CA path info for SSL connection proxy. Specify directory name of the
     * CA certificates which have been prepared using openssl c_rehash utility.
     */
#ifdef USE_SSL
    if(Curl_ssl_supports(data, SSLSUPP_CA_PATH)) {
      /* This does not work on Windows. */
      s->proxy_ssl.custom_capath = TRUE;
      return Curl_setstropt(&s->str[STRING_SSL_CAPATH_PROXY], ptr);
    }
#endif
    return CURLE_NOT_BUILT_IN;
  default:
    return CURLE_UNKNOWN_OPTION;
  }
  return result;
}
#define DEB_KEEP setopt_cptr_proxy
#include "epilogue.h"
