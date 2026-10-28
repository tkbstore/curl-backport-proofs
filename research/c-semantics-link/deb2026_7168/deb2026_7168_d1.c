/* curl lib/setopt.c @ curl-8_14_1 + Debian CVE-2026-7168.patch（D1）
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude_d.h"

static CURLcode setproxy(struct Curl_easy *data, const char *proxy)
{
  if((data->set.str[STRING_PROXY] && proxy) &&
     /* there was one set, is this a new one? */
     !strcmp(data->set.str[STRING_PROXY], proxy))
    return CURLE_OK; /* same one as before */

  Curl_auth_digest_cleanup(&data->state.proxydigest);
  memset(&data->state.authproxy, 0, sizeof(data->state.authproxy));
  return Curl_setstropt(&data->set.str[STRING_PROXY], proxy);
}
static CURLcode setopt_cptr(struct Curl_easy *data, CURLoption option,
                            char *ptr)
{
  CURLcode result = CURLE_OK;
  switch(option) {
  case CURLOPT_SSL_CIPHER_LIST:
    if(Curl_ssl_supports(data, SSLSUPP_CIPHER_LIST))
      /* set a list of cipher we want to use in the SSL connection */
      return Curl_setstropt(&data->set.str[STRING_SSL_CIPHER_LIST], ptr);
    else
      return CURLE_NOT_BUILT_IN;
#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_SSL_CIPHER_LIST:
    if(Curl_ssl_supports(data, SSLSUPP_CIPHER_LIST)) {
      /* set a list of cipher we want to use in the SSL connection for proxy */
      return Curl_setstropt(&data->set.str[STRING_SSL_CIPHER_LIST_PROXY],
                            ptr);
    }
    else
      return CURLE_NOT_BUILT_IN;
#endif
  case CURLOPT_TLS13_CIPHERS:
    if(Curl_ssl_supports(data, SSLSUPP_TLS13_CIPHERSUITES)) {
      /* set preferred list of TLS 1.3 cipher suites */
      return Curl_setstropt(&data->set.str[STRING_SSL_CIPHER13_LIST], ptr);
    }
    else
      return CURLE_NOT_BUILT_IN;
#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_TLS13_CIPHERS:
    if(Curl_ssl_supports(data, SSLSUPP_TLS13_CIPHERSUITES))
      /* set preferred list of TLS 1.3 cipher suites for proxy */
      return Curl_setstropt(&data->set.str[STRING_SSL_CIPHER13_LIST_PROXY],
                            ptr);
    else
      return CURLE_NOT_BUILT_IN;
#endif
  case CURLOPT_RANDOM_FILE:
    break;
  case CURLOPT_EGDSOCKET:
    break;
  case CURLOPT_REQUEST_TARGET:
    return Curl_setstropt(&data->set.str[STRING_TARGET], ptr);
#ifndef CURL_DISABLE_NETRC
  case CURLOPT_NETRC_FILE:
    /*
     * Use this file instead of the $HOME/.netrc file
     */
    return Curl_setstropt(&data->set.str[STRING_NETRC_FILE], ptr);
#endif

#if !defined(CURL_DISABLE_HTTP) || !defined(CURL_DISABLE_MQTT)
  case CURLOPT_COPYPOSTFIELDS:
    /*
     * A string with POST data. Makes curl HTTP POST. Even if it is NULL.
     * If needed, CURLOPT_POSTFIELDSIZE must have been set prior to
     *  CURLOPT_COPYPOSTFIELDS and not altered later.
     */
    if(!ptr || data->set.postfieldsize == -1)
      result = Curl_setstropt(&data->set.str[STRING_COPYPOSTFIELDS], ptr);
    else {
      if(data->set.postfieldsize < 0)
        return CURLE_BAD_FUNCTION_ARGUMENT;
#if SIZEOF_CURL_OFF_T > SIZEOF_SIZE_T
      /*
       *  Check that requested length does not overflow the size_t type.
       */
      else if(data->set.postfieldsize > SIZE_T_MAX)
        return CURLE_OUT_OF_MEMORY;
#endif
      else {
        /* Allocate even when size == 0. This satisfies the need of possible
           later address compare to detect the COPYPOSTFIELDS mode, and to
           mark that postfields is used rather than read function or form
           data.
        */
        char *p = Curl_memdup0(ptr, (size_t)data->set.postfieldsize);
        if(!p)
          return CURLE_OUT_OF_MEMORY;
        else {
          free(data->set.str[STRING_COPYPOSTFIELDS]);
          data->set.str[STRING_COPYPOSTFIELDS] = p;
        }
      }
    }

    data->set.postfields = data->set.str[STRING_COPYPOSTFIELDS];
    data->set.method = HTTPREQ_POST;
    break;

  case CURLOPT_POSTFIELDS:
    /*
     * Like above, but use static data instead of copying it.
     */
    data->set.postfields = ptr;
    /* Release old copied data. */
    Curl_safefree(data->set.str[STRING_COPYPOSTFIELDS]);
    data->set.method = HTTPREQ_POST;
    break;
#endif /* ! CURL_DISABLE_HTTP || ! CURL_DISABLE_MQTT */

#ifndef CURL_DISABLE_HTTP
  case CURLOPT_ACCEPT_ENCODING:
    /*
     * String to use at the value of Accept-Encoding header.
     *
     * If the encoding is set to "" we use an Accept-Encoding header that
     * encompasses all the encodings we support.
     * If the encoding is set to NULL we do not send an Accept-Encoding header
     * and ignore an received Content-Encoding header.
     *
     */
    if(ptr && !*ptr) {
      char all[256];
      Curl_all_content_encodings(all, sizeof(all));
      return Curl_setstropt(&data->set.str[STRING_ENCODING], all);
    }
    return Curl_setstropt(&data->set.str[STRING_ENCODING], ptr);

#if !defined(CURL_DISABLE_AWS)
  case CURLOPT_AWS_SIGV4:
    /*
     * String that is merged to some authentication
     * parameters are used by the algorithm.
     */
    result = Curl_setstropt(&data->set.str[STRING_AWS_SIGV4], ptr);
    /*
     * Basic been set by default it need to be unset here
     */
    if(data->set.str[STRING_AWS_SIGV4])
      data->set.httpauth = CURLAUTH_AWS_SIGV4;
    break;
#endif
  case CURLOPT_REFERER:
    /*
     * String to set in the HTTP Referer: field.
     */
    if(data->state.referer_alloc) {
      Curl_safefree(data->state.referer);
      data->state.referer_alloc = FALSE;
    }
    result = Curl_setstropt(&data->set.str[STRING_SET_REFERER], ptr);
    data->state.referer = data->set.str[STRING_SET_REFERER];
    break;

  case CURLOPT_USERAGENT:
    /*
     * String to use in the HTTP User-Agent field
     */
    return Curl_setstropt(&data->set.str[STRING_USERAGENT], ptr);

#if !defined(CURL_DISABLE_COOKIES)
  case CURLOPT_COOKIE:
    /*
     * Cookie string to send to the remote server in the request.
     */
    return Curl_setstropt(&data->set.str[STRING_COOKIE], ptr);

  case CURLOPT_COOKIEFILE:
    /*
     * Set cookie file to read and parse. Can be used multiple times.
     */
    if(ptr) {
      struct curl_slist *cl;
      /* general protection against mistakes and abuse */
      if(strlen(ptr) > CURL_MAX_INPUT_LENGTH)
        return CURLE_BAD_FUNCTION_ARGUMENT;
      /* append the cookie filename to the list of filenames, and deal with
         them later */
      cl = curl_slist_append(data->state.cookielist, ptr);
      if(!cl) {
        curl_slist_free_all(data->state.cookielist);
        data->state.cookielist = NULL;
        return CURLE_OUT_OF_MEMORY;
      }
      data->state.cookielist = cl; /* store the list for later use */
    }
    else {
      /* clear the list of cookie files */
      curl_slist_free_all(data->state.cookielist);
      data->state.cookielist = NULL;

      if(!data->share || !data->share->cookies) {
        /* throw away all existing cookies if this is not a shared cookie
           container */
        Curl_cookie_clearall(data->cookies);
        Curl_cookie_cleanup(data->cookies);
      }
      /* disable the cookie engine */
      data->cookies = NULL;
    }
    break;

  case CURLOPT_COOKIEJAR:
    /*
     * Set cookie filename to dump all cookies to when we are done.
     */
    result = Curl_setstropt(&data->set.str[STRING_COOKIEJAR], ptr);
    if(!result) {
      /*
       * Activate the cookie parser. This may or may not already
       * have been made.
       */
      struct CookieInfo *newcookies =
        Curl_cookie_init(data, NULL, data->cookies, data->set.cookiesession);
      if(!newcookies)
        result = CURLE_OUT_OF_MEMORY;
      data->cookies = newcookies;
    }
    break;

  case CURLOPT_COOKIELIST:
    if(!ptr)
      break;

    if(strcasecompare(ptr, "ALL")) {
      /* clear all cookies */
      Curl_share_lock(data, CURL_LOCK_DATA_COOKIE, CURL_LOCK_ACCESS_SINGLE);
      Curl_cookie_clearall(data->cookies);
      Curl_share_unlock(data, CURL_LOCK_DATA_COOKIE);
    }
    else if(strcasecompare(ptr, "SESS")) {
      /* clear session cookies */
      Curl_share_lock(data, CURL_LOCK_DATA_COOKIE, CURL_LOCK_ACCESS_SINGLE);
      Curl_cookie_clearsess(data->cookies);
      Curl_share_unlock(data, CURL_LOCK_DATA_COOKIE);
    }
    else if(strcasecompare(ptr, "FLUSH")) {
      /* flush cookies to file, takes care of the locking */
      Curl_flush_cookies(data, FALSE);
    }
    else if(strcasecompare(ptr, "RELOAD")) {
      /* reload cookies from file */
      Curl_cookie_loadfiles(data);
      break;
    }
    else {
      if(!data->cookies) {
        /* if cookie engine was not running, activate it */
        data->cookies = Curl_cookie_init(data, NULL, NULL, TRUE);
        if(!data->cookies)
          return CURLE_OUT_OF_MEMORY;
      }

      /* general protection against mistakes and abuse */
      if(strlen(ptr) > CURL_MAX_INPUT_LENGTH)
        return CURLE_BAD_FUNCTION_ARGUMENT;

      Curl_share_lock(data, CURL_LOCK_DATA_COOKIE, CURL_LOCK_ACCESS_SINGLE);
      if(checkprefix("Set-Cookie:", ptr))
        /* HTTP Header format line */
        Curl_cookie_add(data, data->cookies, TRUE, FALSE, ptr + 11, NULL,
                        NULL, TRUE);
      else
        /* Netscape format line */
        Curl_cookie_add(data, data->cookies, FALSE, FALSE, ptr, NULL,
                        NULL, TRUE);
      Curl_share_unlock(data, CURL_LOCK_DATA_COOKIE);
    }
    break;
#endif /* !CURL_DISABLE_COOKIES */

#endif /* ! CURL_DISABLE_HTTP */

  case CURLOPT_CUSTOMREQUEST:
    /*
     * Set a custom string to use as request
     */
    return Curl_setstropt(&data->set.str[STRING_CUSTOMREQUEST], ptr);

    /* we do not set
       data->set.method = HTTPREQ_CUSTOM;
       here, we continue as if we were using the already set type
       and this just changes the actual request keyword */

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY:
    /*
     * Set proxy server:port to use as proxy.
     *
     * If the proxy is set to "" (and CURLOPT_SOCKS_PROXY is set to "" or NULL)
     * we explicitly say that we do not want to use a proxy
     * (even though there might be environment variables saying so).
     *
     * Setting it to NULL, means no proxy but allows the environment variables
     * to decide for us (if CURLOPT_SOCKS_PROXY setting it to NULL).
     */
    return setproxy(data, ptr);

  case CURLOPT_PRE_PROXY:
    /*
     * Set proxy server:port to use as SOCKS proxy.
     *
     * If the proxy is set to "" or NULL we explicitly say that we do not want
     * to use the socks proxy.
     */
    return Curl_setstropt(&data->set.str[STRING_PRE_PROXY], ptr);
#endif   /* CURL_DISABLE_PROXY */

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_SOCKS5_GSSAPI_SERVICE:
  case CURLOPT_PROXY_SERVICE_NAME:
    /*
     * Set proxy authentication service name for Kerberos 5 and SPNEGO
     */
    return Curl_setstropt(&data->set.str[STRING_PROXY_SERVICE_NAME], ptr);
#endif
  case CURLOPT_SERVICE_NAME:
    /*
     * Set authentication service name for DIGEST-MD5, Kerberos 5 and SPNEGO
     */
    return Curl_setstropt(&data->set.str[STRING_SERVICE_NAME], ptr);

  case CURLOPT_HEADERDATA:
    /*
     * Custom pointer to pass the header write callback function
     */
    data->set.writeheader = ptr;
    break;
  case CURLOPT_READDATA:
    /*
     * FILE pointer to read the file to be uploaded from. Or possibly used as
     * argument to the read callback.
     */
    data->set.in_set = ptr;
    break;
  case CURLOPT_WRITEDATA:
    /*
     * FILE pointer to write to. Or possibly used as argument to the write
     * callback.
     */
    data->set.out = ptr;
    break;
  case CURLOPT_DEBUGDATA:
    /*
     * Set to a void * that should receive all error writes. This
     * defaults to CURLOPT_STDERR for normal operations.
     */
    data->set.debugdata = ptr;
    break;
  case CURLOPT_PROGRESSDATA:
    /*
     * Custom client data to pass to the progress callback
     */
    data->set.progress_client = ptr;
    break;
  case CURLOPT_SEEKDATA:
    /*
     * Seek control callback. Might be NULL.
     */
    data->set.seek_client = ptr;
    break;
  case CURLOPT_IOCTLDATA:
    /*
     * I/O control data pointer. Might be NULL.
     */
    data->set.ioctl_client = ptr;
    break;
  case CURLOPT_SSL_CTX_DATA:
    /*
     * Set an SSL_CTX callback parameter pointer
     */
#ifdef USE_SSL
    if(Curl_ssl_supports(data, SSLSUPP_SSL_CTX)) {
      data->set.ssl.fsslctxp = ptr;
      break;
    }
    else
#endif
      return CURLE_NOT_BUILT_IN;
  case CURLOPT_SOCKOPTDATA:
    /*
     * socket callback data pointer. Might be NULL.
     */
    data->set.sockopt_client = ptr;
    break;
  case CURLOPT_OPENSOCKETDATA:
    /*
     * socket callback data pointer. Might be NULL.
     */
    data->set.opensocket_client = ptr;
    break;
  case CURLOPT_RESOLVER_START_DATA:
    /*
     * resolver start callback data pointer. Might be NULL.
     */
    data->set.resolver_start_client = ptr;
    break;
  case CURLOPT_CLOSESOCKETDATA:
    /*
     * socket callback data pointer. Might be NULL.
     */
    data->set.closesocket_client = ptr;
    break;
  case CURLOPT_TRAILERDATA:
#ifndef CURL_DISABLE_HTTP
    data->set.trailer_data = ptr;
#endif
    break;
  case CURLOPT_PREREQDATA:
    data->set.prereq_userp = ptr;
    break;

  case CURLOPT_ERRORBUFFER:
    /*
     * Error buffer provided by the caller to get the human readable error
     * string in.
     */
    data->set.errorbuffer = ptr;
    break;

#ifndef CURL_DISABLE_FTP
  case CURLOPT_FTPPORT:
    /*
     * Use FTP PORT, this also specifies which IP address to use
     */
    result = Curl_setstropt(&data->set.str[STRING_FTPPORT], ptr);
    data->set.ftp_use_port = !!(data->set.str[STRING_FTPPORT]);
    break;

  case CURLOPT_FTP_ACCOUNT:
    return Curl_setstropt(&data->set.str[STRING_FTP_ACCOUNT], ptr);

  case CURLOPT_FTP_ALTERNATIVE_TO_USER:
    return Curl_setstropt(&data->set.str[STRING_FTP_ALTERNATIVE_TO_USER], ptr);

#ifdef HAVE_GSSAPI
  case CURLOPT_KRBLEVEL:
    /*
     * A string that defines the kerberos security level.
     */
    result = Curl_setstropt(&data->set.str[STRING_KRB_LEVEL], ptr);
    data->set.krb = !!(data->set.str[STRING_KRB_LEVEL]);
    break;
#endif
#endif
  case CURLOPT_URL:
    /*
     * The URL to fetch.
     */
    if(data->state.url_alloc) {
      Curl_safefree(data->state.url);
      data->state.url_alloc = FALSE;
    }
    result = Curl_setstropt(&data->set.str[STRING_SET_URL], ptr);
    data->state.url = data->set.str[STRING_SET_URL];
    break;

  case CURLOPT_USERPWD:
    /*
     * user:password to use in the operation
     */
    return setstropt_userpwd(ptr, &data->set.str[STRING_USERNAME],
                             &data->set.str[STRING_PASSWORD]);

  case CURLOPT_USERNAME:
    /*
     * authentication username to use in the operation
     */
    return Curl_setstropt(&data->set.str[STRING_USERNAME], ptr);

  case CURLOPT_PASSWORD:
    /*
     * authentication password to use in the operation
     */
    return Curl_setstropt(&data->set.str[STRING_PASSWORD], ptr);

  case CURLOPT_LOGIN_OPTIONS:
    /*
     * authentication options to use in the operation
     */
    return Curl_setstropt(&data->set.str[STRING_OPTIONS], ptr);

  case CURLOPT_XOAUTH2_BEARER:
    /*
     * OAuth 2.0 bearer token to use in the operation
     */
    return Curl_setstropt(&data->set.str[STRING_BEARER], ptr);

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXYUSERPWD: {
    /*
     * user:password needed to use the proxy
     */
    char *u = NULL;
    char *p = NULL;
    result = setstropt_userpwd(ptr, &u, &p);

    /* URL decode the components */
    if(!result && u) {
      Curl_safefree(data->set.str[STRING_PROXYUSERNAME]);
      result = Curl_urldecode(u, 0, &data->set.str[STRING_PROXYUSERNAME], NULL,
                              REJECT_ZERO);
    }
    if(!result && p) {
      Curl_safefree(data->set.str[STRING_PROXYPASSWORD]);
      result = Curl_urldecode(p, 0, &data->set.str[STRING_PROXYPASSWORD], NULL,
                              REJECT_ZERO);
    }
    free(u);
    free(p);
  }
    break;
  case CURLOPT_PROXYUSERNAME:
    /*
     * authentication username to use in the operation
     */
    return Curl_setstropt(&data->set.str[STRING_PROXYUSERNAME], ptr);

  case CURLOPT_PROXYPASSWORD:
    /*
     * authentication password to use in the operation
     */
    return Curl_setstropt(&data->set.str[STRING_PROXYPASSWORD], ptr);

  case CURLOPT_NOPROXY:
    /*
     * proxy exception list
     */
    return Curl_setstropt(&data->set.str[STRING_NOPROXY], ptr);
#endif /* ! CURL_DISABLE_PROXY */

  case CURLOPT_RANGE:
    /*
     * What range of the file you want to transfer
     */
    return Curl_setstropt(&data->set.str[STRING_SET_RANGE], ptr);

  case CURLOPT_CURLU:
    /*
     * pass CURLU to set URL
     */
    if(data->state.url_alloc) {
      Curl_safefree(data->state.url);
      data->state.url_alloc = FALSE;
    }
    else
      data->state.url = NULL;
    Curl_safefree(data->set.str[STRING_SET_URL]);
    data->set.uh = (CURLU *)ptr;
    break;
  case CURLOPT_SSLCERT:
    /*
     * String that holds filename of the SSL certificate to use
     */
    return Curl_setstropt(&data->set.str[STRING_CERT], ptr);

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_SSLCERT:
    /*
     * String that holds filename of the SSL certificate to use for proxy
     */
    return Curl_setstropt(&data->set.str[STRING_CERT_PROXY], ptr);

#endif
  case CURLOPT_SSLCERTTYPE:
    /*
     * String that holds file type of the SSL certificate to use
     */
    return Curl_setstropt(&data->set.str[STRING_CERT_TYPE], ptr);

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_SSLCERTTYPE:
    /*
     * String that holds file type of the SSL certificate to use for proxy
     */
    return Curl_setstropt(&data->set.str[STRING_CERT_TYPE_PROXY], ptr);

#endif
  case CURLOPT_SSLKEY:
    /*
     * String that holds filename of the SSL key to use
     */
    return Curl_setstropt(&data->set.str[STRING_KEY], ptr);

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_SSLKEY:
    /*
     * String that holds filename of the SSL key to use for proxy
     */
    return Curl_setstropt(&data->set.str[STRING_KEY_PROXY], ptr);

#endif
  case CURLOPT_SSLKEYTYPE:
    /*
     * String that holds file type of the SSL key to use
     */
    return Curl_setstropt(&data->set.str[STRING_KEY_TYPE], ptr);

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_SSLKEYTYPE:
    /*
     * String that holds file type of the SSL key to use for proxy
     */
    return Curl_setstropt(&data->set.str[STRING_KEY_TYPE_PROXY], ptr);

#endif
  case CURLOPT_KEYPASSWD:
    /*
     * String that holds the SSL or SSH private key password.
     */
    return Curl_setstropt(&data->set.str[STRING_KEY_PASSWD], ptr);

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_KEYPASSWD:
    /*
     * String that holds the SSL private key password for proxy.
     */
    return Curl_setstropt(&data->set.str[STRING_KEY_PASSWD_PROXY], ptr);

#endif
  case CURLOPT_SSLENGINE:
    /*
     * String that holds the SSL crypto engine.
     */
    if(ptr && ptr[0]) {
      result = Curl_setstropt(&data->set.str[STRING_SSL_ENGINE], ptr);
      if(!result) {
        result = Curl_ssl_set_engine(data, ptr);
      }
    }
    break;

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_HAPROXY_CLIENT_IP:
    /*
     * Set the client IP to send through HAProxy PROXY protocol
     */
    result = Curl_setstropt(&data->set.str[STRING_HAPROXY_CLIENT_IP], ptr);
    /* enable the HAProxy protocol */
    data->set.haproxyprotocol = TRUE;
    break;

#endif
  case CURLOPT_INTERFACE:
    /*
     * Set what interface or address/hostname to bind the socket to when
     * performing an operation and thus what from-IP your connection will use.
     */
    return setstropt_interface(ptr,
                               &data->set.str[STRING_DEVICE],
                               &data->set.str[STRING_INTERFACE],
                               &data->set.str[STRING_BINDHOST]);

  case CURLOPT_PINNEDPUBLICKEY:
    /*
     * Set pinned public key for SSL connection.
     * Specify filename of the public key in DER format.
     */
#ifdef USE_SSL
    if(Curl_ssl_supports(data, SSLSUPP_PINNEDPUBKEY))
      return Curl_setstropt(&data->set.str[STRING_SSL_PINNEDPUBLICKEY], ptr);
#endif
    return CURLE_NOT_BUILT_IN;

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_PINNEDPUBLICKEY:
    /*
     * Set pinned public key for SSL connection.
     * Specify filename of the public key in DER format.
     */
#ifdef USE_SSL
    if(Curl_ssl_supports(data, SSLSUPP_PINNEDPUBKEY))
      return Curl_setstropt(&data->set.str[STRING_SSL_PINNEDPUBLICKEY_PROXY],
                            ptr);
#endif
    return CURLE_NOT_BUILT_IN;
#endif
  case CURLOPT_CAINFO:
    /*
     * Set CA info for SSL connection. Specify filename of the CA certificate
     */
    return Curl_setstropt(&data->set.str[STRING_SSL_CAFILE], ptr);

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_CAINFO:
    /*
     * Set CA info SSL connection for proxy. Specify filename of the
     * CA certificate
     */
    return Curl_setstropt(&data->set.str[STRING_SSL_CAFILE_PROXY], ptr);

#endif
  case CURLOPT_CAPATH:
    /*
     * Set CA path info for SSL connection. Specify directory name of the CA
     * certificates which have been prepared using openssl c_rehash utility.
     */
#ifdef USE_SSL
    if(Curl_ssl_supports(data, SSLSUPP_CA_PATH))
      /* This does not work on Windows. */
      return Curl_setstropt(&data->set.str[STRING_SSL_CAPATH], ptr);
#endif
    return CURLE_NOT_BUILT_IN;
#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_CAPATH:
    /*
     * Set CA path info for SSL connection proxy. Specify directory name of the
     * CA certificates which have been prepared using openssl c_rehash utility.
     */
#ifdef USE_SSL
    if(Curl_ssl_supports(data, SSLSUPP_CA_PATH))
      /* This does not work on Windows. */
      return Curl_setstropt(&data->set.str[STRING_SSL_CAPATH_PROXY], ptr);
#endif
    return CURLE_NOT_BUILT_IN;
#endif
  case CURLOPT_CRLFILE:
    /*
     * Set CRL file info for SSL connection. Specify filename of the CRL
     * to check certificates revocation
     */
    return Curl_setstropt(&data->set.str[STRING_SSL_CRLFILE], ptr);

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_CRLFILE:
    /*
     * Set CRL file info for SSL connection for proxy. Specify filename of the
     * CRL to check certificates revocation
     */
    return Curl_setstropt(&data->set.str[STRING_SSL_CRLFILE_PROXY], ptr);

#endif
  case CURLOPT_ISSUERCERT:
    /*
     * Set Issuer certificate file
     * to check certificates issuer
     */
    return Curl_setstropt(&data->set.str[STRING_SSL_ISSUERCERT], ptr);

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_ISSUERCERT:
    /*
     * Set Issuer certificate file
     * to check certificates issuer
     */
    return Curl_setstropt(&data->set.str[STRING_SSL_ISSUERCERT_PROXY], ptr);

#endif
  case CURLOPT_PRIVATE:
    /*
     * Set private data pointer.
     */
    data->set.private_data = ptr;
    break;

#ifdef USE_SSL
  case CURLOPT_SSL_EC_CURVES:
    /*
     * Set accepted curves in SSL connection setup.
     * Specify colon-delimited list of curve algorithm names.
     */
    return Curl_setstropt(&data->set.str[STRING_SSL_EC_CURVES], ptr);

  case CURLOPT_SSL_SIGNATURE_ALGORITHMS:
    /*
     * Set accepted signature algorithms.
     * Specify colon-delimited list of signature scheme names.
     */
    if(Curl_ssl_supports(data, SSLSUPP_SIGNATURE_ALGORITHMS))
      return Curl_setstropt(&data->set.str[STRING_SSL_SIGNATURE_ALGORITHMS],
                            ptr);
    return CURLE_NOT_BUILT_IN;
#endif
#ifdef USE_SSH
  case CURLOPT_SSH_PUBLIC_KEYFILE:
    /*
     * Use this file instead of the $HOME/.ssh/id_dsa.pub file
     */
    return Curl_setstropt(&data->set.str[STRING_SSH_PUBLIC_KEY], ptr);

  case CURLOPT_SSH_PRIVATE_KEYFILE:
    /*
     * Use this file instead of the $HOME/.ssh/id_dsa file
     */
    return Curl_setstropt(&data->set.str[STRING_SSH_PRIVATE_KEY], ptr);

#if defined(USE_LIBSSH2) || defined(USE_LIBSSH)
  case CURLOPT_SSH_HOST_PUBLIC_KEY_MD5:
    /*
     * Option to allow for the MD5 of the host public key to be checked
     * for validation purposes.
     */
    return Curl_setstropt(&data->set.str[STRING_SSH_HOST_PUBLIC_KEY_MD5], ptr);

  case CURLOPT_SSH_KNOWNHOSTS:
    /*
     * Store the filename to read known hosts from.
     */
    return Curl_setstropt(&data->set.str[STRING_SSH_KNOWNHOSTS], ptr);
#endif
  case CURLOPT_SSH_KEYDATA:
    /*
     * Custom client data to pass to the SSH keyfunc callback
     */
    data->set.ssh_keyfunc_userp = ptr;
    break;
#ifdef USE_LIBSSH2
  case CURLOPT_SSH_HOST_PUBLIC_KEY_SHA256:
    /*
     * Option to allow for the SHA256 of the host public key to be checked
     * for validation purposes.
     */
    return Curl_setstropt(&data->set.str[STRING_SSH_HOST_PUBLIC_KEY_SHA256],
                          ptr);

  case CURLOPT_SSH_HOSTKEYDATA:
    /*
     * Custom client data to pass to the SSH keyfunc callback
     */
    data->set.ssh_hostkeyfunc_userp = ptr;
    break;
#endif /* USE_LIBSSH2 */
#endif /* USE_SSH */
  case CURLOPT_PROTOCOLS_STR:
    if(ptr)
      return protocol2num(ptr, &data->set.allowed_protocols);
    /* make a NULL argument reset to default */
    data->set.allowed_protocols = (curl_prot_t) CURLPROTO_ALL;
    break;

  case CURLOPT_REDIR_PROTOCOLS_STR:
    if(ptr)
      return protocol2num(ptr, &data->set.redir_protocols);
    /* make a NULL argument reset to default */
    data->set.redir_protocols = (curl_prot_t) CURLPROTO_REDIR;
    break;

  case CURLOPT_DEFAULT_PROTOCOL:
    /* Set the protocol to use when the URL does not include any protocol */
    return Curl_setstropt(&data->set.str[STRING_DEFAULT_PROTOCOL], ptr);

#ifndef CURL_DISABLE_SMTP
  case CURLOPT_MAIL_FROM:
    /* Set the SMTP mail originator */
    return Curl_setstropt(&data->set.str[STRING_MAIL_FROM], ptr);

  case CURLOPT_MAIL_AUTH:
    /* Set the SMTP auth originator */
    return Curl_setstropt(&data->set.str[STRING_MAIL_AUTH], ptr);
#endif
  case CURLOPT_SASL_AUTHZID:
    /* Authorization identity (identity to act as) */
    return Curl_setstropt(&data->set.str[STRING_SASL_AUTHZID], ptr);

#ifndef CURL_DISABLE_RTSP
  case CURLOPT_RTSP_SESSION_ID:
    /*
     * Set the RTSP Session ID manually. Useful if the application is
     * resuming a previously established RTSP session
     */
    return Curl_setstropt(&data->set.str[STRING_RTSP_SESSION_ID], ptr);

  case CURLOPT_RTSP_STREAM_URI:
    /*
     * Set the Stream URI for the RTSP request. Unless the request is
     * for generic server options, the application will need to set this.
     */
    return Curl_setstropt(&data->set.str[STRING_RTSP_STREAM_URI], ptr);

  case CURLOPT_RTSP_TRANSPORT:
    /*
     * The content of the Transport: header for the RTSP request
     */
    return Curl_setstropt(&data->set.str[STRING_RTSP_TRANSPORT], ptr);

  case CURLOPT_INTERLEAVEDATA:
    data->set.rtp_out = ptr;
    break;
#endif /* ! CURL_DISABLE_RTSP */
#ifndef CURL_DISABLE_FTP
  case CURLOPT_CHUNK_DATA:
    data->set.wildcardptr = ptr;
    break;
  case CURLOPT_FNMATCH_DATA:
    data->set.fnmatch_data = ptr;
    break;
#endif
#ifdef USE_TLS_SRP
  case CURLOPT_TLSAUTH_USERNAME:
    return Curl_setstropt(&data->set.str[STRING_TLSAUTH_USERNAME], ptr);

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_TLSAUTH_USERNAME:
    return Curl_setstropt(&data->set.str[STRING_TLSAUTH_USERNAME_PROXY], ptr);

#endif
  case CURLOPT_TLSAUTH_PASSWORD:
    return Curl_setstropt(&data->set.str[STRING_TLSAUTH_PASSWORD], ptr);

#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_TLSAUTH_PASSWORD:
    return Curl_setstropt(&data->set.str[STRING_TLSAUTH_PASSWORD_PROXY], ptr);
#endif
  case CURLOPT_TLSAUTH_TYPE:
    if(ptr && !strcasecompare(ptr, "SRP"))
      return CURLE_BAD_FUNCTION_ARGUMENT;
    break;
#ifndef CURL_DISABLE_PROXY
  case CURLOPT_PROXY_TLSAUTH_TYPE:
    if(ptr && !strcasecompare(ptr, "SRP"))
      return CURLE_BAD_FUNCTION_ARGUMENT;
    break;
#endif
#endif
#ifdef CURLRES_ARES
  case CURLOPT_DNS_SERVERS:
    result = Curl_setstropt(&data->set.str[STRING_DNS_SERVERS], ptr);
    if(result)
      return result;
    return Curl_async_ares_set_dns_servers(data);

  case CURLOPT_DNS_INTERFACE:
    result = Curl_setstropt(&data->set.str[STRING_DNS_INTERFACE], ptr);
    if(result)
      return result;
    return Curl_async_ares_set_dns_interface(data);

  case CURLOPT_DNS_LOCAL_IP4:
    result = Curl_setstropt(&data->set.str[STRING_DNS_LOCAL_IP4], ptr);
    if(result)
      return result;
    return Curl_async_ares_set_dns_local_ip4(data);

  case CURLOPT_DNS_LOCAL_IP6:
    result = Curl_setstropt(&data->set.str[STRING_DNS_LOCAL_IP6], ptr);
    if(result)
      return result;
    return Curl_async_ares_set_dns_local_ip6(data);

#endif
#ifdef USE_UNIX_SOCKETS
  case CURLOPT_UNIX_SOCKET_PATH:
    data->set.abstract_unix_socket = FALSE;
    return Curl_setstropt(&data->set.str[STRING_UNIX_SOCKET_PATH], ptr);

  case CURLOPT_ABSTRACT_UNIX_SOCKET:
    data->set.abstract_unix_socket = TRUE;
    return Curl_setstropt(&data->set.str[STRING_UNIX_SOCKET_PATH], ptr);

#endif

#ifndef CURL_DISABLE_DOH
  case CURLOPT_DOH_URL:
    result = Curl_setstropt(&data->set.str[STRING_DOH], ptr);
    data->set.doh = !!(data->set.str[STRING_DOH]);
    break;
#endif
#ifndef CURL_DISABLE_HSTS
  case CURLOPT_HSTSREADDATA:
    data->set.hsts_read_userp = ptr;
    break;
  case CURLOPT_HSTSWRITEDATA:
    data->set.hsts_write_userp = ptr;
    break;
  case CURLOPT_HSTS: {
    struct curl_slist *h;
    if(!data->hsts) {
      data->hsts = Curl_hsts_init();
      if(!data->hsts)
        return CURLE_OUT_OF_MEMORY;
    }
    if(ptr) {
      result = Curl_setstropt(&data->set.str[STRING_HSTS], ptr);
      if(result)
        return result;
      /* this needs to build a list of filenames to read from, so that it can
         read them later, as we might get a shared HSTS handle to load them
         into */
      h = curl_slist_append(data->state.hstslist, ptr);
      if(!h) {
        curl_slist_free_all(data->state.hstslist);
        data->state.hstslist = NULL;
        return CURLE_OUT_OF_MEMORY;
      }
      data->state.hstslist = h; /* store the list for later use */
    }
    else {
      /* clear the list of HSTS files */
      curl_slist_free_all(data->state.hstslist);
      data->state.hstslist = NULL;
      if(!data->share || !data->share->hsts)
        /* throw away the HSTS cache unless shared */
        Curl_hsts_cleanup(&data->hsts);
    }
    break;
  }
#endif /* ! CURL_DISABLE_HSTS */
#ifndef CURL_DISABLE_ALTSVC
  case CURLOPT_ALTSVC:
    if(!data->asi) {
      data->asi = Curl_altsvc_init();
      if(!data->asi)
        return CURLE_OUT_OF_MEMORY;
    }
    result = Curl_setstropt(&data->set.str[STRING_ALTSVC], ptr);
    if(result)
      return result;
    if(ptr)
      (void)Curl_altsvc_load(data->asi, ptr);
    break;
#endif /* ! CURL_DISABLE_ALTSVC */
#ifdef USE_ECH
  case CURLOPT_ECH: {
    size_t plen = 0;

    if(!ptr) {
      data->set.tls_ech = CURLECH_DISABLE;
      return CURLE_OK;
    }
    plen = strlen(ptr);
    if(plen > CURL_MAX_INPUT_LENGTH) {
      data->set.tls_ech = CURLECH_DISABLE;
      return CURLE_BAD_FUNCTION_ARGUMENT;
    }
    /* set tls_ech flag value, preserving CLA_CFG bit */
    if(!strcmp(ptr, "false"))
      data->set.tls_ech = CURLECH_DISABLE |
        (data->set.tls_ech & CURLECH_CLA_CFG);
    else if(!strcmp(ptr, "grease"))
      data->set.tls_ech = CURLECH_GREASE |
        (data->set.tls_ech & CURLECH_CLA_CFG);
    else if(!strcmp(ptr, "true"))
      data->set.tls_ech = CURLECH_ENABLE |
        (data->set.tls_ech & CURLECH_CLA_CFG);
    else if(!strcmp(ptr, "hard"))
      data->set.tls_ech = CURLECH_HARD |
        (data->set.tls_ech & CURLECH_CLA_CFG);
    else if(plen > 5 && !strncmp(ptr, "ecl:", 4)) {
      result = Curl_setstropt(&data->set.str[STRING_ECH_CONFIG], ptr + 4);
      if(result)
        return result;
      data->set.tls_ech |= CURLECH_CLA_CFG;
    }
    else if(plen > 4 && !strncmp(ptr, "pn:", 3)) {
      result = Curl_setstropt(&data->set.str[STRING_ECH_PUBLIC], ptr + 3);
      if(result)
        return result;
    }
    break;
  }
#endif
  default:
    return CURLE_UNKNOWN_OPTION;
  }
  return result;
}
#define DEB_KEEP setopt_cptr
#include "epilogue.h"
