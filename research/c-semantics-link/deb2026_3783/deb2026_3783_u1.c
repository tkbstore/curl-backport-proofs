/* curl lib/http.c @ e3d7401a32a46516c9e5ee877e613e62ed35bddc (上流の修正後)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#define SIDE_U 1
#include "enum_u.h"
#include "prelude.h"

static CURLcode output_auth_headers(struct Curl_easy *data,
                                    struct connectdata *conn,
                                    struct auth *authstatus,
                                    const char *request,
                                    const char *path,
                                    bool proxy)
{
  const char *auth = NULL;
  CURLcode result = CURLE_OK;
  (void)conn;

#ifdef CURL_DISABLE_DIGEST_AUTH
  (void)request;
  (void)path;
#endif
#ifndef CURL_DISABLE_AWS
  if((authstatus->picked == CURLAUTH_AWS_SIGV4) && !proxy) {
    /* this method is never for proxy */
    auth = "AWS_SIGV4";
    result = Curl_output_aws_sigv4(data);
    if(result)
      return result;
  }
  else
#endif
#ifdef USE_SPNEGO
  if(authstatus->picked == CURLAUTH_NEGOTIATE) {
    auth = "Negotiate";
    result = Curl_output_negotiate(data, conn, proxy);
    if(result)
      return result;
  }
  else
#endif
#ifdef USE_NTLM
  if(authstatus->picked == CURLAUTH_NTLM) {
    auth = "NTLM";
    result = Curl_output_ntlm(data, proxy);
    if(result)
      return result;
  }
  else
#endif
#ifndef CURL_DISABLE_DIGEST_AUTH
  if(authstatus->picked == CURLAUTH_DIGEST) {
    auth = "Digest";
    result = Curl_output_digest(data,
                                proxy,
                                (const unsigned char *)request,
                                (const unsigned char *)path);
    if(result)
      return result;
  }
  else
#endif
#ifndef CURL_DISABLE_BASIC_AUTH
  if(authstatus->picked == CURLAUTH_BASIC) {
    /* Basic */
    if(
#ifndef CURL_DISABLE_PROXY
       (proxy && conn->bits.proxy_user_passwd &&
        !Curl_checkProxyheaders(data, conn,
                                STRCONST("Proxy-authorization"))) ||
#endif
       (!proxy && data->state.aptr.user &&
        !Curl_checkheaders(data, STRCONST("Authorization")))) {
      auth = "Basic";
      result = http_output_basic(data, proxy);
      if(result)
        return result;
    }

    /* NOTE: this function should set 'done' TRUE, as the other auth
       functions work that way */
    authstatus->done = TRUE;
  }
#endif
#ifndef CURL_DISABLE_BEARER_AUTH
  if(authstatus->picked == CURLAUTH_BEARER) {
    /* Bearer */
    if(!proxy && data->set.str[STRING_BEARER] &&
       Curl_auth_allowed_to_host(data) &&
       !Curl_checkheaders(data, STRCONST("Authorization"))) {
      auth = "Bearer";
      result = http_output_bearer(data);
      if(result)
        return result;
    }

    /* NOTE: this function should set 'done' TRUE, as the other auth
       functions work that way */
    authstatus->done = TRUE;
  }
#endif

  if(auth) {
#ifndef CURL_DISABLE_PROXY
    infof(data, "%s auth using %s with user '%s'",
          proxy ? "Proxy" : "Server", auth,
          proxy ? (data->state.aptr.proxyuser ?
                   data->state.aptr.proxyuser : "") :
          (data->state.aptr.user ?
           data->state.aptr.user : ""));
#else
    (void)proxy;
    infof(data, "Server auth using %s with user '%s'",
          auth, data->state.aptr.user ?
          data->state.aptr.user : "");
#endif
    authstatus->multipass = !authstatus->done;
  }
  else
    authstatus->multipass = FALSE;

  return result;
}
#include "epilogue.h"
