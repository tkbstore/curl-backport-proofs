/* curl lib/curl_sasl.c @ 1a822275d333dc6da6043497160fd04c8fa48640 (上流の修正後)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#define SIDE_U 1
#include "enum_u.h"
#include "prelude.h"

struct sasl_ctx {
  struct SASL *sasl;
  struct connectdata *conn;
  const char *user;
  unsigned short enabledmechs;
  const char *mech;
  saslstate state1;
  saslstate state2;
  struct bufref resp;
  CURLcode result;
};

static bool sasl_choose_external(struct Curl_easy *data, struct sasl_ctx *sctx)
{
  if((sctx->enabledmechs & SASL_MECH_EXTERNAL) && !sctx->conn->passwd[0]) {
    sctx->mech = SASL_MECH_STRING_EXTERNAL;
    sctx->state1 = SASL_EXTERNAL;
    sctx->sasl->authused = SASL_MECH_EXTERNAL;

    if(sctx->sasl->force_ir || data->set.sasl_ir)
      Curl_auth_create_external_message(sctx->conn->user, &sctx->resp);
    return TRUE;
  }
  return FALSE;
}
static bool sasl_choose_oauth(struct Curl_easy *data, struct sasl_ctx *sctx)
{
  const char *oauth_bearer =
    (!data->state.this_is_a_follow || data->set.allow_auth_to_other_hosts) ?
    data->set.str[STRING_BEARER] : NULL;

  if(sctx->user && oauth_bearer &&
     (sctx->enabledmechs & SASL_MECH_OAUTHBEARER)) {
    const char *hostname;
    int port;
    Curl_conn_get_current_host(data, FIRSTSOCKET, &hostname, &port);

    sctx->mech = SASL_MECH_STRING_OAUTHBEARER;
    sctx->state1 = SASL_OAUTH2;
    sctx->state2 = SASL_OAUTH2_RESP;
    sctx->sasl->authused = SASL_MECH_OAUTHBEARER;

    if(sctx->sasl->force_ir || data->set.sasl_ir)
      sctx->result =
        Curl_auth_create_oauth_bearer_message(sctx->conn->user,
                                              hostname, port,
                                              oauth_bearer, &sctx->resp);
    return TRUE;
  }
  return FALSE;
}
static bool sasl_choose_oauth2(struct Curl_easy *data, struct sasl_ctx *sctx)
{
  const char *oauth_bearer =
    (!data->state.this_is_a_follow || data->set.allow_auth_to_other_hosts) ?
    data->set.str[STRING_BEARER] : NULL;

  if(sctx->user && oauth_bearer &&
     (sctx->enabledmechs & SASL_MECH_XOAUTH2)) {
    sctx->mech = SASL_MECH_STRING_XOAUTH2;
    sctx->state1 = SASL_OAUTH2;
    sctx->sasl->authused = SASL_MECH_XOAUTH2;

    if(sctx->sasl->force_ir || data->set.sasl_ir)
      sctx->result = Curl_auth_create_xoauth_bearer_message(sctx->conn->user,
                                                      oauth_bearer,
                                                      &sctx->resp);
    return TRUE;
  }
  return FALSE;
}
static bool sasl_choose_plain(struct Curl_easy *data, struct sasl_ctx *sctx)
{
  if(sctx->user && (sctx->enabledmechs & SASL_MECH_PLAIN)) {
    sctx->mech = SASL_MECH_STRING_PLAIN;
    sctx->state1 = SASL_PLAIN;
    sctx->sasl->authused = SASL_MECH_PLAIN;

    if(sctx->sasl->force_ir || data->set.sasl_ir)
      sctx->result =
        Curl_auth_create_plain_message(sctx->conn->sasl_authzid,
                                       sctx->conn->user, sctx->conn->passwd,
                                       &sctx->resp);
    return TRUE;
  }
  return FALSE;
}
static bool sasl_choose_login(struct Curl_easy *data, struct sasl_ctx *sctx)
{
  if(sctx->user && (sctx->enabledmechs & SASL_MECH_LOGIN)) {
    sctx->mech = SASL_MECH_STRING_LOGIN;
    sctx->state1 = SASL_LOGIN;
    sctx->state2 = SASL_LOGIN_PASSWD;
    sctx->sasl->authused = SASL_MECH_LOGIN;

    if(sctx->sasl->force_ir || data->set.sasl_ir)
      Curl_auth_create_login_message(sctx->conn->user, &sctx->resp);
    return TRUE;
  }
  return FALSE;
}
CURLcode Curl_sasl_start(struct SASL *sasl, struct Curl_easy *data,
                         bool force_ir, saslprogress *progress)
{
  struct sasl_ctx sctx;

  sasl->force_ir = force_ir;    /* Latch for future use */
  sasl->authused = 0;           /* No mechanism used yet */
  *progress = SASL_IDLE;

  memset(&sctx, 0, sizeof(sctx));
  sctx.sasl = sasl;
  sctx.conn = data->conn;
  sctx.user = data->state.aptr.user;
  Curl_bufref_init(&sctx.resp);
  sctx.enabledmechs = sasl->authmechs & sasl->prefmech;
  sctx.state1 = SASL_STOP;
  sctx.state2 = SASL_FINAL;

  /* Calculate the supported authentication mechanism, by decreasing order of
     security, as well as the initial response where appropriate */
  if(sasl_choose_external(data, &sctx) ||
#ifdef USE_KERBEROS5
     sasl_choose_krb5(data, &sctx) ||
#endif
#ifdef USE_GSASL
     sasl_choose_gsasl(data, &sctx) ||
#endif
#ifndef CURL_DISABLE_DIGEST_AUTH
     sasl_choose_digest(data, &sctx) ||
#endif
#ifdef USE_NTLM
     sasl_choose_ntlm(data, &sctx) ||
#endif
     sasl_choose_oauth(data, &sctx) ||
     sasl_choose_oauth2(data, &sctx) ||
     sasl_choose_plain(data, &sctx) ||
     sasl_choose_login(data, &sctx)) {
    /* selected, either we have a mechanism or a failure */
    DEBUGASSERT(sctx.mech || sctx.result);
  }

  if(!sctx.result && sctx.mech) {
    sasl->curmech = sctx.mech;
    if(Curl_bufref_ptr(&sctx.resp))
      sctx.result = build_message(sasl, &sctx.resp);

    if(sasl->params->maxirlen &&
       strlen(sctx.mech) + Curl_bufref_len(&sctx.resp) >
         sasl->params->maxirlen)
      Curl_bufref_free(&sctx.resp);

    if(!sctx.result)
      sctx.result = sasl->params->sendauth(data, sctx.mech, &sctx.resp);

    if(!sctx.result) {
      *progress = SASL_INPROGRESS;
      sasl_state(sasl, data, Curl_bufref_ptr(&sctx.resp) ?
                 sctx.state2 : sctx.state1);
    }
  }

  Curl_bufref_free(&sctx.resp);
  return sctx.result;
}
