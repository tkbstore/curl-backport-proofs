/* curl lib/vquic/vquic-tls.c @ 3d91ca8cdb3b434226e743946d428b4dd3acf2c9 (修正後)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude.h"

CURLcode Curl_vquic_tls_verify_peer(struct curl_tls_ctx *ctx,
                                    struct Curl_cfilter *cf,
                                    struct Curl_easy *data,
                                    struct ssl_peer *peer)
{
  struct ssl_primary_config *conn_config;
  CURLcode result = CURLE_OK;

  conn_config = Curl_ssl_cf_get_primary_config(cf);
  if(!conn_config)
    return CURLE_FAILED_INIT;

#ifdef USE_OPENSSL
  (void)conn_config;
  result = Curl_ossl_check_peer_cert(cf, data, &ctx->ossl, peer);
#elif defined(USE_GNUTLS)
  result = Curl_gtls_verifyserver(cf, data, ctx->gtls.session,
                                  conn_config, &data->set.ssl, peer,
                                  data->set.str[STRING_SSL_PINNEDPUBLICKEY]);
  if(result)
    return result;
#elif defined(USE_WOLFSSL)
  (void)data;
  if(conn_config->verifyhost) {
    WOLFSSL_X509* cert = wolfSSL_get_peer_certificate(ctx->wssl.ssl);
    if(!cert)
      result = CURLE_OUT_OF_MEMORY;
    else if(peer->sni &&
      (wolfSSL_X509_check_host(cert, peer->sni, strlen(peer->sni), 0, NULL)
       == WOLFSSL_FAILURE))
      result = CURLE_PEER_FAILED_VERIFICATION;
    else if(!peer->sni &&
      (wolfSSL_X509_check_ip_asc(cert, peer->hostname, 0)
       == WOLFSSL_FAILURE))
      result = CURLE_PEER_FAILED_VERIFICATION;
    wolfSSL_X509_free(cert);
  }
  if(!result)
    result = Curl_wssl_verify_pinned(cf, data, &ctx->wssl);
#endif
  /* on error, remove any session we might have in the pool */
  if(result)
    Curl_ssl_scache_remove_all(cf, data, peer->scache_key);
  return result;
}