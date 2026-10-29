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
  result = Curl_oss_check_peer_cert(cf, data, &ctx->ossl, peer);
#elif defined(USE_GNUTLS)
  result = Curl_gtls_verifyserver(data, ctx->gtls.session,
                                  conn_config, &data->set.ssl, peer,
                                  data->set.str[STRING_SSL_PINNEDPUBLICKEY]);
  if(result)
    return result;
#elif defined(USE_WOLFSSL)
  (void)data;
  if(conn_config->verifyhost) {
    char *snihost = peer->sni ? peer->sni : peer->hostname;
    WOLFSSL_X509* cert = wolfSSL_get_peer_certificate(ctx->wssl.ssl);
    if(wolfSSL_X509_check_host(cert, snihost, strlen(snihost), 0, NULL)
          == WOLFSSL_FAILURE) {
      result = CURLE_PEER_FAILED_VERIFICATION;
    }
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
