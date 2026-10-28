static bool ossl_cached_x509_store_different(struct Curl_cfilter *cf,
                                             const struct Curl_easy *data,
                                             const struct ossl_x509_share *mb)
{
  struct ssl_primary_config *conn_config = Curl_ssl_cf_get_primary_config(cf);
  struct ssl_config_data *ssl_config =
    Curl_ssl_cf_get_config(cf, CURL_UNCONST(data));
  if(mb->no_partialchain != ssl_config->no_partialchain)
    return TRUE;
  if(!mb->CAfile || !conn_config->CAfile)
    return mb->CAfile != conn_config->CAfile;
  return strcmp(mb->CAfile, conn_config->CAfile);
}
