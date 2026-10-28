static bool cached_x509_store_different(
  struct Curl_cfilter *cf,
  const struct multi_ssl_backend_data *mb)
{
  struct ssl_primary_config *conn_config = Curl_ssl_cf_get_primary_config(cf);
  if(!mb->CAfile || !conn_config->CAfile)
    return mb->CAfile != conn_config->CAfile;

  return strcmp(mb->CAfile, conn_config->CAfile);
}
