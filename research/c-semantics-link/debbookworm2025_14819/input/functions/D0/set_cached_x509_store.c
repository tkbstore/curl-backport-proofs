static void set_cached_x509_store(struct Curl_cfilter *cf,
                                  const struct Curl_easy *data,
                                  X509_STORE *store)
{
  struct ssl_primary_config *conn_config = Curl_ssl_cf_get_primary_config(cf);
  struct Curl_multi *multi = data->multi_easy ? data->multi_easy : data->multi;
  struct multi_ssl_backend_data *mbackend;

  if(!multi)
    return;

  if(!multi->ssl_backend_data) {
    multi->ssl_backend_data = calloc(1, sizeof(struct multi_ssl_backend_data));
    if(!multi->ssl_backend_data)
      return;
  }

  mbackend = multi->ssl_backend_data;

  if(X509_STORE_up_ref(store)) {
    char *CAfile = NULL;

    if(conn_config->CAfile) {
      CAfile = strdup(conn_config->CAfile);
      if(!CAfile) {
        X509_STORE_free(store);
        return;
      }
    }

    if(mbackend->store) {
      X509_STORE_free(mbackend->store);
      free(mbackend->CAfile);
    }

    mbackend->time = Curl_now();
    mbackend->store = store;
    mbackend->CAfile = CAfile;
  }
}
