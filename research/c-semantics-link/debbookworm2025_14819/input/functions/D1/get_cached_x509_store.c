static X509_STORE *get_cached_x509_store(struct Curl_cfilter *cf,
                                         const struct Curl_easy *data)
{
  struct Curl_multi *multi = data->multi_easy ? data->multi_easy : data->multi;
  X509_STORE *store = NULL;

  if(multi &&
     multi->ssl_backend_data &&
     multi->ssl_backend_data->store &&
     !cached_x509_store_expired(data, multi->ssl_backend_data) &&
     !cached_x509_store_different(cf, data, multi->ssl_backend_data)) {
    store = multi->ssl_backend_data->store;
  }

  return store;
}
