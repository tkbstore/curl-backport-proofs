static X509_STORE *ossl_get_cached_x509_store(struct Curl_cfilter *cf,
                                              const struct Curl_easy *data,
                                              bool *pempty)
{
  struct Curl_multi *multi = data->multi;
  struct ossl_x509_share *share;
  X509_STORE *store = NULL;

  DEBUGASSERT(multi);
  *pempty = TRUE;
  share = multi ? Curl_hash_pick(&multi->proto_hash,
                                 CURL_UNCONST(MPROTO_OSSL_X509_KEY),
                                 sizeof(MPROTO_OSSL_X509_KEY) - 1) : NULL;
  if(share && share->store &&
     !ossl_cached_x509_store_expired(data, share) &&
     !ossl_cached_x509_store_different(cf, data, share)) {
    store = share->store;
    *pempty = share->store_is_empty;
  }

  return store;
}
