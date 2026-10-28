static void ossl_set_cached_x509_store(struct Curl_cfilter *cf,
                                       const struct Curl_easy *data,
                                       X509_STORE *store,
                                       bool is_empty)
{
  struct ssl_primary_config *conn_config = Curl_ssl_cf_get_primary_config(cf);
  struct Curl_multi *multi = data->multi;
  struct ossl_x509_share *share;

  DEBUGASSERT(multi);
  if(!multi)
    return;
  share = Curl_hash_pick(&multi->proto_hash,
                         CURL_UNCONST(MPROTO_OSSL_X509_KEY),
                         sizeof(MPROTO_OSSL_X509_KEY) - 1);

  if(!share) {
    share = curlx_calloc(1, sizeof(*share));
    if(!share)
      return;
    if(!Curl_hash_add2(&multi->proto_hash,
                       CURL_UNCONST(MPROTO_OSSL_X509_KEY),
                       sizeof(MPROTO_OSSL_X509_KEY) - 1,
                       share, oss_x509_share_free)) {
      curlx_free(share);
      return;
    }
  }

  if(X509_STORE_up_ref(store)) {
    char *CAfile = NULL;

    if(conn_config->CAfile) {
      CAfile = curlx_strdup(conn_config->CAfile);
      if(!CAfile) {
        X509_STORE_free(store);
        return;
      }
    }

    if(share->store) {
      X509_STORE_free(share->store);
      curlx_free(share->CAfile);
    }

    share->time = data->progress.now;
    share->store = store;
    share->store_is_empty = is_empty;
    share->CAfile = CAfile;
  }
}
