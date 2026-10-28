/* curl lib/vtls/openssl.c (U1、input/U1/lib/vtls/openssl.c、sha256 ccc495acfddccefb036356eae46ea28b7e9ac9a11a9551d9207dc6ebae4747e0)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#define DEBBW_UP 1
#define DEBBW_AFTER 1
#include "prelude.h"

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
#include "epilogue.h"
