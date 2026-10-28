/* curl lib/vtls/openssl.c (D1、input/D1/lib/vtls/openssl.c、sha256 926b585b7eb9e7fa0884a17628c2830f9a2be1fdd6aaff7107fb14284188aa35)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#define DEBBW_AFTER 1
#include "prelude.h"

static bool cached_x509_store_different(
  struct Curl_cfilter *cf,
  const struct Curl_easy *data,
  const struct multi_ssl_backend_data *mb)
{
  struct ssl_primary_config *conn_config = Curl_ssl_cf_get_primary_config(cf);
  struct ssl_config_data *ssl_config =
    Curl_ssl_cf_get_config(cf, (struct Curl_easy *)data);
  if(mb->no_partialchain != ssl_config->no_partialchain)
    return true;
  if(!mb->CAfile || !conn_config->CAfile)
    return mb->CAfile != conn_config->CAfile;

  return strcmp(mb->CAfile, conn_config->CAfile);
}
#include "epilogue.h"
