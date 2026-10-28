/* curl lib/vtls/openssl.c (D0、input/D0/lib/vtls/openssl.c、sha256 82e9e76ce2957cc4e30cf6d057ee55fc19ad5746d63f6b0b04d8d3c748124dd9)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude.h"

static bool cached_x509_store_different(
  struct Curl_cfilter *cf,
  const struct multi_ssl_backend_data *mb)
{
  struct ssl_primary_config *conn_config = Curl_ssl_cf_get_primary_config(cf);
  if(!mb->CAfile || !conn_config->CAfile)
    return mb->CAfile != conn_config->CAfile;

  return strcmp(mb->CAfile, conn_config->CAfile);
}
#include "epilogue.h"
