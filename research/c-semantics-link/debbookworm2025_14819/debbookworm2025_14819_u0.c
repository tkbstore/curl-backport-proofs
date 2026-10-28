/* curl lib/vtls/openssl.c (U0、input/U0/lib/vtls/openssl.c、sha256 2a06ac1123968c6df23d68b68435664ec32853ebf443955070e030d12c4e5fba)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#define DEBBW_UP 1
#include "prelude.h"

static bool ossl_cached_x509_store_different(struct Curl_cfilter *cf,
                                             const struct ossl_x509_share *mb)
{
  struct ssl_primary_config *conn_config = Curl_ssl_cf_get_primary_config(cf);
  if(!mb->CAfile || !conn_config->CAfile)
    return mb->CAfile != conn_config->CAfile;

  return strcmp(mb->CAfile, conn_config->CAfile);
}
#include "epilogue.h"
