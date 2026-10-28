/* curl lib/url.c @ curl-8_14_1（D0）
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude_d.h"

static bool
proxy_info_matches(const struct proxy_info *data,
                   const struct proxy_info *needle)
{
  if((data->proxytype == needle->proxytype) &&
     (data->port == needle->port) &&
     strcasecompare(data->host.name, needle->host.name))
    return TRUE;

  return FALSE;
}
#define DEB_KEEP proxy_info_matches
#include "epilogue.h"
