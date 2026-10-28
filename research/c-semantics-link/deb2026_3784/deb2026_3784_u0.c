/* curl lib/url.c @ e47b6e657aa5dda6dfb79d495ba3ee7b0534532a（U0: 上流の修正前）
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude_u.h"

static bool proxy_info_matches(const struct proxy_info *data,
                               const struct proxy_info *needle)
{
  if((data->proxytype == needle->proxytype) &&
     (data->port == needle->port) &&
     curl_strequal(data->host.name, needle->host.name))
    return TRUE;

  return FALSE;
}
#define DEB_KEEP proxy_info_matches
#include "epilogue.h"
