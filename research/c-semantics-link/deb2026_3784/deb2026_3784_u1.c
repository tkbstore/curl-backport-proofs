/* curl lib/url.c @ 5f13a7645e565c5c1a06f3ef86e97afb856fb364（U1: 上流の修正後）
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude_u.h"

static bool proxy_info_matches(const struct proxy_info *data,
                               const struct proxy_info *needle)
{
  if((data->proxytype == needle->proxytype) &&
     (data->port == needle->port) &&
     curl_strequal(data->host.name, needle->host.name)) {

    if(Curl_timestrcmp(data->user, needle->user) ||
       Curl_timestrcmp(data->passwd, needle->passwd))
      return FALSE;
    return TRUE;
  }
  return FALSE;
}
#define DEB_KEEP proxy_info_matches
#include "epilogue.h"
