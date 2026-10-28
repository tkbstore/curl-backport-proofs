/* curl lib/url.c @ curl-8_14_1 + Debian CVE-2026-3784.patch（D1）
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude_d.h"

static bool
proxy_info_matches(const struct proxy_info *data,
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
