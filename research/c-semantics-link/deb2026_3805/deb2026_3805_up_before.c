/* curl lib/smb.c (@ 22b0cbe65f6738bdf002f0331895aba52ae0633e、上流の修正前)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude.h"

static CURLcode smb_parse_url_path(struct Curl_easy *data,
                                   struct smb_conn *smbc,
                                   struct smb_request *req)
{
  char *path;
  char *slash;
  CURLcode result;

  /* URL decode the path */
  result = Curl_urldecode(data->state.up.path, 0, &path, NULL, REJECT_CTRL);
  if(result)
    return result;

  /* Parse the path for the share */
  smbc->share = curlx_strdup((*path == '/' || *path == '\\')
                             ? path + 1 : path);
  curlx_free(path);
  if(!smbc->share)
    return CURLE_OUT_OF_MEMORY;

  slash = strchr(smbc->share, '/');
  if(!slash)
    slash = strchr(smbc->share, '\\');

  /* The share must be present */
  if(!slash) {
    Curl_safefree(smbc->share);
    failf(data, "missing share in URL path for SMB");
    return CURLE_URL_MALFORMAT;
  }

  /* Parse the path for the file path converting any forward slashes into
     backslashes */
  *slash++ = 0;
  req->path = slash;

  for(; *slash; slash++) {
    if(*slash == '/')
      *slash = '\\';
  }
  return CURLE_OK;
}
#include "epilogue.h"
