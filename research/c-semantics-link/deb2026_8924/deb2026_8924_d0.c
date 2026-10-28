/* curl lib/cookie.c @ curl-8_14_1 (8.14.1、パッチを当てる前)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#define SIDE_D 1
#include "prelude.h"

static int
is_public_suffix(struct Curl_easy *data,
                 struct Cookie *co,
                 const char *domain)
{
#ifdef USE_LIBPSL
  /*
   * Check if the domain is a Public Suffix and if yes, ignore the cookie. We
   * must also check that the data handle is not NULL since the psl code will
   * dereference it.
   */
  DEBUGF(infof(data, "PSL check set-cookie '%s' for domain=%s in %s",
         co->name, co->domain, domain));
  if(data && (domain && co->domain && !Curl_host_is_ipnum(co->domain))) {
    bool acceptable = FALSE;
    char lcase[256];
    char lcookie[256];
    size_t dlen = strlen(domain);
    size_t clen = strlen(co->domain);
    if((dlen < sizeof(lcase)) && (clen < sizeof(lcookie))) {
      const psl_ctx_t *psl = Curl_psl_use(data);
      if(psl) {
        /* the PSL check requires lowercase domain name and pattern */
        Curl_strntolower(lcase, domain, dlen + 1);
        Curl_strntolower(lcookie, co->domain, clen + 1);
        acceptable = psl_is_cookie_domain_acceptable(psl, lcase, lcookie);
        Curl_psl_release(data);
      }
      else
        infof(data, "libpsl problem, rejecting cookie for satety");
    }

    if(!acceptable) {
      infof(data, "cookie '%s' dropped, domain '%s' must not "
            "set cookies for '%s'", co->name, domain, co->domain);
      return CERR_PSL;
    }
  }
#else
  (void)data;
  (void)co;
  (void)domain;
  DEBUGF(infof(data, "NO PSL to check set-cookie '%s' for domain=%s in %s",
         co->name, co->domain, domain));
#endif
  return CERR_OK;
}
#include "epilogue.h"
