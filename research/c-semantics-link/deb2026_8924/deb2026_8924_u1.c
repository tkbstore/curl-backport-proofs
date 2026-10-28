/* curl lib/cookie.c @ 51beed175dbfc37da3113f6acce60c630c070ce8 (上流の修正後)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#define SIDE_U 1
#include "prelude.h"

static bool is_public_suffix(struct Curl_easy *data,
                             const struct Cookie *co,
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

    /* trim trailing dots */
    if(dlen && (domain[dlen - 1] == '.'))
      dlen--;
    if(clen && (co->domain[clen - 1] == '.'))
      clen--;

    if((dlen < sizeof(lcase)) && (clen < sizeof(lcookie))) {
      const psl_ctx_t *psl = Curl_psl_use(data);
      if(psl) {
        /* the PSL check requires lowercase domain name and pattern */
        Curl_strntolower(lcase, domain, dlen);
        lcase[dlen] = 0;
        Curl_strntolower(lcookie, co->domain, clen);
        lcookie[clen] = 0;
        acceptable = psl_is_cookie_domain_acceptable(psl, lcase, lcookie);
        Curl_psl_release(data);
      }
      else
        infof(data, "libpsl problem, rejecting cookie for safety");
    }

    if(!acceptable) {
      infof(data, "cookie '%s' dropped, domain '%s' must not "
            "set cookies for '%s'", co->name, domain, co->domain);
      return TRUE;
    }
  }
#else
  (void)data;
  (void)co;
  (void)domain;
  DEBUGF(infof(data, "NO PSL to check set-cookie '%s' for domain=%s in %s",
               co->name, co->domain, domain));
#endif
  return FALSE;
}
#include "epilogue.h"
