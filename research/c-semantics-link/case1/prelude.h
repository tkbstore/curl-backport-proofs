/*
 * Case 1 (CURL-CVE-2026-92387) の翻訳単位の前置き。PROTOCOL §4 で許した「関数の外側の変更」だけを置く。
 *
 * 出典: curl 753735af87f5c30cb6f60a70342f8bc4bc5fd5db（修正後）と親 4a608405b6911e2fe374fca4239b3480a4e0cb2f（修正前）
 * ビルドの構成: Windows 以外（SOCKERRNO = errno）。errno は glibc の定義（*__errno_location()）
 * - 構造体は、対象の関数が触るフィールドだけに減らした（並びは curl の宣言順を保つ）
 *     struct dynbuf          lib/curlx/dynbuf.h:27  中身は触らない（外部関数だけが触る）ので bufr・leng だけ残す
 *     struct pingpong        lib/pingpong.h:48      nread_resp, recvbuf, overflow, nfinal, endofresp, pending_resp
 *     struct SingleRequest   lib/request.h          headerbytecount（lib/request.h:85）
 *     struct Curl_easy       lib/urldata.h          conn（:1176）, req（:1208）
 * - マクロは curl の非デバッグビルドの定義をそのまま写した
 *     BIT / FALSE                      lib/curl_setup.h
 *     SOCKERRNO                        lib/curl_setup.h:1041
 *     failf                            lib/curl_trc.h:62
 *     CLIENTWRITE_INFO                 lib/sendf.h:44
 * - CURLcode は使う4つの値だけ、curl_infotype は使う1つの値だけ（include/curl/curl.h と同じ値）
 * - 呼ばれる側の関数は extern の宣言にした。仕様は Lean 側で定理の仮定として与える
 *     Curl_conn_recv     lib/cfilters.h:614
 *     curlx_dyn_addn / curlx_dyn_reset / curlx_dyn_tail / curlx_dyn_ptr / curlx_dyn_len  lib/curlx/dynbuf.h:39-52
 *     Curl_failf         lib/curl_trc.h:59（可変長引数）
 *     Curl_debug         lib/curl_trc.h:53
 *     Curl_client_write  lib/sendf.h:62
 *     memchr             <string.h>
 *     __errno_location   glibc <errno.h>
 *   pingpong_read（lib/pingpong.c:224）は同じ翻訳単位の static 関数なので、本体ごと入れる
 */
#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

typedef unsigned int curl_bit;
#define BIT(x) curl_bit x:1
#define FALSE false

typedef enum {
  CURLE_OK = 0,
  CURLE_WEIRD_SERVER_REPLY = 8,
  CURLE_RECV_ERROR = 56,
  CURLE_AGAIN = 81
} CURLcode;

typedef enum {
  CURLINFO_HEADER_IN = 1
} curl_infotype;

#define CLIENTWRITE_INFO (1 << 1)

extern int *__errno_location(void);
#define errno (*__errno_location())
#define SOCKERRNO errno

struct connectdata;

struct dynbuf {
  char *bufr;
  size_t leng;
};

struct SingleRequest {
  unsigned int headerbytecount;
};

struct Curl_easy {
  struct connectdata *conn;
  struct SingleRequest req;
};

struct pingpong {
  size_t nread_resp;
  struct dynbuf recvbuf;
  size_t overflow;
  size_t nfinal;
  bool (*endofresp)(struct Curl_easy *data, struct connectdata *conn,
                    const char *ptr, size_t len, int *code);
  BIT(pending_resp);
};

extern CURLcode Curl_conn_recv(struct Curl_easy *data, int8_t sockindex,
                               char *buf, size_t len, size_t *pnread);
extern CURLcode curlx_dyn_addn(struct dynbuf *s, const void *mem, size_t len);
extern void curlx_dyn_reset(struct dynbuf *s);
extern CURLcode curlx_dyn_tail(struct dynbuf *s, size_t trail);
extern char *curlx_dyn_ptr(const struct dynbuf *s);
extern size_t curlx_dyn_len(const struct dynbuf *s);
extern void Curl_debug(struct Curl_easy *data, curl_infotype type,
                       const char *ptr, size_t size);
extern void Curl_failf(struct Curl_easy *data, const char *fmt, ...);
#define failf Curl_failf
extern CURLcode Curl_client_write(struct Curl_easy *data, int type,
                                  const char *buf, size_t blen);
extern void *memchr(const void *s, int c, size_t n);
