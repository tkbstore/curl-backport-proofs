/*
 * CVE-2025-10148（research/backport-proof-debian/cases/CVE-2025-10148.md）の翻訳単位の前置き。
 * 上流（ws_enc_add_frame）と 8.14.1（ws_enc_write_head）で、呼ばれる側の関数の型が違うので、DEB2025_10148_DEB で切り替える。
 *
 * ビルドの構成: USE_WEBSOCKETS。DEBUGBUILD は定義しない（Curl_rand は 3 引数、DEBUGASSERT は空のループ、CURL_WS_FORCE_ZERO_MASK の分岐は無い）
 * - 構造体 struct ws_encoder は lib/ws.c の宣言のまま（フィールドはすべて使う）。struct Curl_easy・struct bufq は不完全型
 * - マクロの展開: CURLWS_*（include/curl/websockets.h）、WSBIT_MASK・WS_MAX_CNTRL_LEN（lib/ws.c）、FMT_OFF_T は "lld"、
 *   DEBUGASSERT(x) は `do { } while(0)`（lib/curl_setup_once.h）、Curl_rand(a,b,c) は Curl_rand_bytes((a), (b), (c))（lib/rand.h）、
 *   failf は Curl_failf、BIT(x) は `bit x:1`
 * - 呼ばれる側の関数は extern の宣言（仕様は Lean 側で定理の仮定として与える）。ws_frame_flags2firstbyte・ws_enc_info は ws.c の static 関数
 */
typedef unsigned long size_t;
typedef long ssize_t;
typedef long long curl_off_t;
typedef _Bool bool;
typedef unsigned int bit;
#define BIT(x) bit x:1
#define TRUE 1
#define FALSE 0

#define CURLWS_TEXT       (1<<0)
#define CURLWS_BINARY     (1<<1)
#define CURLWS_CONT       (1<<2)
#define CURLWS_CLOSE      (1<<3)
#define CURLWS_PING       (1<<4)
#define CURLWS_PONG       (1<<6)
#define WSBIT_MASK 0x80
#define WS_MAX_CNTRL_LEN    125
#define FMT_OFF_T "lld"
#define DEBUGASSERT(x) do { } while(0)
#define failf Curl_failf
#define Curl_rand(a,b,c)   Curl_rand_bytes((a), (b), (c))

typedef enum {
  CURLE_OK = 0,
  CURLE_SEND_ERROR = 55,
  CURLE_TOO_LARGE = 100
} CURLcode;

struct Curl_easy;
struct bufq;

struct ws_encoder {
  curl_off_t payload_len;  /* payload length of current frame */
  curl_off_t payload_remain;  /* remaining payload of current */
  unsigned int xori; /* xor index */
  unsigned char mask[4]; /* 32-bit mask for this connection */
  unsigned char firstbyte; /* first byte of frame we encode */
  BIT(contfragment); /* set TRUE if the previous fragment sent was not final */
};

extern void Curl_failf(struct Curl_easy *data, const char *fmt, ...);
extern CURLcode Curl_rand_bytes(struct Curl_easy *data, unsigned char *rnd, size_t num);
extern void ws_enc_info(struct ws_encoder *enc, struct Curl_easy *data, const char *msg);
extern void *memcpy(void *dest, const void *src, size_t n);
#ifdef DEB2025_10148_DEB
extern unsigned char ws_frame_flags2firstbyte(struct Curl_easy *data, unsigned int flags,
                                              bool contfragment, CURLcode *err);
extern ssize_t Curl_bufq_write(struct bufq *q, const unsigned char *buf, size_t len,
                               CURLcode *err);
#else
extern CURLcode ws_frame_flags2firstbyte(struct Curl_easy *data, unsigned int flags,
                                         bool contfragment, unsigned char *pfirstbyte);
extern CURLcode Curl_bufq_write(struct bufq *q, const unsigned char *buf, size_t len,
                                size_t *pnwritten);
#endif
