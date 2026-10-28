/* curl lib/ws.c (@ curl-8_14_1、修正前)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#define DEB2025_10148_DEB 1
#include "prelude.h"

static ssize_t ws_enc_write_head(struct Curl_easy *data,
                                 struct ws_encoder *enc,
                                 unsigned int flags,
                                 curl_off_t payload_len,
                                 struct bufq *out,
                                 CURLcode *err)
{
  unsigned char firstbyte = 0;
  unsigned char head[14];
  size_t hlen;
  ssize_t n;

  if(payload_len < 0) {
    failf(data, "[WS] starting new frame with negative payload length %"
                FMT_OFF_T, payload_len);
    *err = CURLE_SEND_ERROR;
    return -1;
  }

  if(enc->payload_remain > 0) {
    /* trying to write a new frame before the previous one is finished */
    failf(data, "[WS] starting new frame with %zd bytes from last one "
                "remaining to be sent", (ssize_t)enc->payload_remain);
    *err = CURLE_SEND_ERROR;
    return -1;
  }

  firstbyte = ws_frame_flags2firstbyte(data, flags, enc->contfragment, err);
  if(*err) {
    return -1;
  }

  /* fragmentation only applies to data frames (text/binary);
   * control frames (close/ping/pong) do not affect the CONT status */
  if(flags & (CURLWS_TEXT | CURLWS_BINARY)) {
    enc->contfragment = (flags & CURLWS_CONT) ? (bit)TRUE : (bit)FALSE;
  }

  if(flags & CURLWS_PING && payload_len > 125) {
    /* The maximum valid size of PING frames is 125 bytes. */
    failf(data, "[WS] given PING frame is too big");
    *err = CURLE_TOO_LARGE;
    return -1;
  }
  if(flags & CURLWS_PONG && payload_len > 125) {
    /* The maximum valid size of PONG frames is 125 bytes. */
    failf(data, "[WS] given PONG frame is too big");
    *err = CURLE_TOO_LARGE;
    return -1;
  }
  if(flags & CURLWS_CLOSE && payload_len > 125) {
    /* The maximum valid size of CLOSE frames is 125 bytes. */
    failf(data, "[WS] given CLOSE frame is too big");
    *err = CURLE_TOO_LARGE;
    return -1;
  }

  head[0] = enc->firstbyte = firstbyte;
  if(payload_len > 65535) {
    head[1] = 127 | WSBIT_MASK;
    head[2] = (unsigned char)((payload_len >> 56) & 0xff);
    head[3] = (unsigned char)((payload_len >> 48) & 0xff);
    head[4] = (unsigned char)((payload_len >> 40) & 0xff);
    head[5] = (unsigned char)((payload_len >> 32) & 0xff);
    head[6] = (unsigned char)((payload_len >> 24) & 0xff);
    head[7] = (unsigned char)((payload_len >> 16) & 0xff);
    head[8] = (unsigned char)((payload_len >> 8) & 0xff);
    head[9] = (unsigned char)(payload_len & 0xff);
    hlen = 10;
  }
  else if(payload_len >= 126) {
    head[1] = 126 | WSBIT_MASK;
    head[2] = (unsigned char)((payload_len >> 8) & 0xff);
    head[3] = (unsigned char)(payload_len & 0xff);
    hlen = 4;
  }
  else {
    head[1] = (unsigned char)payload_len | WSBIT_MASK;
    hlen = 2;
  }

  enc->payload_remain = enc->payload_len = payload_len;
  ws_enc_info(enc, data, "sending");

  /* add 4 bytes mask */
  memcpy(&head[hlen], &enc->mask, 4);
  hlen += 4;
  /* reset for payload to come */
  enc->xori = 0;

  n = Curl_bufq_write(out, head, hlen, err);
  if(n < 0)
    return -1;
  if((size_t)n != hlen) {
    /* We use a bufq with SOFT_LIMIT, writing should always succeed */
    DEBUGASSERT(0);
    *err = CURLE_SEND_ERROR;
    return -1;
  }
  return n;
}
#include "epilogue.h"
