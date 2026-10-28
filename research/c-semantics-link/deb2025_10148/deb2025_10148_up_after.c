/* curl lib/ws.c (@ 84db7a9eae8468c0445b15aa806fa7fa806fa0f2、上流の修正後)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude.h"

static CURLcode ws_enc_add_frame(struct Curl_easy *data,
                                 struct ws_encoder *enc,
                                 unsigned int flags,
                                 curl_off_t payload_len,
                                 struct bufq *out)
{
  unsigned char firstb = 0;
  unsigned char head[14];
  CURLcode result;
  size_t hlen, nwritten;

  if(payload_len < 0) {
    failf(data, "[WS] starting new frame with negative payload length %"
                FMT_OFF_T, payload_len);
    return CURLE_SEND_ERROR;
  }

  if(enc->payload_remain > 0) {
    /* trying to write a new frame before the previous one is finished */
    failf(data, "[WS] starting new frame with %zd bytes from last one "
                "remaining to be sent", (ssize_t)enc->payload_remain);
    return CURLE_SEND_ERROR;
  }

  result = ws_frame_flags2firstbyte(data, flags, enc->contfragment, &firstb);
  if(result)
    return result;

  /* fragmentation only applies to data frames (text/binary);
   * control frames (close/ping/pong) do not affect the CONT status */
  if(flags & (CURLWS_TEXT | CURLWS_BINARY)) {
    enc->contfragment = (flags & CURLWS_CONT) ? (bit)TRUE : (bit)FALSE;
  }

  if(flags & CURLWS_PING && payload_len > WS_MAX_CNTRL_LEN) {
    failf(data, "[WS] given PING frame is too big");
    return CURLE_TOO_LARGE;
  }
  if(flags & CURLWS_PONG && payload_len > WS_MAX_CNTRL_LEN) {
    failf(data, "[WS] given PONG frame is too big");
    return CURLE_TOO_LARGE;
  }
  if(flags & CURLWS_CLOSE && payload_len > WS_MAX_CNTRL_LEN) {
    failf(data, "[WS] given CLOSE frame is too big");
    return CURLE_TOO_LARGE;
  }

  head[0] = enc->firstbyte = firstb;
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

  /* 4 bytes random */

  result = Curl_rand(data, (unsigned char *)&enc->mask, sizeof(enc->mask));
  if(result)
    return result;

#ifdef DEBUGBUILD
  if(getenv("CURL_WS_FORCE_ZERO_MASK"))
    /* force the bit mask to 0x00000000, effectively disabling masking */
    memset(&enc->mask, 0, sizeof(enc->mask));
#endif

  /* add 4 bytes mask */
  memcpy(&head[hlen], &enc->mask, 4);
  hlen += 4;
  /* reset for payload to come */
  enc->xori = 0;

  result = Curl_bufq_write(out, head, hlen, &nwritten);
  if(result)
    return result;
  if(nwritten != hlen) {
    /* We use a bufq with SOFT_LIMIT, writing should always succeed */
    DEBUGASSERT(0);
    return CURLE_SEND_ERROR;
  }
  return CURLE_OK;
}
#include "epilogue.h"
