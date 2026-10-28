/* curl lib/pingpong.c @ 4a608405b6911e2fe374fca4239b3480a4e0cb2f (修正前)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude.h"

static CURLcode pingpong_read(struct Curl_easy *data,
                              int8_t sockindex,
                              char *buffer,
                              size_t buflen,
                              size_t *nread)
{
  return Curl_conn_recv(data, sockindex, buffer, buflen, nread);
}
CURLcode Curl_pp_readresp(struct Curl_easy *data,
                          int8_t sockindex,
                          struct pingpong *pp,
                          int *code, /* return the server code if done */
                          size_t *size) /* size of the response */
{
  struct connectdata *conn = data->conn;
  CURLcode result = CURLE_OK;
  size_t gotbytes;
  char buffer[900];

  *code = 0; /* 0 for errors or not done */
  *size = 0;

  do {
    gotbytes = 0;
    if(pp->nfinal) {
      /* a previous call left this many bytes in the beginning of the buffer as
         that was the final line; now ditch that */
      size_t full = curlx_dyn_len(&pp->recvbuf);

      /* trim off the "final" leading part */
      curlx_dyn_tail(&pp->recvbuf, full - pp->nfinal);

      pp->nfinal = 0; /* now gone */
    }
    if(!pp->overflow) {
      result = pingpong_read(data, sockindex, buffer, sizeof(buffer),
                             &gotbytes);
      if(result == CURLE_AGAIN)
        return CURLE_OK;

      if(result)
        return result;

      if(!gotbytes) {
        failf(data, "response reading failed (errno: %d)", SOCKERRNO);
        return CURLE_RECV_ERROR;
      }

      result = curlx_dyn_addn(&pp->recvbuf, buffer, gotbytes);
      if(result)
        return result;

      data->req.headerbytecount += (unsigned int)gotbytes;

      pp->nread_resp += gotbytes;
    }

    do {
      const char *line = curlx_dyn_ptr(&pp->recvbuf);
      const char *nl = memchr(line, '\n', curlx_dyn_len(&pp->recvbuf));
      if(nl) {
        /* a newline is CRLF in pp-talk, so the CR is ignored as
           the line is not really terminated until the LF comes */
        size_t length = nl - line + 1;

        if(memchr(line, 0, length)) {
          /* The response line is passed on as a "header" below, so reject an
             embedded nul the same way verify_header() does for HTTP. */
          failf(data, "Nul byte in server response line");
          return CURLE_WEIRD_SERVER_REPLY;
        }

        /* output debug output if that is requested */
        Curl_debug(data, CURLINFO_HEADER_IN, line, length);

        /*
         * Pass all response-lines to the callback function registered for
         * "headers". The response lines can be seen as a kind of headers.
         */
        result = Curl_client_write(data, CLIENTWRITE_INFO, line, length);
        if(result)
          return result;

        if(pp->endofresp(data, conn, line, length, code)) {
          /* When at "end of response", keep the endofresp line first in the
             buffer since it will be accessed outside (by pingpong
             parsers). Store the overflow counter to inform about additional
             data in this buffer after the endofresp line. */
          pp->nfinal = length;
          if(curlx_dyn_len(&pp->recvbuf) > length)
            pp->overflow = curlx_dyn_len(&pp->recvbuf) - length;
          else
            pp->overflow = 0;
          *size = pp->nread_resp; /* size of the response */
          pp->nread_resp = 0; /* restart */
          gotbytes = 0; /* force break out of outer loop */
          break;
        }
        if(curlx_dyn_len(&pp->recvbuf) > length)
          /* keep the remaining piece */
          curlx_dyn_tail((&pp->recvbuf), curlx_dyn_len(&pp->recvbuf) - length);
        else
          curlx_dyn_reset(&pp->recvbuf);
      }
      else {
        /* without a newline, there is no overflow */
        pp->overflow = 0;
        break;
      }

    } while(1); /* while there is buffer left to scan */

  } while(gotbytes == sizeof(buffer));

  pp->pending_resp = FALSE;

  return result;
}