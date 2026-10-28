/* curl lib/tftp.c @ curl-8_14_1 (バックポート後)
 * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */
#include "prelude.h"

static CURLcode tftp_send_first(struct tftp_conn *state,
                                tftp_event_t event)
{
  size_t sbytes;
  ssize_t senddata;
  const char *mode = "octet";
  char *filename;
  struct Curl_easy *data = state->data;
  CURLcode result = CURLE_OK;

  /* Set ASCII mode if -B flag was used */
  if(data->state.prefer_ascii)
    mode = "netascii";

  switch(event) {

  case TFTP_EVENT_INIT:    /* Send the first packet out */
  case TFTP_EVENT_TIMEOUT: /* Resend the first packet out */
    /* Increment the retry counter, quit if over the limit */
    state->retries++;
    if(state->retries > state->retry_max) {
      state->error = TFTP_ERR_NORESPONSE;
      state->state = TFTP_STATE_FIN;
      return result;
    }

    if(data->state.upload) {
      /* If we are uploading, send an WRQ */
      setpacketevent(&state->spacket, TFTP_EVENT_WRQ);
      if(data->state.infilesize != -1)
        Curl_pgrsSetUploadSize(data, data->state.infilesize);
    }
    else {
      /* If we are downloading, send an RRQ */
      setpacketevent(&state->spacket, TFTP_EVENT_RRQ);
    }
    /* As RFC3617 describes the separator slash is not actually part of the
       filename so we skip the always-present first letter of the path
       string. */
    result = Curl_urldecode(&state->data->state.up.path[1], 0,
                            &filename, NULL, REJECT_ZERO);
    if(result)
      return result;

    if(strlen(filename) > (state->blksize - strlen(mode) - 4)) {
      failf(data, "TFTP filename too long");
      free(filename);
      return CURLE_TFTP_ILLEGAL; /* too long filename field */
    }

    msnprintf((char *)state->spacket.data + 2,
              state->blksize,
              "%s%c%s%c", filename, '\0',  mode, '\0');
    sbytes = 4 + strlen(filename) + strlen(mode);

    /* optional addition of TFTP options */
    if(!data->set.tftp_no_options) {
      char buf[64];
      /* add tsize option */
      msnprintf(buf, sizeof(buf), "%" FMT_OFF_T,
                data->state.upload && (data->state.infilesize != -1) ?
                data->state.infilesize : 0);

      result = tftp_option_add(state, &sbytes,
                               (char *)state->spacket.data + sbytes,
                               TFTP_OPTION_TSIZE);
      if(result == CURLE_OK)
        result = tftp_option_add(state, &sbytes,
                                 (char *)state->spacket.data + sbytes, buf);

      /* add blksize option */
      msnprintf(buf, sizeof(buf), "%d", state->requested_blksize);
      if(result == CURLE_OK)
        result = tftp_option_add(state, &sbytes,
                                 (char *)state->spacket.data + sbytes,
                                 TFTP_OPTION_BLKSIZE);
      if(result == CURLE_OK)
        result = tftp_option_add(state, &sbytes,
                                 (char *)state->spacket.data + sbytes, buf);

      /* add timeout option */
      msnprintf(buf, sizeof(buf), "%d", state->retry_time);
      if(result == CURLE_OK)
        result = tftp_option_add(state, &sbytes,
                                 (char *)state->spacket.data + sbytes,
                                 TFTP_OPTION_INTERVAL);
      if(result == CURLE_OK)
        result = tftp_option_add(state, &sbytes,
                                 (char *)state->spacket.data + sbytes, buf);

      if(result != CURLE_OK) {
        failf(data, "TFTP buffer too small for options");
        free(filename);
        return CURLE_TFTP_ILLEGAL;
      }
    }

    /* the typecase for the 3rd argument is mostly for systems that do
       not have a size_t argument, like older unixes that want an 'int' */
#ifdef __AMIGA__
#define CURL_SENDTO_ARG5(x) CURL_UNCONST(x)
#else
#define CURL_SENDTO_ARG5(x) (x)
#endif
    senddata = sendto(state->sockfd, (void *)state->spacket.data,
                      (SEND_TYPE_ARG3)sbytes, 0,
                      CURL_SENDTO_ARG5(&data->conn->remote_addr->curl_sa_addr),
                      (curl_socklen_t)data->conn->remote_addr->addrlen);
    if(senddata != (ssize_t)sbytes) {
      char buffer[STRERROR_LEN];
      failf(data, "%s", Curl_strerror(SOCKERRNO, buffer, sizeof(buffer)));
    }
    free(filename);
    break;

  case TFTP_EVENT_OACK:
    if(data->state.upload) {
      result = tftp_connect_for_tx(state, event);
    }
    else {
      result = tftp_connect_for_rx(state, event);
    }
    break;

  case TFTP_EVENT_ACK: /* Connected for transmit */
    if(!data->state.upload)
      return CURLE_TFTP_ILLEGAL;
    result = tftp_connect_for_tx(state, event);
    break;

  case TFTP_EVENT_DATA: /* Connected for receive */
    if(data->state.upload)
      return CURLE_TFTP_ILLEGAL;
    result = tftp_connect_for_rx(state, event);
    break;

  case TFTP_EVENT_ERROR:
    state->state = TFTP_STATE_FIN;
    break;

  default:
    failf(state->data, "tftp_send_first: internal error");
    break;
  }

  return result;
}
static CURLcode tftp_tx(struct tftp_conn *state, tftp_event_t event)
{
  struct Curl_easy *data = state->data;
  ssize_t sbytes;
  CURLcode result = CURLE_OK;
  struct SingleRequest *k = &data->req;
  size_t cb; /* Bytes currently read */
  char buffer[STRERROR_LEN];
  char *bufptr;
  bool eos;

  if(!data->state.upload)
    return CURLE_TFTP_ILLEGAL;

  switch(event) {

  case TFTP_EVENT_ACK:
  case TFTP_EVENT_OACK:
    if(event == TFTP_EVENT_ACK) {
      /* Ack the packet */
      int rblock = getrpacketblock(&state->rpacket);

      if(rblock != state->block &&
         /* There is a bug in tftpd-hpa that causes it to send us an ack for
          * 65535 when the block number wraps to 0. So when we are expecting
          * 0, also accept 65535. See
          * https://www.syslinux.org/archives/2010-September/015612.html
          * */
         !(state->block == 0 && rblock == 65535)) {
        /* This is not the expected block. Log it and up the retry counter */
        infof(data, "Received ACK for block %d, expecting %d",
              rblock, state->block);
        state->retries++;
        /* Bail out if over the maximum */
        if(state->retries > state->retry_max) {
          failf(data, "tftp_tx: giving up waiting for block %d ack",
                state->block);
          result = CURLE_SEND_ERROR;
        }
        else {
          /* Re-send the data packet */
          sbytes = sendto(state->sockfd, (void *)state->spacket.data,
                          4 + (SEND_TYPE_ARG3)state->sbytes, SEND_4TH_ARG,
                          (struct sockaddr *)&state->remote_addr,
                          state->remote_addrlen);
          /* Check all sbytes were sent */
          if(sbytes < 0) {
            failf(data, "%s", Curl_strerror(SOCKERRNO,
                                            buffer, sizeof(buffer)));
            result = CURLE_SEND_ERROR;
          }
        }

        return result;
      }
      /* This is the expected packet. Reset the counters and send the next
         block */
      state->rx_time = time(NULL);
      state->block++;
    }
    else
      state->block = 1; /* first data block is 1 when using OACK */

    state->retries = 0;
    setpacketevent(&state->spacket, TFTP_EVENT_DATA);
    setpacketblock(&state->spacket, state->block);
    if(state->block > 1 && state->sbytes < state->blksize) {
      state->state = TFTP_STATE_FIN;
      return CURLE_OK;
    }

    /* TFTP considers data block size < 512 bytes as an end of session. So
     * in some cases we must wait for additional data to build full (512 bytes)
     * data block.
     * */
    state->sbytes = 0;
    bufptr = (char *)state->spacket.data + 4;
    do {
      result = Curl_client_read(data, bufptr, state->blksize - state->sbytes,
                                &cb, &eos);
      if(result)
        return result;
      state->sbytes += cb;
      bufptr += cb;
    } while(state->sbytes < state->blksize && cb);

    sbytes = sendto(state->sockfd, (void *) state->spacket.data,
                    4 + (SEND_TYPE_ARG3)state->sbytes, SEND_4TH_ARG,
                    (struct sockaddr *)&state->remote_addr,
                    state->remote_addrlen);
    /* Check all sbytes were sent */
    if(sbytes < 0) {
      failf(data, "%s", Curl_strerror(SOCKERRNO, buffer, sizeof(buffer)));
      return CURLE_SEND_ERROR;
    }
    /* Update the progress meter */
    k->writebytecount += state->sbytes;
    Curl_pgrsSetUploadCounter(data, k->writebytecount);
    break;

  case TFTP_EVENT_TIMEOUT:
    /* Increment the retry counter and log the timeout */
    state->retries++;
    infof(data, "Timeout waiting for block %d ACK. "
          " Retries = %d", NEXT_BLOCKNUM(state->block), state->retries);
    /* Decide if we have had enough */
    if(state->retries > state->retry_max) {
      state->error = TFTP_ERR_TIMEOUT;
      state->state = TFTP_STATE_FIN;
    }
    else {
      /* Re-send the data packet */
      sbytes = sendto(state->sockfd, (void *)state->spacket.data,
                      4 + (SEND_TYPE_ARG3)state->sbytes, SEND_4TH_ARG,
                      (struct sockaddr *)&state->remote_addr,
                      state->remote_addrlen);
      /* Check all sbytes were sent */
      if(sbytes < 0) {
        failf(data, "%s", Curl_strerror(SOCKERRNO, buffer, sizeof(buffer)));
        return CURLE_SEND_ERROR;
      }
      /* since this was a re-send, we remain at the still byte position */
      Curl_pgrsSetUploadCounter(data, k->writebytecount);
    }
    break;

  case TFTP_EVENT_ERROR:
    state->state = TFTP_STATE_FIN;
    setpacketevent(&state->spacket, TFTP_EVENT_ERROR);
    setpacketblock(&state->spacket, state->block);
    (void)sendto(state->sockfd, (void *)state->spacket.data, 4, SEND_4TH_ARG,
                 (struct sockaddr *)&state->remote_addr,
                 state->remote_addrlen);
    /* do not bother with the return code, but if the socket is still up we
     * should be a good TFTP client and let the server know we are done */
    state->state = TFTP_STATE_FIN;
    break;

  default:
    failf(data, "tftp_tx: internal error, event: %i", (int)(event));
    break;
  }

  return result;
}
static CURLcode tftp_receive_packet(struct Curl_easy *data,
                                    struct tftp_conn *state)
{
  curl_socklen_t        fromlen;
  CURLcode              result = CURLE_OK;

  /* Receive the packet */
  fromlen = sizeof(state->remote_addr);
  state->rbytes = (int)recvfrom(state->sockfd,
                                (void *)state->rpacket.data,
                                (RECV_TYPE_ARG3)state->blksize + 4,
                                0,
                                (struct sockaddr *)&state->remote_addr,
                                &fromlen);
  state->remote_addrlen = fromlen;

  /* Sanity check packet length */
  if(state->rbytes < 4) {
    failf(data, "Received too short packet");
    /* Not a timeout, but how best to handle it? */
    state->event = TFTP_EVENT_TIMEOUT;
  }
  else {
    /* The event is given by the TFTP packet time */
    unsigned short event = getrpacketevent(&state->rpacket);
    state->event = (tftp_event_t)event;

    switch(state->event) {
    case TFTP_EVENT_DATA:
      if(data->state.upload)
        return CURLE_TFTP_ILLEGAL;
      /* Do not pass to the client empty or retransmitted packets */
      if(state->rbytes > 4 &&
         (NEXT_BLOCKNUM(state->block) == getrpacketblock(&state->rpacket))) {
        result = Curl_client_write(data, CLIENTWRITE_BODY,
                                   (char *)state->rpacket.data + 4,
                                   state->rbytes-4);
        if(result) {
          tftp_state_machine(state, TFTP_EVENT_ERROR);
          return result;
        }
      }
      break;
    case TFTP_EVENT_ERROR:
    {
      unsigned short error = getrpacketblock(&state->rpacket);
      char *str = (char *)state->rpacket.data + 4;
      size_t strn = state->rbytes - 4;
      state->error = (tftp_error_t)error;
      if(tftp_strnlen(str, strn) < strn)
        infof(data, "TFTP error: %s", str);
      break;
    }
    case TFTP_EVENT_ACK:
      break;
    case TFTP_EVENT_OACK:
      result = tftp_parse_option_ack(state,
                                     (const char *)state->rpacket.data + 2,
                                     state->rbytes-2);
      if(result)
        return result;
      break;
    case TFTP_EVENT_RRQ:
    case TFTP_EVENT_WRQ:
    default:
      failf(data, "%s", "Internal error: Unexpected packet");
      break;
    }

    /* Update the progress meter */
    if(Curl_pgrsUpdate(data)) {
      tftp_state_machine(state, TFTP_EVENT_ERROR);
      return CURLE_ABORTED_BY_CALLBACK;
    }
  }
  return result;
}
#include "epilogue.h"
