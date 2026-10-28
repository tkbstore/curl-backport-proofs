/*
 * Case 3 のバックポート（research/backport-proof/PROTOCOL.md）の翻訳単位の前置き。
 * C1 の PROTOCOL §4 で許した「関数の外側の変更」だけを置く。方針は case3/prelude.h と同じ。
 *
 * 出典: curl tag curl-8_14_1。バックポート後は、その lib/tftp.c に 63dd390fab の差分を当てたもの（backport.diff）
 * - 構造体は、対象の3関数が触るフィールドだけに減らした（並びは curl の宣言順を保つ）
 *     struct tftp_packet         lib/tftp.c:120        data
 *     struct tftp_conn           lib/tftp.c:127        mode・local_addr を除いた全部（8.14.1 には remote_pinned が無い）
 *     struct Curl_sockaddr_storage lib/sockaddr.h:29   共用体のうち sa_stor（128 バイト、8 バイト境界）だけ
 *     struct Curl_sockaddr_ex    lib/cf-socket.h:45    addrlen と curl_sa_addr（マクロを展開した先）だけ
 *     struct connectdata         lib/urldata.h:731     remote_addr
 *     struct SingleRequest       lib/request.h:60      writebytecount
 *     struct urlpieces           lib/urldata.h:1104    path
 *     struct UrlState            lib/urldata.h:1120    infilesize, up, prefer_ascii, upload
 *     struct UserDefined         lib/urldata.h:1473    tftp_no_options
 *     struct Curl_easy           lib/urldata.h:1801    conn, req, set, state
 * - enum は tftp.c の定義をそのまま写した。CURLcode は使う値だけ（include/curl/curl.h と同じ値）
 * - マクロ
 *     infof・failf・msnprintf・free は 8.14.1 の lib/curl_trc.h・lib/curl_printf.h:56・lib/curl_memory.h:149 の形
 *     STRERROR_LEN は lib/strerror.h:29
 *     SOCKERRNO は errno（glibc の定義 `*__errno_location()`）
 *     SEND_4TH_ARG は Linux の MSG_NOSIGNAL（0x4000）
 *     CURL_SENDTO_ARG5 は tftp_send_first の本体の中で定義される（__AMIGA__ でないので `(x)`）
 * - tftp.c の static 関数で、対象の3関数から呼ばれるものは extern の宣言にした（仕様は Lean 側で定理の仮定として与える）
 */
typedef unsigned long size_t;
typedef long ssize_t;
typedef long time_t;
typedef long long curl_off_t;
typedef int curl_socket_t;
typedef unsigned int curl_socklen_t;
typedef _Bool bool;
#define TRUE 1
#define FALSE 0
#define NULL ((void *)0)

typedef unsigned int curl_bit;
#define BIT(x) curl_bit x:1

#define STRERROR_LEN 256
#define FIRSTSOCKET 0
#define REJECT_ZERO 4
#define FMT_OFF_T "lld"
#define SEND_TYPE_ARG3 size_t
#define RECV_TYPE_ARG3 size_t
#define SEND_4TH_ARG 0x4000
#define CLIENTWRITE_BODY (1 << 0)
#define TFTP_OPTION_BLKSIZE  "blksize"
#define TFTP_OPTION_TSIZE    "tsize"
#define TFTP_OPTION_INTERVAL "timeout"
#define NEXT_BLOCKNUM(x) (((x) + 1) & 0xffff)

extern int *__errno_location(void);
#define SOCKERRNO (*__errno_location())

typedef enum {
  CURLE_OK = 0,
  CURLE_FAILED_INIT = 2,
  CURLE_ABORTED_BY_CALLBACK = 42,
  CURLE_SEND_ERROR = 55,
  CURLE_RECV_ERROR = 56,
  CURLE_TFTP_ILLEGAL = 71
} CURLcode;

typedef enum {
  TFTP_STATE_START = 0,
  TFTP_STATE_RX,
  TFTP_STATE_TX,
  TFTP_STATE_FIN
} tftp_state_t;

typedef enum {
  TFTP_EVENT_NONE = -1,
  TFTP_EVENT_INIT = 0,
  TFTP_EVENT_RRQ = 1,
  TFTP_EVENT_WRQ = 2,
  TFTP_EVENT_DATA = 3,
  TFTP_EVENT_ACK = 4,
  TFTP_EVENT_ERROR = 5,
  TFTP_EVENT_OACK = 6,
  TFTP_EVENT_TIMEOUT
} tftp_event_t;

typedef enum {
  TFTP_ERR_UNDEF = 0,
  TFTP_ERR_NOTFOUND,
  TFTP_ERR_PERM,
  TFTP_ERR_DISKFULL,
  TFTP_ERR_ILLEGAL,
  TFTP_ERR_UNKNOWNID,
  TFTP_ERR_EXISTS,
  TFTP_ERR_NOSUCHUSER,
  TFTP_ERR_NONE = -100,
  TFTP_ERR_TIMEOUT,
  TFTP_ERR_NORESPONSE
} tftp_error_t;

struct sockaddr {
  unsigned short sa_family;
  char sa_data[14];
};

struct Curl_sockaddr_storage {
  union {
    long sa_stor[16];
  } buffer;
};

struct Curl_sockaddr_ex {
  unsigned int addrlen;
  struct sockaddr curl_sa_addr;
};

struct tftp_packet {
  unsigned char *data;
};

struct Curl_easy;

struct tftp_conn {
  tftp_state_t    state;
  tftp_error_t    error;
  tftp_event_t    event;
  struct Curl_easy *data;
  curl_socket_t   sockfd;
  int             retries;
  int             retry_time;
  int             retry_max;
  time_t          rx_time;
  struct Curl_sockaddr_storage remote_addr;
  curl_socklen_t  remote_addrlen;
  int             rbytes;
  size_t          sbytes;
  unsigned int    blksize;
  unsigned int    requested_blksize;
  unsigned short  block;
  struct tftp_packet rpacket;
  struct tftp_packet spacket;
};

struct connectdata {
  const struct Curl_sockaddr_ex *remote_addr;
};

struct SingleRequest {
  curl_off_t writebytecount;
};

struct urlpieces {
  char *path;
};

struct UrlState {
  curl_off_t infilesize;
  struct urlpieces up;
  BIT(prefer_ascii);
  BIT(upload);
};

struct UserDefined {
  BIT(tftp_no_options);
};

struct Curl_easy {
  struct connectdata *conn;
  struct SingleRequest req;
  struct UserDefined set;
  struct UrlState state;
};

/* libc */
extern ssize_t sendto(int, const void *, size_t, int, const struct sockaddr *,
                      curl_socklen_t);
extern ssize_t recvfrom(int, void *, size_t, int, struct sockaddr *,
                        curl_socklen_t *);
extern size_t strlen(const char *);
extern time_t time(time_t *);

/* curl の他のファイル */
extern void Curl_failf(struct Curl_easy *data, const char *fmt, ...);
#define failf Curl_failf
extern void Curl_infof(struct Curl_easy *data, const char *fmt, ...);
#define infof Curl_infof
extern int curl_msnprintf(char *buffer, size_t maxlength, const char *format,
                          ...);
#define msnprintf curl_msnprintf
extern const char *Curl_strerror(int err, char *buf, size_t buflen);
extern void Curl_cfree(void *ptr);
#define free(ptr) Curl_cfree(ptr)
extern CURLcode Curl_client_write(struct Curl_easy *data, int type,
                                  const char *buf, size_t len);
extern CURLcode Curl_client_read(struct Curl_easy *data, char *buf,
                                 size_t blen, size_t *nread, bool *eos);
extern int Curl_pgrsUpdate(struct Curl_easy *data);
extern void Curl_pgrsSetUploadCounter(struct Curl_easy *data, curl_off_t size);
extern void Curl_pgrsSetUploadSize(struct Curl_easy *data, curl_off_t size);
extern CURLcode Curl_urldecode(const char *string, size_t length,
                               char **ostring, size_t *olen, int ctrl);

/* tftp.c の static 関数（対象の3関数以外） */
extern void setpacketevent(struct tftp_packet *packet, unsigned short num);
extern void setpacketblock(struct tftp_packet *packet, unsigned short num);
extern unsigned short getrpacketevent(const struct tftp_packet *packet);
extern unsigned short getrpacketblock(const struct tftp_packet *packet);
extern size_t tftp_strnlen(const char *string, size_t maxlen);
extern CURLcode tftp_parse_option_ack(struct tftp_conn *state,
                                      const char *ptr, int len);
extern CURLcode tftp_option_add(struct tftp_conn *state, size_t *csize,
                                char *buf, const char *option);
extern CURLcode tftp_connect_for_tx(struct tftp_conn *state,
                                    tftp_event_t event);
extern CURLcode tftp_connect_for_rx(struct tftp_conn *state,
                                    tftp_event_t event);
extern CURLcode tftp_state_machine(struct tftp_conn *state,
                                   tftp_event_t event);
