import Clightdefs
open CC

namespace Case3bp_after

namespace Info
  def version : String := "3.17"
  def build_number : String := ""
  def build_tag : String := ""
  def build_branch : String := ""
  def arch : String := "aarch64"
  def model : String := "default"
  def abi : String := "apple"
  def bitsize : Nat := 64
  def big_endian : Bool := false
  def source_file : String := "case3bp/case3bp_after.c"
  def normalized : Bool := true
end Info

def _Curl_cfree : Ident := identOfString "Curl_cfree"
def _Curl_client_read : Ident := identOfString "Curl_client_read"
def _Curl_client_write : Ident := identOfString "Curl_client_write"
def _Curl_easy : Ident := identOfString "Curl_easy"
def _Curl_failf : Ident := identOfString "Curl_failf"
def _Curl_infof : Ident := identOfString "Curl_infof"
def _Curl_pgrsSetUploadCounter : Ident := identOfString "Curl_pgrsSetUploadCounter"
def _Curl_pgrsSetUploadSize : Ident := identOfString "Curl_pgrsSetUploadSize"
def _Curl_pgrsUpdate : Ident := identOfString "Curl_pgrsUpdate"
def _Curl_sockaddr_ex : Ident := identOfString "Curl_sockaddr_ex"
def _Curl_sockaddr_storage : Ident := identOfString "Curl_sockaddr_storage"
def _Curl_strerror : Ident := identOfString "Curl_strerror"
def _Curl_urldecode : Ident := identOfString "Curl_urldecode"
def _SingleRequest : Ident := identOfString "SingleRequest"
def _UrlState : Ident := identOfString "UrlState"
def _UserDefined : Ident := identOfString "UserDefined"
def __139 : Ident := identOfString "_139"
def ___builtin_annot : Ident := identOfString "__builtin_annot"
def ___builtin_annot_intval : Ident := identOfString "__builtin_annot_intval"
def ___builtin_bswap : Ident := identOfString "__builtin_bswap"
def ___builtin_bswap16 : Ident := identOfString "__builtin_bswap16"
def ___builtin_bswap32 : Ident := identOfString "__builtin_bswap32"
def ___builtin_bswap64 : Ident := identOfString "__builtin_bswap64"
def ___builtin_cls : Ident := identOfString "__builtin_cls"
def ___builtin_clsl : Ident := identOfString "__builtin_clsl"
def ___builtin_clsll : Ident := identOfString "__builtin_clsll"
def ___builtin_clz : Ident := identOfString "__builtin_clz"
def ___builtin_clzl : Ident := identOfString "__builtin_clzl"
def ___builtin_clzll : Ident := identOfString "__builtin_clzll"
def ___builtin_ctz : Ident := identOfString "__builtin_ctz"
def ___builtin_ctzl : Ident := identOfString "__builtin_ctzl"
def ___builtin_ctzll : Ident := identOfString "__builtin_ctzll"
def ___builtin_debug : Ident := identOfString "__builtin_debug"
def ___builtin_expect : Ident := identOfString "__builtin_expect"
def ___builtin_fabs : Ident := identOfString "__builtin_fabs"
def ___builtin_fabsf : Ident := identOfString "__builtin_fabsf"
def ___builtin_fmadd : Ident := identOfString "__builtin_fmadd"
def ___builtin_fmax : Ident := identOfString "__builtin_fmax"
def ___builtin_fmin : Ident := identOfString "__builtin_fmin"
def ___builtin_fmsub : Ident := identOfString "__builtin_fmsub"
def ___builtin_fnmadd : Ident := identOfString "__builtin_fnmadd"
def ___builtin_fnmsub : Ident := identOfString "__builtin_fnmsub"
def ___builtin_fsqrt : Ident := identOfString "__builtin_fsqrt"
def ___builtin_membar : Ident := identOfString "__builtin_membar"
def ___builtin_memcpy_aligned : Ident := identOfString "__builtin_memcpy_aligned"
def ___builtin_sel : Ident := identOfString "__builtin_sel"
def ___builtin_sqrt : Ident := identOfString "__builtin_sqrt"
def ___builtin_unreachable : Ident := identOfString "__builtin_unreachable"
def ___builtin_va_arg : Ident := identOfString "__builtin_va_arg"
def ___builtin_va_copy : Ident := identOfString "__builtin_va_copy"
def ___builtin_va_end : Ident := identOfString "__builtin_va_end"
def ___builtin_va_start : Ident := identOfString "__builtin_va_start"
def ___compcert_i64_dtos : Ident := identOfString "__compcert_i64_dtos"
def ___compcert_i64_dtou : Ident := identOfString "__compcert_i64_dtou"
def ___compcert_i64_sar : Ident := identOfString "__compcert_i64_sar"
def ___compcert_i64_sdiv : Ident := identOfString "__compcert_i64_sdiv"
def ___compcert_i64_shl : Ident := identOfString "__compcert_i64_shl"
def ___compcert_i64_shr : Ident := identOfString "__compcert_i64_shr"
def ___compcert_i64_smod : Ident := identOfString "__compcert_i64_smod"
def ___compcert_i64_smulh : Ident := identOfString "__compcert_i64_smulh"
def ___compcert_i64_stod : Ident := identOfString "__compcert_i64_stod"
def ___compcert_i64_stof : Ident := identOfString "__compcert_i64_stof"
def ___compcert_i64_udiv : Ident := identOfString "__compcert_i64_udiv"
def ___compcert_i64_umod : Ident := identOfString "__compcert_i64_umod"
def ___compcert_i64_umulh : Ident := identOfString "__compcert_i64_umulh"
def ___compcert_i64_utod : Ident := identOfString "__compcert_i64_utod"
def ___compcert_i64_utof : Ident := identOfString "__compcert_i64_utof"
def ___compcert_va_composite : Ident := identOfString "__compcert_va_composite"
def ___compcert_va_float64 : Ident := identOfString "__compcert_va_float64"
def ___compcert_va_int32 : Ident := identOfString "__compcert_va_int32"
def ___compcert_va_int64 : Ident := identOfString "__compcert_va_int64"
def ___errno_location : Ident := identOfString "__errno_location"
def ___stringlit_1 : Ident := identOfString "__stringlit_1"
def ___stringlit_10 : Ident := identOfString "__stringlit_10"
def ___stringlit_11 : Ident := identOfString "__stringlit_11"
def ___stringlit_12 : Ident := identOfString "__stringlit_12"
def ___stringlit_13 : Ident := identOfString "__stringlit_13"
def ___stringlit_14 : Ident := identOfString "__stringlit_14"
def ___stringlit_15 : Ident := identOfString "__stringlit_15"
def ___stringlit_16 : Ident := identOfString "__stringlit_16"
def ___stringlit_17 : Ident := identOfString "__stringlit_17"
def ___stringlit_18 : Ident := identOfString "__stringlit_18"
def ___stringlit_19 : Ident := identOfString "__stringlit_19"
def ___stringlit_2 : Ident := identOfString "__stringlit_2"
def ___stringlit_3 : Ident := identOfString "__stringlit_3"
def ___stringlit_4 : Ident := identOfString "__stringlit_4"
def ___stringlit_5 : Ident := identOfString "__stringlit_5"
def ___stringlit_6 : Ident := identOfString "__stringlit_6"
def ___stringlit_7 : Ident := identOfString "__stringlit_7"
def ___stringlit_8 : Ident := identOfString "__stringlit_8"
def ___stringlit_9 : Ident := identOfString "__stringlit_9"
def _addrlen : Ident := identOfString "addrlen"
def _blksize : Ident := identOfString "blksize"
def _block : Ident := identOfString "block"
def _buf : Ident := identOfString "buf"
def _buffer : Ident := identOfString "buffer"
def _bufptr : Ident := identOfString "bufptr"
def _case3bp_keep_ev : Ident := identOfString "case3bp_keep_ev"
def _case3bp_keep_rp : Ident := identOfString "case3bp_keep_rp"
def _cb : Ident := identOfString "cb"
def _conn : Ident := identOfString "conn"
def _connectdata : Ident := identOfString "connectdata"
def _curl_msnprintf : Ident := identOfString "curl_msnprintf"
def _curl_sa_addr : Ident := identOfString "curl_sa_addr"
def _data : Ident := identOfString "data"
def _eos : Ident := identOfString "eos"
def _error : Ident := identOfString "error"
def _event : Ident := identOfString "event"
def _filename : Ident := identOfString "filename"
def _fromlen : Ident := identOfString "fromlen"
def _getrpacketblock : Ident := identOfString "getrpacketblock"
def _getrpacketevent : Ident := identOfString "getrpacketevent"
def _infilesize : Ident := identOfString "infilesize"
def _k : Ident := identOfString "k"
def _main : Ident := identOfString "main"
def _mode : Ident := identOfString "mode"
def _path : Ident := identOfString "path"
def _prefer_ascii : Ident := identOfString "prefer_ascii"
def _rblock : Ident := identOfString "rblock"
def _rbytes : Ident := identOfString "rbytes"
def _recvfrom : Ident := identOfString "recvfrom"
def _remote_addr : Ident := identOfString "remote_addr"
def _remote_addrlen : Ident := identOfString "remote_addrlen"
def _req : Ident := identOfString "req"
def _requested_blksize : Ident := identOfString "requested_blksize"
def _result : Ident := identOfString "result"
def _retries : Ident := identOfString "retries"
def _retry_max : Ident := identOfString "retry_max"
def _retry_time : Ident := identOfString "retry_time"
def _rpacket : Ident := identOfString "rpacket"
def _rx_time : Ident := identOfString "rx_time"
def _sa_data : Ident := identOfString "sa_data"
def _sa_family : Ident := identOfString "sa_family"
def _sa_stor : Ident := identOfString "sa_stor"
def _sbytes : Ident := identOfString "sbytes"
def _senddata : Ident := identOfString "senddata"
def _sendto : Ident := identOfString "sendto"
def _set : Ident := identOfString "set"
def _setpacketblock : Ident := identOfString "setpacketblock"
def _setpacketevent : Ident := identOfString "setpacketevent"
def _sockaddr : Ident := identOfString "sockaddr"
def _sockfd : Ident := identOfString "sockfd"
def _spacket : Ident := identOfString "spacket"
def _state : Ident := identOfString "state"
def _str : Ident := identOfString "str"
def _strlen : Ident := identOfString "strlen"
def _strn : Ident := identOfString "strn"
def _tftp_conn : Ident := identOfString "tftp_conn"
def _tftp_connect_for_rx : Ident := identOfString "tftp_connect_for_rx"
def _tftp_connect_for_tx : Ident := identOfString "tftp_connect_for_tx"
def _tftp_no_options : Ident := identOfString "tftp_no_options"
def _tftp_option_add : Ident := identOfString "tftp_option_add"
def _tftp_packet : Ident := identOfString "tftp_packet"
def _tftp_parse_option_ack : Ident := identOfString "tftp_parse_option_ack"
def _tftp_receive_packet : Ident := identOfString "tftp_receive_packet"
def _tftp_send_first : Ident := identOfString "tftp_send_first"
def _tftp_state_machine : Ident := identOfString "tftp_state_machine"
def _tftp_strnlen : Ident := identOfString "tftp_strnlen"
def _tftp_tx : Ident := identOfString "tftp_tx"
def _time : Ident := identOfString "time"
def _up : Ident := identOfString "up"
def _upload : Ident := identOfString "upload"
def _urlpieces : Ident := identOfString "urlpieces"
def _writebytecount : Ident := identOfString "writebytecount"
def _t'1 : Ident := (Positive.ofNat 128)
def _t'10 : Ident := (Positive.ofNat 137)
def _t'11 : Ident := (Positive.ofNat 138)
def _t'12 : Ident := (Positive.ofNat 139)
def _t'13 : Ident := (Positive.ofNat 140)
def _t'14 : Ident := (Positive.ofNat 141)
def _t'15 : Ident := (Positive.ofNat 142)
def _t'16 : Ident := (Positive.ofNat 143)
def _t'17 : Ident := (Positive.ofNat 144)
def _t'18 : Ident := (Positive.ofNat 145)
def _t'19 : Ident := (Positive.ofNat 146)
def _t'2 : Ident := (Positive.ofNat 129)
def _t'20 : Ident := (Positive.ofNat 147)
def _t'21 : Ident := (Positive.ofNat 148)
def _t'22 : Ident := (Positive.ofNat 149)
def _t'23 : Ident := (Positive.ofNat 150)
def _t'24 : Ident := (Positive.ofNat 151)
def _t'25 : Ident := (Positive.ofNat 152)
def _t'26 : Ident := (Positive.ofNat 153)
def _t'27 : Ident := (Positive.ofNat 154)
def _t'28 : Ident := (Positive.ofNat 155)
def _t'29 : Ident := (Positive.ofNat 156)
def _t'3 : Ident := (Positive.ofNat 130)
def _t'30 : Ident := (Positive.ofNat 157)
def _t'31 : Ident := (Positive.ofNat 158)
def _t'32 : Ident := (Positive.ofNat 159)
def _t'33 : Ident := (Positive.ofNat 160)
def _t'34 : Ident := (Positive.ofNat 161)
def _t'35 : Ident := (Positive.ofNat 162)
def _t'36 : Ident := (Positive.ofNat 163)
def _t'37 : Ident := (Positive.ofNat 164)
def _t'38 : Ident := (Positive.ofNat 165)
def _t'39 : Ident := (Positive.ofNat 166)
def _t'4 : Ident := (Positive.ofNat 131)
def _t'40 : Ident := (Positive.ofNat 167)
def _t'41 : Ident := (Positive.ofNat 168)
def _t'42 : Ident := (Positive.ofNat 169)
def _t'43 : Ident := (Positive.ofNat 170)
def _t'44 : Ident := (Positive.ofNat 171)
def _t'45 : Ident := (Positive.ofNat 172)
def _t'46 : Ident := (Positive.ofNat 173)
def _t'47 : Ident := (Positive.ofNat 174)
def _t'48 : Ident := (Positive.ofNat 175)
def _t'49 : Ident := (Positive.ofNat 176)
def _t'5 : Ident := (Positive.ofNat 132)
def _t'50 : Ident := (Positive.ofNat 177)
def _t'51 : Ident := (Positive.ofNat 178)
def _t'52 : Ident := (Positive.ofNat 179)
def _t'53 : Ident := (Positive.ofNat 180)
def _t'54 : Ident := (Positive.ofNat 181)
def _t'55 : Ident := (Positive.ofNat 182)
def _t'56 : Ident := (Positive.ofNat 183)
def _t'57 : Ident := (Positive.ofNat 184)
def _t'58 : Ident := (Positive.ofNat 185)
def _t'59 : Ident := (Positive.ofNat 186)
def _t'6 : Ident := (Positive.ofNat 133)
def _t'60 : Ident := (Positive.ofNat 187)
def _t'61 : Ident := (Positive.ofNat 188)
def _t'62 : Ident := (Positive.ofNat 189)
def _t'63 : Ident := (Positive.ofNat 190)
def _t'64 : Ident := (Positive.ofNat 191)
def _t'65 : Ident := (Positive.ofNat 192)
def _t'66 : Ident := (Positive.ofNat 193)
def _t'67 : Ident := (Positive.ofNat 194)
def _t'68 : Ident := (Positive.ofNat 195)
def _t'69 : Ident := (Positive.ofNat 196)
def _t'7 : Ident := (Positive.ofNat 134)
def _t'70 : Ident := (Positive.ofNat 197)
def _t'8 : Ident := (Positive.ofNat 135)
def _t'9 : Ident := (Positive.ofNat 136)

def v___stringlit_12 : GlobVar Ty := {
  gvar_info := (tarray tschar 3),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_9 : GlobVar Ty := {
  gvar_info := (tarray tschar 8),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 98)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 107)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 122)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_14 : GlobVar Ty := {
  gvar_info := (tarray tschar 48),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 84)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 109)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 117)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 119)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 103)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 102)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 98)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 107)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 65)),
                (InitData.Init_int8 (Integers.Int.repr 67)),
                (InitData.Init_int8 (Integers.Int.repr 75)),
                (InitData.Init_int8 (Integers.Int.repr 46)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 82)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 61)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_15 : GlobVar Ty := {
  gvar_info := (tarray tschar 40),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 82)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 118)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 65)),
                (InitData.Init_int8 (Integers.Int.repr 67)),
                (InitData.Init_int8 (Integers.Int.repr 75)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 102)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 98)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 107)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 44)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 120)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 103)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_19 : GlobVar Ty := {
  gvar_info := (tarray tschar 26),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 82)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 118)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 104)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 107)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_10 : GlobVar Ty := {
  gvar_info := (tarray tschar 8),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 109)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 117)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_5 : GlobVar Ty := {
  gvar_info := (tarray tschar 9),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_8 : GlobVar Ty := {
  gvar_info := (tarray tschar 3),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_18 : GlobVar Ty := {
  gvar_info := (tarray tschar 15),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 84)),
                (InitData.Init_int8 (Integers.Int.repr 70)),
                (InitData.Init_int8 (Integers.Int.repr 84)),
                (InitData.Init_int8 (Integers.Int.repr 80)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 58)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_13 : GlobVar Ty := {
  gvar_info := (tarray tschar 35),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 102)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 95)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 120)),
                (InitData.Init_int8 (Integers.Int.repr 58)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 44)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 118)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 58)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_6 : GlobVar Ty := {
  gvar_info := (tarray tschar 5),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_7 : GlobVar Ty := {
  gvar_info := (tarray tschar 6),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 122)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_3 : GlobVar Ty := {
  gvar_info := (tarray tschar 32),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 102)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 95)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 95)),
                (InitData.Init_int8 (Integers.Int.repr 102)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 58)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_4 : GlobVar Ty := {
  gvar_info := (tarray tschar 23),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 84)),
                (InitData.Init_int8 (Integers.Int.repr 70)),
                (InitData.Init_int8 (Integers.Int.repr 84)),
                (InitData.Init_int8 (Integers.Int.repr 80)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 102)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 109)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 103)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_11 : GlobVar Ty := {
  gvar_info := (tarray tschar 34),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 84)),
                (InitData.Init_int8 (Integers.Int.repr 70)),
                (InitData.Init_int8 (Integers.Int.repr 84)),
                (InitData.Init_int8 (Integers.Int.repr 80)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 98)),
                (InitData.Init_int8 (Integers.Int.repr 117)),
                (InitData.Init_int8 (Integers.Int.repr 102)),
                (InitData.Init_int8 (Integers.Int.repr 102)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 109)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 102)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_1 : GlobVar Ty := {
  gvar_info := (tarray tschar 6),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_17 : GlobVar Ty := {
  gvar_info := (tarray tschar 34),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 73)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 58)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 85)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 120)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 107)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_2 : GlobVar Ty := {
  gvar_info := (tarray tschar 9),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_16 : GlobVar Ty := {
  gvar_info := (tarray tschar 44),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 102)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 95)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 120)),
                (InitData.Init_int8 (Integers.Int.repr 58)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 103)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 118)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 103)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 117)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 119)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 103)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 102)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 98)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 107)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 107)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def f_tftp_send_first : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_state, (tptr (Ty.Tstruct _tftp_conn noattr))),
                (_event, tint)],
  fn_vars := [(_sbytes, tulong), (_filename, (tptr tschar)),
              (_buf, (tarray tschar 64)), (_buffer, (tarray tschar 256))],
  fn_temps := [(_senddata, tlong), (_mode, (tptr tschar)),
               (_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
               (_result, tint), (_t'20, tint), (_t'19, tint), (_t'18, tint),
               (_t'17, tint), (_t'16, (tptr tschar)), (_t'15, (tptr tint)),
               (_t'14, tlong), (_t'13, tint), (_t'12, tint), (_t'11, tint),
               (_t'10, tint), (_t'9, tint), (_t'8, tint), (_t'7, tlong),
               (_t'6, tint), (_t'5, tulong), (_t'4, tulong), (_t'3, tulong),
               (_t'2, tulong), (_t'1, tint), (_t'70, tint), (_t'69, tint),
               (_t'68, tint), (_t'67, tint), (_t'66, tlong), (_t'65, tlong),
               (_t'64, tint), (_t'63, (tptr tschar)),
               (_t'62, (tptr (Ty.Tstruct _Curl_easy noattr))),
               (_t'61, (tptr tschar)), (_t'60, (tptr tschar)),
               (_t'59, tuint), (_t'58, (tptr tschar)), (_t'57, tuint),
               (_t'56, (tptr tuchar)), (_t'55, (tptr tschar)),
               (_t'54, tlong), (_t'53, tint), (_t'52, tlong),
               (_t'51, tulong), (_t'50, (tptr tuchar)), (_t'49, tulong),
               (_t'48, (tptr tuchar)), (_t'47, tuint), (_t'46, tulong),
               (_t'45, (tptr tuchar)), (_t'44, tulong),
               (_t'43, (tptr tuchar)), (_t'42, tint), (_t'41, tulong),
               (_t'40, (tptr tuchar)), (_t'39, tulong),
               (_t'38, (tptr tuchar)), (_t'37, (tptr tschar)), (_t'36, tint),
               (_t'35, tuint),
               (_t'34, (tptr (Ty.Tstruct _Curl_sockaddr_ex noattr))),
               (_t'33, (tptr (Ty.Tstruct _connectdata noattr))),
               (_t'32, (tptr (Ty.Tstruct _Curl_sockaddr_ex noattr))),
               (_t'31, (tptr (Ty.Tstruct _connectdata noattr))),
               (_t'30, tulong), (_t'29, (tptr tuchar)), (_t'28, tint),
               (_t'27, tint), (_t'26, tulong), (_t'25, (tptr tschar)),
               (_t'24, tint), (_t'23, tint), (_t'22, tint),
               (_t'21, (tptr (Ty.Tstruct _Curl_easy noattr)))],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Sset _mode (Expr.Evar ___stringlit_1 (tarray tschar 6)))
  (Stmt.Ssequence
    (Stmt.Sset _data
      (Expr.Efield
        (Expr.Ederef
          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
          (Ty.Tstruct _tftp_conn noattr)) _data
        (tptr (Ty.Tstruct _Curl_easy noattr))))
    (Stmt.Ssequence
      (Stmt.Sset _result (Expr.Econst_int (Integers.Int.repr 0) tint))
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Sset _t'70
            (Expr.Efield
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                  (Ty.Tstruct _Curl_easy noattr)) _state
                (Ty.Tstruct _UrlState noattr)) _prefer_ascii tint))
          (Stmt.Sifthenelse (Expr.Etempvar _t'70 tint)
            (Stmt.Sset _mode (Expr.Evar ___stringlit_2 (tarray tschar 9)))
            Stmt.Sskip))
        (Stmt.Ssequence
          (Stmt.Sswitch (Expr.Etempvar _event tint)
            (LStmts.LScons (some 0)
              Stmt.Sskip
              (LStmts.LScons (some 7)
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Sset _t'69
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                          (Ty.Tstruct _tftp_conn noattr)) _retries tint))
                    (Stmt.Sassign
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                          (Ty.Tstruct _tftp_conn noattr)) _retries tint)
                      (Expr.Ebinop Binop.Oadd (Expr.Etempvar _t'69 tint)
                        (Expr.Econst_int (Integers.Int.repr 1) tint) tint)))
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sset _t'67
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                            (Ty.Tstruct _tftp_conn noattr)) _retries tint))
                      (Stmt.Ssequence
                        (Stmt.Sset _t'68
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                              (Ty.Tstruct _tftp_conn noattr)) _retry_max
                            tint))
                        (Stmt.Sifthenelse (Expr.Ebinop Binop.Ogt
                                            (Expr.Etempvar _t'67 tint)
                                            (Expr.Etempvar _t'68 tint) tint)
                          (Stmt.Ssequence
                            (Stmt.Sassign
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                  (Ty.Tstruct _tftp_conn noattr)) _error
                                tint)
                              (Expr.Econst_int (Integers.Int.repr (-98)) tint))
                            (Stmt.Ssequence
                              (Stmt.Sassign
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                    (Ty.Tstruct _tftp_conn noattr)) _state
                                  tint)
                                (Expr.Econst_int (Integers.Int.repr 3) tint))
                              (Stmt.Sreturn (some (Expr.Etempvar _result tint)))))
                          Stmt.Sskip)))
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Sset _t'64
                          (Expr.Efield
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                (Ty.Tstruct _Curl_easy noattr)) _state
                              (Ty.Tstruct _UrlState noattr)) _upload tint))
                        (Stmt.Sifthenelse (Expr.Etempvar _t'64 tint)
                          (Stmt.Ssequence
                            (Stmt.Scall none
                              (Expr.Evar _setpacketevent (Ty.Tfunction
                                                           [(tptr (Ty.Tstruct _tftp_packet noattr)),
                                                            tushort] tvoid
                                                           cc_default))
                              [(Expr.Eaddrof
                                 (Expr.Efield
                                   (Expr.Ederef
                                     (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                     (Ty.Tstruct _tftp_conn noattr)) _spacket
                                   (Ty.Tstruct _tftp_packet noattr))
                                 (tptr (Ty.Tstruct _tftp_packet noattr))),
                               (Expr.Econst_int (Integers.Int.repr 2) tint)])
                            (Stmt.Ssequence
                              (Stmt.Sset _t'65
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                      (Ty.Tstruct _Curl_easy noattr)) _state
                                    (Ty.Tstruct _UrlState noattr))
                                  _infilesize tlong))
                              (Stmt.Sifthenelse (Expr.Ebinop Binop.One
                                                  (Expr.Etempvar _t'65 tlong)
                                                  (Expr.Eunop Unop.Oneg
                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                    tint) tint)
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'66
                                    (Expr.Efield
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                          (Ty.Tstruct _Curl_easy noattr))
                                        _state (Ty.Tstruct _UrlState noattr))
                                      _infilesize tlong))
                                  (Stmt.Scall none
                                    (Expr.Evar _Curl_pgrsSetUploadSize 
                                    (Ty.Tfunction
                                      [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                       tlong] tvoid cc_default))
                                    [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                     (Expr.Etempvar _t'66 tlong)]))
                                Stmt.Sskip)))
                          (Stmt.Scall none
                            (Expr.Evar _setpacketevent (Ty.Tfunction
                                                         [(tptr (Ty.Tstruct _tftp_packet noattr)),
                                                          tushort] tvoid
                                                         cc_default))
                            [(Expr.Eaddrof
                               (Expr.Efield
                                 (Expr.Ederef
                                   (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                   (Ty.Tstruct _tftp_conn noattr)) _spacket
                                 (Ty.Tstruct _tftp_packet noattr))
                               (tptr (Ty.Tstruct _tftp_packet noattr))),
                             (Expr.Econst_int (Integers.Int.repr 1) tint)])))
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'62
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                  (Ty.Tstruct _tftp_conn noattr)) _data
                                (tptr (Ty.Tstruct _Curl_easy noattr))))
                            (Stmt.Ssequence
                              (Stmt.Sset _t'63
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _t'62 (tptr (Ty.Tstruct _Curl_easy noattr)))
                                        (Ty.Tstruct _Curl_easy noattr))
                                      _state (Ty.Tstruct _UrlState noattr))
                                    _up (Ty.Tstruct _urlpieces noattr)) _path
                                  (tptr tschar)))
                              (Stmt.Scall (some _t'1)
                                (Expr.Evar _Curl_urldecode (Ty.Tfunction
                                                             [(tptr tschar),
                                                              tulong,
                                                              (tptr (tptr tschar)),
                                                              (tptr tulong),
                                                              tint] tint
                                                             cc_default))
                                [(Expr.Ebinop Binop.Oadd
                                   (Expr.Etempvar _t'63 (tptr tschar))
                                   (Expr.Econst_int (Integers.Int.repr 1) tint)
                                   (tptr tschar)),
                                 (Expr.Econst_int (Integers.Int.repr 0) tint),
                                 (Expr.Eaddrof
                                   (Expr.Evar _filename (tptr tschar))
                                   (tptr (tptr tschar))),
                                 (Expr.Ecast
                                   (Expr.Econst_int (Integers.Int.repr 0) tint)
                                   (tptr tvoid)),
                                 (Expr.Econst_int (Integers.Int.repr 4) tint)])))
                          (Stmt.Sset _result (Expr.Etempvar _t'1 tint)))
                        (Stmt.Ssequence
                          (Stmt.Sifthenelse (Expr.Etempvar _result tint)
                            (Stmt.Sreturn (some (Expr.Etempvar _result tint)))
                            Stmt.Sskip)
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'61
                                    (Expr.Evar _filename (tptr tschar)))
                                  (Stmt.Scall (some _t'2)
                                    (Expr.Evar _strlen (Ty.Tfunction
                                                         [(tptr tschar)]
                                                         tulong cc_default))
                                    [(Expr.Etempvar _t'61 (tptr tschar))]))
                                (Stmt.Scall (some _t'3)
                                  (Expr.Evar _strlen (Ty.Tfunction
                                                       [(tptr tschar)] tulong
                                                       cc_default))
                                  [(Expr.Etempvar _mode (tptr tschar))]))
                              (Stmt.Ssequence
                                (Stmt.Sset _t'59
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                      (Ty.Tstruct _tftp_conn noattr))
                                    _blksize tuint))
                                (Stmt.Sifthenelse (Expr.Ebinop Binop.Ogt
                                                    (Expr.Etempvar _t'2 tulong)
                                                    (Expr.Ebinop Binop.Osub
                                                      (Expr.Ebinop Binop.Osub
                                                        (Expr.Etempvar _t'59 tuint)
                                                        (Expr.Etempvar _t'3 tulong)
                                                        tulong)
                                                      (Expr.Econst_int (Integers.Int.repr 4) tint)
                                                      tulong) tint)
                                  (Stmt.Ssequence
                                    (Stmt.Scall none
                                      (Expr.Evar _Curl_failf (Ty.Tfunction
                                                               [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                (tptr tschar)]
                                                               tvoid
                                                               { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                      [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                       (Expr.Evar ___stringlit_4 (tarray tschar 23))])
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'60
                                          (Expr.Evar _filename (tptr tschar)))
                                        (Stmt.Scall none
                                          (Expr.Evar _Curl_cfree (Ty.Tfunction
                                                                   [(tptr tvoid)]
                                                                   tvoid
                                                                   cc_default))
                                          [(Expr.Etempvar _t'60 (tptr tschar))]))
                                      (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 71) tint)))))
                                  Stmt.Sskip)))
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Sset _t'56
                                  (Expr.Efield
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                        (Ty.Tstruct _tftp_conn noattr))
                                      _spacket
                                      (Ty.Tstruct _tftp_packet noattr)) _data
                                    (tptr tuchar)))
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'57
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                        (Ty.Tstruct _tftp_conn noattr))
                                      _blksize tuint))
                                  (Stmt.Ssequence
                                    (Stmt.Sset _t'58
                                      (Expr.Evar _filename (tptr tschar)))
                                    (Stmt.Scall none
                                      (Expr.Evar _curl_msnprintf (Ty.Tfunction
                                                                   [(tptr tschar),
                                                                    tulong,
                                                                    (tptr tschar)]
                                                                   tint
                                                                   { cc_vararg := (some 3), cc_unproto := false, cc_structret := false }))
                                      [(Expr.Ebinop Binop.Oadd
                                         (Expr.Ecast
                                           (Expr.Etempvar _t'56 (tptr tuchar))
                                           (tptr tschar))
                                         (Expr.Econst_int (Integers.Int.repr 2) tint)
                                         (tptr tschar)),
                                       (Expr.Etempvar _t'57 tuint),
                                       (Expr.Evar ___stringlit_5 (tarray tschar 9)),
                                       (Expr.Etempvar _t'58 (tptr tschar)),
                                       (Expr.Econst_int (Integers.Int.repr 0) tint),
                                       (Expr.Etempvar _mode (tptr tschar)),
                                       (Expr.Econst_int (Integers.Int.repr 0) tint)]))))
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Sset _t'55
                                        (Expr.Evar _filename (tptr tschar)))
                                      (Stmt.Scall (some _t'4)
                                        (Expr.Evar _strlen (Ty.Tfunction
                                                             [(tptr tschar)]
                                                             tulong
                                                             cc_default))
                                        [(Expr.Etempvar _t'55 (tptr tschar))]))
                                    (Stmt.Scall (some _t'5)
                                      (Expr.Evar _strlen (Ty.Tfunction
                                                           [(tptr tschar)]
                                                           tulong cc_default))
                                      [(Expr.Etempvar _mode (tptr tschar))]))
                                  (Stmt.Sassign (Expr.Evar _sbytes tulong)
                                    (Expr.Ebinop Binop.Oadd
                                      (Expr.Ebinop Binop.Oadd
                                        (Expr.Econst_int (Integers.Int.repr 4) tint)
                                        (Expr.Etempvar _t'4 tulong) tulong)
                                      (Expr.Etempvar _t'5 tulong) tulong)))
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Sset _t'36
                                      (Expr.Efield
                                        (Expr.Efield
                                          (Expr.Ederef
                                            (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                            (Ty.Tstruct _Curl_easy noattr))
                                          _set
                                          (Ty.Tstruct _UserDefined noattr))
                                        _tftp_no_options tint))
                                    (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                                        (Expr.Etempvar _t'36 tint)
                                                        tint)
                                      (Stmt.Ssequence
                                        (Stmt.Ssequence
                                          (Stmt.Ssequence
                                            (Stmt.Ssequence
                                              (Stmt.Sset _t'53
                                                (Expr.Efield
                                                  (Expr.Efield
                                                    (Expr.Ederef
                                                      (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                      (Ty.Tstruct _Curl_easy noattr))
                                                    _state
                                                    (Ty.Tstruct _UrlState noattr))
                                                  _upload tint))
                                              (Stmt.Sifthenelse (Expr.Etempvar _t'53 tint)
                                                (Stmt.Ssequence
                                                  (Stmt.Sset _t'54
                                                    (Expr.Efield
                                                      (Expr.Efield
                                                        (Expr.Ederef
                                                          (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                          (Ty.Tstruct _Curl_easy noattr))
                                                        _state
                                                        (Ty.Tstruct _UrlState noattr))
                                                      _infilesize tlong))
                                                  (Stmt.Sset _t'6
                                                    (Expr.Ecast
                                                      (Expr.Ebinop Binop.One
                                                        (Expr.Etempvar _t'54 tlong)
                                                        (Expr.Eunop Unop.Oneg
                                                          (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                          tint) tint) tbool)))
                                                (Stmt.Sset _t'6
                                                  (Expr.Econst_int (Integers.Int.repr 0) tint))))
                                            (Stmt.Sifthenelse (Expr.Etempvar _t'6 tint)
                                              (Stmt.Ssequence
                                                (Stmt.Sset _t'52
                                                  (Expr.Efield
                                                    (Expr.Efield
                                                      (Expr.Ederef
                                                        (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                        (Ty.Tstruct _Curl_easy noattr))
                                                      _state
                                                      (Ty.Tstruct _UrlState noattr))
                                                    _infilesize tlong))
                                                (Stmt.Sset _t'7
                                                  (Expr.Ecast
                                                    (Expr.Etempvar _t'52 tlong)
                                                    tlong)))
                                              (Stmt.Sset _t'7
                                                (Expr.Ecast
                                                  (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                  tlong))))
                                          (Stmt.Scall none
                                            (Expr.Evar _curl_msnprintf 
                                            (Ty.Tfunction
                                              [(tptr tschar), tulong,
                                               (tptr tschar)] tint
                                              { cc_vararg := (some 3), cc_unproto := false, cc_structret := false }))
                                            [(Expr.Evar _buf (tarray tschar 64)),
                                             (Expr.Esizeof (tarray tschar 64) tulong),
                                             (Expr.Evar ___stringlit_6 (tarray tschar 5)),
                                             (Expr.Etempvar _t'7 tlong)]))
                                        (Stmt.Ssequence
                                          (Stmt.Ssequence
                                            (Stmt.Ssequence
                                              (Stmt.Sset _t'50
                                                (Expr.Efield
                                                  (Expr.Efield
                                                    (Expr.Ederef
                                                      (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                      (Ty.Tstruct _tftp_conn noattr))
                                                    _spacket
                                                    (Ty.Tstruct _tftp_packet noattr))
                                                  _data (tptr tuchar)))
                                              (Stmt.Ssequence
                                                (Stmt.Sset _t'51
                                                  (Expr.Evar _sbytes tulong))
                                                (Stmt.Scall (some _t'8)
                                                  (Expr.Evar _tftp_option_add 
                                                  (Ty.Tfunction
                                                    [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                                     (tptr tulong),
                                                     (tptr tschar),
                                                     (tptr tschar)] tint
                                                    cc_default))
                                                  [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                                                   (Expr.Eaddrof
                                                     (Expr.Evar _sbytes tulong)
                                                     (tptr tulong)),
                                                   (Expr.Ebinop Binop.Oadd
                                                     (Expr.Ecast
                                                       (Expr.Etempvar _t'50 (tptr tuchar))
                                                       (tptr tschar))
                                                     (Expr.Etempvar _t'51 tulong)
                                                     (tptr tschar)),
                                                   (Expr.Evar ___stringlit_7 (tarray tschar 6))])))
                                            (Stmt.Sset _result
                                              (Expr.Etempvar _t'8 tint)))
                                          (Stmt.Ssequence
                                            (Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq
                                                                (Expr.Etempvar _result tint)
                                                                (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                tint)
                                              (Stmt.Ssequence
                                                (Stmt.Ssequence
                                                  (Stmt.Sset _t'48
                                                    (Expr.Efield
                                                      (Expr.Efield
                                                        (Expr.Ederef
                                                          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                          (Ty.Tstruct _tftp_conn noattr))
                                                        _spacket
                                                        (Ty.Tstruct _tftp_packet noattr))
                                                      _data (tptr tuchar)))
                                                  (Stmt.Ssequence
                                                    (Stmt.Sset _t'49
                                                      (Expr.Evar _sbytes tulong))
                                                    (Stmt.Scall (some _t'9)
                                                      (Expr.Evar _tftp_option_add 
                                                      (Ty.Tfunction
                                                        [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                                         (tptr tulong),
                                                         (tptr tschar),
                                                         (tptr tschar)] tint
                                                        cc_default))
                                                      [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                                                       (Expr.Eaddrof
                                                         (Expr.Evar _sbytes tulong)
                                                         (tptr tulong)),
                                                       (Expr.Ebinop Binop.Oadd
                                                         (Expr.Ecast
                                                           (Expr.Etempvar _t'48 (tptr tuchar))
                                                           (tptr tschar))
                                                         (Expr.Etempvar _t'49 tulong)
                                                         (tptr tschar)),
                                                       (Expr.Evar _buf (tarray tschar 64))])))
                                                (Stmt.Sset _result
                                                  (Expr.Etempvar _t'9 tint)))
                                              Stmt.Sskip)
                                            (Stmt.Ssequence
                                              (Stmt.Ssequence
                                                (Stmt.Sset _t'47
                                                  (Expr.Efield
                                                    (Expr.Ederef
                                                      (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                      (Ty.Tstruct _tftp_conn noattr))
                                                    _requested_blksize tuint))
                                                (Stmt.Scall none
                                                  (Expr.Evar _curl_msnprintf 
                                                  (Ty.Tfunction
                                                    [(tptr tschar), tulong,
                                                     (tptr tschar)] tint
                                                    { cc_vararg := (some 3), cc_unproto := false, cc_structret := false }))
                                                  [(Expr.Evar _buf (tarray tschar 64)),
                                                   (Expr.Esizeof (tarray tschar 64) tulong),
                                                   (Expr.Evar ___stringlit_8 (tarray tschar 3)),
                                                   (Expr.Etempvar _t'47 tuint)]))
                                              (Stmt.Ssequence
                                                (Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq
                                                                    (Expr.Etempvar _result tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    tint)
                                                  (Stmt.Ssequence
                                                    (Stmt.Ssequence
                                                      (Stmt.Sset _t'45
                                                        (Expr.Efield
                                                          (Expr.Efield
                                                            (Expr.Ederef
                                                              (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                              (Ty.Tstruct _tftp_conn noattr))
                                                            _spacket
                                                            (Ty.Tstruct _tftp_packet noattr))
                                                          _data
                                                          (tptr tuchar)))
                                                      (Stmt.Ssequence
                                                        (Stmt.Sset _t'46
                                                          (Expr.Evar _sbytes tulong))
                                                        (Stmt.Scall (some _t'10)
                                                          (Expr.Evar _tftp_option_add 
                                                          (Ty.Tfunction
                                                            [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                                             (tptr tulong),
                                                             (tptr tschar),
                                                             (tptr tschar)]
                                                            tint cc_default))
                                                          [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                                                           (Expr.Eaddrof
                                                             (Expr.Evar _sbytes tulong)
                                                             (tptr tulong)),
                                                           (Expr.Ebinop Binop.Oadd
                                                             (Expr.Ecast
                                                               (Expr.Etempvar _t'45 (tptr tuchar))
                                                               (tptr tschar))
                                                             (Expr.Etempvar _t'46 tulong)
                                                             (tptr tschar)),
                                                           (Expr.Evar ___stringlit_9 (tarray tschar 8))])))
                                                    (Stmt.Sset _result
                                                      (Expr.Etempvar _t'10 tint)))
                                                  Stmt.Sskip)
                                                (Stmt.Ssequence
                                                  (Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq
                                                                    (Expr.Etempvar _result tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    tint)
                                                    (Stmt.Ssequence
                                                      (Stmt.Ssequence
                                                        (Stmt.Sset _t'43
                                                          (Expr.Efield
                                                            (Expr.Efield
                                                              (Expr.Ederef
                                                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                                (Ty.Tstruct _tftp_conn noattr))
                                                              _spacket
                                                              (Ty.Tstruct _tftp_packet noattr))
                                                            _data
                                                            (tptr tuchar)))
                                                        (Stmt.Ssequence
                                                          (Stmt.Sset _t'44
                                                            (Expr.Evar _sbytes tulong))
                                                          (Stmt.Scall (some _t'11)
                                                            (Expr.Evar _tftp_option_add 
                                                            (Ty.Tfunction
                                                              [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                                               (tptr tulong),
                                                               (tptr tschar),
                                                               (tptr tschar)]
                                                              tint
                                                              cc_default))
                                                            [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                                                             (Expr.Eaddrof
                                                               (Expr.Evar _sbytes tulong)
                                                               (tptr tulong)),
                                                             (Expr.Ebinop Binop.Oadd
                                                               (Expr.Ecast
                                                                 (Expr.Etempvar _t'43 (tptr tuchar))
                                                                 (tptr tschar))
                                                               (Expr.Etempvar _t'44 tulong)
                                                               (tptr tschar)),
                                                             (Expr.Evar _buf (tarray tschar 64))])))
                                                      (Stmt.Sset _result
                                                        (Expr.Etempvar _t'11 tint)))
                                                    Stmt.Sskip)
                                                  (Stmt.Ssequence
                                                    (Stmt.Ssequence
                                                      (Stmt.Sset _t'42
                                                        (Expr.Efield
                                                          (Expr.Ederef
                                                            (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                            (Ty.Tstruct _tftp_conn noattr))
                                                          _retry_time tint))
                                                      (Stmt.Scall none
                                                        (Expr.Evar _curl_msnprintf 
                                                        (Ty.Tfunction
                                                          [(tptr tschar),
                                                           tulong,
                                                           (tptr tschar)]
                                                          tint
                                                          { cc_vararg := (some 3), cc_unproto := false, cc_structret := false }))
                                                        [(Expr.Evar _buf (tarray tschar 64)),
                                                         (Expr.Esizeof (tarray tschar 64) tulong),
                                                         (Expr.Evar ___stringlit_8 (tarray tschar 3)),
                                                         (Expr.Etempvar _t'42 tint)]))
                                                    (Stmt.Ssequence
                                                      (Stmt.Sifthenelse 
                                                        (Expr.Ebinop Binop.Oeq
                                                          (Expr.Etempvar _result tint)
                                                          (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                          tint)
                                                        (Stmt.Ssequence
                                                          (Stmt.Ssequence
                                                            (Stmt.Sset _t'40
                                                              (Expr.Efield
                                                                (Expr.Efield
                                                                  (Expr.Ederef
                                                                    (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                                    (Ty.Tstruct _tftp_conn noattr))
                                                                  _spacket
                                                                  (Ty.Tstruct _tftp_packet noattr))
                                                                _data
                                                                (tptr tuchar)))
                                                            (Stmt.Ssequence
                                                              (Stmt.Sset _t'41
                                                                (Expr.Evar _sbytes tulong))
                                                              (Stmt.Scall (some _t'12)
                                                                (Expr.Evar _tftp_option_add 
                                                                (Ty.Tfunction
                                                                  [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                                                   (tptr tulong),
                                                                   (tptr tschar),
                                                                   (tptr tschar)]
                                                                  tint
                                                                  cc_default))
                                                                [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                                                                 (Expr.Eaddrof
                                                                   (Expr.Evar _sbytes tulong)
                                                                   (tptr tulong)),
                                                                 (Expr.Ebinop Binop.Oadd
                                                                   (Expr.Ecast
                                                                    (Expr.Etempvar _t'40 (tptr tuchar))
                                                                    (tptr tschar))
                                                                   (Expr.Etempvar _t'41 tulong)
                                                                   (tptr tschar)),
                                                                 (Expr.Evar ___stringlit_10 (tarray tschar 8))])))
                                                          (Stmt.Sset _result
                                                            (Expr.Etempvar _t'12 tint)))
                                                        Stmt.Sskip)
                                                      (Stmt.Ssequence
                                                        (Stmt.Sifthenelse 
                                                          (Expr.Ebinop Binop.Oeq
                                                            (Expr.Etempvar _result tint)
                                                            (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                            tint)
                                                          (Stmt.Ssequence
                                                            (Stmt.Ssequence
                                                              (Stmt.Sset _t'38
                                                                (Expr.Efield
                                                                  (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                                    (Ty.Tstruct _tftp_conn noattr))
                                                                    _spacket
                                                                    (Ty.Tstruct _tftp_packet noattr))
                                                                  _data
                                                                  (tptr tuchar)))
                                                              (Stmt.Ssequence
                                                                (Stmt.Sset _t'39
                                                                  (Expr.Evar _sbytes tulong))
                                                                (Stmt.Scall (some _t'13)
                                                                  (Expr.Evar _tftp_option_add 
                                                                  (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                                                    (tptr tulong),
                                                                    (tptr tschar),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                  [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                                                                   (Expr.Eaddrof
                                                                    (Expr.Evar _sbytes tulong)
                                                                    (tptr tulong)),
                                                                   (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Ecast
                                                                    (Expr.Etempvar _t'38 (tptr tuchar))
                                                                    (tptr tschar))
                                                                    (Expr.Etempvar _t'39 tulong)
                                                                    (tptr tschar)),
                                                                   (Expr.Evar _buf (tarray tschar 64))])))
                                                            (Stmt.Sset _result
                                                              (Expr.Etempvar _t'13 tint)))
                                                          Stmt.Sskip)
                                                        (Stmt.Sifthenelse 
                                                          (Expr.Ebinop Binop.One
                                                            (Expr.Etempvar _result tint)
                                                            (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                            tint)
                                                          (Stmt.Ssequence
                                                            (Stmt.Scall none
                                                              (Expr.Evar _Curl_failf 
                                                              (Ty.Tfunction
                                                                [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                 (tptr tschar)]
                                                                tvoid
                                                                { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                                              [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                               (Expr.Evar ___stringlit_11 (tarray tschar 34))])
                                                            (Stmt.Ssequence
                                                              (Stmt.Ssequence
                                                                (Stmt.Sset _t'37
                                                                  (Expr.Evar _filename (tptr tschar)))
                                                                (Stmt.Scall none
                                                                  (Expr.Evar _Curl_cfree 
                                                                  (Ty.Tfunction
                                                                    [(tptr tvoid)]
                                                                    tvoid
                                                                    cc_default))
                                                                  [(Expr.Etempvar _t'37 (tptr tschar))]))
                                                              (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 71) tint)))))
                                                          Stmt.Sskip))))))))))
                                      Stmt.Sskip))
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'28
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                              (Ty.Tstruct _tftp_conn noattr))
                                            _sockfd tint))
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'29
                                            (Expr.Efield
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                  (Ty.Tstruct _tftp_conn noattr))
                                                _spacket
                                                (Ty.Tstruct _tftp_packet noattr))
                                              _data (tptr tuchar)))
                                          (Stmt.Ssequence
                                            (Stmt.Sset _t'30
                                              (Expr.Evar _sbytes tulong))
                                            (Stmt.Ssequence
                                              (Stmt.Sset _t'31
                                                (Expr.Efield
                                                  (Expr.Ederef
                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                    (Ty.Tstruct _Curl_easy noattr))
                                                  _conn
                                                  (tptr (Ty.Tstruct _connectdata noattr))))
                                              (Stmt.Ssequence
                                                (Stmt.Sset _t'32
                                                  (Expr.Efield
                                                    (Expr.Ederef
                                                      (Expr.Etempvar _t'31 (tptr (Ty.Tstruct _connectdata noattr)))
                                                      (Ty.Tstruct _connectdata noattr))
                                                    _remote_addr
                                                    (tptr (Ty.Tstruct _Curl_sockaddr_ex noattr))))
                                                (Stmt.Ssequence
                                                  (Stmt.Sset _t'33
                                                    (Expr.Efield
                                                      (Expr.Ederef
                                                        (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                        (Ty.Tstruct _Curl_easy noattr))
                                                      _conn
                                                      (tptr (Ty.Tstruct _connectdata noattr))))
                                                  (Stmt.Ssequence
                                                    (Stmt.Sset _t'34
                                                      (Expr.Efield
                                                        (Expr.Ederef
                                                          (Expr.Etempvar _t'33 (tptr (Ty.Tstruct _connectdata noattr)))
                                                          (Ty.Tstruct _connectdata noattr))
                                                        _remote_addr
                                                        (tptr (Ty.Tstruct _Curl_sockaddr_ex noattr))))
                                                    (Stmt.Ssequence
                                                      (Stmt.Sset _t'35
                                                        (Expr.Efield
                                                          (Expr.Ederef
                                                            (Expr.Etempvar _t'34 (tptr (Ty.Tstruct _Curl_sockaddr_ex noattr)))
                                                            (Ty.Tstruct _Curl_sockaddr_ex noattr))
                                                          _addrlen tuint))
                                                      (Stmt.Scall (some _t'14)
                                                        (Expr.Evar _sendto 
                                                        (Ty.Tfunction
                                                          [tint,
                                                           (tptr tvoid),
                                                           tulong, tint,
                                                           (tptr (Ty.Tstruct _sockaddr noattr)),
                                                           tuint] tlong
                                                          cc_default))
                                                        [(Expr.Etempvar _t'28 tint),
                                                         (Expr.Ecast
                                                           (Expr.Etempvar _t'29 (tptr tuchar))
                                                           (tptr tvoid)),
                                                         (Expr.Ecast
                                                           (Expr.Etempvar _t'30 tulong)
                                                           tulong),
                                                         (Expr.Econst_int (Integers.Int.repr 0) tint),
                                                         (Expr.Eaddrof
                                                           (Expr.Efield
                                                             (Expr.Ederef
                                                               (Expr.Etempvar _t'32 (tptr (Ty.Tstruct _Curl_sockaddr_ex noattr)))
                                                               (Ty.Tstruct _Curl_sockaddr_ex noattr))
                                                             _curl_sa_addr
                                                             (Ty.Tstruct _sockaddr noattr))
                                                           (tptr (Ty.Tstruct _sockaddr noattr))),
                                                         (Expr.Ecast
                                                           (Expr.Etempvar _t'35 tuint)
                                                           tuint)])))))))))
                                      (Stmt.Sset _senddata
                                        (Expr.Etempvar _t'14 tlong)))
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'26
                                          (Expr.Evar _sbytes tulong))
                                        (Stmt.Sifthenelse (Expr.Ebinop Binop.One
                                                            (Expr.Etempvar _senddata tlong)
                                                            (Expr.Ecast
                                                              (Expr.Etempvar _t'26 tulong)
                                                              tlong) tint)
                                          (Stmt.Ssequence
                                            (Stmt.Ssequence
                                              (Stmt.Scall (some _t'15)
                                                (Expr.Evar ___errno_location 
                                                (Ty.Tfunction [] (tptr tint)
                                                  cc_default)) [])
                                              (Stmt.Ssequence
                                                (Stmt.Sset _t'27
                                                  (Expr.Ederef
                                                    (Expr.Etempvar _t'15 (tptr tint))
                                                    tint))
                                                (Stmt.Scall (some _t'16)
                                                  (Expr.Evar _Curl_strerror 
                                                  (Ty.Tfunction
                                                    [tint, (tptr tschar),
                                                     tulong] (tptr tschar)
                                                    cc_default))
                                                  [(Expr.Etempvar _t'27 tint),
                                                   (Expr.Evar _buffer (tarray tschar 256)),
                                                   (Expr.Esizeof (tarray tschar 256) tulong)])))
                                            (Stmt.Scall none
                                              (Expr.Evar _Curl_failf 
                                              (Ty.Tfunction
                                                [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                 (tptr tschar)] tvoid
                                                { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                              [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                               (Expr.Evar ___stringlit_12 (tarray tschar 3)),
                                               (Expr.Etempvar _t'16 (tptr tschar))]))
                                          Stmt.Sskip))
                                      (Stmt.Ssequence
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'25
                                            (Expr.Evar _filename (tptr tschar)))
                                          (Stmt.Scall none
                                            (Expr.Evar _Curl_cfree (Ty.Tfunction
                                                                    [(tptr tvoid)]
                                                                    tvoid
                                                                    cc_default))
                                            [(Expr.Etempvar _t'25 (tptr tschar))]))
                                        Stmt.Sbreak))))))))))))
                (LStmts.LScons (some 6)
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sset _t'24
                        (Expr.Efield
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                              (Ty.Tstruct _Curl_easy noattr)) _state
                            (Ty.Tstruct _UrlState noattr)) _upload tint))
                      (Stmt.Sifthenelse (Expr.Etempvar _t'24 tint)
                        (Stmt.Ssequence
                          (Stmt.Scall (some _t'17)
                            (Expr.Evar _tftp_connect_for_tx (Ty.Tfunction
                                                              [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                                               tint] tint
                                                              cc_default))
                            [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                             (Expr.Etempvar _event tint)])
                          (Stmt.Sset _result (Expr.Etempvar _t'17 tint)))
                        (Stmt.Ssequence
                          (Stmt.Scall (some _t'18)
                            (Expr.Evar _tftp_connect_for_rx (Ty.Tfunction
                                                              [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                                               tint] tint
                                                              cc_default))
                            [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                             (Expr.Etempvar _event tint)])
                          (Stmt.Sset _result (Expr.Etempvar _t'18 tint)))))
                    Stmt.Sbreak)
                  (LStmts.LScons (some 4)
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Sset _t'23
                          (Expr.Efield
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                (Ty.Tstruct _Curl_easy noattr)) _state
                              (Ty.Tstruct _UrlState noattr)) _upload tint))
                        (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                            (Expr.Etempvar _t'23 tint) tint)
                          (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 71) tint)))
                          Stmt.Sskip))
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Scall (some _t'19)
                            (Expr.Evar _tftp_connect_for_tx (Ty.Tfunction
                                                              [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                                               tint] tint
                                                              cc_default))
                            [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                             (Expr.Etempvar _event tint)])
                          (Stmt.Sset _result (Expr.Etempvar _t'19 tint)))
                        Stmt.Sbreak))
                    (LStmts.LScons (some 3)
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Sset _t'22
                            (Expr.Efield
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                  (Ty.Tstruct _Curl_easy noattr)) _state
                                (Ty.Tstruct _UrlState noattr)) _upload tint))
                          (Stmt.Sifthenelse (Expr.Etempvar _t'22 tint)
                            (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 71) tint)))
                            Stmt.Sskip))
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Scall (some _t'20)
                              (Expr.Evar _tftp_connect_for_rx (Ty.Tfunction
                                                                [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                                                 tint] tint
                                                                cc_default))
                              [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                               (Expr.Etempvar _event tint)])
                            (Stmt.Sset _result (Expr.Etempvar _t'20 tint)))
                          Stmt.Sbreak))
                      (LStmts.LScons (some 5)
                        (Stmt.Ssequence
                          (Stmt.Sassign
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                (Ty.Tstruct _tftp_conn noattr)) _state tint)
                            (Expr.Econst_int (Integers.Int.repr 3) tint))
                          Stmt.Sbreak)
                        (LStmts.LScons none
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Sset _t'21
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                    (Ty.Tstruct _tftp_conn noattr)) _data
                                  (tptr (Ty.Tstruct _Curl_easy noattr))))
                              (Stmt.Scall none
                                (Expr.Evar _Curl_failf (Ty.Tfunction
                                                         [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                          (tptr tschar)]
                                                         tvoid
                                                         { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                [(Expr.Etempvar _t'21 (tptr (Ty.Tstruct _Curl_easy noattr))),
                                 (Expr.Evar ___stringlit_3 (tarray tschar 32))]))
                            Stmt.Sbreak)
                          LStmts.LSnil))))))))
          (Stmt.Sreturn (some (Expr.Etempvar _result tint))))))))
}

def f_tftp_tx : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_state, (tptr (Ty.Tstruct _tftp_conn noattr))),
                (_event, tint)],
  fn_vars := [(_cb, tulong), (_buffer, (tarray tschar 256)), (_eos, tbool)],
  fn_temps := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
               (_sbytes, tlong), (_result, tint),
               (_k, (tptr (Ty.Tstruct _SingleRequest noattr))),
               (_bufptr, (tptr tschar)), (_rblock, tint),
               (_t'16, (tptr tschar)), (_t'15, (tptr tint)), (_t'14, tlong),
               (_t'13, (tptr tschar)), (_t'12, (tptr tint)), (_t'11, tlong),
               (_t'10, tint), (_t'9, tint), (_t'8, tint), (_t'7, tlong),
               (_t'6, tint), (_t'5, tint), (_t'4, (tptr tschar)),
               (_t'3, (tptr tint)), (_t'2, tlong), (_t'1, tushort),
               (_t'66, tint), (_t'65, tushort), (_t'64, tushort),
               (_t'63, tushort), (_t'62, tint), (_t'61, tushort),
               (_t'60, tuint), (_t'59, tulong), (_t'58, (tptr tuchar)),
               (_t'57, tint), (_t'56, tint), (_t'55, tint), (_t'54, tint),
               (_t'53, tushort), (_t'52, tushort), (_t'51, tuint),
               (_t'50, tulong), (_t'49, tushort), (_t'48, (tptr tuchar)),
               (_t'47, tulong), (_t'46, tuint), (_t'45, tulong),
               (_t'44, tulong), (_t'43, tulong), (_t'42, tulong),
               (_t'41, tuint), (_t'40, tulong), (_t'39, tuint),
               (_t'38, tulong), (_t'37, (tptr tuchar)), (_t'36, tint),
               (_t'35, tint), (_t'34, tulong), (_t'33, tlong),
               (_t'32, tlong), (_t'31, tint), (_t'30, tint),
               (_t'29, tushort), (_t'28, tuint), (_t'27, tulong),
               (_t'26, (tptr tuchar)), (_t'25, tint), (_t'24, tint),
               (_t'23, tlong), (_t'22, tint), (_t'21, tint),
               (_t'20, tushort), (_t'19, tuint), (_t'18, (tptr tuchar)),
               (_t'17, tint)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Sset _data
    (Expr.Efield
      (Expr.Ederef
        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
        (Ty.Tstruct _tftp_conn noattr)) _data
      (tptr (Ty.Tstruct _Curl_easy noattr))))
  (Stmt.Ssequence
    (Stmt.Sset _result (Expr.Econst_int (Integers.Int.repr 0) tint))
    (Stmt.Ssequence
      (Stmt.Sset _k
        (Expr.Eaddrof
          (Expr.Efield
            (Expr.Ederef
              (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
              (Ty.Tstruct _Curl_easy noattr)) _req
            (Ty.Tstruct _SingleRequest noattr))
          (tptr (Ty.Tstruct _SingleRequest noattr))))
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Sset _t'66
            (Expr.Efield
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                  (Ty.Tstruct _Curl_easy noattr)) _state
                (Ty.Tstruct _UrlState noattr)) _upload tint))
          (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                              (Expr.Etempvar _t'66 tint) tint)
            (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 71) tint)))
            Stmt.Sskip))
        (Stmt.Ssequence
          (Stmt.Sswitch (Expr.Etempvar _event tint)
            (LStmts.LScons (some 4)
              Stmt.Sskip
              (LStmts.LScons (some 6)
                (Stmt.Ssequence
                  (Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq
                                      (Expr.Etempvar _event tint)
                                      (Expr.Econst_int (Integers.Int.repr 4) tint)
                                      tint)
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Scall (some _t'1)
                          (Expr.Evar _getrpacketblock (Ty.Tfunction
                                                        [(tptr (Ty.Tstruct _tftp_packet noattr))]
                                                        tushort cc_default))
                          [(Expr.Eaddrof
                             (Expr.Efield
                               (Expr.Ederef
                                 (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                 (Ty.Tstruct _tftp_conn noattr)) _rpacket
                               (Ty.Tstruct _tftp_packet noattr))
                             (tptr (Ty.Tstruct _tftp_packet noattr)))])
                        (Stmt.Sset _rblock (Expr.Etempvar _t'1 tushort)))
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'64
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                  (Ty.Tstruct _tftp_conn noattr)) _block
                                tushort))
                            (Stmt.Sifthenelse (Expr.Ebinop Binop.One
                                                (Expr.Etempvar _rblock tint)
                                                (Expr.Etempvar _t'64 tushort)
                                                tint)
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'65
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                        (Ty.Tstruct _tftp_conn noattr))
                                      _block tushort))
                                  (Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq
                                                      (Expr.Etempvar _t'65 tushort)
                                                      (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                      tint)
                                    (Stmt.Sset _t'6
                                      (Expr.Ecast
                                        (Expr.Ebinop Binop.Oeq
                                          (Expr.Etempvar _rblock tint)
                                          (Expr.Econst_int (Integers.Int.repr 65535) tint)
                                          tint) tbool))
                                    (Stmt.Sset _t'6
                                      (Expr.Econst_int (Integers.Int.repr 0) tint))))
                                (Stmt.Sset _t'5
                                  (Expr.Ecast
                                    (Expr.Eunop Unop.Onotbool
                                      (Expr.Etempvar _t'6 tint) tint) tbool)))
                              (Stmt.Sset _t'5
                                (Expr.Econst_int (Integers.Int.repr 0) tint))))
                          (Stmt.Sifthenelse (Expr.Etempvar _t'5 tint)
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Sset _t'63
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                      (Ty.Tstruct _tftp_conn noattr)) _block
                                    tushort))
                                (Stmt.Scall none
                                  (Expr.Evar _Curl_infof (Ty.Tfunction
                                                           [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                            (tptr tschar)]
                                                           tvoid
                                                           { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                  [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                   (Expr.Evar ___stringlit_15 (tarray tschar 40)),
                                   (Expr.Etempvar _rblock tint),
                                   (Expr.Etempvar _t'63 tushort)]))
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'62
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                        (Ty.Tstruct _tftp_conn noattr))
                                      _retries tint))
                                  (Stmt.Sassign
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                        (Ty.Tstruct _tftp_conn noattr))
                                      _retries tint)
                                    (Expr.Ebinop Binop.Oadd
                                      (Expr.Etempvar _t'62 tint)
                                      (Expr.Econst_int (Integers.Int.repr 1) tint)
                                      tint)))
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Sset _t'54
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                          (Ty.Tstruct _tftp_conn noattr))
                                        _retries tint))
                                    (Stmt.Ssequence
                                      (Stmt.Sset _t'55
                                        (Expr.Efield
                                          (Expr.Ederef
                                            (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                            (Ty.Tstruct _tftp_conn noattr))
                                          _retry_max tint))
                                      (Stmt.Sifthenelse (Expr.Ebinop Binop.Ogt
                                                          (Expr.Etempvar _t'54 tint)
                                                          (Expr.Etempvar _t'55 tint)
                                                          tint)
                                        (Stmt.Ssequence
                                          (Stmt.Ssequence
                                            (Stmt.Sset _t'61
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                  (Ty.Tstruct _tftp_conn noattr))
                                                _block tushort))
                                            (Stmt.Scall none
                                              (Expr.Evar _Curl_failf 
                                              (Ty.Tfunction
                                                [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                 (tptr tschar)] tvoid
                                                { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                              [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                               (Expr.Evar ___stringlit_16 (tarray tschar 44)),
                                               (Expr.Etempvar _t'61 tushort)]))
                                          (Stmt.Sset _result
                                            (Expr.Econst_int (Integers.Int.repr 55) tint)))
                                        (Stmt.Ssequence
                                          (Stmt.Ssequence
                                            (Stmt.Ssequence
                                              (Stmt.Sset _t'57
                                                (Expr.Efield
                                                  (Expr.Ederef
                                                    (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                    (Ty.Tstruct _tftp_conn noattr))
                                                  _sockfd tint))
                                              (Stmt.Ssequence
                                                (Stmt.Sset _t'58
                                                  (Expr.Efield
                                                    (Expr.Efield
                                                      (Expr.Ederef
                                                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                        (Ty.Tstruct _tftp_conn noattr))
                                                      _spacket
                                                      (Ty.Tstruct _tftp_packet noattr))
                                                    _data (tptr tuchar)))
                                                (Stmt.Ssequence
                                                  (Stmt.Sset _t'59
                                                    (Expr.Efield
                                                      (Expr.Ederef
                                                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                        (Ty.Tstruct _tftp_conn noattr))
                                                      _sbytes tulong))
                                                  (Stmt.Ssequence
                                                    (Stmt.Sset _t'60
                                                      (Expr.Efield
                                                        (Expr.Ederef
                                                          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                          (Ty.Tstruct _tftp_conn noattr))
                                                        _remote_addrlen
                                                        tuint))
                                                    (Stmt.Scall (some _t'2)
                                                      (Expr.Evar _sendto 
                                                      (Ty.Tfunction
                                                        [tint, (tptr tvoid),
                                                         tulong, tint,
                                                         (tptr (Ty.Tstruct _sockaddr noattr)),
                                                         tuint] tlong
                                                        cc_default))
                                                      [(Expr.Etempvar _t'57 tint),
                                                       (Expr.Ecast
                                                         (Expr.Etempvar _t'58 (tptr tuchar))
                                                         (tptr tvoid)),
                                                       (Expr.Ebinop Binop.Oadd
                                                         (Expr.Econst_int (Integers.Int.repr 4) tint)
                                                         (Expr.Ecast
                                                           (Expr.Etempvar _t'59 tulong)
                                                           tulong) tulong),
                                                       (Expr.Econst_int (Integers.Int.repr 16384) tint),
                                                       (Expr.Ecast
                                                         (Expr.Eaddrof
                                                           (Expr.Efield
                                                             (Expr.Ederef
                                                               (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                               (Ty.Tstruct _tftp_conn noattr))
                                                             _remote_addr
                                                             (Ty.Tstruct _Curl_sockaddr_storage noattr))
                                                           (tptr (Ty.Tstruct _Curl_sockaddr_storage noattr)))
                                                         (tptr (Ty.Tstruct _sockaddr noattr))),
                                                       (Expr.Etempvar _t'60 tuint)])))))
                                            (Stmt.Sset _sbytes
                                              (Expr.Etempvar _t'2 tlong)))
                                          (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                                              (Expr.Etempvar _sbytes tlong)
                                                              (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                              tint)
                                            (Stmt.Ssequence
                                              (Stmt.Ssequence
                                                (Stmt.Ssequence
                                                  (Stmt.Scall (some _t'3)
                                                    (Expr.Evar ___errno_location 
                                                    (Ty.Tfunction []
                                                      (tptr tint) cc_default))
                                                    [])
                                                  (Stmt.Ssequence
                                                    (Stmt.Sset _t'56
                                                      (Expr.Ederef
                                                        (Expr.Etempvar _t'3 (tptr tint))
                                                        tint))
                                                    (Stmt.Scall (some _t'4)
                                                      (Expr.Evar _Curl_strerror 
                                                      (Ty.Tfunction
                                                        [tint, (tptr tschar),
                                                         tulong]
                                                        (tptr tschar)
                                                        cc_default))
                                                      [(Expr.Etempvar _t'56 tint),
                                                       (Expr.Evar _buffer (tarray tschar 256)),
                                                       (Expr.Esizeof (tarray tschar 256) tulong)])))
                                                (Stmt.Scall none
                                                  (Expr.Evar _Curl_failf 
                                                  (Ty.Tfunction
                                                    [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                     (tptr tschar)] tvoid
                                                    { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                                  [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                   (Expr.Evar ___stringlit_12 (tarray tschar 3)),
                                                   (Expr.Etempvar _t'4 (tptr tschar))]))
                                              (Stmt.Sset _result
                                                (Expr.Econst_int (Integers.Int.repr 55) tint)))
                                            Stmt.Sskip)))))
                                  (Stmt.Sreturn (some (Expr.Etempvar _result tint))))))
                            Stmt.Sskip))
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Scall (some _t'7)
                              (Expr.Evar _time (Ty.Tfunction [(tptr tlong)]
                                                 tlong cc_default))
                              [(Expr.Ecast
                                 (Expr.Econst_int (Integers.Int.repr 0) tint)
                                 (tptr tvoid))])
                            (Stmt.Sassign
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                  (Ty.Tstruct _tftp_conn noattr)) _rx_time
                                tlong) (Expr.Etempvar _t'7 tlong)))
                          (Stmt.Ssequence
                            (Stmt.Sset _t'53
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                  (Ty.Tstruct _tftp_conn noattr)) _block
                                tushort))
                            (Stmt.Sassign
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                  (Ty.Tstruct _tftp_conn noattr)) _block
                                tushort)
                              (Expr.Ebinop Binop.Oadd
                                (Expr.Etempvar _t'53 tushort)
                                (Expr.Econst_int (Integers.Int.repr 1) tint)
                                tint))))))
                    (Stmt.Sassign
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                          (Ty.Tstruct _tftp_conn noattr)) _block tushort)
                      (Expr.Econst_int (Integers.Int.repr 1) tint)))
                  (Stmt.Ssequence
                    (Stmt.Sassign
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                          (Ty.Tstruct _tftp_conn noattr)) _retries tint)
                      (Expr.Econst_int (Integers.Int.repr 0) tint))
                    (Stmt.Ssequence
                      (Stmt.Scall none
                        (Expr.Evar _setpacketevent (Ty.Tfunction
                                                     [(tptr (Ty.Tstruct _tftp_packet noattr)),
                                                      tushort] tvoid
                                                     cc_default))
                        [(Expr.Eaddrof
                           (Expr.Efield
                             (Expr.Ederef
                               (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                               (Ty.Tstruct _tftp_conn noattr)) _spacket
                             (Ty.Tstruct _tftp_packet noattr))
                           (tptr (Ty.Tstruct _tftp_packet noattr))),
                         (Expr.Econst_int (Integers.Int.repr 3) tint)])
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Sset _t'52
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                (Ty.Tstruct _tftp_conn noattr)) _block
                              tushort))
                          (Stmt.Scall none
                            (Expr.Evar _setpacketblock (Ty.Tfunction
                                                         [(tptr (Ty.Tstruct _tftp_packet noattr)),
                                                          tushort] tvoid
                                                         cc_default))
                            [(Expr.Eaddrof
                               (Expr.Efield
                                 (Expr.Ederef
                                   (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                   (Ty.Tstruct _tftp_conn noattr)) _spacket
                                 (Ty.Tstruct _tftp_packet noattr))
                               (tptr (Ty.Tstruct _tftp_packet noattr))),
                             (Expr.Etempvar _t'52 tushort)]))
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Sset _t'49
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                    (Ty.Tstruct _tftp_conn noattr)) _block
                                  tushort))
                              (Stmt.Sifthenelse (Expr.Ebinop Binop.Ogt
                                                  (Expr.Etempvar _t'49 tushort)
                                                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                  tint)
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'50
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                        (Ty.Tstruct _tftp_conn noattr))
                                      _sbytes tulong))
                                  (Stmt.Ssequence
                                    (Stmt.Sset _t'51
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                          (Ty.Tstruct _tftp_conn noattr))
                                        _blksize tuint))
                                    (Stmt.Sset _t'8
                                      (Expr.Ecast
                                        (Expr.Ebinop Binop.Olt
                                          (Expr.Etempvar _t'50 tulong)
                                          (Expr.Etempvar _t'51 tuint) tint)
                                        tbool))))
                                (Stmt.Sset _t'8
                                  (Expr.Econst_int (Integers.Int.repr 0) tint))))
                            (Stmt.Sifthenelse (Expr.Etempvar _t'8 tint)
                              (Stmt.Ssequence
                                (Stmt.Sassign
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                      (Ty.Tstruct _tftp_conn noattr)) _state
                                    tint)
                                  (Expr.Econst_int (Integers.Int.repr 3) tint))
                                (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint))))
                              Stmt.Sskip))
                          (Stmt.Ssequence
                            (Stmt.Sassign
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                  (Ty.Tstruct _tftp_conn noattr)) _sbytes
                                tulong)
                              (Expr.Econst_int (Integers.Int.repr 0) tint))
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Sset _t'48
                                  (Expr.Efield
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                        (Ty.Tstruct _tftp_conn noattr))
                                      _spacket
                                      (Ty.Tstruct _tftp_packet noattr)) _data
                                    (tptr tuchar)))
                                (Stmt.Sset _bufptr
                                  (Expr.Ebinop Binop.Oadd
                                    (Expr.Ecast
                                      (Expr.Etempvar _t'48 (tptr tuchar))
                                      (tptr tschar))
                                    (Expr.Econst_int (Integers.Int.repr 4) tint)
                                    (tptr tschar))))
                              (Stmt.Ssequence
                                (Stmt.Sloop
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'46
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                              (Ty.Tstruct _tftp_conn noattr))
                                            _blksize tuint))
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'47
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                (Ty.Tstruct _tftp_conn noattr))
                                              _sbytes tulong))
                                          (Stmt.Scall (some _t'10)
                                            (Expr.Evar _Curl_client_read 
                                            (Ty.Tfunction
                                              [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                               (tptr tschar), tulong,
                                               (tptr tulong), (tptr tbool)]
                                              tint cc_default))
                                            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                             (Expr.Etempvar _bufptr (tptr tschar)),
                                             (Expr.Ebinop Binop.Osub
                                               (Expr.Etempvar _t'46 tuint)
                                               (Expr.Etempvar _t'47 tulong)
                                               tulong),
                                             (Expr.Eaddrof
                                               (Expr.Evar _cb tulong)
                                               (tptr tulong)),
                                             (Expr.Eaddrof
                                               (Expr.Evar _eos tbool)
                                               (tptr tbool))])))
                                      (Stmt.Sset _result
                                        (Expr.Etempvar _t'10 tint)))
                                    (Stmt.Ssequence
                                      (Stmt.Sifthenelse (Expr.Etempvar _result tint)
                                        (Stmt.Sreturn (some (Expr.Etempvar _result tint)))
                                        Stmt.Sskip)
                                      (Stmt.Ssequence
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'44
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                (Ty.Tstruct _tftp_conn noattr))
                                              _sbytes tulong))
                                          (Stmt.Ssequence
                                            (Stmt.Sset _t'45
                                              (Expr.Evar _cb tulong))
                                            (Stmt.Sassign
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                  (Ty.Tstruct _tftp_conn noattr))
                                                _sbytes tulong)
                                              (Expr.Ebinop Binop.Oadd
                                                (Expr.Etempvar _t'44 tulong)
                                                (Expr.Etempvar _t'45 tulong)
                                                tulong))))
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'43
                                            (Expr.Evar _cb tulong))
                                          (Stmt.Sset _bufptr
                                            (Expr.Ebinop Binop.Oadd
                                              (Expr.Etempvar _bufptr (tptr tschar))
                                              (Expr.Etempvar _t'43 tulong)
                                              (tptr tschar)))))))
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Sset _t'40
                                        (Expr.Efield
                                          (Expr.Ederef
                                            (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                            (Ty.Tstruct _tftp_conn noattr))
                                          _sbytes tulong))
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'41
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                              (Ty.Tstruct _tftp_conn noattr))
                                            _blksize tuint))
                                        (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                                            (Expr.Etempvar _t'40 tulong)
                                                            (Expr.Etempvar _t'41 tuint)
                                                            tint)
                                          (Stmt.Ssequence
                                            (Stmt.Sset _t'42
                                              (Expr.Evar _cb tulong))
                                            (Stmt.Sset _t'9
                                              (Expr.Ecast
                                                (Expr.Etempvar _t'42 tulong)
                                                tbool)))
                                          (Stmt.Sset _t'9
                                            (Expr.Econst_int (Integers.Int.repr 0) tint)))))
                                    (Stmt.Sifthenelse (Expr.Etempvar _t'9 tint)
                                      Stmt.Sskip
                                      Stmt.Sbreak)))
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Sset _t'36
                                        (Expr.Efield
                                          (Expr.Ederef
                                            (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                            (Ty.Tstruct _tftp_conn noattr))
                                          _sockfd tint))
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'37
                                          (Expr.Efield
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                (Ty.Tstruct _tftp_conn noattr))
                                              _spacket
                                              (Ty.Tstruct _tftp_packet noattr))
                                            _data (tptr tuchar)))
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'38
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                (Ty.Tstruct _tftp_conn noattr))
                                              _sbytes tulong))
                                          (Stmt.Ssequence
                                            (Stmt.Sset _t'39
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                  (Ty.Tstruct _tftp_conn noattr))
                                                _remote_addrlen tuint))
                                            (Stmt.Scall (some _t'11)
                                              (Expr.Evar _sendto (Ty.Tfunction
                                                                   [tint,
                                                                    (tptr tvoid),
                                                                    tulong,
                                                                    tint,
                                                                    (tptr (Ty.Tstruct _sockaddr noattr)),
                                                                    tuint]
                                                                   tlong
                                                                   cc_default))
                                              [(Expr.Etempvar _t'36 tint),
                                               (Expr.Ecast
                                                 (Expr.Etempvar _t'37 (tptr tuchar))
                                                 (tptr tvoid)),
                                               (Expr.Ebinop Binop.Oadd
                                                 (Expr.Econst_int (Integers.Int.repr 4) tint)
                                                 (Expr.Ecast
                                                   (Expr.Etempvar _t'38 tulong)
                                                   tulong) tulong),
                                               (Expr.Econst_int (Integers.Int.repr 16384) tint),
                                               (Expr.Ecast
                                                 (Expr.Eaddrof
                                                   (Expr.Efield
                                                     (Expr.Ederef
                                                       (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                       (Ty.Tstruct _tftp_conn noattr))
                                                     _remote_addr
                                                     (Ty.Tstruct _Curl_sockaddr_storage noattr))
                                                   (tptr (Ty.Tstruct _Curl_sockaddr_storage noattr)))
                                                 (tptr (Ty.Tstruct _sockaddr noattr))),
                                               (Expr.Etempvar _t'39 tuint)])))))
                                    (Stmt.Sset _sbytes
                                      (Expr.Etempvar _t'11 tlong)))
                                  (Stmt.Ssequence
                                    (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                                        (Expr.Etempvar _sbytes tlong)
                                                        (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                        tint)
                                      (Stmt.Ssequence
                                        (Stmt.Ssequence
                                          (Stmt.Ssequence
                                            (Stmt.Scall (some _t'12)
                                              (Expr.Evar ___errno_location 
                                              (Ty.Tfunction [] (tptr tint)
                                                cc_default)) [])
                                            (Stmt.Ssequence
                                              (Stmt.Sset _t'35
                                                (Expr.Ederef
                                                  (Expr.Etempvar _t'12 (tptr tint))
                                                  tint))
                                              (Stmt.Scall (some _t'13)
                                                (Expr.Evar _Curl_strerror 
                                                (Ty.Tfunction
                                                  [tint, (tptr tschar),
                                                   tulong] (tptr tschar)
                                                  cc_default))
                                                [(Expr.Etempvar _t'35 tint),
                                                 (Expr.Evar _buffer (tarray tschar 256)),
                                                 (Expr.Esizeof (tarray tschar 256) tulong)])))
                                          (Stmt.Scall none
                                            (Expr.Evar _Curl_failf (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                    (tptr tschar)]
                                                                    tvoid
                                                                    { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                             (Expr.Evar ___stringlit_12 (tarray tschar 3)),
                                             (Expr.Etempvar _t'13 (tptr tschar))]))
                                        (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 55) tint))))
                                      Stmt.Sskip)
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'33
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _k (tptr (Ty.Tstruct _SingleRequest noattr)))
                                              (Ty.Tstruct _SingleRequest noattr))
                                            _writebytecount tlong))
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'34
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                (Ty.Tstruct _tftp_conn noattr))
                                              _sbytes tulong))
                                          (Stmt.Sassign
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _k (tptr (Ty.Tstruct _SingleRequest noattr)))
                                                (Ty.Tstruct _SingleRequest noattr))
                                              _writebytecount tlong)
                                            (Expr.Ebinop Binop.Oadd
                                              (Expr.Etempvar _t'33 tlong)
                                              (Expr.Etempvar _t'34 tulong)
                                              tulong))))
                                      (Stmt.Ssequence
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'32
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _k (tptr (Ty.Tstruct _SingleRequest noattr)))
                                                (Ty.Tstruct _SingleRequest noattr))
                                              _writebytecount tlong))
                                          (Stmt.Scall none
                                            (Expr.Evar _Curl_pgrsSetUploadCounter 
                                            (Ty.Tfunction
                                              [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                               tlong] tvoid cc_default))
                                            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                             (Expr.Etempvar _t'32 tlong)]))
                                        Stmt.Sbreak))))))))))))
                (LStmts.LScons (some 7)
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sset _t'31
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                            (Ty.Tstruct _tftp_conn noattr)) _retries tint))
                      (Stmt.Sassign
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                            (Ty.Tstruct _tftp_conn noattr)) _retries tint)
                        (Expr.Ebinop Binop.Oadd (Expr.Etempvar _t'31 tint)
                          (Expr.Econst_int (Integers.Int.repr 1) tint) tint)))
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Sset _t'29
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                              (Ty.Tstruct _tftp_conn noattr)) _block tushort))
                        (Stmt.Ssequence
                          (Stmt.Sset _t'30
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                (Ty.Tstruct _tftp_conn noattr)) _retries
                              tint))
                          (Stmt.Scall none
                            (Expr.Evar _Curl_infof (Ty.Tfunction
                                                     [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                      (tptr tschar)] tvoid
                                                     { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                             (Expr.Evar ___stringlit_14 (tarray tschar 48)),
                             (Expr.Ebinop Binop.Oand
                               (Expr.Ebinop Binop.Oadd
                                 (Expr.Etempvar _t'29 tushort)
                                 (Expr.Econst_int (Integers.Int.repr 1) tint)
                                 tint)
                               (Expr.Econst_int (Integers.Int.repr 65535) tint)
                               tint), (Expr.Etempvar _t'30 tint)])))
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Sset _t'21
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                (Ty.Tstruct _tftp_conn noattr)) _retries
                              tint))
                          (Stmt.Ssequence
                            (Stmt.Sset _t'22
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                  (Ty.Tstruct _tftp_conn noattr)) _retry_max
                                tint))
                            (Stmt.Sifthenelse (Expr.Ebinop Binop.Ogt
                                                (Expr.Etempvar _t'21 tint)
                                                (Expr.Etempvar _t'22 tint)
                                                tint)
                              (Stmt.Ssequence
                                (Stmt.Sassign
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                      (Ty.Tstruct _tftp_conn noattr)) _error
                                    tint)
                                  (Expr.Econst_int (Integers.Int.repr (-99)) tint))
                                (Stmt.Sassign
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                      (Ty.Tstruct _tftp_conn noattr)) _state
                                    tint)
                                  (Expr.Econst_int (Integers.Int.repr 3) tint)))
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Sset _t'25
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                          (Ty.Tstruct _tftp_conn noattr))
                                        _sockfd tint))
                                    (Stmt.Ssequence
                                      (Stmt.Sset _t'26
                                        (Expr.Efield
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                              (Ty.Tstruct _tftp_conn noattr))
                                            _spacket
                                            (Ty.Tstruct _tftp_packet noattr))
                                          _data (tptr tuchar)))
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'27
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                              (Ty.Tstruct _tftp_conn noattr))
                                            _sbytes tulong))
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'28
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                (Ty.Tstruct _tftp_conn noattr))
                                              _remote_addrlen tuint))
                                          (Stmt.Scall (some _t'14)
                                            (Expr.Evar _sendto (Ty.Tfunction
                                                                 [tint,
                                                                  (tptr tvoid),
                                                                  tulong,
                                                                  tint,
                                                                  (tptr (Ty.Tstruct _sockaddr noattr)),
                                                                  tuint]
                                                                 tlong
                                                                 cc_default))
                                            [(Expr.Etempvar _t'25 tint),
                                             (Expr.Ecast
                                               (Expr.Etempvar _t'26 (tptr tuchar))
                                               (tptr tvoid)),
                                             (Expr.Ebinop Binop.Oadd
                                               (Expr.Econst_int (Integers.Int.repr 4) tint)
                                               (Expr.Ecast
                                                 (Expr.Etempvar _t'27 tulong)
                                                 tulong) tulong),
                                             (Expr.Econst_int (Integers.Int.repr 16384) tint),
                                             (Expr.Ecast
                                               (Expr.Eaddrof
                                                 (Expr.Efield
                                                   (Expr.Ederef
                                                     (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                     (Ty.Tstruct _tftp_conn noattr))
                                                   _remote_addr
                                                   (Ty.Tstruct _Curl_sockaddr_storage noattr))
                                                 (tptr (Ty.Tstruct _Curl_sockaddr_storage noattr)))
                                               (tptr (Ty.Tstruct _sockaddr noattr))),
                                             (Expr.Etempvar _t'28 tuint)])))))
                                  (Stmt.Sset _sbytes
                                    (Expr.Etempvar _t'14 tlong)))
                                (Stmt.Ssequence
                                  (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                                      (Expr.Etempvar _sbytes tlong)
                                                      (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                      tint)
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Ssequence
                                          (Stmt.Scall (some _t'15)
                                            (Expr.Evar ___errno_location 
                                            (Ty.Tfunction [] (tptr tint)
                                              cc_default)) [])
                                          (Stmt.Ssequence
                                            (Stmt.Sset _t'24
                                              (Expr.Ederef
                                                (Expr.Etempvar _t'15 (tptr tint))
                                                tint))
                                            (Stmt.Scall (some _t'16)
                                              (Expr.Evar _Curl_strerror 
                                              (Ty.Tfunction
                                                [tint, (tptr tschar), tulong]
                                                (tptr tschar) cc_default))
                                              [(Expr.Etempvar _t'24 tint),
                                               (Expr.Evar _buffer (tarray tschar 256)),
                                               (Expr.Esizeof (tarray tschar 256) tulong)])))
                                        (Stmt.Scall none
                                          (Expr.Evar _Curl_failf (Ty.Tfunction
                                                                   [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                    (tptr tschar)]
                                                                   tvoid
                                                                   { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                          [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                           (Expr.Evar ___stringlit_12 (tarray tschar 3)),
                                           (Expr.Etempvar _t'16 (tptr tschar))]))
                                      (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 55) tint))))
                                    Stmt.Sskip)
                                  (Stmt.Ssequence
                                    (Stmt.Sset _t'23
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _k (tptr (Ty.Tstruct _SingleRequest noattr)))
                                          (Ty.Tstruct _SingleRequest noattr))
                                        _writebytecount tlong))
                                    (Stmt.Scall none
                                      (Expr.Evar _Curl_pgrsSetUploadCounter 
                                      (Ty.Tfunction
                                        [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                         tlong] tvoid cc_default))
                                      [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                       (Expr.Etempvar _t'23 tlong)])))))))
                        Stmt.Sbreak)))
                  (LStmts.LScons (some 5)
                    (Stmt.Ssequence
                      (Stmt.Sassign
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                            (Ty.Tstruct _tftp_conn noattr)) _state tint)
                        (Expr.Econst_int (Integers.Int.repr 3) tint))
                      (Stmt.Ssequence
                        (Stmt.Scall none
                          (Expr.Evar _setpacketevent (Ty.Tfunction
                                                       [(tptr (Ty.Tstruct _tftp_packet noattr)),
                                                        tushort] tvoid
                                                       cc_default))
                          [(Expr.Eaddrof
                             (Expr.Efield
                               (Expr.Ederef
                                 (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                 (Ty.Tstruct _tftp_conn noattr)) _spacket
                               (Ty.Tstruct _tftp_packet noattr))
                             (tptr (Ty.Tstruct _tftp_packet noattr))),
                           (Expr.Econst_int (Integers.Int.repr 5) tint)])
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'20
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                  (Ty.Tstruct _tftp_conn noattr)) _block
                                tushort))
                            (Stmt.Scall none
                              (Expr.Evar _setpacketblock (Ty.Tfunction
                                                           [(tptr (Ty.Tstruct _tftp_packet noattr)),
                                                            tushort] tvoid
                                                           cc_default))
                              [(Expr.Eaddrof
                                 (Expr.Efield
                                   (Expr.Ederef
                                     (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                     (Ty.Tstruct _tftp_conn noattr)) _spacket
                                   (Ty.Tstruct _tftp_packet noattr))
                                 (tptr (Ty.Tstruct _tftp_packet noattr))),
                               (Expr.Etempvar _t'20 tushort)]))
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Sset _t'17
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                    (Ty.Tstruct _tftp_conn noattr)) _sockfd
                                  tint))
                              (Stmt.Ssequence
                                (Stmt.Sset _t'18
                                  (Expr.Efield
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                        (Ty.Tstruct _tftp_conn noattr))
                                      _spacket
                                      (Ty.Tstruct _tftp_packet noattr)) _data
                                    (tptr tuchar)))
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'19
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                        (Ty.Tstruct _tftp_conn noattr))
                                      _remote_addrlen tuint))
                                  (Stmt.Scall none
                                    (Expr.Evar _sendto (Ty.Tfunction
                                                         [tint, (tptr tvoid),
                                                          tulong, tint,
                                                          (tptr (Ty.Tstruct _sockaddr noattr)),
                                                          tuint] tlong
                                                         cc_default))
                                    [(Expr.Etempvar _t'17 tint),
                                     (Expr.Ecast
                                       (Expr.Etempvar _t'18 (tptr tuchar))
                                       (tptr tvoid)),
                                     (Expr.Econst_int (Integers.Int.repr 4) tint),
                                     (Expr.Econst_int (Integers.Int.repr 16384) tint),
                                     (Expr.Ecast
                                       (Expr.Eaddrof
                                         (Expr.Efield
                                           (Expr.Ederef
                                             (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                             (Ty.Tstruct _tftp_conn noattr))
                                           _remote_addr
                                           (Ty.Tstruct _Curl_sockaddr_storage noattr))
                                         (tptr (Ty.Tstruct _Curl_sockaddr_storage noattr)))
                                       (tptr (Ty.Tstruct _sockaddr noattr))),
                                     (Expr.Etempvar _t'19 tuint)]))))
                            (Stmt.Ssequence
                              (Stmt.Sassign
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                    (Ty.Tstruct _tftp_conn noattr)) _state
                                  tint)
                                (Expr.Econst_int (Integers.Int.repr 3) tint))
                              Stmt.Sbreak)))))
                    (LStmts.LScons none
                      (Stmt.Ssequence
                        (Stmt.Scall none
                          (Expr.Evar _Curl_failf (Ty.Tfunction
                                                   [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                    (tptr tschar)] tvoid
                                                   { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                          [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                           (Expr.Evar ___stringlit_13 (tarray tschar 35)),
                           (Expr.Ecast (Expr.Etempvar _event tint) tint)])
                        Stmt.Sbreak)
                      LStmts.LSnil))))))
          (Stmt.Sreturn (some (Expr.Etempvar _result tint))))))))
}

def f_tftp_receive_packet : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_state, (tptr (Ty.Tstruct _tftp_conn noattr)))],
  fn_vars := [(_fromlen, tuint)],
  fn_temps := [(_result, tint), (_event, tushort), (_error, tushort),
               (_str, (tptr tschar)), (_strn, tulong), (_t'9, tint),
               (_t'8, tint), (_t'7, tulong), (_t'6, tushort),
               (_t'5, tushort), (_t'4, tint), (_t'3, tint), (_t'2, tushort),
               (_t'1, tlong), (_t'24, tuint), (_t'23, (tptr tuchar)),
               (_t'22, tint), (_t'21, tuint), (_t'20, tint),
               (_t'19, tushort), (_t'18, tint), (_t'17, tint),
               (_t'16, (tptr tuchar)), (_t'15, (tptr tuchar)), (_t'14, tint),
               (_t'13, tint), (_t'12, (tptr tuchar)), (_t'11, tint),
               (_t'10, tint)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Sset _result (Expr.Econst_int (Integers.Int.repr 0) tint))
  (Stmt.Ssequence
    (Stmt.Sassign (Expr.Evar _fromlen tuint)
      (Expr.Esizeof (Ty.Tstruct _Curl_sockaddr_storage noattr) tulong))
    (Stmt.Ssequence
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Sset _t'22
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                (Ty.Tstruct _tftp_conn noattr)) _sockfd tint))
          (Stmt.Ssequence
            (Stmt.Sset _t'23
              (Expr.Efield
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                    (Ty.Tstruct _tftp_conn noattr)) _rpacket
                  (Ty.Tstruct _tftp_packet noattr)) _data (tptr tuchar)))
            (Stmt.Ssequence
              (Stmt.Sset _t'24
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                    (Ty.Tstruct _tftp_conn noattr)) _blksize tuint))
              (Stmt.Scall (some _t'1)
                (Expr.Evar _recvfrom (Ty.Tfunction
                                       [tint, (tptr tvoid), tulong, tint,
                                        (tptr (Ty.Tstruct _sockaddr noattr)),
                                        (tptr tuint)] tlong cc_default))
                [(Expr.Etempvar _t'22 tint),
                 (Expr.Ecast (Expr.Etempvar _t'23 (tptr tuchar))
                   (tptr tvoid)),
                 (Expr.Ebinop Binop.Oadd
                   (Expr.Ecast (Expr.Etempvar _t'24 tuint) tulong)
                   (Expr.Econst_int (Integers.Int.repr 4) tint) tulong),
                 (Expr.Econst_int (Integers.Int.repr 0) tint),
                 (Expr.Ecast
                   (Expr.Eaddrof
                     (Expr.Efield
                       (Expr.Ederef
                         (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                         (Ty.Tstruct _tftp_conn noattr)) _remote_addr
                       (Ty.Tstruct _Curl_sockaddr_storage noattr))
                     (tptr (Ty.Tstruct _Curl_sockaddr_storage noattr)))
                   (tptr (Ty.Tstruct _sockaddr noattr))),
                 (Expr.Eaddrof (Expr.Evar _fromlen tuint) (tptr tuint))]))))
        (Stmt.Sassign
          (Expr.Efield
            (Expr.Ederef
              (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
              (Ty.Tstruct _tftp_conn noattr)) _rbytes tint)
          (Expr.Ecast (Expr.Etempvar _t'1 tlong) tint)))
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Sset _t'21 (Expr.Evar _fromlen tuint))
          (Stmt.Sassign
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                (Ty.Tstruct _tftp_conn noattr)) _remote_addrlen tuint)
            (Expr.Etempvar _t'21 tuint)))
        (Stmt.Ssequence
          (Stmt.Ssequence
            (Stmt.Sset _t'10
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                  (Ty.Tstruct _tftp_conn noattr)) _rbytes tint))
            (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                (Expr.Etempvar _t'10 tint)
                                (Expr.Econst_int (Integers.Int.repr 4) tint)
                                tint)
              (Stmt.Ssequence
                (Stmt.Scall none
                  (Expr.Evar _Curl_failf (Ty.Tfunction
                                           [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                            (tptr tschar)] tvoid
                                           { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                  [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                   (Expr.Evar ___stringlit_19 (tarray tschar 26))])
                (Stmt.Sassign
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                      (Ty.Tstruct _tftp_conn noattr)) _event tint)
                  (Expr.Econst_int (Integers.Int.repr 7) tint)))
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Scall (some _t'2)
                    (Expr.Evar _getrpacketevent (Ty.Tfunction
                                                  [(tptr (Ty.Tstruct _tftp_packet noattr))]
                                                  tushort cc_default))
                    [(Expr.Eaddrof
                       (Expr.Efield
                         (Expr.Ederef
                           (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                           (Ty.Tstruct _tftp_conn noattr)) _rpacket
                         (Ty.Tstruct _tftp_packet noattr))
                       (tptr (Ty.Tstruct _tftp_packet noattr)))])
                  (Stmt.Sset _event
                    (Expr.Ecast (Expr.Etempvar _t'2 tushort) tushort)))
                (Stmt.Ssequence
                  (Stmt.Sassign
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                        (Ty.Tstruct _tftp_conn noattr)) _event tint)
                    (Expr.Ecast (Expr.Etempvar _event tushort) tint))
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sset _t'11
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                            (Ty.Tstruct _tftp_conn noattr)) _event tint))
                      (Stmt.Sswitch (Expr.Etempvar _t'11 tint)
                        (LStmts.LScons (some 3)
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Sset _t'20
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                      (Ty.Tstruct _Curl_easy noattr)) _state
                                    (Ty.Tstruct _UrlState noattr)) _upload
                                  tint))
                              (Stmt.Sifthenelse (Expr.Etempvar _t'20 tint)
                                (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 71) tint)))
                                Stmt.Sskip))
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'18
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                        (Ty.Tstruct _tftp_conn noattr))
                                      _rbytes tint))
                                  (Stmt.Sifthenelse (Expr.Ebinop Binop.Ogt
                                                      (Expr.Etempvar _t'18 tint)
                                                      (Expr.Econst_int (Integers.Int.repr 4) tint)
                                                      tint)
                                    (Stmt.Ssequence
                                      (Stmt.Scall (some _t'5)
                                        (Expr.Evar _getrpacketblock (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _tftp_packet noattr))]
                                                                    tushort
                                                                    cc_default))
                                        [(Expr.Eaddrof
                                           (Expr.Efield
                                             (Expr.Ederef
                                               (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                               (Ty.Tstruct _tftp_conn noattr))
                                             _rpacket
                                             (Ty.Tstruct _tftp_packet noattr))
                                           (tptr (Ty.Tstruct _tftp_packet noattr)))])
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'19
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                              (Ty.Tstruct _tftp_conn noattr))
                                            _block tushort))
                                        (Stmt.Sset _t'4
                                          (Expr.Ecast
                                            (Expr.Ebinop Binop.Oeq
                                              (Expr.Ebinop Binop.Oand
                                                (Expr.Ebinop Binop.Oadd
                                                  (Expr.Etempvar _t'19 tushort)
                                                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                  tint)
                                                (Expr.Econst_int (Integers.Int.repr 65535) tint)
                                                tint)
                                              (Expr.Etempvar _t'5 tushort)
                                              tint) tbool))))
                                    (Stmt.Sset _t'4
                                      (Expr.Econst_int (Integers.Int.repr 0) tint))))
                                (Stmt.Sifthenelse (Expr.Etempvar _t'4 tint)
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'16
                                          (Expr.Efield
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                (Ty.Tstruct _tftp_conn noattr))
                                              _rpacket
                                              (Ty.Tstruct _tftp_packet noattr))
                                            _data (tptr tuchar)))
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'17
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                                (Ty.Tstruct _tftp_conn noattr))
                                              _rbytes tint))
                                          (Stmt.Scall (some _t'3)
                                            (Expr.Evar _Curl_client_write 
                                            (Ty.Tfunction
                                              [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                               tint, (tptr tschar), tulong]
                                              tint cc_default))
                                            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                             (Expr.Ebinop Binop.Oshl
                                               (Expr.Econst_int (Integers.Int.repr 1) tint)
                                               (Expr.Econst_int (Integers.Int.repr 0) tint)
                                               tint),
                                             (Expr.Ebinop Binop.Oadd
                                               (Expr.Ecast
                                                 (Expr.Etempvar _t'16 (tptr tuchar))
                                                 (tptr tschar))
                                               (Expr.Econst_int (Integers.Int.repr 4) tint)
                                               (tptr tschar)),
                                             (Expr.Ebinop Binop.Osub
                                               (Expr.Etempvar _t'17 tint)
                                               (Expr.Econst_int (Integers.Int.repr 4) tint)
                                               tint)])))
                                      (Stmt.Sset _result
                                        (Expr.Etempvar _t'3 tint)))
                                    (Stmt.Sifthenelse (Expr.Etempvar _result tint)
                                      (Stmt.Ssequence
                                        (Stmt.Scall none
                                          (Expr.Evar _tftp_state_machine 
                                          (Ty.Tfunction
                                            [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                             tint] tint cc_default))
                                          [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                                           (Expr.Econst_int (Integers.Int.repr 5) tint)])
                                        (Stmt.Sreturn (some (Expr.Etempvar _result tint))))
                                      Stmt.Sskip))
                                  Stmt.Sskip))
                              Stmt.Sbreak))
                          (LStmts.LScons (some 5)
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Scall (some _t'6)
                                  (Expr.Evar _getrpacketblock (Ty.Tfunction
                                                                [(tptr (Ty.Tstruct _tftp_packet noattr))]
                                                                tushort
                                                                cc_default))
                                  [(Expr.Eaddrof
                                     (Expr.Efield
                                       (Expr.Ederef
                                         (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                         (Ty.Tstruct _tftp_conn noattr))
                                       _rpacket
                                       (Ty.Tstruct _tftp_packet noattr))
                                     (tptr (Ty.Tstruct _tftp_packet noattr)))])
                                (Stmt.Sset _error
                                  (Expr.Ecast (Expr.Etempvar _t'6 tushort)
                                    tushort)))
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'15
                                    (Expr.Efield
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                          (Ty.Tstruct _tftp_conn noattr))
                                        _rpacket
                                        (Ty.Tstruct _tftp_packet noattr))
                                      _data (tptr tuchar)))
                                  (Stmt.Sset _str
                                    (Expr.Ebinop Binop.Oadd
                                      (Expr.Ecast
                                        (Expr.Etempvar _t'15 (tptr tuchar))
                                        (tptr tschar))
                                      (Expr.Econst_int (Integers.Int.repr 4) tint)
                                      (tptr tschar))))
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Sset _t'14
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                          (Ty.Tstruct _tftp_conn noattr))
                                        _rbytes tint))
                                    (Stmt.Sset _strn
                                      (Expr.Ecast
                                        (Expr.Ebinop Binop.Osub
                                          (Expr.Etempvar _t'14 tint)
                                          (Expr.Econst_int (Integers.Int.repr 4) tint)
                                          tint) tulong)))
                                  (Stmt.Ssequence
                                    (Stmt.Sassign
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                          (Ty.Tstruct _tftp_conn noattr))
                                        _error tint)
                                      (Expr.Ecast
                                        (Expr.Etempvar _error tushort) tint))
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Scall (some _t'7)
                                          (Expr.Evar _tftp_strnlen (Ty.Tfunction
                                                                    [(tptr tschar),
                                                                    tulong]
                                                                    tulong
                                                                    cc_default))
                                          [(Expr.Etempvar _str (tptr tschar)),
                                           (Expr.Etempvar _strn tulong)])
                                        (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                                            (Expr.Etempvar _t'7 tulong)
                                                            (Expr.Etempvar _strn tulong)
                                                            tint)
                                          (Stmt.Scall none
                                            (Expr.Evar _Curl_infof (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                    (tptr tschar)]
                                                                    tvoid
                                                                    { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                             (Expr.Evar ___stringlit_18 (tarray tschar 15)),
                                             (Expr.Etempvar _str (tptr tschar))])
                                          Stmt.Sskip))
                                      Stmt.Sbreak)))))
                            (LStmts.LScons (some 4)
                              Stmt.Sbreak
                              (LStmts.LScons (some 6)
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Sset _t'12
                                        (Expr.Efield
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                              (Ty.Tstruct _tftp_conn noattr))
                                            _rpacket
                                            (Ty.Tstruct _tftp_packet noattr))
                                          _data (tptr tuchar)))
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'13
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
                                              (Ty.Tstruct _tftp_conn noattr))
                                            _rbytes tint))
                                        (Stmt.Scall (some _t'8)
                                          (Expr.Evar _tftp_parse_option_ack 
                                          (Ty.Tfunction
                                            [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                             (tptr tschar), tint] tint
                                            cc_default))
                                          [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                                           (Expr.Ebinop Binop.Oadd
                                             (Expr.Ecast
                                               (Expr.Etempvar _t'12 (tptr tuchar))
                                               (tptr tschar))
                                             (Expr.Econst_int (Integers.Int.repr 2) tint)
                                             (tptr tschar)),
                                           (Expr.Ebinop Binop.Osub
                                             (Expr.Etempvar _t'13 tint)
                                             (Expr.Econst_int (Integers.Int.repr 2) tint)
                                             tint)])))
                                    (Stmt.Sset _result
                                      (Expr.Etempvar _t'8 tint)))
                                  (Stmt.Ssequence
                                    (Stmt.Sifthenelse (Expr.Etempvar _result tint)
                                      (Stmt.Sreturn (some (Expr.Etempvar _result tint)))
                                      Stmt.Sskip)
                                    Stmt.Sbreak))
                                (LStmts.LScons (some 1)
                                  Stmt.Sskip
                                  (LStmts.LScons (some 2)
                                    Stmt.Sskip
                                    (LStmts.LScons none
                                      (Stmt.Ssequence
                                        (Stmt.Scall none
                                          (Expr.Evar _Curl_failf (Ty.Tfunction
                                                                   [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                    (tptr tschar)]
                                                                   tvoid
                                                                   { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                          [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                           (Expr.Evar ___stringlit_12 (tarray tschar 3)),
                                           (Expr.Evar ___stringlit_17 (tarray tschar 34))])
                                        Stmt.Sbreak)
                                      LStmts.LSnil)))))))))
                    (Stmt.Ssequence
                      (Stmt.Scall (some _t'9)
                        (Expr.Evar _Curl_pgrsUpdate (Ty.Tfunction
                                                      [(tptr (Ty.Tstruct _Curl_easy noattr))]
                                                      tint cc_default))
                        [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))])
                      (Stmt.Sifthenelse (Expr.Etempvar _t'9 tint)
                        (Stmt.Ssequence
                          (Stmt.Scall none
                            (Expr.Evar _tftp_state_machine (Ty.Tfunction
                                                             [(tptr (Ty.Tstruct _tftp_conn noattr)),
                                                              tint] tint
                                                             cc_default))
                            [(Expr.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr))),
                             (Expr.Econst_int (Integers.Int.repr 5) tint)])
                          (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 42) tint))))
                        Stmt.Sskip)))))))
          (Stmt.Sreturn (some (Expr.Etempvar _result tint))))))))
}

def v_case3bp_keep_ev : GlobVar Ty := {
  gvar_info := (tarray (tptr (Ty.Tfunction
                               [(tptr (Ty.Tstruct _tftp_conn noattr)), tint]
                               tint cc_default)) 2),
  gvar_init := [(InitData.Init_addrof _tftp_tx (Integers.Ptrofs.repr 0)),
                (InitData.Init_addrof _tftp_send_first (Integers.Ptrofs.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v_case3bp_keep_rp : GlobVar Ty := {
  gvar_info := (tptr (Ty.Tfunction
                       [(tptr (Ty.Tstruct _Curl_easy noattr)),
                        (tptr (Ty.Tstruct _tftp_conn noattr))] tint
                       cc_default)),
  gvar_init := [(InitData.Init_addrof _tftp_receive_packet (Integers.Ptrofs.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def composites : List CompositeDef :=
[(CompositeDef.Composite _sockaddr SU.Struct
   [(Member.Member_plain _sa_family tushort),
    (Member.Member_plain _sa_data (tarray tschar 14))]
   noattr),
 (CompositeDef.Composite __139 SU.Union
   [(Member.Member_plain _sa_stor (tarray tlong 16))]
   noattr),
 (CompositeDef.Composite _Curl_sockaddr_storage SU.Struct
   [(Member.Member_plain _buffer (Ty.Tunion __139 noattr))]
   noattr),
 (CompositeDef.Composite _Curl_sockaddr_ex SU.Struct
   [(Member.Member_plain _addrlen tuint),
    (Member.Member_plain _curl_sa_addr (Ty.Tstruct _sockaddr noattr))]
   noattr),
 (CompositeDef.Composite _tftp_packet SU.Struct
   [(Member.Member_plain _data (tptr tuchar))]
   noattr),
 (CompositeDef.Composite _tftp_conn SU.Struct
   [(Member.Member_plain _state tint), (Member.Member_plain _error tint),
    (Member.Member_plain _event tint),
    (Member.Member_plain _data (tptr (Ty.Tstruct _Curl_easy noattr))),
    (Member.Member_plain _sockfd tint), (Member.Member_plain _retries tint),
    (Member.Member_plain _retry_time tint),
    (Member.Member_plain _retry_max tint),
    (Member.Member_plain _rx_time tlong),
    (Member.Member_plain _remote_addr
      (Ty.Tstruct _Curl_sockaddr_storage noattr)),
    (Member.Member_plain _remote_addrlen tuint),
    (Member.Member_plain _rbytes tint), (Member.Member_plain _sbytes tulong),
    (Member.Member_plain _blksize tuint),
    (Member.Member_plain _requested_blksize tuint),
    (Member.Member_plain _block tushort),
    (Member.Member_plain _rpacket (Ty.Tstruct _tftp_packet noattr)),
    (Member.Member_plain _spacket (Ty.Tstruct _tftp_packet noattr))]
   noattr),
 (CompositeDef.Composite _connectdata SU.Struct
   [(Member.Member_plain _remote_addr
      (tptr (Ty.Tstruct _Curl_sockaddr_ex noattr)))]
   noattr),
 (CompositeDef.Composite _SingleRequest SU.Struct
   [(Member.Member_plain _writebytecount tlong)]
   noattr),
 (CompositeDef.Composite _urlpieces SU.Struct
   [(Member.Member_plain _path (tptr tschar))]
   noattr),
 (CompositeDef.Composite _UrlState SU.Struct
   [(Member.Member_plain _infilesize tlong),
    (Member.Member_plain _up (Ty.Tstruct _urlpieces noattr)),
    (Member.Member_bitfield _prefer_ascii IntSize.I32 Signedness.Unsigned
      noattr 1 false),
    (Member.Member_bitfield _upload IntSize.I32 Signedness.Unsigned noattr 1
      false)]
   noattr),
 (CompositeDef.Composite _UserDefined SU.Struct
   [(Member.Member_bitfield _tftp_no_options IntSize.I32 Signedness.Unsigned
      noattr 1 false)]
   noattr),
 (CompositeDef.Composite _Curl_easy SU.Struct
   [(Member.Member_plain _conn (tptr (Ty.Tstruct _connectdata noattr))),
    (Member.Member_plain _req (Ty.Tstruct _SingleRequest noattr)),
    (Member.Member_plain _set (Ty.Tstruct _UserDefined noattr)),
    (Member.Member_plain _state (Ty.Tstruct _UrlState noattr))]
   noattr)]

def global_definitions : List (Ident × GlobDef FunDef Ty) :=
[(___compcert_va_int32,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_va_int32"
                                   (mksignature [XType.Xptr] XType.Xint
                                     cc_default)) [(tptr tvoid)] tuint
     cc_default)),
 (___compcert_va_int64,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_va_int64"
                                   (mksignature [XType.Xptr] XType.Xlong
                                     cc_default)) [(tptr tvoid)] tulong
     cc_default)),
 (___compcert_va_float64,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_va_float64"
                                   (mksignature [XType.Xptr] XType.Xfloat
                                     cc_default)) [(tptr tvoid)] tdouble
     cc_default)),
 (___compcert_va_composite,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_va_composite"
                                   (mksignature [XType.Xptr, XType.Xlong]
                                     XType.Xptr cc_default))
     [(tptr tvoid), tulong] (tptr tvoid) cc_default)),
 (___compcert_i64_dtos,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_dtos"
                                   (mksignature [XType.Xfloat] XType.Xlong
                                     cc_default)) [tdouble] tlong
     cc_default)),
 (___compcert_i64_dtou,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_dtou"
                                   (mksignature [XType.Xfloat] XType.Xlong
                                     cc_default)) [tdouble] tulong
     cc_default)),
 (___compcert_i64_stod,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_stod"
                                   (mksignature [XType.Xlong] XType.Xfloat
                                     cc_default)) [tlong] tdouble
     cc_default)),
 (___compcert_i64_utod,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_utod"
                                   (mksignature [XType.Xlong] XType.Xfloat
                                     cc_default)) [tulong] tdouble
     cc_default)),
 (___compcert_i64_stof,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_stof"
                                   (mksignature [XType.Xlong] XType.Xsingle
                                     cc_default)) [tlong] tfloat cc_default)),
 (___compcert_i64_utof,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_utof"
                                   (mksignature [XType.Xlong] XType.Xsingle
                                     cc_default)) [tulong] tfloat
     cc_default)),
 (___compcert_i64_sdiv,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_sdiv"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default)) [tlong, tlong]
     tlong cc_default)),
 (___compcert_i64_udiv,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_udiv"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default))
     [tulong, tulong] tulong cc_default)),
 (___compcert_i64_smod,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_smod"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default)) [tlong, tlong]
     tlong cc_default)),
 (___compcert_i64_umod,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_umod"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default))
     [tulong, tulong] tulong cc_default)),
 (___compcert_i64_shl,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_shl"
                                   (mksignature [XType.Xlong, XType.Xint]
                                     XType.Xlong cc_default)) [tlong, tint]
     tlong cc_default)),
 (___compcert_i64_shr,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_shr"
                                   (mksignature [XType.Xlong, XType.Xint]
                                     XType.Xlong cc_default)) [tulong, tint]
     tulong cc_default)),
 (___compcert_i64_sar,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_sar"
                                   (mksignature [XType.Xlong, XType.Xint]
                                     XType.Xlong cc_default)) [tlong, tint]
     tlong cc_default)),
 (___compcert_i64_smulh,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_smulh"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default)) [tlong, tlong]
     tlong cc_default)),
 (___compcert_i64_umulh,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_umulh"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default))
     [tulong, tulong] tulong cc_default)),
 (___stringlit_12, GlobDef.Gvar v___stringlit_12),
 (___stringlit_9, GlobDef.Gvar v___stringlit_9),
 (___stringlit_14, GlobDef.Gvar v___stringlit_14),
 (___stringlit_15, GlobDef.Gvar v___stringlit_15),
 (___stringlit_19, GlobDef.Gvar v___stringlit_19),
 (___stringlit_10, GlobDef.Gvar v___stringlit_10),
 (___stringlit_5, GlobDef.Gvar v___stringlit_5),
 (___stringlit_8, GlobDef.Gvar v___stringlit_8),
 (___stringlit_18, GlobDef.Gvar v___stringlit_18),
 (___stringlit_13, GlobDef.Gvar v___stringlit_13),
 (___stringlit_6, GlobDef.Gvar v___stringlit_6),
 (___stringlit_7, GlobDef.Gvar v___stringlit_7),
 (___stringlit_3, GlobDef.Gvar v___stringlit_3),
 (___stringlit_4, GlobDef.Gvar v___stringlit_4),
 (___stringlit_11, GlobDef.Gvar v___stringlit_11),
 (___stringlit_1, GlobDef.Gvar v___stringlit_1),
 (___stringlit_17, GlobDef.Gvar v___stringlit_17),
 (___stringlit_2, GlobDef.Gvar v___stringlit_2),
 (___stringlit_16, GlobDef.Gvar v___stringlit_16),
 (___builtin_bswap64,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_bswap64"
                                   (mksignature [XType.Xlong] XType.Xlong
                                     cc_default)) [tulong] tulong
     cc_default)),
 (___builtin_bswap,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_bswap"
                                   (mksignature [XType.Xint] XType.Xint
                                     cc_default)) [tuint] tuint cc_default)),
 (___builtin_bswap32,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_bswap32"
                                   (mksignature [XType.Xint] XType.Xint
                                     cc_default)) [tuint] tuint cc_default)),
 (___builtin_bswap16,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_bswap16"
                                   (mksignature [XType.Xint16unsigned]
                                     XType.Xint16unsigned cc_default))
     [tushort] tushort cc_default)),
 (___builtin_clz,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_clz"
                                   (mksignature [XType.Xint] XType.Xint
                                     cc_default)) [tuint] tint cc_default)),
 (___builtin_clzl,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_clzl"
                                   (mksignature [XType.Xlong] XType.Xint
                                     cc_default)) [tulong] tint cc_default)),
 (___builtin_clzll,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_clzll"
                                   (mksignature [XType.Xlong] XType.Xint
                                     cc_default)) [tulong] tint cc_default)),
 (___builtin_ctz,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_ctz"
                                   (mksignature [XType.Xint] XType.Xint
                                     cc_default)) [tuint] tint cc_default)),
 (___builtin_ctzl,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_ctzl"
                                   (mksignature [XType.Xlong] XType.Xint
                                     cc_default)) [tulong] tint cc_default)),
 (___builtin_ctzll,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_ctzll"
                                   (mksignature [XType.Xlong] XType.Xint
                                     cc_default)) [tulong] tint cc_default)),
 (___builtin_fabs,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fabs"
                                   (mksignature [XType.Xfloat] XType.Xfloat
                                     cc_default)) [tdouble] tdouble
     cc_default)),
 (___builtin_fabsf,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fabsf"
                                   (mksignature [XType.Xsingle] XType.Xsingle
                                     cc_default)) [tfloat] tfloat
     cc_default)),
 (___builtin_fsqrt,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fsqrt"
                                   (mksignature [XType.Xfloat] XType.Xfloat
                                     cc_default)) [tdouble] tdouble
     cc_default)),
 (___builtin_sqrt,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_sqrt"
                                   (mksignature [XType.Xfloat] XType.Xfloat
                                     cc_default)) [tdouble] tdouble
     cc_default)),
 (___builtin_memcpy_aligned,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_memcpy_aligned"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xlong,
                                      XType.Xlong] XType.Xvoid cc_default))
     [(tptr tvoid), (tptr tvoid), tulong, tulong] tvoid cc_default)),
 (___builtin_sel,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_sel"
                                   (mksignature [XType.Xbool] XType.Xvoid
                                     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false }))
     [tbool] tvoid
     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false })),
 (___builtin_annot,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_annot"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false }))
     [(tptr tschar)] tvoid
     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false })),
 (___builtin_annot_intval,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_annot_intval"
                                   (mksignature [XType.Xptr, XType.Xint]
                                     XType.Xint cc_default))
     [(tptr tschar), tint] tint cc_default)),
 (___builtin_membar,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_membar"
                                   (mksignature [] XType.Xvoid cc_default))
     [] tvoid cc_default)),
 (___builtin_va_start,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_va_start"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default)) [(tptr tvoid)] tvoid
     cc_default)),
 (___builtin_va_arg,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_va_arg"
                                   (mksignature [XType.Xptr, XType.Xint]
                                     XType.Xvoid cc_default))
     [(tptr tvoid), tuint] tvoid cc_default)),
 (___builtin_va_copy,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_va_copy"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xvoid cc_default))
     [(tptr tvoid), (tptr tvoid)] tvoid cc_default)),
 (___builtin_va_end,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_va_end"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default)) [(tptr tvoid)] tvoid
     cc_default)),
 (___builtin_unreachable,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_unreachable"
                                   (mksignature [] XType.Xvoid cc_default))
     [] tvoid cc_default)),
 (___builtin_expect,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_expect"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default)) [tlong, tlong]
     tlong cc_default)),
 (___builtin_cls,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_cls"
                                   (mksignature [XType.Xint] XType.Xint
                                     cc_default)) [tint] tint cc_default)),
 (___builtin_clsl,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_clsl"
                                   (mksignature [XType.Xlong] XType.Xint
                                     cc_default)) [tlong] tint cc_default)),
 (___builtin_clsll,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_clsll"
                                   (mksignature [XType.Xlong] XType.Xint
                                     cc_default)) [tlong] tint cc_default)),
 (___builtin_fmadd,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fmadd"
                                   (mksignature
                                     [XType.Xfloat, XType.Xfloat,
                                      XType.Xfloat] XType.Xfloat cc_default))
     [tdouble, tdouble, tdouble] tdouble cc_default)),
 (___builtin_fmsub,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fmsub"
                                   (mksignature
                                     [XType.Xfloat, XType.Xfloat,
                                      XType.Xfloat] XType.Xfloat cc_default))
     [tdouble, tdouble, tdouble] tdouble cc_default)),
 (___builtin_fnmadd,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fnmadd"
                                   (mksignature
                                     [XType.Xfloat, XType.Xfloat,
                                      XType.Xfloat] XType.Xfloat cc_default))
     [tdouble, tdouble, tdouble] tdouble cc_default)),
 (___builtin_fnmsub,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fnmsub"
                                   (mksignature
                                     [XType.Xfloat, XType.Xfloat,
                                      XType.Xfloat] XType.Xfloat cc_default))
     [tdouble, tdouble, tdouble] tdouble cc_default)),
 (___builtin_fmax,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fmax"
                                   (mksignature [XType.Xfloat, XType.Xfloat]
                                     XType.Xfloat cc_default))
     [tdouble, tdouble] tdouble cc_default)),
 (___builtin_fmin,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fmin"
                                   (mksignature [XType.Xfloat, XType.Xfloat]
                                     XType.Xfloat cc_default))
     [tdouble, tdouble] tdouble cc_default)),
 (___builtin_debug,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "__builtin_debug"
                                   (mksignature [XType.Xint] XType.Xvoid
                                     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false }))
     [tint] tvoid
     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false })),
 (___errno_location,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "__errno_location"
                                   (mksignature [] XType.Xptr cc_default)) []
     (tptr tint) cc_default)),
 (_sendto,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "sendto"
                                   (mksignature
                                     [XType.Xint, XType.Xptr, XType.Xlong,
                                      XType.Xint, XType.Xptr, XType.Xint]
                                     XType.Xlong cc_default))
     [tint, (tptr tvoid), tulong, tint, (tptr (Ty.Tstruct _sockaddr noattr)),
      tuint] tlong cc_default)),
 (_recvfrom,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "recvfrom"
                                   (mksignature
                                     [XType.Xint, XType.Xptr, XType.Xlong,
                                      XType.Xint, XType.Xptr, XType.Xptr]
                                     XType.Xlong cc_default))
     [tint, (tptr tvoid), tulong, tint, (tptr (Ty.Tstruct _sockaddr noattr)),
      (tptr tuint)] tlong cc_default)),
 (_strlen,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "strlen"
                                   (mksignature [XType.Xptr] XType.Xlong
                                     cc_default)) [(tptr tschar)] tulong
     cc_default)),
 (_time,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "time"
                                   (mksignature [XType.Xptr] XType.Xlong
                                     cc_default)) [(tptr tlong)] tlong
     cc_default)),
 (_Curl_failf,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_failf"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xvoid
                                     { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar)] tvoid
     { cc_vararg := (some 2), cc_unproto := false, cc_structret := false })),
 (_Curl_infof,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_infof"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xvoid
                                     { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar)] tvoid
     { cc_vararg := (some 2), cc_unproto := false, cc_structret := false })),
 (_curl_msnprintf,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "curl_msnprintf"
                                   (mksignature
                                     [XType.Xptr, XType.Xlong, XType.Xptr]
                                     XType.Xint
                                     { cc_vararg := (some 3), cc_unproto := false, cc_structret := false }))
     [(tptr tschar), tulong, (tptr tschar)] tint
     { cc_vararg := (some 3), cc_unproto := false, cc_structret := false })),
 (_Curl_strerror,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_strerror"
                                   (mksignature
                                     [XType.Xint, XType.Xptr, XType.Xlong]
                                     XType.Xptr cc_default))
     [tint, (tptr tschar), tulong] (tptr tschar) cc_default)),
 (_Curl_cfree,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_cfree"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default)) [(tptr tvoid)] tvoid
     cc_default)),
 (_Curl_client_write,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_client_write"
                                   (mksignature
                                     [XType.Xptr, XType.Xint, XType.Xptr,
                                      XType.Xlong] XType.Xint cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), tint, (tptr tschar), tulong]
     tint cc_default)),
 (_Curl_client_read,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_client_read"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xlong,
                                      XType.Xptr, XType.Xptr] XType.Xint
                                     cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar), tulong,
      (tptr tulong), (tptr tbool)] tint cc_default)),
 (_Curl_pgrsUpdate,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_pgrsUpdate"
                                   (mksignature [XType.Xptr] XType.Xint
                                     cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr))] tint cc_default)),
 (_Curl_pgrsSetUploadCounter,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_pgrsSetUploadCounter"
                                   (mksignature [XType.Xptr, XType.Xlong]
                                     XType.Xvoid cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), tlong] tvoid cc_default)),
 (_Curl_pgrsSetUploadSize,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_pgrsSetUploadSize"
                                   (mksignature [XType.Xptr, XType.Xlong]
                                     XType.Xvoid cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), tlong] tvoid cc_default)),
 (_Curl_urldecode,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_urldecode"
                                   (mksignature
                                     [XType.Xptr, XType.Xlong, XType.Xptr,
                                      XType.Xptr, XType.Xint] XType.Xint
                                     cc_default))
     [(tptr tschar), tulong, (tptr (tptr tschar)), (tptr tulong), tint] tint
     cc_default)),
 (_setpacketevent,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "setpacketevent"
                                   (mksignature
                                     [XType.Xptr, XType.Xint16unsigned]
                                     XType.Xvoid cc_default))
     [(tptr (Ty.Tstruct _tftp_packet noattr)), tushort] tvoid cc_default)),
 (_setpacketblock,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "setpacketblock"
                                   (mksignature
                                     [XType.Xptr, XType.Xint16unsigned]
                                     XType.Xvoid cc_default))
     [(tptr (Ty.Tstruct _tftp_packet noattr)), tushort] tvoid cc_default)),
 (_getrpacketevent,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "getrpacketevent"
                                   (mksignature [XType.Xptr]
                                     XType.Xint16unsigned cc_default))
     [(tptr (Ty.Tstruct _tftp_packet noattr))] tushort cc_default)),
 (_getrpacketblock,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "getrpacketblock"
                                   (mksignature [XType.Xptr]
                                     XType.Xint16unsigned cc_default))
     [(tptr (Ty.Tstruct _tftp_packet noattr))] tushort cc_default)),
 (_tftp_strnlen,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "tftp_strnlen"
                                   (mksignature [XType.Xptr, XType.Xlong]
                                     XType.Xlong cc_default))
     [(tptr tschar), tulong] tulong cc_default)),
 (_tftp_parse_option_ack,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "tftp_parse_option_ack"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xint]
                                     XType.Xint cc_default))
     [(tptr (Ty.Tstruct _tftp_conn noattr)), (tptr tschar), tint] tint
     cc_default)),
 (_tftp_option_add,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "tftp_option_add"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xptr,
                                      XType.Xptr] XType.Xint cc_default))
     [(tptr (Ty.Tstruct _tftp_conn noattr)), (tptr tulong), (tptr tschar),
      (tptr tschar)] tint cc_default)),
 (_tftp_connect_for_tx,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "tftp_connect_for_tx"
                                   (mksignature [XType.Xptr, XType.Xint]
                                     XType.Xint cc_default))
     [(tptr (Ty.Tstruct _tftp_conn noattr)), tint] tint cc_default)),
 (_tftp_connect_for_rx,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "tftp_connect_for_rx"
                                   (mksignature [XType.Xptr, XType.Xint]
                                     XType.Xint cc_default))
     [(tptr (Ty.Tstruct _tftp_conn noattr)), tint] tint cc_default)),
 (_tftp_state_machine,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "tftp_state_machine"
                                   (mksignature [XType.Xptr, XType.Xint]
                                     XType.Xint cc_default))
     [(tptr (Ty.Tstruct _tftp_conn noattr)), tint] tint cc_default)),
 (_tftp_send_first, GlobDef.Gfun (FunDef.Internal f_tftp_send_first)),
 (_tftp_tx, GlobDef.Gfun (FunDef.Internal f_tftp_tx)),
 (_tftp_receive_packet, GlobDef.Gfun (FunDef.Internal f_tftp_receive_packet)),
 (_case3bp_keep_ev, GlobDef.Gvar v_case3bp_keep_ev),
 (_case3bp_keep_rp, GlobDef.Gvar v_case3bp_keep_rp)]

def public_idents : List Ident :=
[_case3bp_keep_rp, _case3bp_keep_ev, _tftp_state_machine,
 _tftp_connect_for_rx, _tftp_connect_for_tx, _tftp_option_add,
 _tftp_parse_option_ack, _tftp_strnlen, _getrpacketblock, _getrpacketevent,
 _setpacketblock, _setpacketevent, _Curl_urldecode, _Curl_pgrsSetUploadSize,
 _Curl_pgrsSetUploadCounter, _Curl_pgrsUpdate, _Curl_client_read,
 _Curl_client_write, _Curl_cfree, _Curl_strerror, _curl_msnprintf,
 _Curl_infof, _Curl_failf, _time, _strlen, _recvfrom, _sendto,
 ___errno_location, ___builtin_debug, ___builtin_fmin, ___builtin_fmax,
 ___builtin_fnmsub, ___builtin_fnmadd, ___builtin_fmsub, ___builtin_fmadd,
 ___builtin_clsll, ___builtin_clsl, ___builtin_cls, ___builtin_expect,
 ___builtin_unreachable, ___builtin_va_end, ___builtin_va_copy,
 ___builtin_va_arg, ___builtin_va_start, ___builtin_membar,
 ___builtin_annot_intval, ___builtin_annot, ___builtin_sel,
 ___builtin_memcpy_aligned, ___builtin_sqrt, ___builtin_fsqrt,
 ___builtin_fabsf, ___builtin_fabs, ___builtin_ctzll, ___builtin_ctzl,
 ___builtin_ctz, ___builtin_clzll, ___builtin_clzl, ___builtin_clz,
 ___builtin_bswap16, ___builtin_bswap32, ___builtin_bswap,
 ___builtin_bswap64, ___compcert_i64_umulh, ___compcert_i64_smulh,
 ___compcert_i64_sar, ___compcert_i64_shr, ___compcert_i64_shl,
 ___compcert_i64_umod, ___compcert_i64_smod, ___compcert_i64_udiv,
 ___compcert_i64_sdiv, ___compcert_i64_utof, ___compcert_i64_stof,
 ___compcert_i64_utod, ___compcert_i64_stod, ___compcert_i64_dtou,
 ___compcert_i64_dtos, ___compcert_va_composite, ___compcert_va_float64,
 ___compcert_va_int64, ___compcert_va_int32]

def prog : Program :=
  mkprogram composites global_definitions public_idents _main

end Case3bp_after

