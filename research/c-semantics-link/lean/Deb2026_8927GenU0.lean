import Clightdefs
open CC

namespace Deb2026_8927_u0

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
  def source_file : String := "deb2026_8927_u0.c"
  def normalized : Bool := true
end Info

def _ConnectBits : Ident := identOfString "ConnectBits"
def _Curl_check_noproxy : Ident := identOfString "Curl_check_noproxy"
def _Curl_easy : Ident := identOfString "Curl_easy"
def _Curl_failf : Ident := identOfString "Curl_failf"
def _Curl_infof : Ident := identOfString "Curl_infof"
def _Curl_peer : Ident := identOfString "Curl_peer"
def _Curl_scheme : Ident := identOfString "Curl_scheme"
def _Curl_scheme_http : Ident := identOfString "Curl_scheme_http"
def _UrlState : Ident := identOfString "UrlState"
def _UserDefined : Ident := identOfString "UserDefined"
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
def ___stringlit_1 : Ident := identOfString "__stringlit_1"
def ___stringlit_2 : Ident := identOfString "__stringlit_2"
def ___stringlit_3 : Ident := identOfString "__stringlit_3"
def ___stringlit_4 : Ident := identOfString "__stringlit_4"
def ___stringlit_5 : Ident := identOfString "__stringlit_5"
def _bits : Ident := identOfString "bits"
def _conn : Ident := identOfString "conn"
def _connectdata : Ident := identOfString "connectdata"
def _curl_getenv : Ident := identOfString "curl_getenv"
def _curlx_free : Ident := identOfString "curlx_free"
def _curlx_strdup : Ident := identOfString "curlx_strdup"
def _data : Ident := identOfString "data"
def _deb_keep : Ident := identOfString "deb_keep"
def _digest : Ident := identOfString "digest"
def _digestdata : Ident := identOfString "digestdata"
def _flags : Ident := identOfString "flags"
def _hostname : Ident := identOfString "hostname"
def _http_proxy : Ident := identOfString "http_proxy"
def _httpproxy : Ident := identOfString "httpproxy"
def _main : Ident := identOfString "main"
def _memset : Ident := identOfString "memset"
def _no_proxy : Ident := identOfString "no_proxy"
def _nonce : Ident := identOfString "nonce"
def _origin : Ident := identOfString "origin"
def _out : Ident := identOfString "out"
def _p : Ident := identOfString "p"
def _parse_proxy : Ident := identOfString "parse_proxy"
def _peer : Ident := identOfString "peer"
def _pre_proxy : Ident := identOfString "pre_proxy"
def _protocol : Ident := identOfString "protocol"
def _proxy : Ident := identOfString "proxy"
def _proxy_info : Ident := identOfString "proxy_info"
def _proxydigest : Ident := identOfString "proxydigest"
def _proxytype : Ident := identOfString "proxytype"
def _result : Ident := identOfString "result"
def _scheme : Ident := identOfString "scheme"
def _set : Ident := identOfString "set"
def _socks_proxy : Ident := identOfString "socks_proxy"
def _socksproxy : Ident := identOfString "socksproxy"
def _state : Ident := identOfString "state"
def _str : Ident := identOfString "str"
def _tunnel_proxy : Ident := identOfString "tunnel_proxy"
def _url_detect_proxy : Ident := identOfString "url_detect_proxy"
def _url_set_conn_proxies : Ident := identOfString "url_set_conn_proxies"
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
def _t'5 : Ident := (Positive.ofNat 132)
def _t'6 : Ident := (Positive.ofNat 133)
def _t'7 : Ident := (Positive.ofNat 134)
def _t'8 : Ident := (Positive.ofNat 135)
def _t'9 : Ident := (Positive.ofNat 136)

def v___stringlit_1 : GlobVar Ty := {
  gvar_info := (tarray tschar 16),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 109)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 109)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 121)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 104)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 103)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_3 : GlobVar Ty := {
  gvar_info := (tarray tschar 9),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 78)),
                (InitData.Init_int8 (Integers.Int.repr 79)),
                (InitData.Init_int8 (Integers.Int.repr 95)),
                (InitData.Init_int8 (Integers.Int.repr 80)),
                (InitData.Init_int8 (Integers.Int.repr 82)),
                (InitData.Init_int8 (Integers.Int.repr 79)),
                (InitData.Init_int8 (Integers.Int.repr 88)),
                (InitData.Init_int8 (Integers.Int.repr 89)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_5 : GlobVar Ty := {
  gvar_info := (tarray tschar 62),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 72)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 118)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 103)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 83)),
                (InitData.Init_int8 (Integers.Int.repr 79)),
                (InitData.Init_int8 (Integers.Int.repr 67)),
                (InitData.Init_int8 (Integers.Int.repr 75)),
                (InitData.Init_int8 (Integers.Int.repr 83)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 45)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 120)),
                (InitData.Init_int8 (Integers.Int.repr 121)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 120)),
                (InitData.Init_int8 (Integers.Int.repr 121)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 117)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 100)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 119)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 104)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 39)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 39)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_2 : GlobVar Ty := {
  gvar_info := (tarray tschar 9),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 95)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 120)),
                (InitData.Init_int8 (Integers.Int.repr 121)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_4 : GlobVar Ty := {
  gvar_info := (tarray tschar 35),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 85)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 120)),
                (InitData.Init_int8 (Integers.Int.repr 121)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 118)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 118)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 98)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 61)),
                (InitData.Init_int8 (Integers.Int.repr 61)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 39)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 39)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v_Curl_scheme_http : GlobVar Ty := {
  gvar_info := (Ty.Tstruct _Curl_scheme noattr),
  gvar_init := [],
  gvar_readonly := true,
  gvar_volatile := false
}

def f_url_set_conn_proxies : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_conn, (tptr (Ty.Tstruct _connectdata noattr)))],
  fn_vars := [],
  fn_temps := [(_proxy, (tptr tschar)), (_pre_proxy, (tptr tschar)),
               (_no_proxy, (tptr tschar)), (_result, tint),
               (_p, (tptr tschar)), (_t'15, tint), (_t'14, tint),
               (_t'13, tint), (_t'12, tint), (_t'11, tint), (_t'10, tint),
               (_t'9, tint), (_t'8, tbool), (_t'7, (tptr tschar)),
               (_t'6, tint), (_t'5, (tptr tschar)), (_t'4, (tptr tschar)),
               (_t'3, (tptr tschar)), (_t'2, (tptr tschar)),
               (_t'1, (tptr tschar)), (_t'43, (tptr tschar)),
               (_t'42, (tptr tschar)), (_t'41, (tptr tschar)),
               (_t'40, (tptr tschar)), (_t'39, (tptr tschar)),
               (_t'38, (tptr tschar)), (_t'37, (tptr tschar)),
               (_t'36, (tptr tschar)),
               (_t'35, (tptr (Ty.Tstruct _Curl_peer noattr))),
               (_t'34, tuint),
               (_t'33, (tptr (Ty.Tstruct _Curl_scheme noattr))),
               (_t'32, tschar), (_t'31, tuint),
               (_t'30, (tptr (Ty.Tstruct _Curl_scheme noattr))),
               (_t'29, tschar),
               (_t'28, (tptr (Ty.Tstruct _Curl_peer noattr))),
               (_t'27, tuchar), (_t'26, tint), (_t'25, tuint),
               (_t'24, (tptr (Ty.Tstruct _Curl_scheme noattr))),
               (_t'23, tlong),
               (_t'22, (tptr (Ty.Tstruct _Curl_scheme noattr))),
               (_t'21, (tptr (Ty.Tstruct _Curl_peer noattr))),
               (_t'20, (tptr (Ty.Tstruct _Curl_peer noattr))),
               (_t'19, (tptr (Ty.Tstruct _Curl_peer noattr))), (_t'18, tint),
               (_t'17, tint), (_t'16, tint)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Sset _proxy
    (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)))
  (Stmt.Ssequence
    (Stmt.Sset _pre_proxy
      (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)))
    (Stmt.Ssequence
      (Stmt.Sset _no_proxy
        (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint)
          (tptr tvoid)))
      (Stmt.Ssequence
        (Stmt.Sset _result (Expr.Econst_int (Integers.Int.repr 0) tint))
        (Stmt.Ssequence
          (Stmt.Ssequence
            (Stmt.Sset _t'42
              (Expr.Ederef
                (Expr.Ebinop Binop.Oadd
                  (Expr.Efield
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                        (Ty.Tstruct _Curl_easy noattr)) _set
                      (Ty.Tstruct _UserDefined noattr)) _str
                    (tarray (tptr tschar) 71))
                  (Expr.Econst_int (Integers.Int.repr 38) tint)
                  (tptr (tptr tschar))) (tptr tschar)))
            (Stmt.Sifthenelse (Expr.Etempvar _t'42 (tptr tschar))
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Sset _t'43
                      (Expr.Ederef
                        (Expr.Ebinop Binop.Oadd
                          (Expr.Efield
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                (Ty.Tstruct _Curl_easy noattr)) _set
                              (Ty.Tstruct _UserDefined noattr)) _str
                            (tarray (tptr tschar) 71))
                          (Expr.Econst_int (Integers.Int.repr 38) tint)
                          (tptr (tptr tschar))) (tptr tschar)))
                    (Stmt.Scall (some _t'1)
                      (Expr.Evar _curlx_strdup (Ty.Tfunction [(tptr tschar)]
                                                 (tptr tschar) cc_default))
                      [(Expr.Etempvar _t'43 (tptr tschar))]))
                  (Stmt.Sset _proxy (Expr.Etempvar _t'1 (tptr tschar))))
                (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                    (Expr.Etempvar _proxy (tptr tschar))
                                    tint)
                  (Stmt.Ssequence
                    (Stmt.Scall none
                      (Expr.Evar _Curl_failf (Ty.Tfunction
                                               [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                (tptr tschar)] tvoid
                                               { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                      [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                       (Expr.Evar ___stringlit_1 (tarray tschar 16))])
                    (Stmt.Ssequence
                      (Stmt.Sset _result
                        (Expr.Econst_int (Integers.Int.repr 27) tint))
                      (Stmt.Sgoto _out)))
                  Stmt.Sskip))
              Stmt.Sskip))
          (Stmt.Ssequence
            (Stmt.Ssequence
              (Stmt.Sset _t'40
                (Expr.Ederef
                  (Expr.Ebinop Binop.Oadd
                    (Expr.Efield
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                          (Ty.Tstruct _Curl_easy noattr)) _set
                        (Ty.Tstruct _UserDefined noattr)) _str
                      (tarray (tptr tschar) 71))
                    (Expr.Econst_int (Integers.Int.repr 39) tint)
                    (tptr (tptr tschar))) (tptr tschar)))
              (Stmt.Sifthenelse (Expr.Etempvar _t'40 (tptr tschar))
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sset _t'41
                        (Expr.Ederef
                          (Expr.Ebinop Binop.Oadd
                            (Expr.Efield
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                  (Ty.Tstruct _Curl_easy noattr)) _set
                                (Ty.Tstruct _UserDefined noattr)) _str
                              (tarray (tptr tschar) 71))
                            (Expr.Econst_int (Integers.Int.repr 39) tint)
                            (tptr (tptr tschar))) (tptr tschar)))
                      (Stmt.Scall (some _t'2)
                        (Expr.Evar _curlx_strdup (Ty.Tfunction
                                                   [(tptr tschar)]
                                                   (tptr tschar) cc_default))
                        [(Expr.Etempvar _t'41 (tptr tschar))]))
                    (Stmt.Sset _pre_proxy (Expr.Etempvar _t'2 (tptr tschar))))
                  (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                      (Expr.Etempvar _pre_proxy (tptr tschar))
                                      tint)
                    (Stmt.Ssequence
                      (Stmt.Scall none
                        (Expr.Evar _Curl_failf (Ty.Tfunction
                                                 [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                  (tptr tschar)] tvoid
                                                 { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                        [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                         (Expr.Evar ___stringlit_1 (tarray tschar 16))])
                      (Stmt.Ssequence
                        (Stmt.Sset _result
                          (Expr.Econst_int (Integers.Int.repr 27) tint))
                        (Stmt.Sgoto _out)))
                    Stmt.Sskip))
                Stmt.Sskip))
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Sset _t'39
                  (Expr.Ederef
                    (Expr.Ebinop Binop.Oadd
                      (Expr.Efield
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                            (Ty.Tstruct _Curl_easy noattr)) _set
                          (Ty.Tstruct _UserDefined noattr)) _str
                        (tarray (tptr tschar) 71))
                      (Expr.Econst_int (Integers.Int.repr 50) tint)
                      (tptr (tptr tschar))) (tptr tschar)))
                (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                    (Expr.Etempvar _t'39 (tptr tschar)) tint)
                  (Stmt.Ssequence
                    (Stmt.Sset _p
                      (Expr.Evar ___stringlit_2 (tarray tschar 9)))
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Scall (some _t'3)
                          (Expr.Evar _curl_getenv (Ty.Tfunction
                                                    [(tptr tschar)]
                                                    (tptr tschar) cc_default))
                          [(Expr.Etempvar _p (tptr tschar))])
                        (Stmt.Sset _no_proxy
                          (Expr.Etempvar _t'3 (tptr tschar))))
                      (Stmt.Ssequence
                        (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                            (Expr.Etempvar _no_proxy (tptr tschar))
                                            tint)
                          (Stmt.Ssequence
                            (Stmt.Sset _p
                              (Expr.Evar ___stringlit_3 (tarray tschar 9)))
                            (Stmt.Ssequence
                              (Stmt.Scall (some _t'4)
                                (Expr.Evar _curl_getenv (Ty.Tfunction
                                                          [(tptr tschar)]
                                                          (tptr tschar)
                                                          cc_default))
                                [(Expr.Etempvar _p (tptr tschar))])
                              (Stmt.Sset _no_proxy
                                (Expr.Etempvar _t'4 (tptr tschar)))))
                          Stmt.Sskip)
                        (Stmt.Sifthenelse (Expr.Etempvar _no_proxy (tptr tschar))
                          (Stmt.Scall none
                            (Expr.Evar _Curl_infof (Ty.Tfunction
                                                     [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                      (tptr tschar)] tvoid
                                                     { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                             (Expr.Evar ___stringlit_4 (tarray tschar 35)),
                             (Expr.Etempvar _p (tptr tschar)),
                             (Expr.Etempvar _no_proxy (tptr tschar))])
                          Stmt.Sskip))))
                  Stmt.Sskip))
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sset _t'37
                        (Expr.Ederef
                          (Expr.Ebinop Binop.Oadd
                            (Expr.Efield
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                  (Ty.Tstruct _Curl_easy noattr)) _set
                                (Ty.Tstruct _UserDefined noattr)) _str
                              (tarray (tptr tschar) 71))
                            (Expr.Econst_int (Integers.Int.repr 50) tint)
                            (tptr (tptr tschar))) (tptr tschar)))
                      (Stmt.Sifthenelse (Expr.Etempvar _t'37 (tptr tschar))
                        (Stmt.Ssequence
                          (Stmt.Sset _t'38
                            (Expr.Ederef
                              (Expr.Ebinop Binop.Oadd
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                      (Ty.Tstruct _Curl_easy noattr)) _set
                                    (Ty.Tstruct _UserDefined noattr)) _str
                                  (tarray (tptr tschar) 71))
                                (Expr.Econst_int (Integers.Int.repr 50) tint)
                                (tptr (tptr tschar))) (tptr tschar)))
                          (Stmt.Sset _t'7
                            (Expr.Ecast (Expr.Etempvar _t'38 (tptr tschar))
                              (tptr tschar))))
                        (Stmt.Sset _t'7
                          (Expr.Ecast (Expr.Etempvar _no_proxy (tptr tschar))
                            (tptr tschar)))))
                    (Stmt.Ssequence
                      (Stmt.Sset _t'35
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                            (Ty.Tstruct _connectdata noattr)) _origin
                          (tptr (Ty.Tstruct _Curl_peer noattr))))
                      (Stmt.Ssequence
                        (Stmt.Sset _t'36
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _t'35 (tptr (Ty.Tstruct _Curl_peer noattr)))
                              (Ty.Tstruct _Curl_peer noattr)) _hostname
                            (tptr tschar)))
                        (Stmt.Scall (some _t'8)
                          (Expr.Evar _Curl_check_noproxy (Ty.Tfunction
                                                           [(tptr tschar),
                                                            (tptr tschar)]
                                                           tbool cc_default))
                          [(Expr.Etempvar _t'36 (tptr tschar)),
                           (Expr.Etempvar _t'7 (tptr tschar))]))))
                  (Stmt.Sifthenelse (Expr.Etempvar _t'8 tbool)
                    (Stmt.Ssequence
                      (Stmt.Sloop
                        (Stmt.Ssequence
                          (Stmt.Scall none
                            (Expr.Evar _curlx_free (Ty.Tfunction
                                                     [(tptr tvoid)] tvoid
                                                     cc_default))
                            [(Expr.Etempvar _proxy (tptr tschar))])
                          (Stmt.Sset _proxy
                            (Expr.Ecast
                              (Expr.Econst_int (Integers.Int.repr 0) tint)
                              (tptr tvoid))))
                        Stmt.Sbreak)
                      (Stmt.Sloop
                        (Stmt.Ssequence
                          (Stmt.Scall none
                            (Expr.Evar _curlx_free (Ty.Tfunction
                                                     [(tptr tvoid)] tvoid
                                                     cc_default))
                            [(Expr.Etempvar _pre_proxy (tptr tschar))])
                          (Stmt.Sset _pre_proxy
                            (Expr.Ecast
                              (Expr.Econst_int (Integers.Int.repr 0) tint)
                              (tptr tvoid))))
                        Stmt.Sbreak))
                    (Stmt.Ssequence
                      (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                          (Expr.Etempvar _proxy (tptr tschar))
                                          tint)
                        (Stmt.Sset _t'6
                          (Expr.Ecast
                            (Expr.Eunop Unop.Onotbool
                              (Expr.Etempvar _pre_proxy (tptr tschar)) tint)
                            tbool))
                        (Stmt.Sset _t'6
                          (Expr.Econst_int (Integers.Int.repr 0) tint)))
                      (Stmt.Sifthenelse (Expr.Etempvar _t'6 tint)
                        (Stmt.Ssequence
                          (Stmt.Scall (some _t'5)
                            (Expr.Evar _url_detect_proxy (Ty.Tfunction
                                                           [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                            (tptr (Ty.Tstruct _connectdata noattr))]
                                                           (tptr tschar)
                                                           cc_default))
                            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                             (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))])
                          (Stmt.Sset _proxy
                            (Expr.Etempvar _t'5 (tptr tschar))))
                        Stmt.Sskip))))
                (Stmt.Ssequence
                  (Stmt.Sloop
                    (Stmt.Ssequence
                      (Stmt.Scall none
                        (Expr.Evar _curlx_free (Ty.Tfunction [(tptr tvoid)]
                                                 tvoid cc_default))
                        [(Expr.Etempvar _no_proxy (tptr tschar))])
                      (Stmt.Sset _no_proxy
                        (Expr.Ecast
                          (Expr.Econst_int (Integers.Int.repr 0) tint)
                          (tptr tvoid))))
                    Stmt.Sbreak)
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sifthenelse (Expr.Etempvar _proxy (tptr tschar))
                        (Stmt.Ssequence
                          (Stmt.Sset _t'32
                            (Expr.Ederef (Expr.Etempvar _proxy (tptr tschar))
                              tschar))
                          (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                              (Expr.Etempvar _t'32 tschar)
                                              tint)
                            (Stmt.Sset _t'9
                              (Expr.Ecast
                                (Expr.Econst_int (Integers.Int.repr 1) tint)
                                tbool))
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Sset _t'33
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                      (Ty.Tstruct _connectdata noattr))
                                    _scheme
                                    (tptr (Ty.Tstruct _Curl_scheme noattr))))
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'34
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _t'33 (tptr (Ty.Tstruct _Curl_scheme noattr)))
                                        (Ty.Tstruct _Curl_scheme noattr))
                                      _flags tuint))
                                  (Stmt.Sset _t'9
                                    (Expr.Ecast
                                      (Expr.Ebinop Binop.Oand
                                        (Expr.Etempvar _t'34 tuint)
                                        (Expr.Ebinop Binop.Oshl
                                          (Expr.Econst_int (Integers.Int.repr 1) tint)
                                          (Expr.Econst_int (Integers.Int.repr 4) tint)
                                          tint) tuint) tbool))))
                              (Stmt.Sset _t'9
                                (Expr.Ecast (Expr.Etempvar _t'9 tint) tbool)))))
                        (Stmt.Sset _t'9
                          (Expr.Econst_int (Integers.Int.repr 0) tint)))
                      (Stmt.Sifthenelse (Expr.Etempvar _t'9 tint)
                        (Stmt.Ssequence
                          (Stmt.Scall none
                            (Expr.Evar _curlx_free (Ty.Tfunction
                                                     [(tptr tvoid)] tvoid
                                                     cc_default))
                            [(Expr.Etempvar _proxy (tptr tschar))])
                          (Stmt.Sset _proxy
                            (Expr.Ecast
                              (Expr.Econst_int (Integers.Int.repr 0) tint)
                              (tptr tvoid))))
                        Stmt.Sskip))
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Sifthenelse (Expr.Etempvar _pre_proxy (tptr tschar))
                          (Stmt.Ssequence
                            (Stmt.Sset _t'29
                              (Expr.Ederef
                                (Expr.Etempvar _pre_proxy (tptr tschar))
                                tschar))
                            (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                                (Expr.Etempvar _t'29 tschar)
                                                tint)
                              (Stmt.Sset _t'10
                                (Expr.Ecast
                                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                                  tbool))
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'30
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                        (Ty.Tstruct _connectdata noattr))
                                      _scheme
                                      (tptr (Ty.Tstruct _Curl_scheme noattr))))
                                  (Stmt.Ssequence
                                    (Stmt.Sset _t'31
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _t'30 (tptr (Ty.Tstruct _Curl_scheme noattr)))
                                          (Ty.Tstruct _Curl_scheme noattr))
                                        _flags tuint))
                                    (Stmt.Sset _t'10
                                      (Expr.Ecast
                                        (Expr.Ebinop Binop.Oand
                                          (Expr.Etempvar _t'31 tuint)
                                          (Expr.Ebinop Binop.Oshl
                                            (Expr.Econst_int (Integers.Int.repr 1) tint)
                                            (Expr.Econst_int (Integers.Int.repr 4) tint)
                                            tint) tuint) tbool))))
                                (Stmt.Sset _t'10
                                  (Expr.Ecast (Expr.Etempvar _t'10 tint)
                                    tbool)))))
                          (Stmt.Sset _t'10
                            (Expr.Econst_int (Integers.Int.repr 0) tint)))
                        (Stmt.Sifthenelse (Expr.Etempvar _t'10 tint)
                          (Stmt.Ssequence
                            (Stmt.Scall none
                              (Expr.Evar _curlx_free (Ty.Tfunction
                                                       [(tptr tvoid)] tvoid
                                                       cc_default))
                              [(Expr.Etempvar _pre_proxy (tptr tschar))])
                            (Stmt.Sset _pre_proxy
                              (Expr.Ecast
                                (Expr.Econst_int (Integers.Int.repr 0) tint)
                                (tptr tvoid))))
                          Stmt.Sskip))
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Sifthenelse (Expr.Etempvar _proxy (tptr tschar))
                            (Stmt.Sset _t'14
                              (Expr.Econst_int (Integers.Int.repr 1) tint))
                            (Stmt.Sset _t'14
                              (Expr.Ecast
                                (Expr.Etempvar _pre_proxy (tptr tschar))
                                tbool)))
                          (Stmt.Sifthenelse (Expr.Etempvar _t'14 tint)
                            (Stmt.Ssequence
                              (Stmt.Sifthenelse (Expr.Etempvar _pre_proxy (tptr tschar))
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Scall (some _t'11)
                                      (Expr.Evar _parse_proxy (Ty.Tfunction
                                                                [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                 (tptr tschar),
                                                                 tbool,
                                                                 (tptr (Ty.Tstruct _proxy_info noattr))]
                                                                tint
                                                                cc_default))
                                      [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                       (Expr.Etempvar _pre_proxy (tptr tschar)),
                                       (Expr.Econst_int (Integers.Int.repr 1) tint),
                                       (Expr.Eaddrof
                                         (Expr.Efield
                                           (Expr.Ederef
                                             (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                             (Ty.Tstruct _connectdata noattr))
                                           _socks_proxy
                                           (Ty.Tstruct _proxy_info noattr))
                                         (tptr (Ty.Tstruct _proxy_info noattr)))])
                                    (Stmt.Sset _result
                                      (Expr.Etempvar _t'11 tint)))
                                  (Stmt.Sifthenelse (Expr.Etempvar _result tint)
                                    (Stmt.Sgoto _out)
                                    Stmt.Sskip))
                                Stmt.Sskip)
                              (Stmt.Ssequence
                                (Stmt.Sifthenelse (Expr.Etempvar _proxy (tptr tschar))
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Scall (some _t'12)
                                        (Expr.Evar _parse_proxy (Ty.Tfunction
                                                                  [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                   (tptr tschar),
                                                                   tbool,
                                                                   (tptr (Ty.Tstruct _proxy_info noattr))]
                                                                  tint
                                                                  cc_default))
                                        [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                         (Expr.Etempvar _proxy (tptr tschar)),
                                         (Expr.Econst_int (Integers.Int.repr 0) tint),
                                         (Expr.Eaddrof
                                           (Expr.Efield
                                             (Expr.Ederef
                                               (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                               (Ty.Tstruct _connectdata noattr))
                                             _http_proxy
                                             (Ty.Tstruct _proxy_info noattr))
                                           (tptr (Ty.Tstruct _proxy_info noattr)))])
                                      (Stmt.Sset _result
                                        (Expr.Etempvar _t'12 tint)))
                                    (Stmt.Ssequence
                                      (Stmt.Sifthenelse (Expr.Etempvar _result tint)
                                        (Stmt.Sgoto _out)
                                        Stmt.Sskip)
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'27
                                          (Expr.Efield
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                (Ty.Tstruct _connectdata noattr))
                                              _http_proxy
                                              (Ty.Tstruct _proxy_info noattr))
                                            _proxytype tuchar))
                                        (Stmt.Sswitch (Expr.Etempvar _t'27 tuchar)
                                          (LStmts.LScons (some 4)
                                            Stmt.Sskip
                                            (LStmts.LScons (some 6)
                                              Stmt.Sskip
                                              (LStmts.LScons (some 5)
                                                Stmt.Sskip
                                                (LStmts.LScons (some 7)
                                                  (Stmt.Ssequence
                                                    (Stmt.Ssequence
                                                      (Stmt.Sset _t'28
                                                        (Expr.Efield
                                                          (Expr.Efield
                                                            (Expr.Ederef
                                                              (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                              (Ty.Tstruct _connectdata noattr))
                                                            _socks_proxy
                                                            (Ty.Tstruct _proxy_info noattr))
                                                          _peer
                                                          (tptr (Ty.Tstruct _Curl_peer noattr))))
                                                      (Stmt.Sifthenelse (Expr.Etempvar _t'28 (tptr (Ty.Tstruct _Curl_peer noattr)))
                                                        (Stmt.Ssequence
                                                          (Stmt.Scall none
                                                            (Expr.Evar _Curl_failf 
                                                            (Ty.Tfunction
                                                              [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                               (tptr tschar)]
                                                              tvoid
                                                              { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                                            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                             (Expr.Evar ___stringlit_5 (tarray tschar 62)),
                                                             (Expr.Etempvar _proxy (tptr tschar))])
                                                          (Stmt.Ssequence
                                                            (Stmt.Sset _result
                                                              (Expr.Econst_int (Integers.Int.repr 5) tint))
                                                            (Stmt.Sgoto _out)))
                                                        Stmt.Sskip))
                                                    (Stmt.Ssequence
                                                      (Stmt.Sassign
                                                        (Expr.Efield
                                                          (Expr.Ederef
                                                            (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                            (Ty.Tstruct _connectdata noattr))
                                                          _socks_proxy
                                                          (Ty.Tstruct _proxy_info noattr))
                                                        (Expr.Efield
                                                          (Expr.Ederef
                                                            (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                            (Ty.Tstruct _connectdata noattr))
                                                          _http_proxy
                                                          (Ty.Tstruct _proxy_info noattr)))
                                                      (Stmt.Ssequence
                                                        (Stmt.Scall none
                                                          (Expr.Evar _memset 
                                                          (Ty.Tfunction
                                                            [(tptr tvoid),
                                                             tint, tulong]
                                                            (tptr tvoid)
                                                            cc_default))
                                                          [(Expr.Eaddrof
                                                             (Expr.Efield
                                                               (Expr.Ederef
                                                                 (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                                 (Ty.Tstruct _connectdata noattr))
                                                               _http_proxy
                                                               (Ty.Tstruct _proxy_info noattr))
                                                             (tptr (Ty.Tstruct _proxy_info noattr))),
                                                           (Expr.Econst_int (Integers.Int.repr 0) tint),
                                                           (Expr.Esizeof (Ty.Tstruct _proxy_info noattr) tulong)])
                                                        Stmt.Sbreak)))
                                                  (LStmts.LScons none
                                                    Stmt.Sbreak
                                                    LStmts.LSnil)))))))))
                                  Stmt.Sskip)
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'21
                                    (Expr.Efield
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                          (Ty.Tstruct _connectdata noattr))
                                        _http_proxy
                                        (Ty.Tstruct _proxy_info noattr))
                                      _peer
                                      (tptr (Ty.Tstruct _Curl_peer noattr))))
                                  (Stmt.Sifthenelse (Expr.Etempvar _t'21 (tptr (Ty.Tstruct _Curl_peer noattr)))
                                    (Stmt.Ssequence
                                      (Stmt.Sset _t'22
                                        (Expr.Efield
                                          (Expr.Ederef
                                            (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                            (Ty.Tstruct _connectdata noattr))
                                          _scheme
                                          (tptr (Ty.Tstruct _Curl_scheme noattr))))
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'23
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _t'22 (tptr (Ty.Tstruct _Curl_scheme noattr)))
                                              (Ty.Tstruct _Curl_scheme noattr))
                                            _protocol tlong))
                                        (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                                            (Expr.Ebinop Binop.Oand
                                                              (Expr.Etempvar _t'23 tlong)
                                                              (Expr.Ebinop Binop.Oor
                                                                (Expr.Ebinop Binop.Oor
                                                                  (Expr.Ebinop Binop.Oor
                                                                    (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_long (Integers.Int64.repr 1) tlong)
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    tlong)
                                                                    (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_long (Integers.Int64.repr 1) tlong)
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    tlong)
                                                                    tlong)
                                                                  (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_long (Integers.Int64.repr 1) tlong)
                                                                    (Expr.Econst_int (Integers.Int.repr 30) tint)
                                                                    tlong)
                                                                  tlong)
                                                                (Expr.Ebinop Binop.Oshl
                                                                  (Expr.Ecast
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    tlong)
                                                                  (Expr.Econst_int (Integers.Int.repr 31) tint)
                                                                  tlong)
                                                                tlong) tlong)
                                                            tint)
                                          (Stmt.Ssequence
                                            (Stmt.Ssequence
                                              (Stmt.Sset _t'24
                                                (Expr.Efield
                                                  (Expr.Ederef
                                                    (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                    (Ty.Tstruct _connectdata noattr))
                                                  _scheme
                                                  (tptr (Ty.Tstruct _Curl_scheme noattr))))
                                              (Stmt.Ssequence
                                                (Stmt.Sset _t'25
                                                  (Expr.Efield
                                                    (Expr.Ederef
                                                      (Expr.Etempvar _t'24 (tptr (Ty.Tstruct _Curl_scheme noattr)))
                                                      (Ty.Tstruct _Curl_scheme noattr))
                                                    _flags tuint))
                                                (Stmt.Sifthenelse (Expr.Ebinop Binop.Oand
                                                                    (Expr.Etempvar _t'25 tuint)
                                                                    (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 11) tint)
                                                                    tint)
                                                                    tuint)
                                                  (Stmt.Ssequence
                                                    (Stmt.Sset _t'26
                                                      (Expr.Efield
                                                        (Expr.Efield
                                                          (Expr.Ederef
                                                            (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                            (Ty.Tstruct _connectdata noattr))
                                                          _bits
                                                          (Ty.Tstruct _ConnectBits noattr))
                                                        _tunnel_proxy tint))
                                                    (Stmt.Sset _t'13
                                                      (Expr.Ecast
                                                        (Expr.Eunop Unop.Onotbool
                                                          (Expr.Etempvar _t'26 tint)
                                                          tint) tbool)))
                                                  (Stmt.Sset _t'13
                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)))))
                                            (Stmt.Sifthenelse (Expr.Etempvar _t'13 tint)
                                              (Stmt.Sassign
                                                (Expr.Efield
                                                  (Expr.Ederef
                                                    (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                    (Ty.Tstruct _connectdata noattr))
                                                  _scheme
                                                  (tptr (Ty.Tstruct _Curl_scheme noattr)))
                                                (Expr.Eaddrof
                                                  (Expr.Evar _Curl_scheme_http (Ty.Tstruct _Curl_scheme noattr))
                                                  (tptr (Ty.Tstruct _Curl_scheme noattr))))
                                              (Stmt.Sassign
                                                (Expr.Efield
                                                  (Expr.Efield
                                                    (Expr.Ederef
                                                      (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                      (Ty.Tstruct _connectdata noattr))
                                                    _bits
                                                    (Ty.Tstruct _ConnectBits noattr))
                                                  _tunnel_proxy tint)
                                                (Expr.Econst_int (Integers.Int.repr 1) tint))))
                                          Stmt.Sskip)))
                                    (Stmt.Sassign
                                      (Expr.Efield
                                        (Expr.Efield
                                          (Expr.Ederef
                                            (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                            (Ty.Tstruct _connectdata noattr))
                                          _bits
                                          (Ty.Tstruct _ConnectBits noattr))
                                        _tunnel_proxy tint)
                                      (Expr.Econst_int (Integers.Int.repr 0) tint))))))
                            Stmt.Sskip))
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'20
                              (Expr.Efield
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                    (Ty.Tstruct _connectdata noattr))
                                  _socks_proxy
                                  (Ty.Tstruct _proxy_info noattr)) _peer
                                (tptr (Ty.Tstruct _Curl_peer noattr))))
                            (Stmt.Sassign
                              (Expr.Efield
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                    (Ty.Tstruct _connectdata noattr)) _bits
                                  (Ty.Tstruct _ConnectBits noattr))
                                _socksproxy tint)
                              (Expr.Eunop Unop.Onotbool
                                (Expr.Eunop Unop.Onotbool
                                  (Expr.Etempvar _t'20 (tptr (Ty.Tstruct _Curl_peer noattr)))
                                  tint) tint)))
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Sset _t'19
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                      (Ty.Tstruct _connectdata noattr))
                                    _http_proxy
                                    (Ty.Tstruct _proxy_info noattr)) _peer
                                  (tptr (Ty.Tstruct _Curl_peer noattr))))
                              (Stmt.Sassign
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                      (Ty.Tstruct _connectdata noattr)) _bits
                                    (Ty.Tstruct _ConnectBits noattr))
                                  _httpproxy tint)
                                (Expr.Eunop Unop.Onotbool
                                  (Expr.Eunop Unop.Onotbool
                                    (Expr.Etempvar _t'19 (tptr (Ty.Tstruct _Curl_peer noattr)))
                                    tint) tint)))
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'17
                                    (Expr.Efield
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                          (Ty.Tstruct _connectdata noattr))
                                        _bits
                                        (Ty.Tstruct _ConnectBits noattr))
                                      _httpproxy tint))
                                  (Stmt.Sifthenelse (Expr.Etempvar _t'17 tint)
                                    (Stmt.Sset _t'15
                                      (Expr.Econst_int (Integers.Int.repr 1) tint))
                                    (Stmt.Ssequence
                                      (Stmt.Sset _t'18
                                        (Expr.Efield
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                              (Ty.Tstruct _connectdata noattr))
                                            _bits
                                            (Ty.Tstruct _ConnectBits noattr))
                                          _socksproxy tint))
                                      (Stmt.Sset _t'15
                                        (Expr.Ecast
                                          (Expr.Etempvar _t'18 tint) tbool)))))
                                (Stmt.Sassign
                                  (Expr.Efield
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                        (Ty.Tstruct _connectdata noattr))
                                      _bits (Ty.Tstruct _ConnectBits noattr))
                                    _proxy tint) (Expr.Etempvar _t'15 tint)))
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'16
                                    (Expr.Efield
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                          (Ty.Tstruct _connectdata noattr))
                                        _bits
                                        (Ty.Tstruct _ConnectBits noattr))
                                      _proxy tint))
                                  (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                                      (Expr.Etempvar _t'16 tint)
                                                      tint)
                                    (Stmt.Ssequence
                                      (Stmt.Sassign
                                        (Expr.Efield
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                              (Ty.Tstruct _connectdata noattr))
                                            _bits
                                            (Ty.Tstruct _ConnectBits noattr))
                                          _proxy tint)
                                        (Expr.Econst_int (Integers.Int.repr 0) tint))
                                      (Stmt.Ssequence
                                        (Stmt.Sassign
                                          (Expr.Efield
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                (Ty.Tstruct _connectdata noattr))
                                              _bits
                                              (Ty.Tstruct _ConnectBits noattr))
                                            _httpproxy tint)
                                          (Expr.Econst_int (Integers.Int.repr 0) tint))
                                        (Stmt.Ssequence
                                          (Stmt.Sassign
                                            (Expr.Efield
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                  (Ty.Tstruct _connectdata noattr))
                                                _bits
                                                (Ty.Tstruct _ConnectBits noattr))
                                              _socksproxy tint)
                                            (Expr.Econst_int (Integers.Int.repr 0) tint))
                                          (Stmt.Ssequence
                                            (Stmt.Sassign
                                              (Expr.Efield
                                                (Expr.Efield
                                                  (Expr.Ederef
                                                    (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                    (Ty.Tstruct _connectdata noattr))
                                                  _bits
                                                  (Ty.Tstruct _ConnectBits noattr))
                                                _tunnel_proxy tint)
                                              (Expr.Econst_int (Integers.Int.repr 0) tint))
                                            (Stmt.Sassign
                                              (Expr.Efield
                                                (Expr.Efield
                                                  (Expr.Ederef
                                                    (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                                    (Ty.Tstruct _connectdata noattr))
                                                  _http_proxy
                                                  (Ty.Tstruct _proxy_info noattr))
                                                _proxytype tuchar)
                                              (Expr.Econst_int (Integers.Int.repr 0) tint))))))
                                    Stmt.Sskip))
                                (Stmt.Ssequence
                                  (Stmt.Slabel _out
                                    (Stmt.Scall none
                                      (Expr.Evar _curlx_free (Ty.Tfunction
                                                               [(tptr tvoid)]
                                                               tvoid
                                                               cc_default))
                                      [(Expr.Etempvar _pre_proxy (tptr tschar))]))
                                  (Stmt.Ssequence
                                    (Stmt.Scall none
                                      (Expr.Evar _curlx_free (Ty.Tfunction
                                                               [(tptr tvoid)]
                                                               tvoid
                                                               cc_default))
                                      [(Expr.Etempvar _proxy (tptr tschar))])
                                    (Stmt.Sreturn (some (Expr.Etempvar _result tint)))))))))))))))))))))
}

def v_deb_keep : GlobVar Ty := {
  gvar_info := (tptr (Ty.Tfunction
                       [(tptr (Ty.Tstruct _Curl_easy noattr)),
                        (tptr (Ty.Tstruct _connectdata noattr))] tint
                       cc_default)),
  gvar_init := [(InitData.Init_addrof _url_set_conn_proxies (Integers.Ptrofs.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def composites : List CompositeDef :=
[(CompositeDef.Composite _Curl_peer SU.Struct
   [(Member.Member_plain _hostname (tptr tschar))]
   noattr),
 (CompositeDef.Composite _Curl_scheme SU.Struct
   [(Member.Member_plain _protocol tlong),
    (Member.Member_plain _flags tuint)]
   noattr),
 (CompositeDef.Composite _proxy_info SU.Struct
   [(Member.Member_plain _peer (tptr (Ty.Tstruct _Curl_peer noattr))),
    (Member.Member_plain _proxytype tuchar)]
   noattr),
 (CompositeDef.Composite _ConnectBits SU.Struct
   [(Member.Member_bitfield _httpproxy IntSize.I32 Signedness.Unsigned noattr
      1 false),
    (Member.Member_bitfield _socksproxy IntSize.I32 Signedness.Unsigned
      noattr 1 false),
    (Member.Member_bitfield _tunnel_proxy IntSize.I32 Signedness.Unsigned
      noattr 1 false),
    (Member.Member_bitfield _proxy IntSize.I32 Signedness.Unsigned noattr 1
      false)]
   noattr),
 (CompositeDef.Composite _connectdata SU.Struct
   [(Member.Member_plain _origin (tptr (Ty.Tstruct _Curl_peer noattr))),
    (Member.Member_plain _socks_proxy (Ty.Tstruct _proxy_info noattr)),
    (Member.Member_plain _http_proxy (Ty.Tstruct _proxy_info noattr)),
    (Member.Member_plain _bits (Ty.Tstruct _ConnectBits noattr)),
    (Member.Member_plain _scheme (tptr (Ty.Tstruct _Curl_scheme noattr)))]
   noattr),
 (CompositeDef.Composite _digestdata SU.Struct
   [(Member.Member_plain _nonce (tptr tschar))]
   noattr),
 (CompositeDef.Composite _UserDefined SU.Struct
   [(Member.Member_plain _str (tarray (tptr tschar) 71))]
   noattr),
 (CompositeDef.Composite _UrlState SU.Struct
   [(Member.Member_plain _digest (Ty.Tstruct _digestdata noattr)),
    (Member.Member_plain _proxydigest (Ty.Tstruct _digestdata noattr))]
   noattr),
 (CompositeDef.Composite _Curl_easy SU.Struct
   [(Member.Member_plain _set (Ty.Tstruct _UserDefined noattr)),
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
 (___stringlit_1, GlobDef.Gvar v___stringlit_1),
 (___stringlit_3, GlobDef.Gvar v___stringlit_3),
 (___stringlit_5, GlobDef.Gvar v___stringlit_5),
 (___stringlit_2, GlobDef.Gvar v___stringlit_2),
 (___stringlit_4, GlobDef.Gvar v___stringlit_4),
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
 (_Curl_scheme_http, GlobDef.Gvar v_Curl_scheme_http),
 (_curlx_strdup,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "curlx_strdup"
                                   (mksignature [XType.Xptr] XType.Xptr
                                     cc_default)) [(tptr tschar)]
     (tptr tschar) cc_default)),
 (_curlx_free,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "curlx_free"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default)) [(tptr tvoid)] tvoid
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
 (_curl_getenv,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "curl_getenv"
                                   (mksignature [XType.Xptr] XType.Xptr
                                     cc_default)) [(tptr tschar)]
     (tptr tschar) cc_default)),
 (_Curl_check_noproxy,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_check_noproxy"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xbool cc_default))
     [(tptr tschar), (tptr tschar)] tbool cc_default)),
 (_url_detect_proxy,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "url_detect_proxy"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xptr cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)),
      (tptr (Ty.Tstruct _connectdata noattr))] (tptr tschar) cc_default)),
 (_parse_proxy,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "parse_proxy"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xbool,
                                      XType.Xptr] XType.Xint cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar), tbool,
      (tptr (Ty.Tstruct _proxy_info noattr))] tint cc_default)),
 (_memset,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "memset"
                                   (mksignature
                                     [XType.Xptr, XType.Xint, XType.Xlong]
                                     XType.Xptr cc_default))
     [(tptr tvoid), tint, tulong] (tptr tvoid) cc_default)),
 (_url_set_conn_proxies, GlobDef.Gfun (FunDef.Internal f_url_set_conn_proxies)),
 (_deb_keep, GlobDef.Gvar v_deb_keep)]

def public_idents : List Ident :=
[_deb_keep, _memset, _parse_proxy, _url_detect_proxy, _Curl_check_noproxy,
 _curl_getenv, _Curl_infof, _Curl_failf, _curlx_free, _curlx_strdup,
 _Curl_scheme_http, ___builtin_debug, ___builtin_fmin, ___builtin_fmax,
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

end Deb2026_8927_u0

