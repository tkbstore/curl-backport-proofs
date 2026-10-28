import Clightdefs
open CC

namespace Case2_before

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
  def source_file : String := "case2_before.c"
  def normalized : Bool := true
end Info

def _Curl_cpool_find : Ident := identOfString "Curl_cpool_find"
def _Curl_cpool_get_instance : Ident := identOfString "Curl_cpool_get_instance"
def _Curl_cpool_prune_dead : Ident := identOfString "Curl_cpool_prune_dead"
def _Curl_creds : Ident := identOfString "Curl_creds"
def _Curl_creds_same : Ident := identOfString "Curl_creds_same"
def _Curl_easy : Ident := identOfString "Curl_easy"
def _Curl_peer : Ident := identOfString "Curl_peer"
def _Curl_peer_equal : Ident := identOfString "Curl_peer_equal"
def _Curl_pgrs_now : Ident := identOfString "Curl_pgrs_now"
def _Curl_scheme : Ident := identOfString "Curl_scheme"
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
def _auth : Ident := identOfString "auth"
def _authhost : Ident := identOfString "authhost"
def _case2_keep : Ident := identOfString "case2_keep"
def _conn : Ident := identOfString "conn"
def _connectdata : Ident := identOfString "connectdata"
def _cpool : Ident := identOfString "cpool"
def _cpool__1 : Ident := identOfString "cpool__1"
def _creds : Ident := identOfString "creds"
def _creds_origin : Ident := identOfString "creds_origin"
def _curltime : Ident := identOfString "curltime"
def _data : Ident := identOfString "data"
def _destination : Ident := identOfString "destination"
def _force_reuse : Ident := identOfString "force_reuse"
def _found : Ident := identOfString "found"
def _http_negotiate_state : Ident := identOfString "http_negotiate_state"
def _m : Ident := identOfString "m"
def _main : Ident := identOfString "main"
def _match : Ident := identOfString "match"
def _may_multiplex : Ident := identOfString "may_multiplex"
def _may_tls : Ident := identOfString "may_tls"
def _memset : Ident := identOfString "memset"
def _needle : Ident := identOfString "needle"
def _now : Ident := identOfString "now"
def _origin : Ident := identOfString "origin"
def _protocol : Ident := identOfString "protocol"
def _proxy_negotiate_state : Ident := identOfString "proxy_negotiate_state"
def _require_tls : Ident := identOfString "require_tls"
def _scheme : Ident := identOfString "scheme"
def _set : Ident := identOfString "set"
def _state : Ident := identOfString "state"
def _success : Ident := identOfString "success"
def _tv_sec : Ident := identOfString "tv_sec"
def _tv_usec : Ident := identOfString "tv_usec"
def _url_attach_existing : Ident := identOfString "url_attach_existing"
def _url_conn_match : Ident := identOfString "url_conn_match"
def _url_match_auth_nego : Ident := identOfString "url_match_auth_nego"
def _url_match_conn : Ident := identOfString "url_match_conn"
def _url_match_result : Ident := identOfString "url_match_result"
def _use_ssl : Ident := identOfString "use_ssl"
def _wait_pipe : Ident := identOfString "wait_pipe"
def _waitpipe : Ident := identOfString "waitpipe"
def _want : Ident := identOfString "want"
def _want_nego_http : Ident := identOfString "want_nego_http"
def _want_proxy_nego_http : Ident := identOfString "want_proxy_nego_http"
def _xfer_may_multiplex : Ident := identOfString "xfer_may_multiplex"
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
def _t'4 : Ident := (Positive.ofNat 131)
def _t'5 : Ident := (Positive.ofNat 132)
def _t'6 : Ident := (Positive.ofNat 133)
def _t'7 : Ident := (Positive.ofNat 134)
def _t'8 : Ident := (Positive.ofNat 135)
def _t'9 : Ident := (Positive.ofNat 136)

def f_url_match_auth_nego : Function := {
  fn_return := tbool,
  fn_callconv := cc_default,
  fn_params := [(_conn, (tptr (Ty.Tstruct _connectdata noattr))),
                (_m, (tptr (Ty.Tstruct _url_conn_match noattr)))],
  fn_vars := [],
  fn_temps := [(_t'10, tint), (_t'9, tint), (_t'8, tint), (_t'7, tbool),
               (_t'6, tbool), (_t'5, tint), (_t'4, tbool), (_t'3, tint),
               (_t'2, tbool), (_t'1, tint),
               (_t'32, (tptr (Ty.Tstruct _Curl_creds noattr))),
               (_t'31, (tptr (Ty.Tstruct _Curl_easy noattr))),
               (_t'30, (tptr (Ty.Tstruct _Curl_creds noattr))),
               (_t'29, tint), (_t'28, (tptr (Ty.Tstruct _Curl_peer noattr))),
               (_t'27, (tptr (Ty.Tstruct _Curl_easy noattr))),
               (_t'26, (tptr (Ty.Tstruct _Curl_peer noattr))),
               (_t'25, (tptr (Ty.Tstruct _Curl_creds noattr))),
               (_t'24, (tptr (Ty.Tstruct _Curl_easy noattr))),
               (_t'23, (tptr (Ty.Tstruct _Curl_creds noattr))),
               (_t'22, (tptr (Ty.Tstruct _Curl_peer noattr))),
               (_t'21, (tptr (Ty.Tstruct _Curl_easy noattr))),
               (_t'20, (tptr (Ty.Tstruct _Curl_peer noattr))),
               (_t'19, (tptr (Ty.Tstruct _Curl_creds noattr))),
               (_t'18, tint), (_t'17, tint), (_t'16, tint), (_t'15, tint),
               (_t'14, tint), (_t'13, tint), (_t'12, tint), (_t'11, tint)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Ssequence
    (Stmt.Sset _t'17
      (Expr.Efield
        (Expr.Ederef
          (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
          (Ty.Tstruct _connectdata noattr)) _http_negotiate_state tint))
    (Stmt.Sifthenelse (Expr.Ebinop Binop.One (Expr.Etempvar _t'17 tint)
                        (Expr.Econst_int (Integers.Int.repr 0) tint) tint)
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Ssequence
            (Stmt.Sset _t'29
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
                  (Ty.Tstruct _url_conn_match noattr)) _want_nego_http tint))
            (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                (Expr.Etempvar _t'29 tint) tint)
              (Stmt.Sset _t'1 (Expr.Econst_int (Integers.Int.repr 1) tint))
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Sset _t'30
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                        (Ty.Tstruct _connectdata noattr)) _creds
                      (tptr (Ty.Tstruct _Curl_creds noattr))))
                  (Stmt.Ssequence
                    (Stmt.Sset _t'31
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
                          (Ty.Tstruct _url_conn_match noattr)) _data
                        (tptr (Ty.Tstruct _Curl_easy noattr))))
                    (Stmt.Ssequence
                      (Stmt.Sset _t'32
                        (Expr.Efield
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _t'31 (tptr (Ty.Tstruct _Curl_easy noattr)))
                              (Ty.Tstruct _Curl_easy noattr)) _state
                            (Ty.Tstruct _UrlState noattr)) _creds
                          (tptr (Ty.Tstruct _Curl_creds noattr))))
                      (Stmt.Scall (some _t'2)
                        (Expr.Evar _Curl_creds_same (Ty.Tfunction
                                                      [(tptr (Ty.Tstruct _Curl_creds noattr)),
                                                       (tptr (Ty.Tstruct _Curl_creds noattr))]
                                                      tbool cc_default))
                        [(Expr.Etempvar _t'30 (tptr (Ty.Tstruct _Curl_creds noattr))),
                         (Expr.Etempvar _t'32 (tptr (Ty.Tstruct _Curl_creds noattr)))]))))
                (Stmt.Sset _t'1
                  (Expr.Ecast
                    (Expr.Eunop Unop.Onotbool (Expr.Etempvar _t'2 tbool)
                      tint) tbool)))))
          (Stmt.Sifthenelse (Expr.Etempvar _t'1 tint)
            (Stmt.Sset _t'3 (Expr.Econst_int (Integers.Int.repr 1) tint))
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Sset _t'26
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                      (Ty.Tstruct _connectdata noattr)) _creds_origin
                    (tptr (Ty.Tstruct _Curl_peer noattr))))
                (Stmt.Ssequence
                  (Stmt.Sset _t'27
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
                        (Ty.Tstruct _url_conn_match noattr)) _data
                      (tptr (Ty.Tstruct _Curl_easy noattr))))
                  (Stmt.Ssequence
                    (Stmt.Sset _t'28
                      (Expr.Efield
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _t'27 (tptr (Ty.Tstruct _Curl_easy noattr)))
                            (Ty.Tstruct _Curl_easy noattr)) _state
                          (Ty.Tstruct _UrlState noattr)) _origin
                        (tptr (Ty.Tstruct _Curl_peer noattr))))
                    (Stmt.Scall (some _t'4)
                      (Expr.Evar _Curl_peer_equal (Ty.Tfunction
                                                    [(tptr (Ty.Tstruct _Curl_peer noattr)),
                                                     (tptr (Ty.Tstruct _Curl_peer noattr))]
                                                    tbool cc_default))
                      [(Expr.Etempvar _t'26 (tptr (Ty.Tstruct _Curl_peer noattr))),
                       (Expr.Etempvar _t'28 (tptr (Ty.Tstruct _Curl_peer noattr)))]))))
              (Stmt.Sset _t'3
                (Expr.Ecast
                  (Expr.Eunop Unop.Onotbool (Expr.Etempvar _t'4 tbool) tint)
                  tbool)))))
        (Stmt.Sifthenelse (Expr.Etempvar _t'3 tint)
          (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint)))
          Stmt.Sskip))
      (Stmt.Ssequence
        (Stmt.Sset _t'18
          (Expr.Efield
            (Expr.Ederef
              (Expr.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
              (Ty.Tstruct _url_conn_match noattr)) _want_nego_http tint))
        (Stmt.Sifthenelse (Expr.Etempvar _t'18 tint)
          (Stmt.Ssequence
            (Stmt.Ssequence
              (Stmt.Sset _t'19
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                    (Ty.Tstruct _connectdata noattr)) _creds
                  (tptr (Ty.Tstruct _Curl_creds noattr))))
              (Stmt.Sifthenelse (Expr.Etempvar _t'19 (tptr (Ty.Tstruct _Curl_creds noattr)))
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Sset _t'23
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                          (Ty.Tstruct _connectdata noattr)) _creds
                        (tptr (Ty.Tstruct _Curl_creds noattr))))
                    (Stmt.Ssequence
                      (Stmt.Sset _t'24
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
                            (Ty.Tstruct _url_conn_match noattr)) _data
                          (tptr (Ty.Tstruct _Curl_easy noattr))))
                      (Stmt.Ssequence
                        (Stmt.Sset _t'25
                          (Expr.Efield
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _t'24 (tptr (Ty.Tstruct _Curl_easy noattr)))
                                (Ty.Tstruct _Curl_easy noattr)) _state
                              (Ty.Tstruct _UrlState noattr)) _creds
                            (tptr (Ty.Tstruct _Curl_creds noattr))))
                        (Stmt.Scall (some _t'6)
                          (Expr.Evar _Curl_creds_same (Ty.Tfunction
                                                        [(tptr (Ty.Tstruct _Curl_creds noattr)),
                                                         (tptr (Ty.Tstruct _Curl_creds noattr))]
                                                        tbool cc_default))
                          [(Expr.Etempvar _t'23 (tptr (Ty.Tstruct _Curl_creds noattr))),
                           (Expr.Etempvar _t'25 (tptr (Ty.Tstruct _Curl_creds noattr)))]))))
                  (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                      (Expr.Etempvar _t'6 tbool) tint)
                    (Stmt.Sset _t'5
                      (Expr.Ecast
                        (Expr.Econst_int (Integers.Int.repr 1) tint) tbool))
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Sset _t'20
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                (Ty.Tstruct _connectdata noattr))
                              _creds_origin
                              (tptr (Ty.Tstruct _Curl_peer noattr))))
                          (Stmt.Ssequence
                            (Stmt.Sset _t'21
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
                                  (Ty.Tstruct _url_conn_match noattr)) _data
                                (tptr (Ty.Tstruct _Curl_easy noattr))))
                            (Stmt.Ssequence
                              (Stmt.Sset _t'22
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _t'21 (tptr (Ty.Tstruct _Curl_easy noattr)))
                                      (Ty.Tstruct _Curl_easy noattr)) _state
                                    (Ty.Tstruct _UrlState noattr)) _origin
                                  (tptr (Ty.Tstruct _Curl_peer noattr))))
                              (Stmt.Scall (some _t'7)
                                (Expr.Evar _Curl_peer_equal (Ty.Tfunction
                                                              [(tptr (Ty.Tstruct _Curl_peer noattr)),
                                                               (tptr (Ty.Tstruct _Curl_peer noattr))]
                                                              tbool
                                                              cc_default))
                                [(Expr.Etempvar _t'20 (tptr (Ty.Tstruct _Curl_peer noattr))),
                                 (Expr.Etempvar _t'22 (tptr (Ty.Tstruct _Curl_peer noattr)))]))))
                        (Stmt.Sset _t'5
                          (Expr.Ecast
                            (Expr.Eunop Unop.Onotbool
                              (Expr.Etempvar _t'7 tbool) tint) tbool)))
                      (Stmt.Sset _t'5
                        (Expr.Ecast (Expr.Etempvar _t'5 tint) tbool)))))
                (Stmt.Sset _t'5 (Expr.Econst_int (Integers.Int.repr 0) tint))))
            (Stmt.Sifthenelse (Expr.Etempvar _t'5 tint)
              (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint)))
              Stmt.Sskip))
          Stmt.Sskip))))
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Ssequence
        (Stmt.Sset _t'15
          (Expr.Efield
            (Expr.Ederef
              (Expr.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
              (Ty.Tstruct _url_conn_match noattr)) _want_nego_http tint))
        (Stmt.Sifthenelse (Expr.Etempvar _t'15 tint)
          (Stmt.Sset _t'10 (Expr.Econst_int (Integers.Int.repr 1) tint))
          (Stmt.Ssequence
            (Stmt.Sset _t'16
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
                  (Ty.Tstruct _url_conn_match noattr)) _want_proxy_nego_http
                tint))
            (Stmt.Sset _t'10 (Expr.Ecast (Expr.Etempvar _t'16 tint) tbool)))))
      (Stmt.Sifthenelse (Expr.Etempvar _t'10 tint)
        (Stmt.Ssequence
          (Stmt.Sassign
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
                (Ty.Tstruct _url_conn_match noattr)) _found
              (tptr (Ty.Tstruct _connectdata noattr)))
            (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr))))
          (Stmt.Ssequence
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Sset _t'13
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
                        (Ty.Tstruct _url_conn_match noattr)) _want_nego_http
                      tint))
                  (Stmt.Sifthenelse (Expr.Etempvar _t'13 tint)
                    (Stmt.Ssequence
                      (Stmt.Sset _t'14
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                            (Ty.Tstruct _connectdata noattr))
                          _http_negotiate_state tint))
                      (Stmt.Sset _t'8
                        (Expr.Ecast
                          (Expr.Ebinop Binop.One (Expr.Etempvar _t'14 tint)
                            (Expr.Econst_int (Integers.Int.repr 0) tint)
                            tint) tbool)))
                    (Stmt.Sset _t'8
                      (Expr.Econst_int (Integers.Int.repr 0) tint))))
                (Stmt.Sifthenelse (Expr.Etempvar _t'8 tint)
                  (Stmt.Sset _t'9
                    (Expr.Econst_int (Integers.Int.repr 1) tint))
                  (Stmt.Ssequence
                    (Stmt.Sset _t'11
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
                          (Ty.Tstruct _url_conn_match noattr))
                        _want_proxy_nego_http tint))
                    (Stmt.Sifthenelse (Expr.Etempvar _t'11 tint)
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Sset _t'12
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                                (Ty.Tstruct _connectdata noattr))
                              _proxy_negotiate_state tint))
                          (Stmt.Sset _t'9
                            (Expr.Ecast
                              (Expr.Ebinop Binop.One
                                (Expr.Etempvar _t'12 tint)
                                (Expr.Econst_int (Integers.Int.repr 0) tint)
                                tint) tbool)))
                        (Stmt.Sset _t'9
                          (Expr.Ecast (Expr.Etempvar _t'9 tint) tbool)))
                      (Stmt.Sset _t'9
                        (Expr.Ecast
                          (Expr.Econst_int (Integers.Int.repr 0) tint) tbool))))))
              (Stmt.Sifthenelse (Expr.Etempvar _t'9 tint)
                (Stmt.Ssequence
                  (Stmt.Sassign
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
                        (Ty.Tstruct _url_conn_match noattr)) _force_reuse
                      tint) (Expr.Econst_int (Integers.Int.repr 1) tint))
                  (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 1) tint))))
                Stmt.Sskip))
            (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint)))))
        Stmt.Sskip))
    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 1) tint)))))
}

def f_url_attach_existing : Function := {
  fn_return := tbool,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_needle, (tptr (Ty.Tstruct _connectdata noattr))),
                (_waitpipe, (tptr tbool))],
  fn_vars := [(_match, (Ty.Tstruct _url_conn_match noattr))],
  fn_temps := [(_cpool__1, (tptr (Ty.Tstruct _cpool noattr))),
               (_success, tbool), (_t'5, tbool), (_t'4, tint), (_t'3, tbool),
               (_t'2, (tptr (Ty.Tstruct _curltime noattr))),
               (_t'1, (tptr (Ty.Tstruct _cpool noattr))), (_t'12, tlong),
               (_t'11, (tptr (Ty.Tstruct _Curl_scheme noattr))),
               (_t'10, tuint), (_t'9, tuchar), (_t'8, tuchar),
               (_t'7, (tptr tschar)), (_t'6, tint)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Ssequence
    (Stmt.Scall (some _t'1)
      (Expr.Evar _Curl_cpool_get_instance (Ty.Tfunction
                                            [(tptr (Ty.Tstruct _Curl_easy noattr))]
                                            (tptr (Ty.Tstruct _cpool noattr))
                                            cc_default))
      [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))])
    (Stmt.Sset _cpool__1
      (Expr.Etempvar _t'1 (tptr (Ty.Tstruct _cpool noattr)))))
  (Stmt.Ssequence
    (Stmt.Sloop Stmt.Sskip Stmt.Sbreak)
    (Stmt.Ssequence
      (Stmt.Scall none
        (Expr.Evar _memset (Ty.Tfunction [(tptr tvoid), tint, tulong]
                             (tptr tvoid) cc_default))
        [(Expr.Eaddrof (Expr.Evar _match (Ty.Tstruct _url_conn_match noattr))
           (tptr (Ty.Tstruct _url_conn_match noattr))),
         (Expr.Econst_int (Integers.Int.repr 0) tint),
         (Expr.Esizeof (Ty.Tstruct _url_conn_match noattr) tulong)])
      (Stmt.Ssequence
        (Stmt.Sassign
          (Expr.Efield (Expr.Evar _match (Ty.Tstruct _url_conn_match noattr))
            _data (tptr (Ty.Tstruct _Curl_easy noattr)))
          (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))))
        (Stmt.Ssequence
          (Stmt.Sassign
            (Expr.Efield
              (Expr.Evar _match (Ty.Tstruct _url_conn_match noattr)) _needle
              (tptr (Ty.Tstruct _connectdata noattr)))
            (Expr.Etempvar _needle (tptr (Ty.Tstruct _connectdata noattr))))
          (Stmt.Ssequence
            (Stmt.Ssequence
              (Stmt.Scall (some _t'2)
                (Expr.Evar _Curl_pgrs_now (Ty.Tfunction
                                            [(tptr (Ty.Tstruct _Curl_easy noattr))]
                                            (tptr (Ty.Tstruct _curltime noattr))
                                            cc_default))
                [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))])
              (Stmt.Sassign
                (Expr.Efield
                  (Expr.Evar _match (Ty.Tstruct _url_conn_match noattr)) _now
                  (Ty.Tstruct _curltime noattr))
                (Expr.Ederef
                  (Expr.Etempvar _t'2 (tptr (Ty.Tstruct _curltime noattr)))
                  (Ty.Tstruct _curltime noattr))))
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Scall (some _t'3)
                  (Expr.Evar _xfer_may_multiplex (Ty.Tfunction
                                                   [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                    (tptr (Ty.Tstruct _connectdata noattr))]
                                                   tbool cc_default))
                  [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                   (Expr.Etempvar _needle (tptr (Ty.Tstruct _connectdata noattr)))])
                (Stmt.Sassign
                  (Expr.Efield
                    (Expr.Evar _match (Ty.Tstruct _url_conn_match noattr))
                    _may_multiplex tint) (Expr.Etempvar _t'3 tbool)))
              (Stmt.Ssequence
                (Stmt.Scall none
                  (Expr.Evar _Curl_cpool_prune_dead (Ty.Tfunction
                                                      [(tptr (Ty.Tstruct _cpool noattr)),
                                                       (tptr (Ty.Tstruct _Curl_easy noattr))]
                                                      tvoid cc_default))
                  [(Expr.Etempvar _cpool__1 (tptr (Ty.Tstruct _cpool noattr))),
                   (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))])
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sset _t'10
                        (Expr.Efield
                          (Expr.Efield
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                (Ty.Tstruct _Curl_easy noattr)) _state
                              (Ty.Tstruct _UrlState noattr)) _authhost
                            (Ty.Tstruct _auth noattr)) _want tuint))
                      (Stmt.Sifthenelse (Expr.Ebinop Binop.Oand
                                          (Expr.Etempvar _t'10 tuint)
                                          (Expr.Ebinop Binop.Oshl
                                            (Expr.Ecast
                                              (Expr.Econst_int (Integers.Int.repr 1) tint)
                                              tulong)
                                            (Expr.Econst_int (Integers.Int.repr 2) tint)
                                            tulong) tulong)
                        (Stmt.Ssequence
                          (Stmt.Sset _t'11
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _needle (tptr (Ty.Tstruct _connectdata noattr)))
                                (Ty.Tstruct _connectdata noattr)) _scheme
                              (tptr (Ty.Tstruct _Curl_scheme noattr))))
                          (Stmt.Ssequence
                            (Stmt.Sset _t'12
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _t'11 (tptr (Ty.Tstruct _Curl_scheme noattr)))
                                  (Ty.Tstruct _Curl_scheme noattr)) _protocol
                                tlong))
                            (Stmt.Sset _t'4
                              (Expr.Ecast
                                (Expr.Ebinop Binop.Oand
                                  (Expr.Etempvar _t'12 tlong)
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
                                          tlong) tlong)
                                      (Expr.Ebinop Binop.Oshl
                                        (Expr.Econst_long (Integers.Int64.repr 1) tlong)
                                        (Expr.Econst_int (Integers.Int.repr 30) tint)
                                        tlong) tlong)
                                    (Expr.Ebinop Binop.Oshl
                                      (Expr.Ecast
                                        (Expr.Econst_int (Integers.Int.repr 1) tint)
                                        tlong)
                                      (Expr.Econst_int (Integers.Int.repr 31) tint)
                                      tlong) tlong) tlong) tbool))))
                        (Stmt.Sset _t'4
                          (Expr.Econst_int (Integers.Int.repr 0) tint))))
                    (Stmt.Sassign
                      (Expr.Efield
                        (Expr.Evar _match (Ty.Tstruct _url_conn_match noattr))
                        _want_nego_http tint) (Expr.Etempvar _t'4 tint)))
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sset _t'9
                        (Expr.Efield
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                              (Ty.Tstruct _Curl_easy noattr)) _set
                            (Ty.Tstruct _UserDefined noattr)) _use_ssl
                          tuchar))
                      (Stmt.Sassign
                        (Expr.Efield
                          (Expr.Evar _match (Ty.Tstruct _url_conn_match noattr))
                          _require_tls tint)
                        (Expr.Ebinop Binop.Oge (Expr.Etempvar _t'9 tuchar)
                          (Expr.Econst_long (Integers.Int64.repr 2) tlong)
                          tint)))
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Sset _t'8
                          (Expr.Efield
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                (Ty.Tstruct _Curl_easy noattr)) _set
                              (Ty.Tstruct _UserDefined noattr)) _use_ssl
                            tuchar))
                        (Stmt.Sassign
                          (Expr.Efield
                            (Expr.Evar _match (Ty.Tstruct _url_conn_match noattr))
                            _may_tls tint)
                          (Expr.Ebinop Binop.Ogt (Expr.Etempvar _t'8 tuchar)
                            (Expr.Econst_long (Integers.Int64.repr 0) tlong)
                            tint)))
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'7
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _needle (tptr (Ty.Tstruct _connectdata noattr)))
                                  (Ty.Tstruct _connectdata noattr))
                                _destination (tptr tschar)))
                            (Stmt.Scall (some _t'5)
                              (Expr.Evar _Curl_cpool_find (Ty.Tfunction
                                                            [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                             (tptr tschar),
                                                             (tptr (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _connectdata noattr)),
                                                                    (tptr tvoid)]
                                                                    tbool
                                                                    cc_default)),
                                                             (tptr (Ty.Tfunction
                                                                    [(tptr tvoid)]
                                                                    tbool
                                                                    cc_default)),
                                                             (tptr tvoid)]
                                                            tbool cc_default))
                              [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                               (Expr.Etempvar _t'7 (tptr tschar)),
                               (Expr.Evar _url_match_conn (Ty.Tfunction
                                                            [(tptr (Ty.Tstruct _connectdata noattr)),
                                                             (tptr tvoid)]
                                                            tbool cc_default)),
                               (Expr.Evar _url_match_result (Ty.Tfunction
                                                              [(tptr tvoid)]
                                                              tbool
                                                              cc_default)),
                               (Expr.Eaddrof
                                 (Expr.Evar _match (Ty.Tstruct _url_conn_match noattr))
                                 (tptr (Ty.Tstruct _url_conn_match noattr)))]))
                          (Stmt.Sset _success
                            (Expr.Ecast (Expr.Etempvar _t'5 tbool) tbool)))
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'6
                              (Expr.Efield
                                (Expr.Evar _match (Ty.Tstruct _url_conn_match noattr))
                                _wait_pipe tint))
                            (Stmt.Sassign
                              (Expr.Ederef
                                (Expr.Etempvar _waitpipe (tptr tbool)) tbool)
                              (Expr.Ecast (Expr.Etempvar _t'6 tint) tbool)))
                          (Stmt.Sreturn (some (Expr.Etempvar _success tbool))))))))))))))))
}

def v_case2_keep : GlobVar Ty := {
  gvar_info := (tarray (tptr tvoid) 2),
  gvar_init := [(InitData.Init_addrof _url_match_auth_nego (Integers.Ptrofs.repr 0)),
                (InitData.Init_addrof _url_attach_existing (Integers.Ptrofs.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def composites : List CompositeDef :=
[(CompositeDef.Composite _Curl_scheme SU.Struct
   [(Member.Member_plain _protocol tlong)]
   noattr),
 (CompositeDef.Composite _connectdata SU.Struct
   [(Member.Member_plain _creds (tptr (Ty.Tstruct _Curl_creds noattr))),
    (Member.Member_plain _creds_origin (tptr (Ty.Tstruct _Curl_peer noattr))),
    (Member.Member_plain _scheme (tptr (Ty.Tstruct _Curl_scheme noattr))),
    (Member.Member_plain _destination (tptr tschar)),
    (Member.Member_plain _http_negotiate_state tint),
    (Member.Member_plain _proxy_negotiate_state tint)]
   noattr),
 (CompositeDef.Composite _auth SU.Struct
   [(Member.Member_plain _want tuint)]
   noattr),
 (CompositeDef.Composite _UrlState SU.Struct
   [(Member.Member_plain _origin (tptr (Ty.Tstruct _Curl_peer noattr))),
    (Member.Member_plain _authhost (Ty.Tstruct _auth noattr)),
    (Member.Member_plain _creds (tptr (Ty.Tstruct _Curl_creds noattr)))]
   noattr),
 (CompositeDef.Composite _UserDefined SU.Struct
   [(Member.Member_plain _use_ssl tuchar)]
   noattr),
 (CompositeDef.Composite _Curl_easy SU.Struct
   [(Member.Member_plain _set (Ty.Tstruct _UserDefined noattr)),
    (Member.Member_plain _state (Ty.Tstruct _UrlState noattr))]
   noattr),
 (CompositeDef.Composite _curltime SU.Struct
   [(Member.Member_plain _tv_sec tlong), (Member.Member_plain _tv_usec tint)]
   noattr),
 (CompositeDef.Composite _url_conn_match SU.Struct
   [(Member.Member_plain _found (tptr (Ty.Tstruct _connectdata noattr))),
    (Member.Member_plain _data (tptr (Ty.Tstruct _Curl_easy noattr))),
    (Member.Member_plain _needle (tptr (Ty.Tstruct _connectdata noattr))),
    (Member.Member_plain _now (Ty.Tstruct _curltime noattr)),
    (Member.Member_bitfield _may_multiplex IntSize.I32 Signedness.Unsigned
      noattr 1 false),
    (Member.Member_bitfield _want_nego_http IntSize.I32 Signedness.Unsigned
      noattr 1 false),
    (Member.Member_bitfield _want_proxy_nego_http IntSize.I32
      Signedness.Unsigned noattr 1 false),
    (Member.Member_bitfield _may_tls IntSize.I32 Signedness.Unsigned noattr 1
      false),
    (Member.Member_bitfield _require_tls IntSize.I32 Signedness.Unsigned
      noattr 1 false),
    (Member.Member_bitfield _wait_pipe IntSize.I32 Signedness.Unsigned noattr
      1 false),
    (Member.Member_bitfield _force_reuse IntSize.I32 Signedness.Unsigned
      noattr 1 false)]
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
 (_memset,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "memset"
                                   (mksignature
                                     [XType.Xptr, XType.Xint, XType.Xlong]
                                     XType.Xptr cc_default))
     [(tptr tvoid), tint, tulong] (tptr tvoid) cc_default)),
 (_Curl_creds_same,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_creds_same"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xbool cc_default))
     [(tptr (Ty.Tstruct _Curl_creds noattr)),
      (tptr (Ty.Tstruct _Curl_creds noattr))] tbool cc_default)),
 (_Curl_peer_equal,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_peer_equal"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xbool cc_default))
     [(tptr (Ty.Tstruct _Curl_peer noattr)),
      (tptr (Ty.Tstruct _Curl_peer noattr))] tbool cc_default)),
 (_Curl_cpool_get_instance,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_cpool_get_instance"
                                   (mksignature [XType.Xptr] XType.Xptr
                                     cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr))]
     (tptr (Ty.Tstruct _cpool noattr)) cc_default)),
 (_Curl_pgrs_now,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_pgrs_now"
                                   (mksignature [XType.Xptr] XType.Xptr
                                     cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr))]
     (tptr (Ty.Tstruct _curltime noattr)) cc_default)),
 (_Curl_cpool_prune_dead,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_cpool_prune_dead"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xvoid cc_default))
     [(tptr (Ty.Tstruct _cpool noattr)),
      (tptr (Ty.Tstruct _Curl_easy noattr))] tvoid cc_default)),
 (_Curl_cpool_find,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_cpool_find"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xptr,
                                      XType.Xptr, XType.Xptr] XType.Xbool
                                     cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar),
      (tptr (Ty.Tfunction
              [(tptr (Ty.Tstruct _connectdata noattr)), (tptr tvoid)] tbool
              cc_default)),
      (tptr (Ty.Tfunction [(tptr tvoid)] tbool cc_default)), (tptr tvoid)]
     tbool cc_default)),
 (_xfer_may_multiplex,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "xfer_may_multiplex"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xbool cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)),
      (tptr (Ty.Tstruct _connectdata noattr))] tbool cc_default)),
 (_url_match_conn,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "url_match_conn"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xbool cc_default))
     [(tptr (Ty.Tstruct _connectdata noattr)), (tptr tvoid)] tbool
     cc_default)),
 (_url_match_result,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "url_match_result"
                                   (mksignature [XType.Xptr] XType.Xbool
                                     cc_default)) [(tptr tvoid)] tbool
     cc_default)),
 (_url_match_auth_nego, GlobDef.Gfun (FunDef.Internal f_url_match_auth_nego)),
 (_url_attach_existing, GlobDef.Gfun (FunDef.Internal f_url_attach_existing)),
 (_case2_keep, GlobDef.Gvar v_case2_keep)]

def public_idents : List Ident :=
[_case2_keep, _url_match_result, _url_match_conn, _xfer_may_multiplex,
 _Curl_cpool_find, _Curl_cpool_prune_dead, _Curl_pgrs_now,
 _Curl_cpool_get_instance, _Curl_peer_equal, _Curl_creds_same, _memset,
 ___builtin_debug, ___builtin_fmin, ___builtin_fmax, ___builtin_fnmsub,
 ___builtin_fnmadd, ___builtin_fmsub, ___builtin_fmadd, ___builtin_clsll,
 ___builtin_clsl, ___builtin_cls, ___builtin_expect, ___builtin_unreachable,
 ___builtin_va_end, ___builtin_va_copy, ___builtin_va_arg,
 ___builtin_va_start, ___builtin_membar, ___builtin_annot_intval,
 ___builtin_annot, ___builtin_sel, ___builtin_memcpy_aligned,
 ___builtin_sqrt, ___builtin_fsqrt, ___builtin_fabsf, ___builtin_fabs,
 ___builtin_ctzll, ___builtin_ctzl, ___builtin_ctz, ___builtin_clzll,
 ___builtin_clzl, ___builtin_clz, ___builtin_bswap16, ___builtin_bswap32,
 ___builtin_bswap, ___builtin_bswap64, ___compcert_i64_umulh,
 ___compcert_i64_smulh, ___compcert_i64_sar, ___compcert_i64_shr,
 ___compcert_i64_shl, ___compcert_i64_umod, ___compcert_i64_smod,
 ___compcert_i64_udiv, ___compcert_i64_sdiv, ___compcert_i64_utof,
 ___compcert_i64_stof, ___compcert_i64_utod, ___compcert_i64_stod,
 ___compcert_i64_dtou, ___compcert_i64_dtos, ___compcert_va_composite,
 ___compcert_va_float64, ___compcert_va_int64, ___compcert_va_int32]

def prog : Program :=
  mkprogram composites global_definitions public_idents _main

end Case2_before

