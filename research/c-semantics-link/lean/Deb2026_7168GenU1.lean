import Clightdefs
open CC

namespace Deb2026_7168_u1

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
  def source_file : String := "deb2026_7168_u1.c"
  def normalized : Bool := true
end Info

def _Curl_auth_digest_cleanup : Ident := identOfString "Curl_auth_digest_cleanup"
def _Curl_easy : Ident := identOfString "Curl_easy"
def _Curl_setstropt : Ident := identOfString "Curl_setstropt"
def _Curl_ssl_supports : Ident := identOfString "Curl_ssl_supports"
def _Curl_urldecode : Ident := identOfString "Curl_urldecode"
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
def _authproxy : Ident := identOfString "authproxy"
def _curlx_free : Ident := identOfString "curlx_free"
def _custom_cafile : Ident := identOfString "custom_cafile"
def _custom_capath : Ident := identOfString "custom_capath"
def _data : Ident := identOfString "data"
def _deb_keep : Ident := identOfString "deb_keep"
def _digestdata : Ident := identOfString "digestdata"
def _haproxyprotocol : Ident := identOfString "haproxyprotocol"
def _main : Ident := identOfString "main"
def _memset : Ident := identOfString "memset"
def _nonce : Ident := identOfString "nonce"
def _option : Ident := identOfString "option"
def _p : Ident := identOfString "p"
def _picked : Ident := identOfString "picked"
def _proxy : Ident := identOfString "proxy"
def _proxy_ssl : Ident := identOfString "proxy_ssl"
def _proxydigest : Ident := identOfString "proxydigest"
def _ptr : Ident := identOfString "ptr"
def _result : Ident := identOfString "result"
def _s : Ident := identOfString "s"
def _set : Ident := identOfString "set"
def _setopt_cptr_proxy : Ident := identOfString "setopt_cptr_proxy"
def _setproxy : Ident := identOfString "setproxy"
def _setstropt_userpwd : Ident := identOfString "setstropt_userpwd"
def _ssl_config_data : Ident := identOfString "ssl_config_data"
def _state : Ident := identOfString "state"
def _str : Ident := identOfString "str"
def _strcmp : Ident := identOfString "strcmp"
def _u : Ident := identOfString "u"
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
def _t'4 : Ident := (Positive.ofNat 131)
def _t'5 : Ident := (Positive.ofNat 132)
def _t'6 : Ident := (Positive.ofNat 133)
def _t'7 : Ident := (Positive.ofNat 134)
def _t'8 : Ident := (Positive.ofNat 135)
def _t'9 : Ident := (Positive.ofNat 136)

def f_setproxy : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_proxy, (tptr tschar))],
  fn_vars := [],
  fn_temps := [(_t'4, tint), (_t'3, tint), (_t'2, tint), (_t'1, tint),
               (_t'6, (tptr tschar)), (_t'5, (tptr tschar))],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Ssequence
        (Stmt.Sset _t'6
          (Expr.Ederef
            (Expr.Ebinop Binop.Oadd
              (Expr.Efield
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                    (Ty.Tstruct _Curl_easy noattr)) _set
                  (Ty.Tstruct _UserDefined noattr)) _str
                (tarray (tptr tschar) 55))
              (Expr.Econst_int (Integers.Int.repr 32) tint)
              (tptr (tptr tschar))) (tptr tschar)))
        (Stmt.Sifthenelse (Expr.Etempvar _t'6 (tptr tschar))
          (Stmt.Sset _t'1
            (Expr.Ecast (Expr.Etempvar _proxy (tptr tschar)) tbool))
          (Stmt.Sset _t'1 (Expr.Econst_int (Integers.Int.repr 0) tint))))
      (Stmt.Sifthenelse (Expr.Etempvar _t'1 tint)
        (Stmt.Ssequence
          (Stmt.Ssequence
            (Stmt.Sset _t'5
              (Expr.Ederef
                (Expr.Ebinop Binop.Oadd
                  (Expr.Efield
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                        (Ty.Tstruct _Curl_easy noattr)) _set
                      (Ty.Tstruct _UserDefined noattr)) _str
                    (tarray (tptr tschar) 55))
                  (Expr.Econst_int (Integers.Int.repr 32) tint)
                  (tptr (tptr tschar))) (tptr tschar)))
            (Stmt.Scall (some _t'3)
              (Expr.Evar _strcmp (Ty.Tfunction [(tptr tschar), (tptr tschar)]
                                   tint cc_default))
              [(Expr.Etempvar _t'5 (tptr tschar)),
               (Expr.Etempvar _proxy (tptr tschar))]))
          (Stmt.Sset _t'2
            (Expr.Ecast
              (Expr.Eunop Unop.Onotbool (Expr.Etempvar _t'3 tint) tint)
              tbool)))
        (Stmt.Sset _t'2 (Expr.Econst_int (Integers.Int.repr 0) tint))))
    (Stmt.Sifthenelse (Expr.Etempvar _t'2 tint)
      (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint)))
      Stmt.Sskip))
  (Stmt.Ssequence
    (Stmt.Scall none
      (Expr.Evar _Curl_auth_digest_cleanup (Ty.Tfunction
                                             [(tptr (Ty.Tstruct _digestdata noattr))]
                                             tvoid cc_default))
      [(Expr.Eaddrof
         (Expr.Efield
           (Expr.Efield
             (Expr.Ederef
               (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
               (Ty.Tstruct _Curl_easy noattr)) _state
             (Ty.Tstruct _UrlState noattr)) _proxydigest
           (Ty.Tstruct _digestdata noattr))
         (tptr (Ty.Tstruct _digestdata noattr)))])
    (Stmt.Ssequence
      (Stmt.Scall none
        (Expr.Evar _memset (Ty.Tfunction [(tptr tvoid), tint, tulong]
                             (tptr tvoid) cc_default))
        [(Expr.Eaddrof
           (Expr.Efield
             (Expr.Efield
               (Expr.Ederef
                 (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                 (Ty.Tstruct _Curl_easy noattr)) _state
               (Ty.Tstruct _UrlState noattr)) _authproxy
             (Ty.Tstruct _auth noattr)) (tptr (Ty.Tstruct _auth noattr))),
         (Expr.Econst_int (Integers.Int.repr 0) tint),
         (Expr.Esizeof (Ty.Tstruct _auth noattr) tulong)])
      (Stmt.Ssequence
        (Stmt.Scall (some _t'4)
          (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                       [(tptr (tptr tschar)), (tptr tschar)]
                                       tint cc_default))
          [(Expr.Ebinop Binop.Oadd
             (Expr.Efield
               (Expr.Efield
                 (Expr.Ederef
                   (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                   (Ty.Tstruct _Curl_easy noattr)) _set
                 (Ty.Tstruct _UserDefined noattr)) _str
               (tarray (tptr tschar) 55))
             (Expr.Econst_int (Integers.Int.repr 32) tint)
             (tptr (tptr tschar))), (Expr.Etempvar _proxy (tptr tschar))])
        (Stmt.Sreturn (some (Expr.Etempvar _t'4 tint)))))))
}

def f_setopt_cptr_proxy : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_option, tint), (_ptr, (tptr tschar))],
  fn_vars := [(_u, (tptr tschar)), (_p, (tptr tschar))],
  fn_temps := [(_result, tint),
               (_s, (tptr (Ty.Tstruct _UserDefined noattr))), (_t'28, tbool),
               (_t'27, tint), (_t'26, tint), (_t'25, tint), (_t'24, tint),
               (_t'23, tint), (_t'22, tbool), (_t'21, tint), (_t'20, tint),
               (_t'19, tint), (_t'18, tint), (_t'17, tbool), (_t'16, tint),
               (_t'15, tbool), (_t'14, tint), (_t'13, tint), (_t'12, tint),
               (_t'11, tint), (_t'10, tint), (_t'9, tint), (_t'8, tint),
               (_t'7, tint), (_t'6, tint), (_t'5, tint), (_t'4, tint),
               (_t'3, tint), (_t'2, tint), (_t'1, tint),
               (_t'37, (tptr tschar)), (_t'36, (tptr tschar)),
               (_t'35, (tptr tschar)), (_t'34, (tptr tschar)),
               (_t'33, (tptr tschar)), (_t'32, (tptr tschar)),
               (_t'31, (tptr tschar)), (_t'30, (tptr tschar)),
               (_t'29, (tptr tschar))],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Sset _result (Expr.Econst_int (Integers.Int.repr 0) tint))
  (Stmt.Ssequence
    (Stmt.Sset _s
      (Expr.Eaddrof
        (Expr.Efield
          (Expr.Ederef
            (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
            (Ty.Tstruct _Curl_easy noattr)) _set
          (Ty.Tstruct _UserDefined noattr))
        (tptr (Ty.Tstruct _UserDefined noattr))))
    (Stmt.Ssequence
      (Stmt.Sswitch (Expr.Etempvar _option tint)
        (LStmts.LScons (some 10006)
          (Stmt.Ssequence
            (Stmt.Sassign (Expr.Evar _u (tptr tschar))
              (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint)
                (tptr tvoid)))
            (Stmt.Ssequence
              (Stmt.Sassign (Expr.Evar _p (tptr tschar))
                (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint)
                  (tptr tvoid)))
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Scall (some _t'1)
                    (Expr.Evar _setstropt_userpwd (Ty.Tfunction
                                                    [(tptr tschar),
                                                     (tptr (tptr tschar)),
                                                     (tptr (tptr tschar))]
                                                    tint cc_default))
                    [(Expr.Etempvar _ptr (tptr tschar)),
                     (Expr.Eaddrof (Expr.Evar _u (tptr tschar))
                       (tptr (tptr tschar))),
                     (Expr.Eaddrof (Expr.Evar _p (tptr tschar))
                       (tptr (tptr tschar)))])
                  (Stmt.Sset _result (Expr.Etempvar _t'1 tint)))
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                        (Expr.Etempvar _result tint) tint)
                      (Stmt.Ssequence
                        (Stmt.Sset _t'37 (Expr.Evar _u (tptr tschar)))
                        (Stmt.Sset _t'3
                          (Expr.Ecast (Expr.Etempvar _t'37 (tptr tschar))
                            tbool)))
                      (Stmt.Sset _t'3
                        (Expr.Econst_int (Integers.Int.repr 0) tint)))
                    (Stmt.Sifthenelse (Expr.Etempvar _t'3 tint)
                      (Stmt.Ssequence
                        (Stmt.Sloop
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Sset _t'36
                                (Expr.Ederef
                                  (Expr.Ebinop Binop.Oadd
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                        (Ty.Tstruct _UserDefined noattr))
                                      _str (tarray (tptr tschar) 55))
                                    (Expr.Econst_int (Integers.Int.repr 42) tint)
                                    (tptr (tptr tschar))) (tptr tschar)))
                              (Stmt.Scall none
                                (Expr.Evar _curlx_free (Ty.Tfunction
                                                         [(tptr tvoid)] tvoid
                                                         cc_default))
                                [(Expr.Etempvar _t'36 (tptr tschar))]))
                            (Stmt.Sassign
                              (Expr.Ederef
                                (Expr.Ebinop Binop.Oadd
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                      (Ty.Tstruct _UserDefined noattr)) _str
                                    (tarray (tptr tschar) 55))
                                  (Expr.Econst_int (Integers.Int.repr 42) tint)
                                  (tptr (tptr tschar))) (tptr tschar))
                              (Expr.Ecast
                                (Expr.Econst_int (Integers.Int.repr 0) tint)
                                (tptr tvoid))))
                          Stmt.Sbreak)
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'35 (Expr.Evar _u (tptr tschar)))
                            (Stmt.Scall (some _t'2)
                              (Expr.Evar _Curl_urldecode (Ty.Tfunction
                                                           [(tptr tschar),
                                                            tulong,
                                                            (tptr (tptr tschar)),
                                                            (tptr tulong),
                                                            tint] tint
                                                           cc_default))
                              [(Expr.Etempvar _t'35 (tptr tschar)),
                               (Expr.Econst_int (Integers.Int.repr 0) tint),
                               (Expr.Ebinop Binop.Oadd
                                 (Expr.Efield
                                   (Expr.Ederef
                                     (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                     (Ty.Tstruct _UserDefined noattr)) _str
                                   (tarray (tptr tschar) 55))
                                 (Expr.Econst_int (Integers.Int.repr 42) tint)
                                 (tptr (tptr tschar))),
                               (Expr.Ecast
                                 (Expr.Econst_int (Integers.Int.repr 0) tint)
                                 (tptr tvoid)),
                               (Expr.Econst_int (Integers.Int.repr 4) tint)]))
                          (Stmt.Sset _result (Expr.Etempvar _t'2 tint))))
                      Stmt.Sskip))
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                          (Expr.Etempvar _result tint) tint)
                        (Stmt.Ssequence
                          (Stmt.Sset _t'34 (Expr.Evar _p (tptr tschar)))
                          (Stmt.Sset _t'5
                            (Expr.Ecast (Expr.Etempvar _t'34 (tptr tschar))
                              tbool)))
                        (Stmt.Sset _t'5
                          (Expr.Econst_int (Integers.Int.repr 0) tint)))
                      (Stmt.Sifthenelse (Expr.Etempvar _t'5 tint)
                        (Stmt.Ssequence
                          (Stmt.Sloop
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Sset _t'33
                                  (Expr.Ederef
                                    (Expr.Ebinop Binop.Oadd
                                      (Expr.Efield
                                        (Expr.Ederef
                                          (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                          (Ty.Tstruct _UserDefined noattr))
                                        _str (tarray (tptr tschar) 55))
                                      (Expr.Econst_int (Integers.Int.repr 43) tint)
                                      (tptr (tptr tschar))) (tptr tschar)))
                                (Stmt.Scall none
                                  (Expr.Evar _curlx_free (Ty.Tfunction
                                                           [(tptr tvoid)]
                                                           tvoid cc_default))
                                  [(Expr.Etempvar _t'33 (tptr tschar))]))
                              (Stmt.Sassign
                                (Expr.Ederef
                                  (Expr.Ebinop Binop.Oadd
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                        (Ty.Tstruct _UserDefined noattr))
                                      _str (tarray (tptr tschar) 55))
                                    (Expr.Econst_int (Integers.Int.repr 43) tint)
                                    (tptr (tptr tschar))) (tptr tschar))
                                (Expr.Ecast
                                  (Expr.Econst_int (Integers.Int.repr 0) tint)
                                  (tptr tvoid))))
                            Stmt.Sbreak)
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Sset _t'32 (Expr.Evar _p (tptr tschar)))
                              (Stmt.Scall (some _t'4)
                                (Expr.Evar _Curl_urldecode (Ty.Tfunction
                                                             [(tptr tschar),
                                                              tulong,
                                                              (tptr (tptr tschar)),
                                                              (tptr tulong),
                                                              tint] tint
                                                             cc_default))
                                [(Expr.Etempvar _t'32 (tptr tschar)),
                                 (Expr.Econst_int (Integers.Int.repr 0) tint),
                                 (Expr.Ebinop Binop.Oadd
                                   (Expr.Efield
                                     (Expr.Ederef
                                       (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                       (Ty.Tstruct _UserDefined noattr)) _str
                                     (tarray (tptr tschar) 55))
                                   (Expr.Econst_int (Integers.Int.repr 43) tint)
                                   (tptr (tptr tschar))),
                                 (Expr.Ecast
                                   (Expr.Econst_int (Integers.Int.repr 0) tint)
                                   (tptr tvoid)),
                                 (Expr.Econst_int (Integers.Int.repr 4) tint)]))
                            (Stmt.Sset _result (Expr.Etempvar _t'4 tint))))
                        Stmt.Sskip))
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Sset _t'31 (Expr.Evar _u (tptr tschar)))
                        (Stmt.Scall none
                          (Expr.Evar _curlx_free (Ty.Tfunction [(tptr tvoid)]
                                                   tvoid cc_default))
                          [(Expr.Etempvar _t'31 (tptr tschar))]))
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Sset _t'30 (Expr.Evar _p (tptr tschar)))
                          (Stmt.Scall none
                            (Expr.Evar _curlx_free (Ty.Tfunction
                                                     [(tptr tvoid)] tvoid
                                                     cc_default))
                            [(Expr.Etempvar _t'30 (tptr tschar))]))
                        Stmt.Sbreak)))))))
          (LStmts.LScons (some 10175)
            (Stmt.Ssequence
              (Stmt.Scall (some _t'6)
                (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                             [(tptr (tptr tschar)),
                                              (tptr tschar)] tint cc_default))
                [(Expr.Ebinop Binop.Oadd
                   (Expr.Efield
                     (Expr.Ederef
                       (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                       (Ty.Tstruct _UserDefined noattr)) _str
                     (tarray (tptr tschar) 55))
                   (Expr.Econst_int (Integers.Int.repr 42) tint)
                   (tptr (tptr tschar))), (Expr.Etempvar _ptr (tptr tschar))])
              (Stmt.Sreturn (some (Expr.Etempvar _t'6 tint))))
            (LStmts.LScons (some 10176)
              (Stmt.Ssequence
                (Stmt.Scall (some _t'7)
                  (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                               [(tptr (tptr tschar)),
                                                (tptr tschar)] tint
                                               cc_default))
                  [(Expr.Ebinop Binop.Oadd
                     (Expr.Efield
                       (Expr.Ederef
                         (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                         (Ty.Tstruct _UserDefined noattr)) _str
                       (tarray (tptr tschar) 55))
                     (Expr.Econst_int (Integers.Int.repr 43) tint)
                     (tptr (tptr tschar))),
                   (Expr.Etempvar _ptr (tptr tschar))])
                (Stmt.Sreturn (some (Expr.Etempvar _t'7 tint))))
              (LStmts.LScons (some 10177)
                (Stmt.Ssequence
                  (Stmt.Scall (some _t'8)
                    (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                 [(tptr (tptr tschar)),
                                                  (tptr tschar)] tint
                                                 cc_default))
                    [(Expr.Ebinop Binop.Oadd
                       (Expr.Efield
                         (Expr.Ederef
                           (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                           (Ty.Tstruct _UserDefined noattr)) _str
                         (tarray (tptr tschar) 55))
                       (Expr.Econst_int (Integers.Int.repr 44) tint)
                       (tptr (tptr tschar))),
                     (Expr.Etempvar _ptr (tptr tschar))])
                  (Stmt.Sreturn (some (Expr.Etempvar _t'8 tint))))
                (LStmts.LScons (some 10254)
                  (Stmt.Ssequence
                    (Stmt.Scall (some _t'9)
                      (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                   [(tptr (tptr tschar)),
                                                    (tptr tschar)] tint
                                                   cc_default))
                      [(Expr.Ebinop Binop.Oadd
                         (Expr.Efield
                           (Expr.Ederef
                             (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                             (Ty.Tstruct _UserDefined noattr)) _str
                           (tarray (tptr tschar) 55))
                         (Expr.Econst_int (Integers.Int.repr 13) tint)
                         (tptr (tptr tschar))),
                       (Expr.Etempvar _ptr (tptr tschar))])
                    (Stmt.Sreturn (some (Expr.Etempvar _t'9 tint))))
                  (LStmts.LScons (some 10255)
                    (Stmt.Ssequence
                      (Stmt.Scall (some _t'10)
                        (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                     [(tptr (tptr tschar)),
                                                      (tptr tschar)] tint
                                                     cc_default))
                        [(Expr.Ebinop Binop.Oadd
                           (Expr.Efield
                             (Expr.Ederef
                               (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                               (Ty.Tstruct _UserDefined noattr)) _str
                             (tarray (tptr tschar) 55))
                           (Expr.Econst_int (Integers.Int.repr 14) tint)
                           (tptr (tptr tschar))),
                         (Expr.Etempvar _ptr (tptr tschar))])
                      (Stmt.Sreturn (some (Expr.Etempvar _t'10 tint))))
                    (LStmts.LScons (some 10256)
                      (Stmt.Ssequence
                        (Stmt.Scall (some _t'11)
                          (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                       [(tptr (tptr tschar)),
                                                        (tptr tschar)] tint
                                                       cc_default))
                          [(Expr.Ebinop Binop.Oadd
                             (Expr.Efield
                               (Expr.Ederef
                                 (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                 (Ty.Tstruct _UserDefined noattr)) _str
                               (tarray (tptr tschar) 55))
                             (Expr.Econst_int (Integers.Int.repr 15) tint)
                             (tptr (tptr tschar))),
                           (Expr.Etempvar _ptr (tptr tschar))])
                        (Stmt.Sreturn (some (Expr.Etempvar _t'11 tint))))
                      (LStmts.LScons (some 10258)
                        (Stmt.Ssequence
                          (Stmt.Scall (some _t'12)
                            (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                         [(tptr (tptr tschar)),
                                                          (tptr tschar)] tint
                                                         cc_default))
                            [(Expr.Ebinop Binop.Oadd
                               (Expr.Efield
                                 (Expr.Ederef
                                   (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                   (Ty.Tstruct _UserDefined noattr)) _str
                                 (tarray (tptr tschar) 55))
                               (Expr.Econst_int (Integers.Int.repr 16) tint)
                               (tptr (tptr tschar))),
                             (Expr.Etempvar _ptr (tptr tschar))])
                          (Stmt.Sreturn (some (Expr.Etempvar _t'12 tint))))
                        (LStmts.LScons (some 10257)
                          (Stmt.Ssequence
                            (Stmt.Scall (some _t'13)
                              (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                           [(tptr (tptr tschar)),
                                                            (tptr tschar)]
                                                           tint cc_default))
                              [(Expr.Ebinop Binop.Oadd
                                 (Expr.Efield
                                   (Expr.Ederef
                                     (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                     (Ty.Tstruct _UserDefined noattr)) _str
                                   (tarray (tptr tschar) 55))
                                 (Expr.Econst_int (Integers.Int.repr 17) tint)
                                 (tptr (tptr tschar))),
                               (Expr.Etempvar _ptr (tptr tschar))])
                            (Stmt.Sreturn (some (Expr.Etempvar _t'13 tint))))
                          (LStmts.LScons (some 10259)
                            (Stmt.Ssequence
                              (Stmt.Scall (some _t'15)
                                (Expr.Evar _Curl_ssl_supports (Ty.Tfunction
                                                                [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                 tuint] tbool
                                                                cc_default))
                                [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                 (Expr.Ebinop Binop.Oshl
                                   (Expr.Econst_int (Integers.Int.repr 1) tint)
                                   (Expr.Econst_int (Integers.Int.repr 9) tint)
                                   tint)])
                              (Stmt.Sifthenelse (Expr.Etempvar _t'15 tbool)
                                (Stmt.Ssequence
                                  (Stmt.Scall (some _t'14)
                                    (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                                 [(tptr (tptr tschar)),
                                                                  (tptr tschar)]
                                                                 tint
                                                                 cc_default))
                                    [(Expr.Ebinop Binop.Oadd
                                       (Expr.Efield
                                         (Expr.Ederef
                                           (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                           (Ty.Tstruct _UserDefined noattr))
                                         _str (tarray (tptr tschar) 55))
                                       (Expr.Econst_int (Integers.Int.repr 21) tint)
                                       (tptr (tptr tschar))),
                                     (Expr.Etempvar _ptr (tptr tschar))])
                                  (Stmt.Sreturn (some (Expr.Etempvar _t'14 tint))))
                                (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint)))))
                            (LStmts.LScons (some 10277)
                              (Stmt.Ssequence
                                (Stmt.Scall (some _t'17)
                                  (Expr.Evar _Curl_ssl_supports (Ty.Tfunction
                                                                  [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                   tuint]
                                                                  tbool
                                                                  cc_default))
                                  [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                   (Expr.Ebinop Binop.Oshl
                                     (Expr.Econst_int (Integers.Int.repr 1) tint)
                                     (Expr.Econst_int (Integers.Int.repr 5) tint)
                                     tint)])
                                (Stmt.Sifthenelse (Expr.Etempvar _t'17 tbool)
                                  (Stmt.Ssequence
                                    (Stmt.Scall (some _t'16)
                                      (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                                   [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                   tint
                                                                   cc_default))
                                      [(Expr.Ebinop Binop.Oadd
                                         (Expr.Efield
                                           (Expr.Ederef
                                             (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                             (Ty.Tstruct _UserDefined noattr))
                                           _str (tarray (tptr tschar) 55))
                                         (Expr.Econst_int (Integers.Int.repr 22) tint)
                                         (tptr (tptr tschar))),
                                       (Expr.Etempvar _ptr (tptr tschar))])
                                    (Stmt.Sreturn (some (Expr.Etempvar _t'16 tint))))
                                  (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint)))))
                              (LStmts.LScons (some 10004)
                                (Stmt.Ssequence
                                  (Stmt.Scall (some _t'18)
                                    (Expr.Evar _setproxy (Ty.Tfunction
                                                           [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                            (tptr tschar)]
                                                           tint cc_default))
                                    [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                     (Expr.Etempvar _ptr (tptr tschar))])
                                  (Stmt.Sreturn (some (Expr.Etempvar _t'18 tint))))
                                (LStmts.LScons (some 10262)
                                  (Stmt.Ssequence
                                    (Stmt.Scall (some _t'19)
                                      (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                                   [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                   tint
                                                                   cc_default))
                                      [(Expr.Ebinop Binop.Oadd
                                         (Expr.Efield
                                           (Expr.Ederef
                                             (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                             (Ty.Tstruct _UserDefined noattr))
                                           _str (tarray (tptr tschar) 55))
                                         (Expr.Econst_int (Integers.Int.repr 33) tint)
                                         (tptr (tptr tschar))),
                                       (Expr.Etempvar _ptr (tptr tschar))])
                                    (Stmt.Sreturn (some (Expr.Etempvar _t'19 tint))))
                                  (LStmts.LScons (some 10179)
                                    Stmt.Sskip
                                    (LStmts.LScons (some 10235)
                                      (Stmt.Ssequence
                                        (Stmt.Scall (some _t'20)
                                          (Expr.Evar _Curl_setstropt 
                                          (Ty.Tfunction
                                            [(tptr (tptr tschar)),
                                             (tptr tschar)] tint cc_default))
                                          [(Expr.Ebinop Binop.Oadd
                                             (Expr.Efield
                                               (Expr.Ederef
                                                 (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                                 (Ty.Tstruct _UserDefined noattr))
                                               _str
                                               (tarray (tptr tschar) 55))
                                             (Expr.Econst_int (Integers.Int.repr 25) tint)
                                             (tptr (tptr tschar))),
                                           (Expr.Etempvar _ptr (tptr tschar))])
                                        (Stmt.Sreturn (some (Expr.Etempvar _t'20 tint))))
                                      (LStmts.LScons (some 10263)
                                        (Stmt.Ssequence
                                          (Stmt.Ssequence
                                            (Stmt.Scall (some _t'22)
                                              (Expr.Evar _Curl_ssl_supports 
                                              (Ty.Tfunction
                                                [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                 tuint] tbool cc_default))
                                              [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                               (Expr.Ebinop Binop.Oshl
                                                 (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                 (Expr.Econst_int (Integers.Int.repr 2) tint)
                                                 tint)])
                                            (Stmt.Sifthenelse (Expr.Etempvar _t'22 tbool)
                                              (Stmt.Ssequence
                                                (Stmt.Scall (some _t'21)
                                                  (Expr.Evar _Curl_setstropt 
                                                  (Ty.Tfunction
                                                    [(tptr (tptr tschar)),
                                                     (tptr tschar)] tint
                                                    cc_default))
                                                  [(Expr.Ebinop Binop.Oadd
                                                     (Expr.Efield
                                                       (Expr.Ederef
                                                         (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                                         (Ty.Tstruct _UserDefined noattr))
                                                       _str
                                                       (tarray (tptr tschar) 55))
                                                     (Expr.Econst_int (Integers.Int.repr 20) tint)
                                                     (tptr (tptr tschar))),
                                                   (Expr.Etempvar _ptr (tptr tschar))])
                                                (Stmt.Sreturn (some (Expr.Etempvar _t'21 tint))))
                                              Stmt.Sskip))
                                          (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint))))
                                        (LStmts.LScons (some 10323)
                                          (Stmt.Ssequence
                                            (Stmt.Ssequence
                                              (Stmt.Scall (some _t'23)
                                                (Expr.Evar _Curl_setstropt 
                                                (Ty.Tfunction
                                                  [(tptr (tptr tschar)),
                                                   (tptr tschar)] tint
                                                  cc_default))
                                                [(Expr.Ebinop Binop.Oadd
                                                   (Expr.Efield
                                                     (Expr.Ederef
                                                       (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                                       (Ty.Tstruct _UserDefined noattr))
                                                     _str
                                                     (tarray (tptr tschar) 55))
                                                   (Expr.Econst_int (Integers.Int.repr 49) tint)
                                                   (tptr (tptr tschar))),
                                                 (Expr.Etempvar _ptr (tptr tschar))])
                                              (Stmt.Sset _result
                                                (Expr.Etempvar _t'23 tint)))
                                            (Stmt.Ssequence
                                              (Stmt.Ssequence
                                                (Stmt.Sset _t'29
                                                  (Expr.Ederef
                                                    (Expr.Ebinop Binop.Oadd
                                                      (Expr.Efield
                                                        (Expr.Ederef
                                                          (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                                          (Ty.Tstruct _UserDefined noattr))
                                                        _str
                                                        (tarray (tptr tschar) 55))
                                                      (Expr.Econst_int (Integers.Int.repr 49) tint)
                                                      (tptr (tptr tschar)))
                                                    (tptr tschar)))
                                                (Stmt.Sassign
                                                  (Expr.Efield
                                                    (Expr.Ederef
                                                      (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                                      (Ty.Tstruct _UserDefined noattr))
                                                    _haproxyprotocol tint)
                                                  (Expr.Eunop Unop.Onotbool
                                                    (Expr.Eunop Unop.Onotbool
                                                      (Expr.Etempvar _t'29 (tptr tschar))
                                                      tint) tint)))
                                              Stmt.Sbreak))
                                          (LStmts.LScons (some 10246)
                                            (Stmt.Ssequence
                                              (Stmt.Sassign
                                                (Expr.Efield
                                                  (Expr.Efield
                                                    (Expr.Ederef
                                                      (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                                      (Ty.Tstruct _UserDefined noattr))
                                                    _proxy_ssl
                                                    (Ty.Tstruct _ssl_config_data noattr))
                                                  _custom_cafile tint)
                                                (Expr.Econst_int (Integers.Int.repr 1) tint))
                                              (Stmt.Ssequence
                                                (Stmt.Scall (some _t'24)
                                                  (Expr.Evar _Curl_setstropt 
                                                  (Ty.Tfunction
                                                    [(tptr (tptr tschar)),
                                                     (tptr tschar)] tint
                                                    cc_default))
                                                  [(Expr.Ebinop Binop.Oadd
                                                     (Expr.Efield
                                                       (Expr.Ederef
                                                         (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                                         (Ty.Tstruct _UserDefined noattr))
                                                       _str
                                                       (tarray (tptr tschar) 55))
                                                     (Expr.Econst_int (Integers.Int.repr 19) tint)
                                                     (tptr (tptr tschar))),
                                                   (Expr.Etempvar _ptr (tptr tschar))])
                                                (Stmt.Sreturn (some (Expr.Etempvar _t'24 tint)))))
                                            (LStmts.LScons (some 10260)
                                              (Stmt.Ssequence
                                                (Stmt.Scall (some _t'25)
                                                  (Expr.Evar _Curl_setstropt 
                                                  (Ty.Tfunction
                                                    [(tptr (tptr tschar)),
                                                     (tptr tschar)] tint
                                                    cc_default))
                                                  [(Expr.Ebinop Binop.Oadd
                                                     (Expr.Efield
                                                       (Expr.Ederef
                                                         (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                                         (Ty.Tstruct _UserDefined noattr))
                                                       _str
                                                       (tarray (tptr tschar) 55))
                                                     (Expr.Econst_int (Integers.Int.repr 23) tint)
                                                     (tptr (tptr tschar))),
                                                   (Expr.Etempvar _ptr (tptr tschar))])
                                                (Stmt.Sreturn (some (Expr.Etempvar _t'25 tint))))
                                              (LStmts.LScons (some 10296)
                                                (Stmt.Ssequence
                                                  (Stmt.Scall (some _t'26)
                                                    (Expr.Evar _Curl_setstropt 
                                                    (Ty.Tfunction
                                                      [(tptr (tptr tschar)),
                                                       (tptr tschar)] tint
                                                      cc_default))
                                                    [(Expr.Ebinop Binop.Oadd
                                                       (Expr.Efield
                                                         (Expr.Ederef
                                                           (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                                           (Ty.Tstruct _UserDefined noattr))
                                                         _str
                                                         (tarray (tptr tschar) 55))
                                                       (Expr.Econst_int (Integers.Int.repr 24) tint)
                                                       (tptr (tptr tschar))),
                                                     (Expr.Etempvar _ptr (tptr tschar))])
                                                  (Stmt.Sreturn (some (Expr.Etempvar _t'26 tint))))
                                                (LStmts.LScons (some 10247)
                                                  (Stmt.Ssequence
                                                    (Stmt.Ssequence
                                                      (Stmt.Scall (some _t'28)
                                                        (Expr.Evar _Curl_ssl_supports 
                                                        (Ty.Tfunction
                                                          [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                           tuint] tbool
                                                          cc_default))
                                                        [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                         (Expr.Ebinop Binop.Oshl
                                                           (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                           (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                           tint)])
                                                      (Stmt.Sifthenelse (Expr.Etempvar _t'28 tbool)
                                                        (Stmt.Ssequence
                                                          (Stmt.Sassign
                                                            (Expr.Efield
                                                              (Expr.Efield
                                                                (Expr.Ederef
                                                                  (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                                                  (Ty.Tstruct _UserDefined noattr))
                                                                _proxy_ssl
                                                                (Ty.Tstruct _ssl_config_data noattr))
                                                              _custom_capath
                                                              tint)
                                                            (Expr.Econst_int (Integers.Int.repr 1) tint))
                                                          (Stmt.Ssequence
                                                            (Stmt.Scall (some _t'27)
                                                              (Expr.Evar _Curl_setstropt 
                                                              (Ty.Tfunction
                                                                [(tptr (tptr tschar)),
                                                                 (tptr tschar)]
                                                                tint
                                                                cc_default))
                                                              [(Expr.Ebinop Binop.Oadd
                                                                 (Expr.Efield
                                                                   (Expr.Ederef
                                                                    (Expr.Etempvar _s (tptr (Ty.Tstruct _UserDefined noattr)))
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                   _str
                                                                   (tarray (tptr tschar) 55))
                                                                 (Expr.Econst_int (Integers.Int.repr 18) tint)
                                                                 (tptr (tptr tschar))),
                                                               (Expr.Etempvar _ptr (tptr tschar))])
                                                            (Stmt.Sreturn (some (Expr.Etempvar _t'27 tint)))))
                                                        Stmt.Sskip))
                                                    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint))))
                                                  (LStmts.LScons none
                                                    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 48) tint)))
                                                    LStmts.LSnil)))))))))))))))))))))))
      (Stmt.Sreturn (some (Expr.Etempvar _result tint))))))
}

def v_deb_keep : GlobVar Ty := {
  gvar_info := (tptr tvoid),
  gvar_init := [(InitData.Init_addrof _setopt_cptr_proxy (Integers.Ptrofs.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def composites : List CompositeDef :=
[(CompositeDef.Composite _ssl_config_data SU.Struct
   [(Member.Member_bitfield _custom_cafile IntSize.I32 Signedness.Unsigned
      noattr 1 false),
    (Member.Member_bitfield _custom_capath IntSize.I32 Signedness.Unsigned
      noattr 1 false)]
   noattr),
 (CompositeDef.Composite _UserDefined SU.Struct
   [(Member.Member_plain _proxy_ssl (Ty.Tstruct _ssl_config_data noattr)),
    (Member.Member_plain _str (tarray (tptr tschar) 55)),
    (Member.Member_bitfield _haproxyprotocol IntSize.I32 Signedness.Unsigned
      noattr 1 false)]
   noattr),
 (CompositeDef.Composite _digestdata SU.Struct
   [(Member.Member_plain _nonce (tptr tschar))]
   noattr),
 (CompositeDef.Composite _auth SU.Struct
   [(Member.Member_plain _picked tuint)]
   noattr),
 (CompositeDef.Composite _UrlState SU.Struct
   [(Member.Member_plain _proxydigest (Ty.Tstruct _digestdata noattr)),
    (Member.Member_plain _authproxy (Ty.Tstruct _auth noattr))]
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
 (_curlx_free,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "curlx_free"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default)) [(tptr tvoid)] tvoid
     cc_default)),
 (_Curl_setstropt,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_setstropt"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xint cc_default))
     [(tptr (tptr tschar)), (tptr tschar)] tint cc_default)),
 (_setstropt_userpwd,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "setstropt_userpwd"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xptr]
                                     XType.Xint cc_default))
     [(tptr tschar), (tptr (tptr tschar)), (tptr (tptr tschar))] tint
     cc_default)),
 (_Curl_urldecode,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_urldecode"
                                   (mksignature
                                     [XType.Xptr, XType.Xlong, XType.Xptr,
                                      XType.Xptr, XType.Xint] XType.Xint
                                     cc_default))
     [(tptr tschar), tulong, (tptr (tptr tschar)), (tptr tulong), tint] tint
     cc_default)),
 (_Curl_ssl_supports,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_ssl_supports"
                                   (mksignature [XType.Xptr, XType.Xint]
                                     XType.Xbool cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), tuint] tbool cc_default)),
 (_strcmp,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "strcmp"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xint cc_default))
     [(tptr tschar), (tptr tschar)] tint cc_default)),
 (_memset,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "memset"
                                   (mksignature
                                     [XType.Xptr, XType.Xint, XType.Xlong]
                                     XType.Xptr cc_default))
     [(tptr tvoid), tint, tulong] (tptr tvoid) cc_default)),
 (_Curl_auth_digest_cleanup,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_auth_digest_cleanup"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default))
     [(tptr (Ty.Tstruct _digestdata noattr))] tvoid cc_default)),
 (_setproxy, GlobDef.Gfun (FunDef.Internal f_setproxy)),
 (_setopt_cptr_proxy, GlobDef.Gfun (FunDef.Internal f_setopt_cptr_proxy)),
 (_deb_keep, GlobDef.Gvar v_deb_keep)]

def public_idents : List Ident :=
[_deb_keep, _Curl_auth_digest_cleanup, _memset, _strcmp, _Curl_ssl_supports,
 _Curl_urldecode, _setstropt_userpwd, _Curl_setstropt, _curlx_free,
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

end Deb2026_7168_u1

