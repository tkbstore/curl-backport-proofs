import Clightdefs
open CC

namespace Deb2026_7168_d1

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
  def source_file : String := "deb2026_7168_d1.c"
  def normalized : Bool := true
end Info

def _Curl_URL : Ident := identOfString "Curl_URL"
def _Curl_all_content_encodings : Ident := identOfString "Curl_all_content_encodings"
def _Curl_auth_digest_cleanup : Ident := identOfString "Curl_auth_digest_cleanup"
def _Curl_cfree : Ident := identOfString "Curl_cfree"
def _Curl_easy : Ident := identOfString "Curl_easy"
def _Curl_memdup0 : Ident := identOfString "Curl_memdup0"
def _Curl_setstropt : Ident := identOfString "Curl_setstropt"
def _Curl_ssl_set_engine : Ident := identOfString "Curl_ssl_set_engine"
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
def _all : Ident := identOfString "all"
def _allowed_protocols : Ident := identOfString "allowed_protocols"
def _auth : Ident := identOfString "auth"
def _authproxy : Ident := identOfString "authproxy"
def _closesocket_client : Ident := identOfString "closesocket_client"
def _data : Ident := identOfString "data"
def _deb_keep : Ident := identOfString "deb_keep"
def _debugdata : Ident := identOfString "debugdata"
def _digestdata : Ident := identOfString "digestdata"
def _errorbuffer : Ident := identOfString "errorbuffer"
def _fsslctxp : Ident := identOfString "fsslctxp"
def _haproxyprotocol : Ident := identOfString "haproxyprotocol"
def _in_set : Ident := identOfString "in_set"
def _ioctl_client : Ident := identOfString "ioctl_client"
def _main : Ident := identOfString "main"
def _memset : Ident := identOfString "memset"
def _method : Ident := identOfString "method"
def _nonce : Ident := identOfString "nonce"
def _opensocket_client : Ident := identOfString "opensocket_client"
def _option : Ident := identOfString "option"
def _out : Ident := identOfString "out"
def _p : Ident := identOfString "p"
def _p__1 : Ident := identOfString "p__1"
def _picked : Ident := identOfString "picked"
def _postfields : Ident := identOfString "postfields"
def _postfieldsize : Ident := identOfString "postfieldsize"
def _prereq_userp : Ident := identOfString "prereq_userp"
def _private_data : Ident := identOfString "private_data"
def _progress_client : Ident := identOfString "progress_client"
def _protocol2num : Ident := identOfString "protocol2num"
def _proxy : Ident := identOfString "proxy"
def _proxydigest : Ident := identOfString "proxydigest"
def _ptr : Ident := identOfString "ptr"
def _redir_protocols : Ident := identOfString "redir_protocols"
def _referer : Ident := identOfString "referer"
def _referer_alloc : Ident := identOfString "referer_alloc"
def _resolver_start_client : Ident := identOfString "resolver_start_client"
def _result : Ident := identOfString "result"
def _seek_client : Ident := identOfString "seek_client"
def _set : Ident := identOfString "set"
def _setopt_cptr : Ident := identOfString "setopt_cptr"
def _setproxy : Ident := identOfString "setproxy"
def _setstropt_interface : Ident := identOfString "setstropt_interface"
def _setstropt_userpwd : Ident := identOfString "setstropt_userpwd"
def _sockopt_client : Ident := identOfString "sockopt_client"
def _ssl : Ident := identOfString "ssl"
def _ssl_config_data : Ident := identOfString "ssl_config_data"
def _state : Ident := identOfString "state"
def _str : Ident := identOfString "str"
def _strcmp : Ident := identOfString "strcmp"
def _trailer_data : Ident := identOfString "trailer_data"
def _u : Ident := identOfString "u"
def _uh : Ident := identOfString "uh"
def _url : Ident := identOfString "url"
def _url_alloc : Ident := identOfString "url_alloc"
def _writeheader : Ident := identOfString "writeheader"
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
def _t'71 : Ident := (Positive.ofNat 198)
def _t'72 : Ident := (Positive.ofNat 199)
def _t'73 : Ident := (Positive.ofNat 200)
def _t'74 : Ident := (Positive.ofNat 201)
def _t'75 : Ident := (Positive.ofNat 202)
def _t'76 : Ident := (Positive.ofNat 203)
def _t'77 : Ident := (Positive.ofNat 204)
def _t'78 : Ident := (Positive.ofNat 205)
def _t'79 : Ident := (Positive.ofNat 206)
def _t'8 : Ident := (Positive.ofNat 135)
def _t'80 : Ident := (Positive.ofNat 207)
def _t'81 : Ident := (Positive.ofNat 208)
def _t'82 : Ident := (Positive.ofNat 209)
def _t'83 : Ident := (Positive.ofNat 210)
def _t'84 : Ident := (Positive.ofNat 211)
def _t'85 : Ident := (Positive.ofNat 212)
def _t'86 : Ident := (Positive.ofNat 213)
def _t'87 : Ident := (Positive.ofNat 214)
def _t'88 : Ident := (Positive.ofNat 215)
def _t'89 : Ident := (Positive.ofNat 216)
def _t'9 : Ident := (Positive.ofNat 136)
def _t'90 : Ident := (Positive.ofNat 217)
def _t'91 : Ident := (Positive.ofNat 218)
def _t'92 : Ident := (Positive.ofNat 219)
def _t'93 : Ident := (Positive.ofNat 220)
def _t'94 : Ident := (Positive.ofNat 221)
def _t'95 : Ident := (Positive.ofNat 222)
def _t'96 : Ident := (Positive.ofNat 223)
def _t'97 : Ident := (Positive.ofNat 224)
def _t'98 : Ident := (Positive.ofNat 225)
def _t'99 : Ident := (Positive.ofNat 226)

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

def f_setopt_cptr : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_option, tint), (_ptr, (tptr tschar))],
  fn_vars := [(_all, (tarray tschar 256)), (_u, (tptr tschar)),
              (_p__1, (tptr tschar))],
  fn_temps := [(_result, tint), (_p, (tptr tschar)), (_t'74, tint),
               (_t'73, tint), (_t'72, tint), (_t'71, tint), (_t'70, tbool),
               (_t'69, tint), (_t'68, tint), (_t'67, tint), (_t'66, tint),
               (_t'65, tint), (_t'64, tint), (_t'63, tbool), (_t'62, tint),
               (_t'61, tbool), (_t'60, tint), (_t'59, tint), (_t'58, tint),
               (_t'57, tbool), (_t'56, tint), (_t'55, tbool), (_t'54, tint),
               (_t'53, tint), (_t'52, tint), (_t'51, tint), (_t'50, tint),
               (_t'49, tint), (_t'48, tint), (_t'47, tint), (_t'46, tint),
               (_t'45, tint), (_t'44, tint), (_t'43, tint), (_t'42, tint),
               (_t'41, tint), (_t'40, tint), (_t'39, tint), (_t'38, tint),
               (_t'37, tint), (_t'36, tint), (_t'35, tint), (_t'34, tint),
               (_t'33, tint), (_t'32, tint), (_t'31, tint), (_t'30, tint),
               (_t'29, tint), (_t'28, tint), (_t'27, tint), (_t'26, tint),
               (_t'25, tint), (_t'24, tint), (_t'23, tbool), (_t'22, tint),
               (_t'21, tint), (_t'20, tint), (_t'19, tint), (_t'18, tint),
               (_t'17, tint), (_t'16, tint), (_t'15, tint), (_t'14, tint),
               (_t'13, tint), (_t'12, tint), (_t'11, (tptr tvoid)),
               (_t'10, tint), (_t'9, tint), (_t'8, tbool), (_t'7, tint),
               (_t'6, tbool), (_t'5, tint), (_t'4, tbool), (_t'3, tint),
               (_t'2, tbool), (_t'1, tint), (_t'99, tlong), (_t'98, tlong),
               (_t'97, (tptr tschar)), (_t'96, tlong),
               (_t'95, (tptr tschar)), (_t'94, (tptr tschar)),
               (_t'93, tschar), (_t'92, (tptr tschar)), (_t'91, tint),
               (_t'90, (tptr tschar)), (_t'89, (tptr tschar)), (_t'88, tint),
               (_t'87, (tptr tschar)), (_t'86, (tptr tschar)),
               (_t'85, (tptr tschar)), (_t'84, (tptr tschar)),
               (_t'83, (tptr tschar)), (_t'82, (tptr tschar)),
               (_t'81, (tptr tschar)), (_t'80, (tptr tschar)),
               (_t'79, (tptr tschar)), (_t'78, (tptr tschar)), (_t'77, tint),
               (_t'76, (tptr tschar)), (_t'75, tschar)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Sset _result (Expr.Econst_int (Integers.Int.repr 0) tint))
  (Stmt.Ssequence
    (Stmt.Sswitch (Expr.Etempvar _option tint)
      (LStmts.LScons (some 10083)
        (Stmt.Ssequence
          (Stmt.Scall (some _t'2)
            (Expr.Evar _Curl_ssl_supports (Ty.Tfunction
                                            [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                             tuint] tbool cc_default))
            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
             (Expr.Ebinop Binop.Oshl
               (Expr.Econst_int (Integers.Int.repr 1) tint)
               (Expr.Econst_int (Integers.Int.repr 9) tint) tint)])
          (Stmt.Sifthenelse (Expr.Etempvar _t'2 tbool)
            (Stmt.Ssequence
              (Stmt.Scall (some _t'1)
                (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                             [(tptr (tptr tschar)),
                                              (tptr tschar)] tint cc_default))
                [(Expr.Ebinop Binop.Oadd
                   (Expr.Efield
                     (Expr.Efield
                       (Expr.Ederef
                         (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                         (Ty.Tstruct _Curl_easy noattr)) _set
                       (Ty.Tstruct _UserDefined noattr)) _str
                     (tarray (tptr tschar) 55))
                   (Expr.Econst_int (Integers.Int.repr 8) tint)
                   (tptr (tptr tschar))), (Expr.Etempvar _ptr (tptr tschar))])
              (Stmt.Sreturn (some (Expr.Etempvar _t'1 tint))))
            (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint)))))
        (LStmts.LScons (some 10259)
          (Stmt.Ssequence
            (Stmt.Scall (some _t'4)
              (Expr.Evar _Curl_ssl_supports (Ty.Tfunction
                                              [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                               tuint] tbool cc_default))
              [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
               (Expr.Ebinop Binop.Oshl
                 (Expr.Econst_int (Integers.Int.repr 1) tint)
                 (Expr.Econst_int (Integers.Int.repr 9) tint) tint)])
            (Stmt.Sifthenelse (Expr.Etempvar _t'4 tbool)
              (Stmt.Ssequence
                (Stmt.Scall (some _t'3)
                  (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                               [(tptr (tptr tschar)),
                                                (tptr tschar)] tint
                                               cc_default))
                  [(Expr.Ebinop Binop.Oadd
                     (Expr.Efield
                       (Expr.Efield
                         (Expr.Ederef
                           (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                           (Ty.Tstruct _Curl_easy noattr)) _set
                         (Ty.Tstruct _UserDefined noattr)) _str
                       (tarray (tptr tschar) 55))
                     (Expr.Econst_int (Integers.Int.repr 21) tint)
                     (tptr (tptr tschar))),
                   (Expr.Etempvar _ptr (tptr tschar))])
                (Stmt.Sreturn (some (Expr.Etempvar _t'3 tint))))
              (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint)))))
          (LStmts.LScons (some 10276)
            (Stmt.Ssequence
              (Stmt.Scall (some _t'6)
                (Expr.Evar _Curl_ssl_supports (Ty.Tfunction
                                                [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                 tuint] tbool cc_default))
                [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                 (Expr.Ebinop Binop.Oshl
                   (Expr.Econst_int (Integers.Int.repr 1) tint)
                   (Expr.Econst_int (Integers.Int.repr 5) tint) tint)])
              (Stmt.Sifthenelse (Expr.Etempvar _t'6 tbool)
                (Stmt.Ssequence
                  (Stmt.Scall (some _t'5)
                    (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                 [(tptr (tptr tschar)),
                                                  (tptr tschar)] tint
                                                 cc_default))
                    [(Expr.Ebinop Binop.Oadd
                       (Expr.Efield
                         (Expr.Efield
                           (Expr.Ederef
                             (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                             (Ty.Tstruct _Curl_easy noattr)) _set
                           (Ty.Tstruct _UserDefined noattr)) _str
                         (tarray (tptr tschar) 55))
                       (Expr.Econst_int (Integers.Int.repr 9) tint)
                       (tptr (tptr tschar))),
                     (Expr.Etempvar _ptr (tptr tschar))])
                  (Stmt.Sreturn (some (Expr.Etempvar _t'5 tint))))
                (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint)))))
            (LStmts.LScons (some 10277)
              (Stmt.Ssequence
                (Stmt.Scall (some _t'8)
                  (Expr.Evar _Curl_ssl_supports (Ty.Tfunction
                                                  [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                   tuint] tbool cc_default))
                  [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                   (Expr.Ebinop Binop.Oshl
                     (Expr.Econst_int (Integers.Int.repr 1) tint)
                     (Expr.Econst_int (Integers.Int.repr 5) tint) tint)])
                (Stmt.Sifthenelse (Expr.Etempvar _t'8 tbool)
                  (Stmt.Ssequence
                    (Stmt.Scall (some _t'7)
                      (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                   [(tptr (tptr tschar)),
                                                    (tptr tschar)] tint
                                                   cc_default))
                      [(Expr.Ebinop Binop.Oadd
                         (Expr.Efield
                           (Expr.Efield
                             (Expr.Ederef
                               (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                               (Ty.Tstruct _Curl_easy noattr)) _set
                             (Ty.Tstruct _UserDefined noattr)) _str
                           (tarray (tptr tschar) 55))
                         (Expr.Econst_int (Integers.Int.repr 22) tint)
                         (tptr (tptr tschar))),
                       (Expr.Etempvar _ptr (tptr tschar))])
                    (Stmt.Sreturn (some (Expr.Etempvar _t'7 tint))))
                  (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint)))))
              (LStmts.LScons (some 10076)
                Stmt.Sbreak
                (LStmts.LScons (some 10077)
                  Stmt.Sbreak
                  (LStmts.LScons (some 10266)
                    (Stmt.Ssequence
                      (Stmt.Scall (some _t'9)
                        (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                     [(tptr (tptr tschar)),
                                                      (tptr tschar)] tint
                                                     cc_default))
                        [(Expr.Ebinop Binop.Oadd
                           (Expr.Efield
                             (Expr.Efield
                               (Expr.Ederef
                                 (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                 (Ty.Tstruct _Curl_easy noattr)) _set
                               (Ty.Tstruct _UserDefined noattr)) _str
                             (tarray (tptr tschar) 55))
                           (Expr.Econst_int (Integers.Int.repr 46) tint)
                           (tptr (tptr tschar))),
                         (Expr.Etempvar _ptr (tptr tschar))])
                      (Stmt.Sreturn (some (Expr.Etempvar _t'9 tint))))
                    (LStmts.LScons (some 10165)
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                              (Expr.Etempvar _ptr (tptr tschar))
                                              tint)
                            (Stmt.Sset _t'12
                              (Expr.Econst_int (Integers.Int.repr 1) tint))
                            (Stmt.Ssequence
                              (Stmt.Sset _t'99
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                      (Ty.Tstruct _Curl_easy noattr)) _set
                                    (Ty.Tstruct _UserDefined noattr))
                                  _postfieldsize tlong))
                              (Stmt.Sset _t'12
                                (Expr.Ecast
                                  (Expr.Ebinop Binop.Oeq
                                    (Expr.Etempvar _t'99 tlong)
                                    (Expr.Eunop Unop.Oneg
                                      (Expr.Econst_int (Integers.Int.repr 1) tint)
                                      tint) tint) tbool))))
                          (Stmt.Sifthenelse (Expr.Etempvar _t'12 tint)
                            (Stmt.Ssequence
                              (Stmt.Scall (some _t'10)
                                (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                             [(tptr (tptr tschar)),
                                                              (tptr tschar)]
                                                             tint cc_default))
                                [(Expr.Ebinop Binop.Oadd
                                   (Expr.Efield
                                     (Expr.Efield
                                       (Expr.Ederef
                                         (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                         (Ty.Tstruct _Curl_easy noattr)) _set
                                       (Ty.Tstruct _UserDefined noattr)) _str
                                     (tarray (tptr tschar) 55))
                                   (Expr.Econst_int (Integers.Int.repr 54) tint)
                                   (tptr (tptr tschar))),
                                 (Expr.Etempvar _ptr (tptr tschar))])
                              (Stmt.Sset _result (Expr.Etempvar _t'10 tint)))
                            (Stmt.Ssequence
                              (Stmt.Sset _t'96
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                      (Ty.Tstruct _Curl_easy noattr)) _set
                                    (Ty.Tstruct _UserDefined noattr))
                                  _postfieldsize tlong))
                              (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                                  (Expr.Etempvar _t'96 tlong)
                                                  (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                  tint)
                                (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 43) tint)))
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Sset _t'98
                                        (Expr.Efield
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                              (Ty.Tstruct _Curl_easy noattr))
                                            _set
                                            (Ty.Tstruct _UserDefined noattr))
                                          _postfieldsize tlong))
                                      (Stmt.Scall (some _t'11)
                                        (Expr.Evar _Curl_memdup0 (Ty.Tfunction
                                                                   [(tptr tschar),
                                                                    tulong]
                                                                   (tptr tvoid)
                                                                   cc_default))
                                        [(Expr.Etempvar _ptr (tptr tschar)),
                                         (Expr.Ecast
                                           (Expr.Etempvar _t'98 tlong)
                                           tulong)]))
                                    (Stmt.Sset _p
                                      (Expr.Etempvar _t'11 (tptr tvoid))))
                                  (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                                      (Expr.Etempvar _p (tptr tschar))
                                                      tint)
                                    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 27) tint)))
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'97
                                          (Expr.Ederef
                                            (Expr.Ebinop Binop.Oadd
                                              (Expr.Efield
                                                (Expr.Efield
                                                  (Expr.Ederef
                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                    (Ty.Tstruct _Curl_easy noattr))
                                                  _set
                                                  (Ty.Tstruct _UserDefined noattr))
                                                _str
                                                (tarray (tptr tschar) 55))
                                              (Expr.Econst_int (Integers.Int.repr 54) tint)
                                              (tptr (tptr tschar)))
                                            (tptr tschar)))
                                        (Stmt.Scall none
                                          (Expr.Evar _Curl_cfree (Ty.Tfunction
                                                                   [(tptr tvoid)]
                                                                   tvoid
                                                                   cc_default))
                                          [(Expr.Etempvar _t'97 (tptr tschar))]))
                                      (Stmt.Sassign
                                        (Expr.Ederef
                                          (Expr.Ebinop Binop.Oadd
                                            (Expr.Efield
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                  (Ty.Tstruct _Curl_easy noattr))
                                                _set
                                                (Ty.Tstruct _UserDefined noattr))
                                              _str (tarray (tptr tschar) 55))
                                            (Expr.Econst_int (Integers.Int.repr 54) tint)
                                            (tptr (tptr tschar)))
                                          (tptr tschar))
                                        (Expr.Etempvar _p (tptr tschar))))))))))
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'95
                              (Expr.Ederef
                                (Expr.Ebinop Binop.Oadd
                                  (Expr.Efield
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                        (Ty.Tstruct _Curl_easy noattr)) _set
                                      (Ty.Tstruct _UserDefined noattr)) _str
                                    (tarray (tptr tschar) 55))
                                  (Expr.Econst_int (Integers.Int.repr 54) tint)
                                  (tptr (tptr tschar))) (tptr tschar)))
                            (Stmt.Sassign
                              (Expr.Efield
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                    (Ty.Tstruct _Curl_easy noattr)) _set
                                  (Ty.Tstruct _UserDefined noattr))
                                _postfields (tptr tvoid))
                              (Expr.Etempvar _t'95 (tptr tschar))))
                          (Stmt.Ssequence
                            (Stmt.Sassign
                              (Expr.Efield
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                    (Ty.Tstruct _Curl_easy noattr)) _set
                                  (Ty.Tstruct _UserDefined noattr)) _method
                                tuchar)
                              (Expr.Econst_int (Integers.Int.repr 1) tint))
                            Stmt.Sbreak)))
                      (LStmts.LScons (some 10015)
                        (Stmt.Ssequence
                          (Stmt.Sassign
                            (Expr.Efield
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                  (Ty.Tstruct _Curl_easy noattr)) _set
                                (Ty.Tstruct _UserDefined noattr)) _postfields
                              (tptr tvoid))
                            (Expr.Etempvar _ptr (tptr tschar)))
                          (Stmt.Ssequence
                            (Stmt.Sloop
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'94
                                    (Expr.Ederef
                                      (Expr.Ebinop Binop.Oadd
                                        (Expr.Efield
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                              (Ty.Tstruct _Curl_easy noattr))
                                            _set
                                            (Ty.Tstruct _UserDefined noattr))
                                          _str (tarray (tptr tschar) 55))
                                        (Expr.Econst_int (Integers.Int.repr 54) tint)
                                        (tptr (tptr tschar))) (tptr tschar)))
                                  (Stmt.Scall none
                                    (Expr.Evar _Curl_cfree (Ty.Tfunction
                                                             [(tptr tvoid)]
                                                             tvoid
                                                             cc_default))
                                    [(Expr.Etempvar _t'94 (tptr tschar))]))
                                (Stmt.Sassign
                                  (Expr.Ederef
                                    (Expr.Ebinop Binop.Oadd
                                      (Expr.Efield
                                        (Expr.Efield
                                          (Expr.Ederef
                                            (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                            (Ty.Tstruct _Curl_easy noattr))
                                          _set
                                          (Ty.Tstruct _UserDefined noattr))
                                        _str (tarray (tptr tschar) 55))
                                      (Expr.Econst_int (Integers.Int.repr 54) tint)
                                      (tptr (tptr tschar))) (tptr tschar))
                                  (Expr.Ecast
                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                    (tptr tvoid))))
                              Stmt.Sbreak)
                            (Stmt.Ssequence
                              (Stmt.Sassign
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                      (Ty.Tstruct _Curl_easy noattr)) _set
                                    (Ty.Tstruct _UserDefined noattr)) _method
                                  tuchar)
                                (Expr.Econst_int (Integers.Int.repr 1) tint))
                              Stmt.Sbreak)))
                        (LStmts.LScons (some 10102)
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Sifthenelse (Expr.Etempvar _ptr (tptr tschar))
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'93
                                    (Expr.Ederef
                                      (Expr.Etempvar _ptr (tptr tschar))
                                      tschar))
                                  (Stmt.Sset _t'14
                                    (Expr.Ecast
                                      (Expr.Eunop Unop.Onotbool
                                        (Expr.Etempvar _t'93 tschar) tint)
                                      tbool)))
                                (Stmt.Sset _t'14
                                  (Expr.Econst_int (Integers.Int.repr 0) tint)))
                              (Stmt.Sifthenelse (Expr.Etempvar _t'14 tint)
                                (Stmt.Ssequence
                                  (Stmt.Scall none
                                    (Expr.Evar _Curl_all_content_encodings 
                                    (Ty.Tfunction [(tptr tschar), tulong]
                                      tvoid cc_default))
                                    [(Expr.Evar _all (tarray tschar 256)),
                                     (Expr.Esizeof (tarray tschar 256) tulong)])
                                  (Stmt.Ssequence
                                    (Stmt.Scall (some _t'13)
                                      (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                                   [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                   tint
                                                                   cc_default))
                                      [(Expr.Ebinop Binop.Oadd
                                         (Expr.Efield
                                           (Expr.Efield
                                             (Expr.Ederef
                                               (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                               (Ty.Tstruct _Curl_easy noattr))
                                             _set
                                             (Ty.Tstruct _UserDefined noattr))
                                           _str (tarray (tptr tschar) 55))
                                         (Expr.Econst_int (Integers.Int.repr 31) tint)
                                         (tptr (tptr tschar))),
                                       (Expr.Evar _all (tarray tschar 256))])
                                    (Stmt.Sreturn (some (Expr.Etempvar _t'13 tint)))))
                                Stmt.Sskip))
                            (Stmt.Ssequence
                              (Stmt.Scall (some _t'15)
                                (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                             [(tptr (tptr tschar)),
                                                              (tptr tschar)]
                                                             tint cc_default))
                                [(Expr.Ebinop Binop.Oadd
                                   (Expr.Efield
                                     (Expr.Efield
                                       (Expr.Ederef
                                         (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                         (Ty.Tstruct _Curl_easy noattr)) _set
                                       (Ty.Tstruct _UserDefined noattr)) _str
                                     (tarray (tptr tschar) 55))
                                   (Expr.Econst_int (Integers.Int.repr 31) tint)
                                   (tptr (tptr tschar))),
                                 (Expr.Etempvar _ptr (tptr tschar))])
                              (Stmt.Sreturn (some (Expr.Etempvar _t'15 tint)))))
                          (LStmts.LScons (some 10016)
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Sset _t'91
                                  (Expr.Efield
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                        (Ty.Tstruct _Curl_easy noattr))
                                      _state (Ty.Tstruct _UrlState noattr))
                                    _referer_alloc tint))
                                (Stmt.Sifthenelse (Expr.Etempvar _t'91 tint)
                                  (Stmt.Ssequence
                                    (Stmt.Sloop
                                      (Stmt.Ssequence
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'92
                                            (Expr.Efield
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                  (Ty.Tstruct _Curl_easy noattr))
                                                _state
                                                (Ty.Tstruct _UrlState noattr))
                                              _referer (tptr tschar)))
                                          (Stmt.Scall none
                                            (Expr.Evar _Curl_cfree (Ty.Tfunction
                                                                    [(tptr tvoid)]
                                                                    tvoid
                                                                    cc_default))
                                            [(Expr.Etempvar _t'92 (tptr tschar))]))
                                        (Stmt.Sassign
                                          (Expr.Efield
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                (Ty.Tstruct _Curl_easy noattr))
                                              _state
                                              (Ty.Tstruct _UrlState noattr))
                                            _referer (tptr tschar))
                                          (Expr.Ecast
                                            (Expr.Econst_int (Integers.Int.repr 0) tint)
                                            (tptr tvoid))))
                                      Stmt.Sbreak)
                                    (Stmt.Sassign
                                      (Expr.Efield
                                        (Expr.Efield
                                          (Expr.Ederef
                                            (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                            (Ty.Tstruct _Curl_easy noattr))
                                          _state
                                          (Ty.Tstruct _UrlState noattr))
                                        _referer_alloc tint)
                                      (Expr.Econst_int (Integers.Int.repr 0) tint)))
                                  Stmt.Sskip))
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Scall (some _t'16)
                                    (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                                 [(tptr (tptr tschar)),
                                                                  (tptr tschar)]
                                                                 tint
                                                                 cc_default))
                                    [(Expr.Ebinop Binop.Oadd
                                       (Expr.Efield
                                         (Expr.Efield
                                           (Expr.Ederef
                                             (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                             (Ty.Tstruct _Curl_easy noattr))
                                           _set
                                           (Ty.Tstruct _UserDefined noattr))
                                         _str (tarray (tptr tschar) 55))
                                       (Expr.Econst_int (Integers.Int.repr 35) tint)
                                       (tptr (tptr tschar))),
                                     (Expr.Etempvar _ptr (tptr tschar))])
                                  (Stmt.Sset _result
                                    (Expr.Etempvar _t'16 tint)))
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Sset _t'90
                                      (Expr.Ederef
                                        (Expr.Ebinop Binop.Oadd
                                          (Expr.Efield
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                (Ty.Tstruct _Curl_easy noattr))
                                              _set
                                              (Ty.Tstruct _UserDefined noattr))
                                            _str (tarray (tptr tschar) 55))
                                          (Expr.Econst_int (Integers.Int.repr 35) tint)
                                          (tptr (tptr tschar)))
                                        (tptr tschar)))
                                    (Stmt.Sassign
                                      (Expr.Efield
                                        (Expr.Efield
                                          (Expr.Ederef
                                            (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                            (Ty.Tstruct _Curl_easy noattr))
                                          _state
                                          (Ty.Tstruct _UrlState noattr))
                                        _referer (tptr tschar))
                                      (Expr.Etempvar _t'90 (tptr tschar))))
                                  Stmt.Sbreak)))
                            (LStmts.LScons (some 10018)
                              (Stmt.Ssequence
                                (Stmt.Scall (some _t'17)
                                  (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                               [(tptr (tptr tschar)),
                                                                (tptr tschar)]
                                                               tint
                                                               cc_default))
                                  [(Expr.Ebinop Binop.Oadd
                                     (Expr.Efield
                                       (Expr.Efield
                                         (Expr.Ederef
                                           (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                           (Ty.Tstruct _Curl_easy noattr))
                                         _set
                                         (Ty.Tstruct _UserDefined noattr))
                                       _str (tarray (tptr tschar) 55))
                                     (Expr.Econst_int (Integers.Int.repr 37) tint)
                                     (tptr (tptr tschar))),
                                   (Expr.Etempvar _ptr (tptr tschar))])
                                (Stmt.Sreturn (some (Expr.Etempvar _t'17 tint))))
                              (LStmts.LScons (some 10036)
                                (Stmt.Ssequence
                                  (Stmt.Scall (some _t'18)
                                    (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                                 [(tptr (tptr tschar)),
                                                                  (tptr tschar)]
                                                                 tint
                                                                 cc_default))
                                    [(Expr.Ebinop Binop.Oadd
                                       (Expr.Efield
                                         (Expr.Efield
                                           (Expr.Ederef
                                             (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                             (Ty.Tstruct _Curl_easy noattr))
                                           _set
                                           (Ty.Tstruct _UserDefined noattr))
                                         _str (tarray (tptr tschar) 55))
                                       (Expr.Econst_int (Integers.Int.repr 26) tint)
                                       (tptr (tptr tschar))),
                                     (Expr.Etempvar _ptr (tptr tschar))])
                                  (Stmt.Sreturn (some (Expr.Etempvar _t'18 tint))))
                                (LStmts.LScons (some 10004)
                                  (Stmt.Ssequence
                                    (Stmt.Scall (some _t'19)
                                      (Expr.Evar _setproxy (Ty.Tfunction
                                                             [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                              (tptr tschar)]
                                                             tint cc_default))
                                      [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                       (Expr.Etempvar _ptr (tptr tschar))])
                                    (Stmt.Sreturn (some (Expr.Etempvar _t'19 tint))))
                                  (LStmts.LScons (some 10262)
                                    (Stmt.Ssequence
                                      (Stmt.Scall (some _t'20)
                                        (Expr.Evar _Curl_setstropt (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                        [(Expr.Ebinop Binop.Oadd
                                           (Expr.Efield
                                             (Expr.Efield
                                               (Expr.Ederef
                                                 (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                 (Ty.Tstruct _Curl_easy noattr))
                                               _set
                                               (Ty.Tstruct _UserDefined noattr))
                                             _str (tarray (tptr tschar) 55))
                                           (Expr.Econst_int (Integers.Int.repr 33) tint)
                                           (tptr (tptr tschar))),
                                         (Expr.Etempvar _ptr (tptr tschar))])
                                      (Stmt.Sreturn (some (Expr.Etempvar _t'20 tint))))
                                    (LStmts.LScons (some 10179)
                                      Stmt.Sskip
                                      (LStmts.LScons (some 10235)
                                        (Stmt.Ssequence
                                          (Stmt.Scall (some _t'21)
                                            (Expr.Evar _Curl_setstropt 
                                            (Ty.Tfunction
                                              [(tptr (tptr tschar)),
                                               (tptr tschar)] tint
                                              cc_default))
                                            [(Expr.Ebinop Binop.Oadd
                                               (Expr.Efield
                                                 (Expr.Efield
                                                   (Expr.Ederef
                                                     (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                     (Ty.Tstruct _Curl_easy noattr))
                                                   _set
                                                   (Ty.Tstruct _UserDefined noattr))
                                                 _str
                                                 (tarray (tptr tschar) 55))
                                               (Expr.Econst_int (Integers.Int.repr 25) tint)
                                               (tptr (tptr tschar))),
                                             (Expr.Etempvar _ptr (tptr tschar))])
                                          (Stmt.Sreturn (some (Expr.Etempvar _t'21 tint))))
                                        (LStmts.LScons (some 10236)
                                          (Stmt.Ssequence
                                            (Stmt.Scall (some _t'22)
                                              (Expr.Evar _Curl_setstropt 
                                              (Ty.Tfunction
                                                [(tptr (tptr tschar)),
                                                 (tptr tschar)] tint
                                                cc_default))
                                              [(Expr.Ebinop Binop.Oadd
                                                 (Expr.Efield
                                                   (Expr.Efield
                                                     (Expr.Ederef
                                                       (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                       (Ty.Tstruct _Curl_easy noattr))
                                                     _set
                                                     (Ty.Tstruct _UserDefined noattr))
                                                   _str
                                                   (tarray (tptr tschar) 55))
                                                 (Expr.Econst_int (Integers.Int.repr 12) tint)
                                                 (tptr (tptr tschar))),
                                               (Expr.Etempvar _ptr (tptr tschar))])
                                            (Stmt.Sreturn (some (Expr.Etempvar _t'22 tint))))
                                          (LStmts.LScons (some 10029)
                                            (Stmt.Ssequence
                                              (Stmt.Sassign
                                                (Expr.Efield
                                                  (Expr.Efield
                                                    (Expr.Ederef
                                                      (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                      (Ty.Tstruct _Curl_easy noattr))
                                                    _set
                                                    (Ty.Tstruct _UserDefined noattr))
                                                  _writeheader (tptr tvoid))
                                                (Expr.Etempvar _ptr (tptr tschar)))
                                              Stmt.Sbreak)
                                            (LStmts.LScons (some 10009)
                                              (Stmt.Ssequence
                                                (Stmt.Sassign
                                                  (Expr.Efield
                                                    (Expr.Efield
                                                      (Expr.Ederef
                                                        (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                        (Ty.Tstruct _Curl_easy noattr))
                                                      _set
                                                      (Ty.Tstruct _UserDefined noattr))
                                                    _in_set (tptr tvoid))
                                                  (Expr.Etempvar _ptr (tptr tschar)))
                                                Stmt.Sbreak)
                                              (LStmts.LScons (some 10001)
                                                (Stmt.Ssequence
                                                  (Stmt.Sassign
                                                    (Expr.Efield
                                                      (Expr.Efield
                                                        (Expr.Ederef
                                                          (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                          (Ty.Tstruct _Curl_easy noattr))
                                                        _set
                                                        (Ty.Tstruct _UserDefined noattr))
                                                      _out (tptr tvoid))
                                                    (Expr.Etempvar _ptr (tptr tschar)))
                                                  Stmt.Sbreak)
                                                (LStmts.LScons (some 10095)
                                                  (Stmt.Ssequence
                                                    (Stmt.Sassign
                                                      (Expr.Efield
                                                        (Expr.Efield
                                                          (Expr.Ederef
                                                            (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                            (Ty.Tstruct _Curl_easy noattr))
                                                          _set
                                                          (Ty.Tstruct _UserDefined noattr))
                                                        _debugdata
                                                        (tptr tvoid))
                                                      (Expr.Etempvar _ptr (tptr tschar)))
                                                    Stmt.Sbreak)
                                                  (LStmts.LScons (some 10057)
                                                    (Stmt.Ssequence
                                                      (Stmt.Sassign
                                                        (Expr.Efield
                                                          (Expr.Efield
                                                            (Expr.Ederef
                                                              (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                              (Ty.Tstruct _Curl_easy noattr))
                                                            _set
                                                            (Ty.Tstruct _UserDefined noattr))
                                                          _progress_client
                                                          (tptr tvoid))
                                                        (Expr.Etempvar _ptr (tptr tschar)))
                                                      Stmt.Sbreak)
                                                    (LStmts.LScons (some 10168)
                                                      (Stmt.Ssequence
                                                        (Stmt.Sassign
                                                          (Expr.Efield
                                                            (Expr.Efield
                                                              (Expr.Ederef
                                                                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                (Ty.Tstruct _Curl_easy noattr))
                                                              _set
                                                              (Ty.Tstruct _UserDefined noattr))
                                                            _seek_client
                                                            (tptr tvoid))
                                                          (Expr.Etempvar _ptr (tptr tschar)))
                                                        Stmt.Sbreak)
                                                      (LStmts.LScons (some 10131)
                                                        (Stmt.Ssequence
                                                          (Stmt.Sassign
                                                            (Expr.Efield
                                                              (Expr.Efield
                                                                (Expr.Ederef
                                                                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                  (Ty.Tstruct _Curl_easy noattr))
                                                                _set
                                                                (Ty.Tstruct _UserDefined noattr))
                                                              _ioctl_client
                                                              (tptr tvoid))
                                                            (Expr.Etempvar _ptr (tptr tschar)))
                                                          Stmt.Sbreak)
                                                        (LStmts.LScons (some 10109)
                                                          (Stmt.Ssequence
                                                            (Stmt.Scall (some _t'23)
                                                              (Expr.Evar _Curl_ssl_supports 
                                                              (Ty.Tfunction
                                                                [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                 tuint] tbool
                                                                cc_default))
                                                              [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                               (Expr.Ebinop Binop.Oshl
                                                                 (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                 (Expr.Econst_int (Integers.Int.repr 3) tint)
                                                                 tint)])
                                                            (Stmt.Sifthenelse (Expr.Etempvar _t'23 tbool)
                                                              (Stmt.Ssequence
                                                                (Stmt.Sassign
                                                                  (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _ssl
                                                                    (Ty.Tstruct _ssl_config_data noattr))
                                                                    _fsslctxp
                                                                    (tptr tvoid))
                                                                  (Expr.Etempvar _ptr (tptr tschar)))
                                                                Stmt.Sbreak)
                                                              (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint)))))
                                                          (LStmts.LScons (some 10149)
                                                            (Stmt.Ssequence
                                                              (Stmt.Sassign
                                                                (Expr.Efield
                                                                  (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                  _sockopt_client
                                                                  (tptr tvoid))
                                                                (Expr.Etempvar _ptr (tptr tschar)))
                                                              Stmt.Sbreak)
                                                            (LStmts.LScons (some 10164)
                                                              (Stmt.Ssequence
                                                                (Stmt.Sassign
                                                                  (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _opensocket_client
                                                                    (tptr tvoid))
                                                                  (Expr.Etempvar _ptr (tptr tschar)))
                                                                Stmt.Sbreak)
                                                              (LStmts.LScons (some 10273)
                                                                (Stmt.Ssequence
                                                                  (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _resolver_start_client
                                                                    (tptr tvoid))
                                                                    (Expr.Etempvar _ptr (tptr tschar)))
                                                                  Stmt.Sbreak)
                                                                (LStmts.LScons (some 10209)
                                                                  (Stmt.Ssequence
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _closesocket_client
                                                                    (tptr tvoid))
                                                                    (Expr.Etempvar _ptr (tptr tschar)))
                                                                    Stmt.Sbreak)
                                                                  (LStmts.LScons (some 10284)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _trailer_data
                                                                    (tptr tvoid))
                                                                    (Expr.Etempvar _ptr (tptr tschar)))
                                                                    Stmt.Sbreak)
                                                                    (LStmts.LScons (some 10313)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _prereq_userp
                                                                    (tptr tvoid))
                                                                    (Expr.Etempvar _ptr (tptr tschar)))
                                                                    Stmt.Sbreak)
                                                                    (LStmts.LScons (some 10010)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _errorbuffer
                                                                    (tptr tschar))
                                                                    (Expr.Etempvar _ptr (tptr tschar)))
                                                                    Stmt.Sbreak)
                                                                    (LStmts.LScons (some 10002)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'88
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _state
                                                                    (Ty.Tstruct _UrlState noattr))
                                                                    _url_alloc
                                                                    tint))
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _t'88 tint)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sloop
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'89
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _state
                                                                    (Ty.Tstruct _UrlState noattr))
                                                                    _url
                                                                    (tptr tschar)))
                                                                    (Stmt.Scall none
                                                                    (Expr.Evar _Curl_cfree 
                                                                    (Ty.Tfunction
                                                                    [(tptr tvoid)]
                                                                    tvoid
                                                                    cc_default))
                                                                    [(Expr.Etempvar _t'89 (tptr tschar))]))
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _state
                                                                    (Ty.Tstruct _UrlState noattr))
                                                                    _url
                                                                    (tptr tschar))
                                                                    (Expr.Ecast
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    (tptr tvoid))))
                                                                    Stmt.Sbreak)
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _state
                                                                    (Ty.Tstruct _UrlState noattr))
                                                                    _url_alloc
                                                                    tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)))
                                                                    Stmt.Sskip))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'24)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 36) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sset _result
                                                                    (Expr.Etempvar _t'24 tint)))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'87
                                                                    (Expr.Ederef
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 36) tint)
                                                                    (tptr (tptr tschar)))
                                                                    (tptr tschar)))
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _state
                                                                    (Ty.Tstruct _UrlState noattr))
                                                                    _url
                                                                    (tptr tschar))
                                                                    (Expr.Etempvar _t'87 (tptr tschar))))
                                                                    Stmt.Sbreak)))
                                                                    (LStmts.LScons (some 10005)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'25)
                                                                    (Expr.Evar _setstropt_userpwd 
                                                                    (Ty.Tfunction
                                                                    [(tptr tschar),
                                                                    (tptr (tptr tschar)),
                                                                    (tptr (tptr tschar))]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Etempvar _ptr (tptr tschar)),
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 39) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 40) tint)
                                                                    (tptr (tptr tschar)))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'25 tint))))
                                                                    (LStmts.LScons (some 10173)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'26)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 39) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'26 tint))))
                                                                    (LStmts.LScons (some 10174)
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
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 40) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'27 tint))))
                                                                    (LStmts.LScons (some 10224)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'28)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 41) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'28 tint))))
                                                                    (LStmts.LScons (some 10220)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'29)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 45) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'29 tint))))
                                                                    (LStmts.LScons (some 10006)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sassign
                                                                    (Expr.Evar _u (tptr tschar))
                                                                    (Expr.Ecast
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    (tptr tvoid)))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sassign
                                                                    (Expr.Evar _p__1 (tptr tschar))
                                                                    (Expr.Ecast
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    (tptr tvoid)))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'30)
                                                                    (Expr.Evar _setstropt_userpwd 
                                                                    (Ty.Tfunction
                                                                    [(tptr tschar),
                                                                    (tptr (tptr tschar)),
                                                                    (tptr (tptr tschar))]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Etempvar _ptr (tptr tschar)),
                                                                    (Expr.Eaddrof
                                                                    (Expr.Evar _u (tptr tschar))
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Eaddrof
                                                                    (Expr.Evar _p__1 (tptr tschar))
                                                                    (tptr (tptr tschar)))])
                                                                    (Stmt.Sset _result
                                                                    (Expr.Etempvar _t'30 tint)))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sifthenelse 
                                                                    (Expr.Eunop Unop.Onotbool
                                                                    (Expr.Etempvar _result tint)
                                                                    tint)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'86
                                                                    (Expr.Evar _u (tptr tschar)))
                                                                    (Stmt.Sset _t'32
                                                                    (Expr.Ecast
                                                                    (Expr.Etempvar _t'86 (tptr tschar))
                                                                    tbool)))
                                                                    (Stmt.Sset _t'32
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)))
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _t'32 tint)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sloop
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'85
                                                                    (Expr.Ederef
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 42) tint)
                                                                    (tptr (tptr tschar)))
                                                                    (tptr tschar)))
                                                                    (Stmt.Scall none
                                                                    (Expr.Evar _Curl_cfree 
                                                                    (Ty.Tfunction
                                                                    [(tptr tvoid)]
                                                                    tvoid
                                                                    cc_default))
                                                                    [(Expr.Etempvar _t'85 (tptr tschar))]))
                                                                    (Stmt.Sassign
                                                                    (Expr.Ederef
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 42) tint)
                                                                    (tptr (tptr tschar)))
                                                                    (tptr tschar))
                                                                    (Expr.Ecast
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    (tptr tvoid))))
                                                                    Stmt.Sbreak)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'84
                                                                    (Expr.Evar _u (tptr tschar)))
                                                                    (Stmt.Scall (some _t'31)
                                                                    (Expr.Evar _Curl_urldecode 
                                                                    (Ty.Tfunction
                                                                    [(tptr tschar),
                                                                    tulong,
                                                                    (tptr (tptr tschar)),
                                                                    (tptr tulong),
                                                                    tint]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Etempvar _t'84 (tptr tschar)),
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint),
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 42) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Ecast
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    (tptr tvoid)),
                                                                    (Expr.Econst_int (Integers.Int.repr 4) tint)]))
                                                                    (Stmt.Sset _result
                                                                    (Expr.Etempvar _t'31 tint))))
                                                                    Stmt.Sskip))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sifthenelse 
                                                                    (Expr.Eunop Unop.Onotbool
                                                                    (Expr.Etempvar _result tint)
                                                                    tint)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'83
                                                                    (Expr.Evar _p__1 (tptr tschar)))
                                                                    (Stmt.Sset _t'34
                                                                    (Expr.Ecast
                                                                    (Expr.Etempvar _t'83 (tptr tschar))
                                                                    tbool)))
                                                                    (Stmt.Sset _t'34
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)))
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _t'34 tint)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sloop
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'82
                                                                    (Expr.Ederef
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 43) tint)
                                                                    (tptr (tptr tschar)))
                                                                    (tptr tschar)))
                                                                    (Stmt.Scall none
                                                                    (Expr.Evar _Curl_cfree 
                                                                    (Ty.Tfunction
                                                                    [(tptr tvoid)]
                                                                    tvoid
                                                                    cc_default))
                                                                    [(Expr.Etempvar _t'82 (tptr tschar))]))
                                                                    (Stmt.Sassign
                                                                    (Expr.Ederef
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 43) tint)
                                                                    (tptr (tptr tschar)))
                                                                    (tptr tschar))
                                                                    (Expr.Ecast
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    (tptr tvoid))))
                                                                    Stmt.Sbreak)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'81
                                                                    (Expr.Evar _p__1 (tptr tschar)))
                                                                    (Stmt.Scall (some _t'33)
                                                                    (Expr.Evar _Curl_urldecode 
                                                                    (Ty.Tfunction
                                                                    [(tptr tschar),
                                                                    tulong,
                                                                    (tptr (tptr tschar)),
                                                                    (tptr tulong),
                                                                    tint]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Etempvar _t'81 (tptr tschar)),
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint),
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 43) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Ecast
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    (tptr tvoid)),
                                                                    (Expr.Econst_int (Integers.Int.repr 4) tint)]))
                                                                    (Stmt.Sset _result
                                                                    (Expr.Etempvar _t'33 tint))))
                                                                    Stmt.Sskip))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'80
                                                                    (Expr.Evar _u (tptr tschar)))
                                                                    (Stmt.Scall none
                                                                    (Expr.Evar _Curl_cfree 
                                                                    (Ty.Tfunction
                                                                    [(tptr tvoid)]
                                                                    tvoid
                                                                    cc_default))
                                                                    [(Expr.Etempvar _t'80 (tptr tschar))]))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'79
                                                                    (Expr.Evar _p__1 (tptr tschar)))
                                                                    (Stmt.Scall none
                                                                    (Expr.Evar _Curl_cfree 
                                                                    (Ty.Tfunction
                                                                    [(tptr tvoid)]
                                                                    tvoid
                                                                    cc_default))
                                                                    [(Expr.Etempvar _t'79 (tptr tschar))]))
                                                                    Stmt.Sbreak)))))))
                                                                    (LStmts.LScons (some 10175)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'35)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 42) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'35 tint))))
                                                                    (LStmts.LScons (some 10176)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'36)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 43) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'36 tint))))
                                                                    (LStmts.LScons (some 10177)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'37)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 44) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'37 tint))))
                                                                    (LStmts.LScons (some 10007)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'38)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 34) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'38 tint))))
                                                                    (LStmts.LScons (some 10282)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'77
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _state
                                                                    (Ty.Tstruct _UrlState noattr))
                                                                    _url_alloc
                                                                    tint))
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _t'77 tint)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sloop
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'78
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _state
                                                                    (Ty.Tstruct _UrlState noattr))
                                                                    _url
                                                                    (tptr tschar)))
                                                                    (Stmt.Scall none
                                                                    (Expr.Evar _Curl_cfree 
                                                                    (Ty.Tfunction
                                                                    [(tptr tvoid)]
                                                                    tvoid
                                                                    cc_default))
                                                                    [(Expr.Etempvar _t'78 (tptr tschar))]))
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _state
                                                                    (Ty.Tstruct _UrlState noattr))
                                                                    _url
                                                                    (tptr tschar))
                                                                    (Expr.Ecast
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    (tptr tvoid))))
                                                                    Stmt.Sbreak)
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _state
                                                                    (Ty.Tstruct _UrlState noattr))
                                                                    _url_alloc
                                                                    tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)))
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _state
                                                                    (Ty.Tstruct _UrlState noattr))
                                                                    _url
                                                                    (tptr tschar))
                                                                    (Expr.Ecast
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    (tptr tvoid)))))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sloop
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'76
                                                                    (Expr.Ederef
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 36) tint)
                                                                    (tptr (tptr tschar)))
                                                                    (tptr tschar)))
                                                                    (Stmt.Scall none
                                                                    (Expr.Evar _Curl_cfree 
                                                                    (Ty.Tfunction
                                                                    [(tptr tvoid)]
                                                                    tvoid
                                                                    cc_default))
                                                                    [(Expr.Etempvar _t'76 (tptr tschar))]))
                                                                    (Stmt.Sassign
                                                                    (Expr.Ederef
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 36) tint)
                                                                    (tptr (tptr tschar)))
                                                                    (tptr tschar))
                                                                    (Expr.Ecast
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    (tptr tvoid))))
                                                                    Stmt.Sbreak)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _uh
                                                                    (tptr (Ty.Tstruct _Curl_URL noattr)))
                                                                    (Expr.Ecast
                                                                    (Expr.Etempvar _ptr (tptr tschar))
                                                                    (tptr (Ty.Tstruct _Curl_URL noattr))))
                                                                    Stmt.Sbreak)))
                                                                    (LStmts.LScons (some 10025)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'39)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'39 tint))))
                                                                    (LStmts.LScons (some 10254)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'40)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 13) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'40 tint))))
                                                                    (LStmts.LScons (some 10086)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'41)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'41 tint))))
                                                                    (LStmts.LScons (some 10255)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'42)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 14) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'42 tint))))
                                                                    (LStmts.LScons (some 10087)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'43)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 2) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'43 tint))))
                                                                    (LStmts.LScons (some 10256)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'44)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 15) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'44 tint))))
                                                                    (LStmts.LScons (some 10088)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'45)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 4) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'45 tint))))
                                                                    (LStmts.LScons (some 10257)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'46)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 17) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'46 tint))))
                                                                    (LStmts.LScons (some 10026)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'47)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 3) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'47 tint))))
                                                                    (LStmts.LScons (some 10258)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'48)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 16) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'48 tint))))
                                                                    (LStmts.LScons (some 10089)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _ptr (tptr tschar))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sset _t'75
                                                                    (Expr.Ederef
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Etempvar _ptr (tptr tschar))
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    (tptr tschar))
                                                                    tschar))
                                                                    (Stmt.Sset _t'51
                                                                    (Expr.Ecast
                                                                    (Expr.Etempvar _t'75 tschar)
                                                                    tbool)))
                                                                    (Stmt.Sset _t'51
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)))
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _t'51 tint)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'49)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 38) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sset _result
                                                                    (Expr.Etempvar _t'49 tint)))
                                                                    (Stmt.Sifthenelse 
                                                                    (Expr.Eunop Unop.Onotbool
                                                                    (Expr.Etempvar _result tint)
                                                                    tint)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'50)
                                                                    (Expr.Evar _Curl_ssl_set_engine 
                                                                    (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sset _result
                                                                    (Expr.Etempvar _t'50 tint)))
                                                                    Stmt.Sskip))
                                                                    Stmt.Sskip))
                                                                    Stmt.Sbreak)
                                                                    (LStmts.LScons (some 10323)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'52)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 49) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sset _result
                                                                    (Expr.Etempvar _t'52 tint)))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _haproxyprotocol
                                                                    tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint))
                                                                    Stmt.Sbreak))
                                                                    (LStmts.LScons (some 10062)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'53)
                                                                    (Expr.Evar _setstropt_interface 
                                                                    (Ty.Tfunction
                                                                    [(tptr tschar),
                                                                    (tptr (tptr tschar)),
                                                                    (tptr (tptr tschar)),
                                                                    (tptr (tptr tschar))]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Etempvar _ptr (tptr tschar)),
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 28) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 29) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 30) tint)
                                                                    (tptr (tptr tschar)))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'53 tint))))
                                                                    (LStmts.LScons (some 10230)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'55)
                                                                    (Expr.Evar _Curl_ssl_supports 
                                                                    (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                    tuint]
                                                                    tbool
                                                                    cc_default))
                                                                    [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                                    (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 2) tint)
                                                                    tint)])
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _t'55 tbool)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'54)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 7) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'54 tint))))
                                                                    Stmt.Sskip))
                                                                    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint))))
                                                                    (LStmts.LScons (some 10263)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'57)
                                                                    (Expr.Evar _Curl_ssl_supports 
                                                                    (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                    tuint]
                                                                    tbool
                                                                    cc_default))
                                                                    [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                                    (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 2) tint)
                                                                    tint)])
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _t'57 tbool)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'56)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 20) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'56 tint))))
                                                                    Stmt.Sskip))
                                                                    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint))))
                                                                    (LStmts.LScons (some 10065)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'58)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 6) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'58 tint))))
                                                                    (LStmts.LScons (some 10246)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'59)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 19) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'59 tint))))
                                                                    (LStmts.LScons (some 10097)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'61)
                                                                    (Expr.Evar _Curl_ssl_supports 
                                                                    (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                    tuint]
                                                                    tbool
                                                                    cc_default))
                                                                    [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                                    (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    tint)])
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _t'61 tbool)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'60)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 5) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'60 tint))))
                                                                    Stmt.Sskip))
                                                                    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint))))
                                                                    (LStmts.LScons (some 10247)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'63)
                                                                    (Expr.Evar _Curl_ssl_supports 
                                                                    (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                    tuint]
                                                                    tbool
                                                                    cc_default))
                                                                    [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                                    (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    tint)])
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _t'63 tbool)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'62)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 18) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'62 tint))))
                                                                    Stmt.Sskip))
                                                                    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint))))
                                                                    (LStmts.LScons (some 10169)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'64)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 10) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'64 tint))))
                                                                    (LStmts.LScons (some 10260)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'65)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 23) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'65 tint))))
                                                                    (LStmts.LScons (some 10170)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'66)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 11) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'66 tint))))
                                                                    (LStmts.LScons (some 10296)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'67)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 24) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'67 tint))))
                                                                    (LStmts.LScons (some 10103)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _private_data
                                                                    (tptr tvoid))
                                                                    (Expr.Etempvar _ptr (tptr tschar)))
                                                                    Stmt.Sbreak)
                                                                    (LStmts.LScons (some 10298)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'68)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 48) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'68 tint))))
                                                                    (LStmts.LScons (some 10328)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'70)
                                                                    (Expr.Evar _Curl_ssl_supports 
                                                                    (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                    tuint]
                                                                    tbool
                                                                    cc_default))
                                                                    [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                                    (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 10) tint)
                                                                    tint)])
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _t'70 tbool)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'69)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 52) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'69 tint))))
                                                                    Stmt.Sskip))
                                                                    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 4) tint))))
                                                                    (LStmts.LScons (some 10318)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _ptr (tptr tschar))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'71)
                                                                    (Expr.Evar _protocol2num 
                                                                    (Ty.Tfunction
                                                                    [(tptr tschar),
                                                                    (tptr tlong)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Etempvar _ptr (tptr tschar)),
                                                                    (Expr.Eaddrof
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _allowed_protocols
                                                                    tlong)
                                                                    (tptr tlong))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'71 tint))))
                                                                    Stmt.Sskip)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _allowed_protocols
                                                                    tlong)
                                                                    (Expr.Ecast
                                                                    (Expr.Eunop Unop.Onotint
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    tint)
                                                                    tlong))
                                                                    Stmt.Sbreak))
                                                                    (LStmts.LScons (some 10319)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sifthenelse (Expr.Etempvar _ptr (tptr tschar))
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'72)
                                                                    (Expr.Evar _protocol2num 
                                                                    (Ty.Tfunction
                                                                    [(tptr tschar),
                                                                    (tptr tlong)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Etempvar _ptr (tptr tschar)),
                                                                    (Expr.Eaddrof
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _redir_protocols
                                                                    tlong)
                                                                    (tptr tlong))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'72 tint))))
                                                                    Stmt.Sskip)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Sassign
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _redir_protocols
                                                                    tlong)
                                                                    (Expr.Ecast
                                                                    (Expr.Ebinop Binop.Oor
                                                                    (Expr.Ebinop Binop.Oor
                                                                    (Expr.Ebinop Binop.Oor
                                                                    (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    tint)
                                                                    (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Expr.Ebinop Binop.Oshl
                                                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                    (Expr.Econst_int (Integers.Int.repr 3) tint)
                                                                    tint)
                                                                    tint)
                                                                    tlong))
                                                                    Stmt.Sbreak))
                                                                    (LStmts.LScons (some 10238)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'73)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 27) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'73 tint))))
                                                                    (LStmts.LScons (some 10289)
                                                                    (Stmt.Ssequence
                                                                    (Stmt.Scall (some _t'74)
                                                                    (Expr.Evar _Curl_setstropt 
                                                                    (Ty.Tfunction
                                                                    [(tptr (tptr tschar)),
                                                                    (tptr tschar)]
                                                                    tint
                                                                    cc_default))
                                                                    [(Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                                    (Ty.Tstruct _Curl_easy noattr))
                                                                    _set
                                                                    (Ty.Tstruct _UserDefined noattr))
                                                                    _str
                                                                    (tarray (tptr tschar) 55))
                                                                    (Expr.Econst_int (Integers.Int.repr 47) tint)
                                                                    (tptr (tptr tschar))),
                                                                    (Expr.Etempvar _ptr (tptr tschar))])
                                                                    (Stmt.Sreturn (some (Expr.Etempvar _t'74 tint))))
                                                                    (LStmts.LScons none
                                                                    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 48) tint)))
                                                                    LStmts.LSnil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (Stmt.Sreturn (some (Expr.Etempvar _result tint)))))
}

def v_deb_keep : GlobVar Ty := {
  gvar_info := (tptr tvoid),
  gvar_init := [(InitData.Init_addrof _setopt_cptr (Integers.Ptrofs.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def composites : List CompositeDef :=
[(CompositeDef.Composite _ssl_config_data SU.Struct
   [(Member.Member_plain _fsslctxp (tptr tvoid))]
   noattr),
 (CompositeDef.Composite _UserDefined SU.Struct
   [(Member.Member_plain _debugdata (tptr tvoid)),
    (Member.Member_plain _errorbuffer (tptr tschar)),
    (Member.Member_plain _out (tptr tvoid)),
    (Member.Member_plain _in_set (tptr tvoid)),
    (Member.Member_plain _writeheader (tptr tvoid)),
    (Member.Member_plain _postfields (tptr tvoid)),
    (Member.Member_plain _postfieldsize tlong),
    (Member.Member_plain _sockopt_client (tptr tvoid)),
    (Member.Member_plain _opensocket_client (tptr tvoid)),
    (Member.Member_plain _closesocket_client (tptr tvoid)),
    (Member.Member_plain _prereq_userp (tptr tvoid)),
    (Member.Member_plain _seek_client (tptr tvoid)),
    (Member.Member_plain _progress_client (tptr tvoid)),
    (Member.Member_plain _ioctl_client (tptr tvoid)),
    (Member.Member_plain _ssl (Ty.Tstruct _ssl_config_data noattr)),
    (Member.Member_plain _private_data (tptr tvoid)),
    (Member.Member_plain _str (tarray (tptr tschar) 55)),
    (Member.Member_plain _allowed_protocols tlong),
    (Member.Member_plain _redir_protocols tlong),
    (Member.Member_plain _resolver_start_client (tptr tvoid)),
    (Member.Member_plain _uh (tptr (Ty.Tstruct _Curl_URL noattr))),
    (Member.Member_plain _trailer_data (tptr tvoid)),
    (Member.Member_plain _method tuchar),
    (Member.Member_bitfield _haproxyprotocol IntSize.I32 Signedness.Unsigned
      noattr 1 false)]
   noattr),
 (CompositeDef.Composite _digestdata SU.Struct
   [(Member.Member_plain _nonce (tptr tschar))]
   noattr),
 (CompositeDef.Composite _auth SU.Struct
   [(Member.Member_plain _picked tulong)]
   noattr),
 (CompositeDef.Composite _UrlState SU.Struct
   [(Member.Member_plain _proxydigest (Ty.Tstruct _digestdata noattr)),
    (Member.Member_plain _authproxy (Ty.Tstruct _auth noattr)),
    (Member.Member_plain _url (tptr tschar)),
    (Member.Member_plain _referer (tptr tschar)),
    (Member.Member_bitfield _url_alloc IntSize.I32 Signedness.Unsigned noattr
      1 false),
    (Member.Member_bitfield _referer_alloc IntSize.I32 Signedness.Unsigned
      noattr 1 false)]
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
 (_Curl_cfree,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_cfree"
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
 (_setstropt_interface,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "setstropt_interface"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xptr,
                                      XType.Xptr] XType.Xint cc_default))
     [(tptr tschar), (tptr (tptr tschar)), (tptr (tptr tschar)),
      (tptr (tptr tschar))] tint cc_default)),
 (_protocol2num,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "protocol2num"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xint cc_default))
     [(tptr tschar), (tptr tlong)] tint cc_default)),
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
 (_Curl_ssl_set_engine,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_ssl_set_engine"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xint cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar)] tint cc_default)),
 (_Curl_memdup0,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_memdup0"
                                   (mksignature [XType.Xptr, XType.Xlong]
                                     XType.Xptr cc_default))
     [(tptr tschar), tulong] (tptr tvoid) cc_default)),
 (_Curl_all_content_encodings,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_all_content_encodings"
                                   (mksignature [XType.Xptr, XType.Xlong]
                                     XType.Xvoid cc_default))
     [(tptr tschar), tulong] tvoid cc_default)),
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
 (_setopt_cptr, GlobDef.Gfun (FunDef.Internal f_setopt_cptr)),
 (_deb_keep, GlobDef.Gvar v_deb_keep)]

def public_idents : List Ident :=
[_deb_keep, _Curl_auth_digest_cleanup, _memset, _strcmp,
 _Curl_all_content_encodings, _Curl_memdup0, _Curl_ssl_set_engine,
 _Curl_ssl_supports, _Curl_urldecode, _protocol2num, _setstropt_interface,
 _setstropt_userpwd, _Curl_setstropt, _Curl_cfree, ___builtin_debug,
 ___builtin_fmin, ___builtin_fmax, ___builtin_fnmsub, ___builtin_fnmadd,
 ___builtin_fmsub, ___builtin_fmadd, ___builtin_clsll, ___builtin_clsl,
 ___builtin_cls, ___builtin_expect, ___builtin_unreachable,
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

end Deb2026_7168_d1

