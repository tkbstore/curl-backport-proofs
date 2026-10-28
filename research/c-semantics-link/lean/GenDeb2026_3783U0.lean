import Clightdefs
open CC

namespace Deb2026_3783_u0

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
  def source_file : String := "deb2026_3783_u0.c"
  def normalized : Bool := true
end Info

def _ConnectBits : Ident := identOfString "ConnectBits"
def _Curl_checkProxyheaders : Ident := identOfString "Curl_checkProxyheaders"
def _Curl_checkheaders : Ident := identOfString "Curl_checkheaders"
def _Curl_easy : Ident := identOfString "Curl_easy"
def _Curl_infof : Ident := identOfString "Curl_infof"
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
def ___stringlit_6 : Ident := identOfString "__stringlit_6"
def ___stringlit_7 : Ident := identOfString "__stringlit_7"
def ___stringlit_8 : Ident := identOfString "__stringlit_8"
def _aptr : Ident := identOfString "aptr"
def _auth : Ident := identOfString "auth"
def _auth__1 : Ident := identOfString "auth__1"
def _authstatus : Ident := identOfString "authstatus"
def _avail : Ident := identOfString "avail"
def _bits : Ident := identOfString "bits"
def _conn : Ident := identOfString "conn"
def _connectdata : Ident := identOfString "connectdata"
def _data : Ident := identOfString "data"
def _deb2026_3783_keep : Ident := identOfString "deb2026_3783_keep"
def _done : Ident := identOfString "done"
def _dynamically_allocated_data : Ident := identOfString "dynamically_allocated_data"
def _http_output_basic : Ident := identOfString "http_output_basic"
def _http_output_bearer : Ident := identOfString "http_output_bearer"
def _iestyle : Ident := identOfString "iestyle"
def _main : Ident := identOfString "main"
def _multipass : Ident := identOfString "multipass"
def _output_auth_headers : Ident := identOfString "output_auth_headers"
def _path : Ident := identOfString "path"
def _picked : Ident := identOfString "picked"
def _proxy : Ident := identOfString "proxy"
def _proxy_user_passwd : Ident := identOfString "proxy_user_passwd"
def _proxyuser : Ident := identOfString "proxyuser"
def _request : Ident := identOfString "request"
def _result : Ident := identOfString "result"
def _set : Ident := identOfString "set"
def _state : Ident := identOfString "state"
def _str : Ident := identOfString "str"
def _user : Ident := identOfString "user"
def _want : Ident := identOfString "want"
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
def _t'3 : Ident := (Positive.ofNat 130)
def _t'4 : Ident := (Positive.ofNat 131)
def _t'5 : Ident := (Positive.ofNat 132)
def _t'6 : Ident := (Positive.ofNat 133)
def _t'7 : Ident := (Positive.ofNat 134)
def _t'8 : Ident := (Positive.ofNat 135)
def _t'9 : Ident := (Positive.ofNat 136)

def v___stringlit_1 : GlobVar Ty := {
  gvar_info := (tarray tschar 14),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 65)),
                (InitData.Init_int8 (Integers.Int.repr 117)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 104)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 122)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_6 : GlobVar Ty := {
  gvar_info := (tarray tschar 7),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 83)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 118)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_7 : GlobVar Ty := {
  gvar_info := (tarray tschar 6),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 80)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 120)),
                (InitData.Init_int8 (Integers.Int.repr 121)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_3 : GlobVar Ty := {
  gvar_info := (tarray tschar 6),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 66)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 99)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_2 : GlobVar Ty := {
  gvar_info := (tarray tschar 20),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 80)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 120)),
                (InitData.Init_int8 (Integers.Int.repr 121)),
                (InitData.Init_int8 (Integers.Int.repr 45)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 117)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 104)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 122)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_4 : GlobVar Ty := {
  gvar_info := (tarray tschar 7),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 66)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_8 : GlobVar Ty := {
  gvar_info := (tarray tschar 32),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 117)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 104)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 117)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 103)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 119)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 104)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 117)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 39)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 39)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_5 : GlobVar Ty := {
  gvar_info := (tarray tschar 1),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def f_output_auth_headers : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_conn, (tptr (Ty.Tstruct _connectdata noattr))),
                (_authstatus, (tptr (Ty.Tstruct _auth noattr))),
                (_request, (tptr tschar)), (_path, (tptr tschar)),
                (_proxy, tbool)],
  fn_vars := [],
  fn_temps := [(_auth__1, (tptr tschar)), (_result, tint),
               (_t'13, (tptr tschar)), (_t'12, (tptr tschar)),
               (_t'11, (tptr tschar)), (_t'10, tint), (_t'9, tint),
               (_t'8, tint), (_t'7, (tptr tschar)), (_t'6, tint),
               (_t'5, tint), (_t'4, (tptr tschar)), (_t'3, tint),
               (_t'2, tint), (_t'1, tint), (_t'23, tint),
               (_t'22, (tptr tschar)), (_t'21, tuint),
               (_t'20, (tptr tschar)), (_t'19, tuint),
               (_t'18, (tptr tschar)), (_t'17, (tptr tschar)),
               (_t'16, (tptr tschar)), (_t'15, (tptr tschar)), (_t'14, tint)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Sset _auth__1
    (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)))
  (Stmt.Ssequence
    (Stmt.Sset _result (Expr.Econst_int (Integers.Int.repr 0) tint))
    (Stmt.Ssequence
      (Stmt.Ssequence
        (Stmt.Sset _t'21
          (Expr.Efield
            (Expr.Ederef
              (Expr.Etempvar _authstatus (tptr (Ty.Tstruct _auth noattr)))
              (Ty.Tstruct _auth noattr)) _picked tuint))
        (Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq (Expr.Etempvar _t'21 tuint)
                            (Expr.Ebinop Binop.Oshl
                              (Expr.Ecast
                                (Expr.Econst_int (Integers.Int.repr 1) tint)
                                tulong)
                              (Expr.Econst_int (Integers.Int.repr 0) tint)
                              tulong) tint)
          (Stmt.Ssequence
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Sifthenelse (Expr.Etempvar _proxy tbool)
                    (Stmt.Ssequence
                      (Stmt.Sset _t'23
                        (Expr.Efield
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr)))
                              (Ty.Tstruct _connectdata noattr)) _bits
                            (Ty.Tstruct _ConnectBits noattr))
                          _proxy_user_passwd tint))
                      (Stmt.Sset _t'2
                        (Expr.Ecast (Expr.Etempvar _t'23 tint) tbool)))
                    (Stmt.Sset _t'2
                      (Expr.Econst_int (Integers.Int.repr 0) tint)))
                  (Stmt.Sifthenelse (Expr.Etempvar _t'2 tint)
                    (Stmt.Ssequence
                      (Stmt.Scall (some _t'4)
                        (Expr.Evar _Curl_checkProxyheaders (Ty.Tfunction
                                                             [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                              (tptr (Ty.Tstruct _connectdata noattr)),
                                                              (tptr tschar),
                                                              tulong]
                                                             (tptr tschar)
                                                             cc_default))
                        [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                         (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr))),
                         (Expr.Evar ___stringlit_2 (tarray tschar 20)),
                         (Expr.Ebinop Binop.Osub
                           (Expr.Esizeof (tarray tschar 20) tulong)
                           (Expr.Econst_int (Integers.Int.repr 1) tint)
                           tulong)])
                      (Stmt.Sset _t'3
                        (Expr.Ecast
                          (Expr.Eunop Unop.Onotbool
                            (Expr.Etempvar _t'4 (tptr tschar)) tint) tbool)))
                    (Stmt.Sset _t'3
                      (Expr.Econst_int (Integers.Int.repr 0) tint))))
                (Stmt.Sifthenelse (Expr.Etempvar _t'3 tint)
                  (Stmt.Sset _t'5
                    (Expr.Econst_int (Integers.Int.repr 1) tint))
                  (Stmt.Ssequence
                    (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                        (Expr.Etempvar _proxy tbool) tint)
                      (Stmt.Ssequence
                        (Stmt.Sset _t'22
                          (Expr.Efield
                            (Expr.Efield
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                  (Ty.Tstruct _Curl_easy noattr)) _state
                                (Ty.Tstruct _UrlState noattr)) _aptr
                              (Ty.Tstruct _dynamically_allocated_data noattr))
                            _user (tptr tschar)))
                        (Stmt.Sset _t'6
                          (Expr.Ecast (Expr.Etempvar _t'22 (tptr tschar))
                            tbool)))
                      (Stmt.Sset _t'6
                        (Expr.Econst_int (Integers.Int.repr 0) tint)))
                    (Stmt.Sifthenelse (Expr.Etempvar _t'6 tint)
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Scall (some _t'7)
                            (Expr.Evar _Curl_checkheaders (Ty.Tfunction
                                                            [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                             (tptr tschar),
                                                             tulong]
                                                            (tptr tschar)
                                                            cc_default))
                            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                             (Expr.Evar ___stringlit_1 (tarray tschar 14)),
                             (Expr.Ebinop Binop.Osub
                               (Expr.Esizeof (tarray tschar 14) tulong)
                               (Expr.Econst_int (Integers.Int.repr 1) tint)
                               tulong)])
                          (Stmt.Sset _t'5
                            (Expr.Ecast
                              (Expr.Eunop Unop.Onotbool
                                (Expr.Etempvar _t'7 (tptr tschar)) tint)
                              tbool)))
                        (Stmt.Sset _t'5
                          (Expr.Ecast (Expr.Etempvar _t'5 tint) tbool)))
                      (Stmt.Sset _t'5
                        (Expr.Ecast
                          (Expr.Econst_int (Integers.Int.repr 0) tint) tbool))))))
              (Stmt.Sifthenelse (Expr.Etempvar _t'5 tint)
                (Stmt.Ssequence
                  (Stmt.Sset _auth__1
                    (Expr.Evar ___stringlit_3 (tarray tschar 6)))
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Scall (some _t'1)
                        (Expr.Evar _http_output_basic (Ty.Tfunction
                                                        [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                         tbool] tint
                                                        cc_default))
                        [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                         (Expr.Etempvar _proxy tbool)])
                      (Stmt.Sset _result (Expr.Etempvar _t'1 tint)))
                    (Stmt.Sifthenelse (Expr.Etempvar _result tint)
                      (Stmt.Sreturn (some (Expr.Etempvar _result tint)))
                      Stmt.Sskip)))
                Stmt.Sskip))
            (Stmt.Sassign
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _authstatus (tptr (Ty.Tstruct _auth noattr)))
                  (Ty.Tstruct _auth noattr)) _done tint)
              (Expr.Econst_int (Integers.Int.repr 1) tint)))
          Stmt.Sskip))
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Sset _t'19
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _authstatus (tptr (Ty.Tstruct _auth noattr)))
                (Ty.Tstruct _auth noattr)) _picked tuint))
          (Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq
                              (Expr.Etempvar _t'19 tuint)
                              (Expr.Ebinop Binop.Oshl
                                (Expr.Ecast
                                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                                  tulong)
                                (Expr.Econst_int (Integers.Int.repr 6) tint)
                                tulong) tint)
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                      (Expr.Etempvar _proxy tbool) tint)
                    (Stmt.Ssequence
                      (Stmt.Sset _t'20
                        (Expr.Ederef
                          (Expr.Ebinop Binop.Oadd
                            (Expr.Efield
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                  (Ty.Tstruct _Curl_easy noattr)) _set
                                (Ty.Tstruct _UserDefined noattr)) _str
                              (tarray (tptr tschar) 70))
                            (Expr.Econst_int (Integers.Int.repr 56) tint)
                            (tptr (tptr tschar))) (tptr tschar)))
                      (Stmt.Sset _t'9
                        (Expr.Ecast (Expr.Etempvar _t'20 (tptr tschar))
                          tbool)))
                    (Stmt.Sset _t'9
                      (Expr.Econst_int (Integers.Int.repr 0) tint)))
                  (Stmt.Sifthenelse (Expr.Etempvar _t'9 tint)
                    (Stmt.Ssequence
                      (Stmt.Scall (some _t'11)
                        (Expr.Evar _Curl_checkheaders (Ty.Tfunction
                                                        [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                         (tptr tschar),
                                                         tulong]
                                                        (tptr tschar)
                                                        cc_default))
                        [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                         (Expr.Evar ___stringlit_1 (tarray tschar 14)),
                         (Expr.Ebinop Binop.Osub
                           (Expr.Esizeof (tarray tschar 14) tulong)
                           (Expr.Econst_int (Integers.Int.repr 1) tint)
                           tulong)])
                      (Stmt.Sset _t'10
                        (Expr.Ecast
                          (Expr.Eunop Unop.Onotbool
                            (Expr.Etempvar _t'11 (tptr tschar)) tint) tbool)))
                    (Stmt.Sset _t'10
                      (Expr.Econst_int (Integers.Int.repr 0) tint))))
                (Stmt.Sifthenelse (Expr.Etempvar _t'10 tint)
                  (Stmt.Ssequence
                    (Stmt.Sset _auth__1
                      (Expr.Evar ___stringlit_4 (tarray tschar 7)))
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Scall (some _t'8)
                          (Expr.Evar _http_output_bearer (Ty.Tfunction
                                                           [(tptr (Ty.Tstruct _Curl_easy noattr))]
                                                           tint cc_default))
                          [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))])
                        (Stmt.Sset _result (Expr.Etempvar _t'8 tint)))
                      (Stmt.Sifthenelse (Expr.Etempvar _result tint)
                        (Stmt.Sreturn (some (Expr.Etempvar _result tint)))
                        Stmt.Sskip)))
                  Stmt.Sskip))
              (Stmt.Sassign
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _authstatus (tptr (Ty.Tstruct _auth noattr)))
                    (Ty.Tstruct _auth noattr)) _done tint)
                (Expr.Econst_int (Integers.Int.repr 1) tint)))
            Stmt.Sskip))
        (Stmt.Ssequence
          (Stmt.Sifthenelse (Expr.Etempvar _auth__1 (tptr tschar))
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Sifthenelse (Expr.Etempvar _proxy tbool)
                    (Stmt.Sset _t'12
                      (Expr.Ecast
                        (Expr.Evar ___stringlit_7 (tarray tschar 6))
                        (tptr tschar)))
                    (Stmt.Sset _t'12
                      (Expr.Ecast
                        (Expr.Evar ___stringlit_6 (tarray tschar 7))
                        (tptr tschar))))
                  (Stmt.Sifthenelse (Expr.Etempvar _proxy tbool)
                    (Stmt.Ssequence
                      (Stmt.Sset _t'17
                        (Expr.Efield
                          (Expr.Efield
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                (Ty.Tstruct _Curl_easy noattr)) _state
                              (Ty.Tstruct _UrlState noattr)) _aptr
                            (Ty.Tstruct _dynamically_allocated_data noattr))
                          _proxyuser (tptr tschar)))
                      (Stmt.Sifthenelse (Expr.Etempvar _t'17 (tptr tschar))
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'18
                              (Expr.Efield
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                      (Ty.Tstruct _Curl_easy noattr)) _state
                                    (Ty.Tstruct _UrlState noattr)) _aptr
                                  (Ty.Tstruct _dynamically_allocated_data noattr))
                                _proxyuser (tptr tschar)))
                            (Stmt.Sset _t'13
                              (Expr.Ecast (Expr.Etempvar _t'18 (tptr tschar))
                                (tptr tschar))))
                          (Stmt.Sset _t'13
                            (Expr.Ecast (Expr.Etempvar _t'13 (tptr tschar))
                              (tptr tschar))))
                        (Stmt.Ssequence
                          (Stmt.Sset _t'13
                            (Expr.Ecast
                              (Expr.Evar ___stringlit_5 (tarray tschar 1))
                              (tptr tschar)))
                          (Stmt.Sset _t'13
                            (Expr.Ecast (Expr.Etempvar _t'13 (tptr tschar))
                              (tptr tschar))))))
                    (Stmt.Ssequence
                      (Stmt.Sset _t'15
                        (Expr.Efield
                          (Expr.Efield
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                (Ty.Tstruct _Curl_easy noattr)) _state
                              (Ty.Tstruct _UrlState noattr)) _aptr
                            (Ty.Tstruct _dynamically_allocated_data noattr))
                          _user (tptr tschar)))
                      (Stmt.Sifthenelse (Expr.Etempvar _t'15 (tptr tschar))
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'16
                              (Expr.Efield
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                      (Ty.Tstruct _Curl_easy noattr)) _state
                                    (Ty.Tstruct _UrlState noattr)) _aptr
                                  (Ty.Tstruct _dynamically_allocated_data noattr))
                                _user (tptr tschar)))
                            (Stmt.Sset _t'13
                              (Expr.Ecast (Expr.Etempvar _t'16 (tptr tschar))
                                (tptr tschar))))
                          (Stmt.Sset _t'13
                            (Expr.Ecast (Expr.Etempvar _t'13 (tptr tschar))
                              (tptr tschar))))
                        (Stmt.Ssequence
                          (Stmt.Sset _t'13
                            (Expr.Ecast
                              (Expr.Evar ___stringlit_5 (tarray tschar 1))
                              (tptr tschar)))
                          (Stmt.Sset _t'13
                            (Expr.Ecast (Expr.Etempvar _t'13 (tptr tschar))
                              (tptr tschar))))))))
                (Stmt.Scall none
                  (Expr.Evar _Curl_infof (Ty.Tfunction
                                           [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                            (tptr tschar)] tvoid
                                           { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                  [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                   (Expr.Evar ___stringlit_8 (tarray tschar 32)),
                   (Expr.Etempvar _t'12 (tptr tschar)),
                   (Expr.Etempvar _auth__1 (tptr tschar)),
                   (Expr.Etempvar _t'13 (tptr tschar))]))
              (Stmt.Ssequence
                (Stmt.Sset _t'14
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _authstatus (tptr (Ty.Tstruct _auth noattr)))
                      (Ty.Tstruct _auth noattr)) _done tint))
                (Stmt.Sassign
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _authstatus (tptr (Ty.Tstruct _auth noattr)))
                      (Ty.Tstruct _auth noattr)) _multipass tint)
                  (Expr.Eunop Unop.Onotbool (Expr.Etempvar _t'14 tint) tint))))
            (Stmt.Sassign
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _authstatus (tptr (Ty.Tstruct _auth noattr)))
                  (Ty.Tstruct _auth noattr)) _multipass tint)
              (Expr.Econst_int (Integers.Int.repr 0) tint)))
          (Stmt.Sreturn (some (Expr.Etempvar _result tint))))))))
}

def v_deb2026_3783_keep : GlobVar Ty := {
  gvar_info := (tptr (Ty.Tfunction
                       [(tptr (Ty.Tstruct _Curl_easy noattr)),
                        (tptr (Ty.Tstruct _connectdata noattr)),
                        (tptr (Ty.Tstruct _auth noattr)), (tptr tschar),
                        (tptr tschar), tbool] tint cc_default)),
  gvar_init := [(InitData.Init_addrof _output_auth_headers (Integers.Ptrofs.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def composites : List CompositeDef :=
[(CompositeDef.Composite _auth SU.Struct
   [(Member.Member_plain _want tuint), (Member.Member_plain _picked tuint),
    (Member.Member_plain _avail tuint),
    (Member.Member_bitfield _done IntSize.I32 Signedness.Unsigned noattr 1
      false),
    (Member.Member_bitfield _multipass IntSize.I32 Signedness.Unsigned noattr
      1 false),
    (Member.Member_bitfield _iestyle IntSize.I32 Signedness.Unsigned noattr 1
      false)]
   noattr),
 (CompositeDef.Composite _ConnectBits SU.Struct
   [(Member.Member_bitfield _proxy_user_passwd IntSize.I32
      Signedness.Unsigned noattr 1 false)]
   noattr),
 (CompositeDef.Composite _connectdata SU.Struct
   [(Member.Member_plain _bits (Ty.Tstruct _ConnectBits noattr))]
   noattr),
 (CompositeDef.Composite _dynamically_allocated_data SU.Struct
   [(Member.Member_plain _user (tptr tschar)),
    (Member.Member_plain _proxyuser (tptr tschar))]
   noattr),
 (CompositeDef.Composite _UrlState SU.Struct
   [(Member.Member_plain _aptr
      (Ty.Tstruct _dynamically_allocated_data noattr))]
   noattr),
 (CompositeDef.Composite _UserDefined SU.Struct
   [(Member.Member_plain _str (tarray (tptr tschar) 70))]
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
 (___stringlit_6, GlobDef.Gvar v___stringlit_6),
 (___stringlit_7, GlobDef.Gvar v___stringlit_7),
 (___stringlit_3, GlobDef.Gvar v___stringlit_3),
 (___stringlit_2, GlobDef.Gvar v___stringlit_2),
 (___stringlit_4, GlobDef.Gvar v___stringlit_4),
 (___stringlit_8, GlobDef.Gvar v___stringlit_8),
 (___stringlit_5, GlobDef.Gvar v___stringlit_5),
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
 (_Curl_checkProxyheaders,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_checkProxyheaders"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xptr,
                                      XType.Xlong] XType.Xptr cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)),
      (tptr (Ty.Tstruct _connectdata noattr)), (tptr tschar), tulong]
     (tptr tschar) cc_default)),
 (_Curl_checkheaders,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_checkheaders"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xlong]
                                     XType.Xptr cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar), tulong]
     (tptr tschar) cc_default)),
 (_http_output_basic,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "http_output_basic"
                                   (mksignature [XType.Xptr, XType.Xbool]
                                     XType.Xint cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), tbool] tint cc_default)),
 (_http_output_bearer,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "http_output_bearer"
                                   (mksignature [XType.Xptr] XType.Xint
                                     cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr))] tint cc_default)),
 (_Curl_infof,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_infof"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xvoid
                                     { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar)] tvoid
     { cc_vararg := (some 2), cc_unproto := false, cc_structret := false })),
 (_output_auth_headers, GlobDef.Gfun (FunDef.Internal f_output_auth_headers)),
 (_deb2026_3783_keep, GlobDef.Gvar v_deb2026_3783_keep)]

def public_idents : List Ident :=
[_deb2026_3783_keep, _Curl_infof, _http_output_bearer, _http_output_basic,
 _Curl_checkheaders, _Curl_checkProxyheaders, ___builtin_debug,
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

end Deb2026_3783_u0

