import Clightdefs
open CC

namespace DebBookworm2023_27533_u0

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
  def source_file : String := "debbookworm2023_27533_u0.c"
  def normalized : Bool := true
end Info

def _Curl_easy : Ident := identOfString "Curl_easy"
def _Curl_failf : Ident := identOfString "Curl_failf"
def _Curl_raw_tolower : Ident := identOfString "Curl_raw_tolower"
def _Curl_strncasecompare : Ident := identOfString "Curl_strncasecompare"
def _SingleRequest : Ident := identOfString "SingleRequest"
def _TELNET : Ident := identOfString "TELNET"
def _UrlState : Ident := identOfString "UrlState"
def _UserDefined : Ident := identOfString "UserDefined"
def __105 : Ident := identOfString "_105"
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
def _arg : Ident := identOfString "arg"
def _atoi : Ident := identOfString "atoi"
def _beg : Ident := identOfString "beg"
def _binary_option : Ident := identOfString "binary_option"
def _buffer : Ident := identOfString "buffer"
def _check_telnet_options : Ident := identOfString "check_telnet_options"
def _conn : Ident := identOfString "conn"
def _connectdata : Ident := identOfString "connectdata"
def _curl_msnprintf : Ident := identOfString "curl_msnprintf"
def _curl_slist : Ident := identOfString "curl_slist"
def _curl_slist_append : Ident := identOfString "curl_slist_append"
def _curl_slist_free_all : Ident := identOfString "curl_slist_free_all"
def _data : Ident := identOfString "data"
def _debbookworm2023_27533_keep : Ident := identOfString "debbookworm2023_27533_keep"
def _dynamically_allocated_data : Ident := identOfString "dynamically_allocated_data"
def _head : Ident := identOfString "head"
def _him_preferred : Ident := identOfString "him_preferred"
def _main : Ident := identOfString "main"
def _next : Ident := identOfString "next"
def _olen : Ident := identOfString "olen"
def _option : Ident := identOfString "option"
def _p : Ident := identOfString "p"
def _req : Ident := identOfString "req"
def _result : Ident := identOfString "result"
def _sep : Ident := identOfString "sep"
def _set : Ident := identOfString "set"
def _state : Ident := identOfString "state"
def _strchr : Ident := identOfString "strchr"
def _strncpy : Ident := identOfString "strncpy"
def _strtoul : Ident := identOfString "strtoul"
def _subopt_ttype : Ident := identOfString "subopt_ttype"
def _subopt_wsx : Ident := identOfString "subopt_wsx"
def _subopt_wsy : Ident := identOfString "subopt_wsy"
def _subopt_xdisploc : Ident := identOfString "subopt_xdisploc"
def _telnet : Ident := identOfString "telnet"
def _telnet_options : Ident := identOfString "telnet_options"
def _telnet_vars : Ident := identOfString "telnet_vars"
def _tn : Ident := identOfString "tn"
def _us_preferred : Ident := identOfString "us_preferred"
def _user : Ident := identOfString "user"
def _x : Ident := identOfString "x"
def _y : Ident := identOfString "y"
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
def _t'4 : Ident := (Positive.ofNat 131)
def _t'5 : Ident := (Positive.ofNat 132)
def _t'6 : Ident := (Positive.ofNat 133)
def _t'7 : Ident := (Positive.ofNat 134)
def _t'8 : Ident := (Positive.ofNat 135)
def _t'9 : Ident := (Positive.ofNat 136)

def v___stringlit_7 : GlobVar Ty := {
  gvar_info := (tarray tschar 9),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 88)),
                (InitData.Init_int8 (Integers.Int.repr 68)),
                (InitData.Init_int8 (Integers.Int.repr 73)),
                (InitData.Init_int8 (Integers.Int.repr 83)),
                (InitData.Init_int8 (Integers.Int.repr 80)),
                (InitData.Init_int8 (Integers.Int.repr 76)),
                (InitData.Init_int8 (Integers.Int.repr 79)),
                (InitData.Init_int8 (Integers.Int.repr 67)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_3 : GlobVar Ty := {
  gvar_info := (tarray tschar 25),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 85)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 107)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 119)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_2 : GlobVar Ty := {
  gvar_info := (tarray tschar 34),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 83)),
                (InitData.Init_int8 (Integers.Int.repr 121)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 120)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 108)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 58)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_1 : GlobVar Ty := {
  gvar_info := (tarray tschar 8),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 85)),
                (InitData.Init_int8 (Integers.Int.repr 83)),
                (InitData.Init_int8 (Integers.Int.repr 69)),
                (InitData.Init_int8 (Integers.Int.repr 82)),
                (InitData.Init_int8 (Integers.Int.repr 44)),
                (InitData.Init_int8 (Integers.Int.repr 37)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_5 : GlobVar Ty := {
  gvar_info := (tarray tschar 3),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 87)),
                (InitData.Init_int8 (Integers.Int.repr 83)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_8 : GlobVar Ty := {
  gvar_info := (tarray tschar 6),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 84)),
                (InitData.Init_int8 (Integers.Int.repr 84)),
                (InitData.Init_int8 (Integers.Int.repr 89)),
                (InitData.Init_int8 (Integers.Int.repr 80)),
                (InitData.Init_int8 (Integers.Int.repr 69)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_4 : GlobVar Ty := {
  gvar_info := (tarray tschar 7),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 66)),
                (InitData.Init_int8 (Integers.Int.repr 73)),
                (InitData.Init_int8 (Integers.Int.repr 78)),
                (InitData.Init_int8 (Integers.Int.repr 65)),
                (InitData.Init_int8 (Integers.Int.repr 82)),
                (InitData.Init_int8 (Integers.Int.repr 89)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_6 : GlobVar Ty := {
  gvar_info := (tarray tschar 8),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 78)),
                (InitData.Init_int8 (Integers.Int.repr 69)),
                (InitData.Init_int8 (Integers.Int.repr 87)),
                (InitData.Init_int8 (Integers.Int.repr 95)),
                (InitData.Init_int8 (Integers.Int.repr 69)),
                (InitData.Init_int8 (Integers.Int.repr 78)),
                (InitData.Init_int8 (Integers.Int.repr 86)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def f_check_telnet_options : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr)))],
  fn_vars := [(_buffer, (tarray tschar 256)), (_p, (tptr tschar))],
  fn_temps := [(_head, (tptr (Ty.Tstruct _curl_slist noattr))),
               (_beg, (tptr (Ty.Tstruct _curl_slist noattr))),
               (_tn, (tptr (Ty.Tstruct _TELNET noattr))), (_result, tint),
               (_olen, tulong), (_option, (tptr tschar)),
               (_arg, (tptr tschar)), (_sep, (tptr tschar)), (_x, tulong),
               (_y, tulong), (_binary_option, tint), (_t'17, tint),
               (_t'16, tint), (_t'15, tint), (_t'14, tschar), (_t'13, tint),
               (_t'12, tint), (_t'11, tint), (_t'10, tulong), (_t'9, tulong),
               (_t'8, tint), (_t'7, (tptr (Ty.Tstruct _curl_slist noattr))),
               (_t'6, tint), (_t'5, tint), (_t'4, (tptr tschar)),
               (_t'3, (tptr tschar)), (_t'2, tint),
               (_t'1, (tptr (Ty.Tstruct _curl_slist noattr))),
               (_t'31, (tptr tschar)),
               (_t'30, (tptr (Ty.Tstruct _connectdata noattr))),
               (_t'29, (tptr (Ty.Tstruct _curl_slist noattr))),
               (_t'28, (tptr (Ty.Tstruct _curl_slist noattr))),
               (_t'27, (tptr tschar)),
               (_t'26, (tptr (Ty.Tstruct _curl_slist noattr))),
               (_t'25, tschar), (_t'24, (tptr tschar)),
               (_t'23, (tptr tschar)), (_t'22, (tptr tschar)),
               (_t'21, (tptr tschar)), (_t'20, (tptr tschar)),
               (_t'19, (tptr tschar)),
               (_t'18, (tptr (Ty.Tstruct _curl_slist noattr)))],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Sset _tn
    (Expr.Efield
      (Expr.Efield
        (Expr.Efield
          (Expr.Ederef
            (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
            (Ty.Tstruct _Curl_easy noattr)) _req
          (Ty.Tstruct _SingleRequest noattr)) _p (Ty.Tstruct __105 noattr))
      _telnet (tptr (Ty.Tstruct _TELNET noattr))))
  (Stmt.Ssequence
    (Stmt.Sset _result (Expr.Econst_int (Integers.Int.repr 0) tint))
    (Stmt.Ssequence
      (Stmt.Ssequence
        (Stmt.Sset _t'27
          (Expr.Efield
            (Expr.Efield
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                  (Ty.Tstruct _Curl_easy noattr)) _state
                (Ty.Tstruct _UrlState noattr)) _aptr
              (Ty.Tstruct _dynamically_allocated_data noattr)) _user
            (tptr tschar)))
        (Stmt.Sifthenelse (Expr.Etempvar _t'27 (tptr tschar))
          (Stmt.Ssequence
            (Stmt.Ssequence
              (Stmt.Sset _t'30
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                    (Ty.Tstruct _Curl_easy noattr)) _conn
                  (tptr (Ty.Tstruct _connectdata noattr))))
              (Stmt.Ssequence
                (Stmt.Sset _t'31
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _t'30 (tptr (Ty.Tstruct _connectdata noattr)))
                      (Ty.Tstruct _connectdata noattr)) _user (tptr tschar)))
                (Stmt.Scall none
                  (Expr.Evar _curl_msnprintf (Ty.Tfunction
                                               [(tptr tschar), tulong,
                                                (tptr tschar), (tptr tschar)]
                                               tint cc_default))
                  [(Expr.Evar _buffer (tarray tschar 256)),
                   (Expr.Esizeof (tarray tschar 256) tulong),
                   (Expr.Evar ___stringlit_1 (tarray tschar 8)),
                   (Expr.Etempvar _t'31 (tptr tschar))])))
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Sset _t'29
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                        (Ty.Tstruct _TELNET noattr)) _telnet_vars
                      (tptr (Ty.Tstruct _curl_slist noattr))))
                  (Stmt.Scall (some _t'1)
                    (Expr.Evar _curl_slist_append (Ty.Tfunction
                                                    [(tptr (Ty.Tstruct _curl_slist noattr)),
                                                     (tptr tschar)]
                                                    (tptr (Ty.Tstruct _curl_slist noattr))
                                                    cc_default))
                    [(Expr.Etempvar _t'29 (tptr (Ty.Tstruct _curl_slist noattr))),
                     (Expr.Evar _buffer (tarray tschar 256))]))
                (Stmt.Sset _beg
                  (Expr.Etempvar _t'1 (tptr (Ty.Tstruct _curl_slist noattr)))))
              (Stmt.Ssequence
                (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                    (Expr.Etempvar _beg (tptr (Ty.Tstruct _curl_slist noattr)))
                                    tint)
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sset _t'28
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                            (Ty.Tstruct _TELNET noattr)) _telnet_vars
                          (tptr (Ty.Tstruct _curl_slist noattr))))
                      (Stmt.Scall none
                        (Expr.Evar _curl_slist_free_all (Ty.Tfunction
                                                          [(tptr (Ty.Tstruct _curl_slist noattr))]
                                                          tvoid cc_default))
                        [(Expr.Etempvar _t'28 (tptr (Ty.Tstruct _curl_slist noattr)))]))
                    (Stmt.Ssequence
                      (Stmt.Sassign
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                            (Ty.Tstruct _TELNET noattr)) _telnet_vars
                          (tptr (Ty.Tstruct _curl_slist noattr)))
                        (Expr.Ecast
                          (Expr.Econst_int (Integers.Int.repr 0) tint)
                          (tptr tvoid)))
                      (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 27) tint)))))
                  Stmt.Sskip)
                (Stmt.Ssequence
                  (Stmt.Sassign
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                        (Ty.Tstruct _TELNET noattr)) _telnet_vars
                      (tptr (Ty.Tstruct _curl_slist noattr)))
                    (Expr.Etempvar _beg (tptr (Ty.Tstruct _curl_slist noattr))))
                  (Stmt.Sassign
                    (Expr.Ederef
                      (Expr.Ebinop Binop.Oadd
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                            (Ty.Tstruct _TELNET noattr)) _us_preferred
                          (tarray tint 256))
                        (Expr.Econst_int (Integers.Int.repr 39) tint)
                        (tptr tint)) tint)
                    (Expr.Econst_int (Integers.Int.repr 1) tint))))))
          Stmt.Sskip))
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Sset _head
            (Expr.Efield
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                  (Ty.Tstruct _Curl_easy noattr)) _set
                (Ty.Tstruct _UserDefined noattr)) _telnet_options
              (tptr (Ty.Tstruct _curl_slist noattr))))
          (Stmt.Sloop
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Sifthenelse (Expr.Etempvar _head (tptr (Ty.Tstruct _curl_slist noattr)))
                  (Stmt.Sset _t'2
                    (Expr.Ecast
                      (Expr.Eunop Unop.Onotbool (Expr.Etempvar _result tint)
                        tint) tbool))
                  (Stmt.Sset _t'2
                    (Expr.Econst_int (Integers.Int.repr 0) tint)))
                (Stmt.Sifthenelse (Expr.Etempvar _t'2 tint)
                  Stmt.Sskip
                  Stmt.Sbreak))
              (Stmt.Ssequence
                (Stmt.Sset _option
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _head (tptr (Ty.Tstruct _curl_slist noattr)))
                      (Ty.Tstruct _curl_slist noattr)) _data (tptr tschar)))
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Scall (some _t'3)
                      (Expr.Evar _strchr (Ty.Tfunction [(tptr tschar), tint]
                                           (tptr tschar) cc_default))
                      [(Expr.Etempvar _option (tptr tschar)),
                       (Expr.Econst_int (Integers.Int.repr 61) tint)])
                    (Stmt.Sset _sep (Expr.Etempvar _t'3 (tptr tschar))))
                  (Stmt.Sifthenelse (Expr.Etempvar _sep (tptr tschar))
                    (Stmt.Ssequence
                      (Stmt.Sset _olen
                        (Expr.Ebinop Binop.Osub
                          (Expr.Etempvar _sep (tptr tschar))
                          (Expr.Etempvar _option (tptr tschar)) tlong))
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'4
                              (Expr.Ecast
                                (Expr.Ebinop Binop.Oadd
                                  (Expr.Etempvar _sep (tptr tschar))
                                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                                  (tptr tschar)) (tptr tschar)))
                            (Stmt.Sset _sep
                              (Expr.Etempvar _t'4 (tptr tschar))))
                          (Stmt.Sset _arg (Expr.Etempvar _t'4 (tptr tschar))))
                        (Stmt.Sswitch (Expr.Etempvar _olen tulong)
                          (LStmts.LScons (some 5)
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Scall (some _t'5)
                                  (Expr.Evar _Curl_strncasecompare (Ty.Tfunction
                                                                    [(tptr tschar),
                                                                    (tptr tschar),
                                                                    tulong]
                                                                    tint
                                                                    cc_default))
                                  [(Expr.Etempvar _option (tptr tschar)),
                                   (Expr.Evar ___stringlit_8 (tarray tschar 6)),
                                   (Expr.Econst_int (Integers.Int.repr 5) tint)])
                                (Stmt.Sifthenelse (Expr.Etempvar _t'5 tint)
                                  (Stmt.Ssequence
                                    (Stmt.Scall none
                                      (Expr.Evar _strncpy (Ty.Tfunction
                                                            [(tptr tschar),
                                                             (tptr tschar),
                                                             tulong]
                                                            (tptr tschar)
                                                            cc_default))
                                      [(Expr.Efield
                                         (Expr.Ederef
                                           (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                           (Ty.Tstruct _TELNET noattr))
                                         _subopt_ttype (tarray tschar 32)),
                                       (Expr.Etempvar _arg (tptr tschar)),
                                       (Expr.Econst_int (Integers.Int.repr 31) tint)])
                                    (Stmt.Ssequence
                                      (Stmt.Sassign
                                        (Expr.Ederef
                                          (Expr.Ebinop Binop.Oadd
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                                (Ty.Tstruct _TELNET noattr))
                                              _subopt_ttype
                                              (tarray tschar 32))
                                            (Expr.Econst_int (Integers.Int.repr 31) tint)
                                            (tptr tschar)) tschar)
                                        (Expr.Econst_int (Integers.Int.repr 0) tint))
                                      (Stmt.Sassign
                                        (Expr.Ederef
                                          (Expr.Ebinop Binop.Oadd
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                                (Ty.Tstruct _TELNET noattr))
                                              _us_preferred
                                              (tarray tint 256))
                                            (Expr.Econst_int (Integers.Int.repr 24) tint)
                                            (tptr tint)) tint)
                                        (Expr.Econst_int (Integers.Int.repr 1) tint))))
                                  (Stmt.Sset _result
                                    (Expr.Econst_int (Integers.Int.repr 48) tint))))
                              Stmt.Sbreak)
                            (LStmts.LScons (some 8)
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Scall (some _t'6)
                                    (Expr.Evar _Curl_strncasecompare 
                                    (Ty.Tfunction
                                      [(tptr tschar), (tptr tschar), tulong]
                                      tint cc_default))
                                    [(Expr.Etempvar _option (tptr tschar)),
                                     (Expr.Evar ___stringlit_7 (tarray tschar 9)),
                                     (Expr.Econst_int (Integers.Int.repr 8) tint)])
                                  (Stmt.Sifthenelse (Expr.Etempvar _t'6 tint)
                                    (Stmt.Ssequence
                                      (Stmt.Scall none
                                        (Expr.Evar _strncpy (Ty.Tfunction
                                                              [(tptr tschar),
                                                               (tptr tschar),
                                                               tulong]
                                                              (tptr tschar)
                                                              cc_default))
                                        [(Expr.Efield
                                           (Expr.Ederef
                                             (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                             (Ty.Tstruct _TELNET noattr))
                                           _subopt_xdisploc
                                           (tarray tschar 128)),
                                         (Expr.Etempvar _arg (tptr tschar)),
                                         (Expr.Econst_int (Integers.Int.repr 127) tint)])
                                      (Stmt.Ssequence
                                        (Stmt.Sassign
                                          (Expr.Ederef
                                            (Expr.Ebinop Binop.Oadd
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                                  (Ty.Tstruct _TELNET noattr))
                                                _subopt_xdisploc
                                                (tarray tschar 128))
                                              (Expr.Econst_int (Integers.Int.repr 127) tint)
                                              (tptr tschar)) tschar)
                                          (Expr.Econst_int (Integers.Int.repr 0) tint))
                                        (Stmt.Sassign
                                          (Expr.Ederef
                                            (Expr.Ebinop Binop.Oadd
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                                  (Ty.Tstruct _TELNET noattr))
                                                _us_preferred
                                                (tarray tint 256))
                                              (Expr.Econst_int (Integers.Int.repr 35) tint)
                                              (tptr tint)) tint)
                                          (Expr.Econst_int (Integers.Int.repr 1) tint))))
                                    (Stmt.Sset _result
                                      (Expr.Econst_int (Integers.Int.repr 48) tint))))
                                Stmt.Sbreak)
                              (LStmts.LScons (some 7)
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Scall (some _t'8)
                                      (Expr.Evar _Curl_strncasecompare 
                                      (Ty.Tfunction
                                        [(tptr tschar), (tptr tschar),
                                         tulong] tint cc_default))
                                      [(Expr.Etempvar _option (tptr tschar)),
                                       (Expr.Evar ___stringlit_6 (tarray tschar 8)),
                                       (Expr.Econst_int (Integers.Int.repr 7) tint)])
                                    (Stmt.Sifthenelse (Expr.Etempvar _t'8 tint)
                                      (Stmt.Ssequence
                                        (Stmt.Ssequence
                                          (Stmt.Ssequence
                                            (Stmt.Sset _t'26
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                                  (Ty.Tstruct _TELNET noattr))
                                                _telnet_vars
                                                (tptr (Ty.Tstruct _curl_slist noattr))))
                                            (Stmt.Scall (some _t'7)
                                              (Expr.Evar _curl_slist_append 
                                              (Ty.Tfunction
                                                [(tptr (Ty.Tstruct _curl_slist noattr)),
                                                 (tptr tschar)]
                                                (tptr (Ty.Tstruct _curl_slist noattr))
                                                cc_default))
                                              [(Expr.Etempvar _t'26 (tptr (Ty.Tstruct _curl_slist noattr))),
                                               (Expr.Etempvar _arg (tptr tschar))]))
                                          (Stmt.Sset _beg
                                            (Expr.Etempvar _t'7 (tptr (Ty.Tstruct _curl_slist noattr)))))
                                        (Stmt.Ssequence
                                          (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                                              (Expr.Etempvar _beg (tptr (Ty.Tstruct _curl_slist noattr)))
                                                              tint)
                                            (Stmt.Ssequence
                                              (Stmt.Sset _result
                                                (Expr.Econst_int (Integers.Int.repr 27) tint))
                                              Stmt.Sbreak)
                                            Stmt.Sskip)
                                          (Stmt.Ssequence
                                            (Stmt.Sassign
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                                  (Ty.Tstruct _TELNET noattr))
                                                _telnet_vars
                                                (tptr (Ty.Tstruct _curl_slist noattr)))
                                              (Expr.Etempvar _beg (tptr (Ty.Tstruct _curl_slist noattr))))
                                            (Stmt.Sassign
                                              (Expr.Ederef
                                                (Expr.Ebinop Binop.Oadd
                                                  (Expr.Efield
                                                    (Expr.Ederef
                                                      (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                                      (Ty.Tstruct _TELNET noattr))
                                                    _us_preferred
                                                    (tarray tint 256))
                                                  (Expr.Econst_int (Integers.Int.repr 39) tint)
                                                  (tptr tint)) tint)
                                              (Expr.Econst_int (Integers.Int.repr 1) tint)))))
                                      (Stmt.Sset _result
                                        (Expr.Econst_int (Integers.Int.repr 48) tint))))
                                  Stmt.Sbreak)
                                (LStmts.LScons (some 2)
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Scall (some _t'15)
                                        (Expr.Evar _Curl_strncasecompare 
                                        (Ty.Tfunction
                                          [(tptr tschar), (tptr tschar),
                                           tulong] tint cc_default))
                                        [(Expr.Etempvar _option (tptr tschar)),
                                         (Expr.Evar ___stringlit_5 (tarray tschar 3)),
                                         (Expr.Econst_int (Integers.Int.repr 2) tint)])
                                      (Stmt.Sifthenelse (Expr.Etempvar _t'15 tint)
                                        (Stmt.Ssequence
                                          (Stmt.Ssequence
                                            (Stmt.Scall (some _t'9)
                                              (Expr.Evar _strtoul (Ty.Tfunction
                                                                    [(tptr tschar),
                                                                    (tptr (tptr tschar)),
                                                                    tint]
                                                                    tulong
                                                                    cc_default))
                                              [(Expr.Etempvar _arg (tptr tschar)),
                                               (Expr.Eaddrof
                                                 (Expr.Evar _p (tptr tschar))
                                                 (tptr (tptr tschar))),
                                               (Expr.Econst_int (Integers.Int.repr 10) tint)])
                                            (Stmt.Sset _x
                                              (Expr.Etempvar _t'9 tulong)))
                                          (Stmt.Ssequence
                                            (Stmt.Sset _y
                                              (Expr.Ecast
                                                (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                tulong))
                                            (Stmt.Ssequence
                                              (Stmt.Ssequence
                                                (Stmt.Ssequence
                                                  (Stmt.Sifthenelse (Expr.Etempvar _x tulong)
                                                    (Stmt.Sset _t'12
                                                      (Expr.Ecast
                                                        (Expr.Ebinop Binop.Ole
                                                          (Expr.Etempvar _x tulong)
                                                          (Expr.Econst_int (Integers.Int.repr 65535) tint)
                                                          tint) tbool))
                                                    (Stmt.Sset _t'12
                                                      (Expr.Econst_int (Integers.Int.repr 0) tint)))
                                                  (Stmt.Sifthenelse (Expr.Etempvar _t'12 tint)
                                                    (Stmt.Ssequence
                                                      (Stmt.Ssequence
                                                        (Stmt.Sset _t'24
                                                          (Expr.Evar _p (tptr tschar)))
                                                        (Stmt.Ssequence
                                                          (Stmt.Sset _t'25
                                                            (Expr.Ederef
                                                              (Expr.Etempvar _t'24 (tptr tschar))
                                                              tschar))
                                                          (Stmt.Scall (some _t'14)
                                                            (Expr.Evar _Curl_raw_tolower 
                                                            (Ty.Tfunction
                                                              [tschar] tschar
                                                              cc_default))
                                                            [(Expr.Etempvar _t'25 tschar)])))
                                                      (Stmt.Sset _t'13
                                                        (Expr.Ecast
                                                          (Expr.Ebinop Binop.Oeq
                                                            (Expr.Etempvar _t'14 tschar)
                                                            (Expr.Econst_int (Integers.Int.repr 120) tint)
                                                            tint) tbool)))
                                                    (Stmt.Sset _t'13
                                                      (Expr.Econst_int (Integers.Int.repr 0) tint))))
                                                (Stmt.Sifthenelse (Expr.Etempvar _t'13 tint)
                                                  (Stmt.Ssequence
                                                    (Stmt.Ssequence
                                                      (Stmt.Sset _t'23
                                                        (Expr.Evar _p (tptr tschar)))
                                                      (Stmt.Sassign
                                                        (Expr.Evar _p (tptr tschar))
                                                        (Expr.Ebinop Binop.Oadd
                                                          (Expr.Etempvar _t'23 (tptr tschar))
                                                          (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                          (tptr tschar))))
                                                    (Stmt.Ssequence
                                                      (Stmt.Ssequence
                                                        (Stmt.Ssequence
                                                          (Stmt.Sset _t'22
                                                            (Expr.Evar _p (tptr tschar)))
                                                          (Stmt.Scall (some _t'10)
                                                            (Expr.Evar _strtoul 
                                                            (Ty.Tfunction
                                                              [(tptr tschar),
                                                               (tptr (tptr tschar)),
                                                               tint] tulong
                                                              cc_default))
                                                            [(Expr.Etempvar _t'22 (tptr tschar)),
                                                             (Expr.Ecast
                                                               (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                               (tptr tvoid)),
                                                             (Expr.Econst_int (Integers.Int.repr 10) tint)]))
                                                        (Stmt.Sset _y
                                                          (Expr.Etempvar _t'10 tulong)))
                                                      (Stmt.Ssequence
                                                        (Stmt.Sifthenelse (Expr.Etempvar _y tulong)
                                                          (Stmt.Sset _t'11
                                                            (Expr.Ecast
                                                              (Expr.Ebinop Binop.Ole
                                                                (Expr.Etempvar _y tulong)
                                                                (Expr.Econst_int (Integers.Int.repr 65535) tint)
                                                                tint) tbool))
                                                          (Stmt.Sset _t'11
                                                            (Expr.Econst_int (Integers.Int.repr 0) tint)))
                                                        (Stmt.Sifthenelse (Expr.Etempvar _t'11 tint)
                                                          (Stmt.Ssequence
                                                            (Stmt.Sassign
                                                              (Expr.Efield
                                                                (Expr.Ederef
                                                                  (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                                                  (Ty.Tstruct _TELNET noattr))
                                                                _subopt_wsx
                                                                tushort)
                                                              (Expr.Ecast
                                                                (Expr.Etempvar _x tulong)
                                                                tushort))
                                                            (Stmt.Ssequence
                                                              (Stmt.Sassign
                                                                (Expr.Efield
                                                                  (Expr.Ederef
                                                                    (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                                                    (Ty.Tstruct _TELNET noattr))
                                                                  _subopt_wsy
                                                                  tushort)
                                                                (Expr.Ecast
                                                                  (Expr.Etempvar _y tulong)
                                                                  tushort))
                                                              (Stmt.Sassign
                                                                (Expr.Ederef
                                                                  (Expr.Ebinop Binop.Oadd
                                                                    (Expr.Efield
                                                                    (Expr.Ederef
                                                                    (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                                                    (Ty.Tstruct _TELNET noattr))
                                                                    _us_preferred
                                                                    (tarray tint 256))
                                                                    (Expr.Econst_int (Integers.Int.repr 31) tint)
                                                                    (tptr tint))
                                                                  tint)
                                                                (Expr.Econst_int (Integers.Int.repr 1) tint))))
                                                          Stmt.Sskip))))
                                                  Stmt.Sskip))
                                              (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                                                  (Expr.Etempvar _y tulong)
                                                                  tint)
                                                (Stmt.Ssequence
                                                  (Stmt.Ssequence
                                                    (Stmt.Sset _t'21
                                                      (Expr.Efield
                                                        (Expr.Ederef
                                                          (Expr.Etempvar _head (tptr (Ty.Tstruct _curl_slist noattr)))
                                                          (Ty.Tstruct _curl_slist noattr))
                                                        _data (tptr tschar)))
                                                    (Stmt.Scall none
                                                      (Expr.Evar _Curl_failf 
                                                      (Ty.Tfunction
                                                        [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                         (tptr tschar)] tvoid
                                                        { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                                      [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                       (Expr.Evar ___stringlit_2 (tarray tschar 34)),
                                                       (Expr.Etempvar _t'21 (tptr tschar))]))
                                                  (Stmt.Sset _result
                                                    (Expr.Econst_int (Integers.Int.repr 49) tint)))
                                                Stmt.Sskip))))
                                        (Stmt.Sset _result
                                          (Expr.Econst_int (Integers.Int.repr 48) tint))))
                                    Stmt.Sbreak)
                                  (LStmts.LScons (some 6)
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Scall (some _t'17)
                                          (Expr.Evar _Curl_strncasecompare 
                                          (Ty.Tfunction
                                            [(tptr tschar), (tptr tschar),
                                             tulong] tint cc_default))
                                          [(Expr.Etempvar _option (tptr tschar)),
                                           (Expr.Evar ___stringlit_4 (tarray tschar 7)),
                                           (Expr.Econst_int (Integers.Int.repr 6) tint)])
                                        (Stmt.Sifthenelse (Expr.Etempvar _t'17 tint)
                                          (Stmt.Ssequence
                                            (Stmt.Ssequence
                                              (Stmt.Scall (some _t'16)
                                                (Expr.Evar _atoi (Ty.Tfunction
                                                                   [(tptr tschar)]
                                                                   tint
                                                                   cc_default))
                                                [(Expr.Etempvar _arg (tptr tschar))])
                                              (Stmt.Sset _binary_option
                                                (Expr.Etempvar _t'16 tint)))
                                            (Stmt.Sifthenelse (Expr.Ebinop Binop.One
                                                                (Expr.Etempvar _binary_option tint)
                                                                (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                tint)
                                              (Stmt.Ssequence
                                                (Stmt.Sassign
                                                  (Expr.Ederef
                                                    (Expr.Ebinop Binop.Oadd
                                                      (Expr.Efield
                                                        (Expr.Ederef
                                                          (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                                          (Ty.Tstruct _TELNET noattr))
                                                        _us_preferred
                                                        (tarray tint 256))
                                                      (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                      (tptr tint)) tint)
                                                  (Expr.Econst_int (Integers.Int.repr 0) tint))
                                                (Stmt.Sassign
                                                  (Expr.Ederef
                                                    (Expr.Ebinop Binop.Oadd
                                                      (Expr.Efield
                                                        (Expr.Ederef
                                                          (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                                                          (Ty.Tstruct _TELNET noattr))
                                                        _him_preferred
                                                        (tarray tint 256))
                                                      (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                      (tptr tint)) tint)
                                                  (Expr.Econst_int (Integers.Int.repr 0) tint)))
                                              Stmt.Sskip))
                                          (Stmt.Sset _result
                                            (Expr.Econst_int (Integers.Int.repr 48) tint))))
                                      Stmt.Sbreak)
                                    (LStmts.LScons none
                                      (Stmt.Ssequence
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'20
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _head (tptr (Ty.Tstruct _curl_slist noattr)))
                                                (Ty.Tstruct _curl_slist noattr))
                                              _data (tptr tschar)))
                                          (Stmt.Scall none
                                            (Expr.Evar _Curl_failf (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                    (tptr tschar)]
                                                                    tvoid
                                                                    { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                             (Expr.Evar ___stringlit_3 (tarray tschar 25)),
                                             (Expr.Etempvar _t'20 (tptr tschar))]))
                                        (Stmt.Ssequence
                                          (Stmt.Sset _result
                                            (Expr.Econst_int (Integers.Int.repr 48) tint))
                                          Stmt.Sbreak))
                                      LStmts.LSnil)))))))))
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Sset _t'19
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _head (tptr (Ty.Tstruct _curl_slist noattr)))
                              (Ty.Tstruct _curl_slist noattr)) _data
                            (tptr tschar)))
                        (Stmt.Scall none
                          (Expr.Evar _Curl_failf (Ty.Tfunction
                                                   [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                    (tptr tschar)] tvoid
                                                   { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                          [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                           (Expr.Evar ___stringlit_2 (tarray tschar 34)),
                           (Expr.Etempvar _t'19 (tptr tschar))]))
                      (Stmt.Sset _result
                        (Expr.Econst_int (Integers.Int.repr 49) tint)))))))
            (Stmt.Sset _head
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _head (tptr (Ty.Tstruct _curl_slist noattr)))
                  (Ty.Tstruct _curl_slist noattr)) _next
                (tptr (Ty.Tstruct _curl_slist noattr))))))
        (Stmt.Ssequence
          (Stmt.Sifthenelse (Expr.Etempvar _result tint)
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Sset _t'18
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                      (Ty.Tstruct _TELNET noattr)) _telnet_vars
                    (tptr (Ty.Tstruct _curl_slist noattr))))
                (Stmt.Scall none
                  (Expr.Evar _curl_slist_free_all (Ty.Tfunction
                                                    [(tptr (Ty.Tstruct _curl_slist noattr))]
                                                    tvoid cc_default))
                  [(Expr.Etempvar _t'18 (tptr (Ty.Tstruct _curl_slist noattr)))]))
              (Stmt.Sassign
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _tn (tptr (Ty.Tstruct _TELNET noattr)))
                    (Ty.Tstruct _TELNET noattr)) _telnet_vars
                  (tptr (Ty.Tstruct _curl_slist noattr)))
                (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint)
                  (tptr tvoid))))
            Stmt.Sskip)
          (Stmt.Sreturn (some (Expr.Etempvar _result tint))))))))
}

def v_debbookworm2023_27533_keep : GlobVar Ty := {
  gvar_info := (tptr tvoid),
  gvar_init := [(InitData.Init_addrof _check_telnet_options (Integers.Ptrofs.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def composites : List CompositeDef :=
[(CompositeDef.Composite _curl_slist SU.Struct
   [(Member.Member_plain _data (tptr tschar)),
    (Member.Member_plain _next (tptr (Ty.Tstruct _curl_slist noattr)))]
   noattr),
 (CompositeDef.Composite _TELNET SU.Struct
   [(Member.Member_plain _us_preferred (tarray tint 256)),
    (Member.Member_plain _him_preferred (tarray tint 256)),
    (Member.Member_plain _subopt_ttype (tarray tschar 32)),
    (Member.Member_plain _subopt_xdisploc (tarray tschar 128)),
    (Member.Member_plain _subopt_wsx tushort),
    (Member.Member_plain _subopt_wsy tushort),
    (Member.Member_plain _telnet_vars (tptr (Ty.Tstruct _curl_slist noattr)))]
   noattr),
 (CompositeDef.Composite _connectdata SU.Struct
   [(Member.Member_plain _user (tptr tschar))]
   noattr),
 (CompositeDef.Composite _dynamically_allocated_data SU.Struct
   [(Member.Member_plain _user (tptr tschar))]
   noattr),
 (CompositeDef.Composite _UrlState SU.Struct
   [(Member.Member_plain _aptr
      (Ty.Tstruct _dynamically_allocated_data noattr))]
   noattr),
 (CompositeDef.Composite _UserDefined SU.Struct
   [(Member.Member_plain _telnet_options
      (tptr (Ty.Tstruct _curl_slist noattr)))]
   noattr),
 (CompositeDef.Composite __105 SU.Struct
   [(Member.Member_plain _telnet (tptr (Ty.Tstruct _TELNET noattr)))]
   noattr),
 (CompositeDef.Composite _SingleRequest SU.Struct
   [(Member.Member_plain _p (Ty.Tstruct __105 noattr))]
   noattr),
 (CompositeDef.Composite _Curl_easy SU.Struct
   [(Member.Member_plain _conn (tptr (Ty.Tstruct _connectdata noattr))),
    (Member.Member_plain _req (Ty.Tstruct _SingleRequest noattr)),
    (Member.Member_plain _state (Ty.Tstruct _UrlState noattr)),
    (Member.Member_plain _set (Ty.Tstruct _UserDefined noattr))]
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
 (___stringlit_7, GlobDef.Gvar v___stringlit_7),
 (___stringlit_3, GlobDef.Gvar v___stringlit_3),
 (___stringlit_2, GlobDef.Gvar v___stringlit_2),
 (___stringlit_1, GlobDef.Gvar v___stringlit_1),
 (___stringlit_5, GlobDef.Gvar v___stringlit_5),
 (___stringlit_8, GlobDef.Gvar v___stringlit_8),
 (___stringlit_4, GlobDef.Gvar v___stringlit_4),
 (___stringlit_6, GlobDef.Gvar v___stringlit_6),
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
 (_curl_msnprintf,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "curl_msnprintf"
                                   (mksignature
                                     [XType.Xptr, XType.Xlong, XType.Xptr,
                                      XType.Xptr] XType.Xint cc_default))
     [(tptr tschar), tulong, (tptr tschar), (tptr tschar)] tint cc_default)),
 (_curl_slist_append,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "curl_slist_append"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xptr cc_default))
     [(tptr (Ty.Tstruct _curl_slist noattr)), (tptr tschar)]
     (tptr (Ty.Tstruct _curl_slist noattr)) cc_default)),
 (_curl_slist_free_all,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "curl_slist_free_all"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default))
     [(tptr (Ty.Tstruct _curl_slist noattr))] tvoid cc_default)),
 (_Curl_failf,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_failf"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xvoid
                                     { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar)] tvoid
     { cc_vararg := (some 2), cc_unproto := false, cc_structret := false })),
 (_Curl_strncasecompare,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_strncasecompare"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xlong]
                                     XType.Xint cc_default))
     [(tptr tschar), (tptr tschar), tulong] tint cc_default)),
 (_strchr,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "strchr"
                                   (mksignature [XType.Xptr, XType.Xint]
                                     XType.Xptr cc_default))
     [(tptr tschar), tint] (tptr tschar) cc_default)),
 (_strncpy,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "strncpy"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xlong]
                                     XType.Xptr cc_default))
     [(tptr tschar), (tptr tschar), tulong] (tptr tschar) cc_default)),
 (_strtoul,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "strtoul"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xint]
                                     XType.Xlong cc_default))
     [(tptr tschar), (tptr (tptr tschar)), tint] tulong cc_default)),
 (_atoi,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "atoi"
                                   (mksignature [XType.Xptr] XType.Xint
                                     cc_default)) [(tptr tschar)] tint
     cc_default)),
 (_Curl_raw_tolower,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_raw_tolower"
                                   (mksignature [XType.Xint8signed]
                                     XType.Xint8signed cc_default)) [tschar]
     tschar cc_default)),
 (_check_telnet_options, GlobDef.Gfun (FunDef.Internal f_check_telnet_options)),
 (_debbookworm2023_27533_keep, GlobDef.Gvar v_debbookworm2023_27533_keep)]

def public_idents : List Ident :=
[_debbookworm2023_27533_keep, _Curl_raw_tolower, _atoi, _strtoul, _strncpy,
 _strchr, _Curl_strncasecompare, _Curl_failf, _curl_slist_free_all,
 _curl_slist_append, _curl_msnprintf, ___builtin_debug, ___builtin_fmin,
 ___builtin_fmax, ___builtin_fnmsub, ___builtin_fnmadd, ___builtin_fmsub,
 ___builtin_fmadd, ___builtin_clsll, ___builtin_clsl, ___builtin_cls,
 ___builtin_expect, ___builtin_unreachable, ___builtin_va_end,
 ___builtin_va_copy, ___builtin_va_arg, ___builtin_va_start,
 ___builtin_membar, ___builtin_annot_intval, ___builtin_annot,
 ___builtin_sel, ___builtin_memcpy_aligned, ___builtin_sqrt,
 ___builtin_fsqrt, ___builtin_fabsf, ___builtin_fabs, ___builtin_ctzll,
 ___builtin_ctzl, ___builtin_ctz, ___builtin_clzll, ___builtin_clzl,
 ___builtin_clz, ___builtin_bswap16, ___builtin_bswap32, ___builtin_bswap,
 ___builtin_bswap64, ___compcert_i64_umulh, ___compcert_i64_smulh,
 ___compcert_i64_sar, ___compcert_i64_shr, ___compcert_i64_shl,
 ___compcert_i64_umod, ___compcert_i64_smod, ___compcert_i64_udiv,
 ___compcert_i64_sdiv, ___compcert_i64_utof, ___compcert_i64_stof,
 ___compcert_i64_utod, ___compcert_i64_stod, ___compcert_i64_dtou,
 ___compcert_i64_dtos, ___compcert_va_composite, ___compcert_va_float64,
 ___compcert_va_int64, ___compcert_va_int32]

def prog : Program :=
  mkprogram composites global_definitions public_idents _main

end DebBookworm2023_27533_u0

