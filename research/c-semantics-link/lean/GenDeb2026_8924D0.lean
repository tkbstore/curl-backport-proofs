import Clightdefs
open CC

namespace Deb2026_8924_d0

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
  def source_file : String := "deb2026_8924_d0.c"
  def normalized : Bool := true
end Info

def _Cookie : Ident := identOfString "Cookie"
def _Curl_easy : Ident := identOfString "Curl_easy"
def _Curl_host_is_ipnum : Ident := identOfString "Curl_host_is_ipnum"
def _Curl_psl_release : Ident := identOfString "Curl_psl_release"
def _Curl_psl_use : Ident := identOfString "Curl_psl_use"
def _Curl_strntolower : Ident := identOfString "Curl_strntolower"
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
def _acceptable : Ident := identOfString "acceptable"
def _clen : Ident := identOfString "clen"
def _co : Ident := identOfString "co"
def _data : Ident := identOfString "data"
def _deb2026_8924_keep : Ident := identOfString "deb2026_8924_keep"
def _dlen : Ident := identOfString "dlen"
def _domain : Ident := identOfString "domain"
def _is_public_suffix : Ident := identOfString "is_public_suffix"
def _lcase : Ident := identOfString "lcase"
def _lcookie : Ident := identOfString "lcookie"
def _main : Ident := identOfString "main"
def _name : Ident := identOfString "name"
def _psl : Ident := identOfString "psl"
def _psl_ctx_st : Ident := identOfString "psl_ctx_st"
def _psl_is_cookie_domain_acceptable : Ident := identOfString "psl_is_cookie_domain_acceptable"
def _strlen : Ident := identOfString "strlen"
def _t'1 : Ident := (Positive.ofNat 128)
def _t'10 : Ident := (Positive.ofNat 137)
def _t'11 : Ident := (Positive.ofNat 138)
def _t'12 : Ident := (Positive.ofNat 139)
def _t'2 : Ident := (Positive.ofNat 129)
def _t'3 : Ident := (Positive.ofNat 130)
def _t'4 : Ident := (Positive.ofNat 131)
def _t'5 : Ident := (Positive.ofNat 132)
def _t'6 : Ident := (Positive.ofNat 133)
def _t'7 : Ident := (Positive.ofNat 134)
def _t'8 : Ident := (Positive.ofNat 135)
def _t'9 : Ident := (Positive.ofNat 136)

def f_is_public_suffix : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_co, (tptr (Ty.Tstruct _Cookie noattr))),
                (_domain, (tptr tschar))],
  fn_vars := [(_lcase, (tarray tschar 256)), (_lcookie, (tarray tschar 256))],
  fn_temps := [(_acceptable, tbool), (_dlen, tulong), (_clen, tulong),
               (_psl, (tptr (Ty.Tstruct _psl_ctx_st noattr))), (_t'8, tbool),
               (_t'7, tint), (_t'6, tint), (_t'5, tint), (_t'4, tint),
               (_t'3, (tptr (Ty.Tstruct _psl_ctx_st noattr))),
               (_t'2, tulong), (_t'1, tulong), (_t'12, (tptr tschar)),
               (_t'11, (tptr tschar)), (_t'10, (tptr tschar)),
               (_t'9, (tptr tschar))],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Sloop Stmt.Sskip Stmt.Sbreak)
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Sifthenelse (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
        (Stmt.Ssequence
          (Stmt.Sifthenelse (Expr.Etempvar _domain (tptr tschar))
            (Stmt.Ssequence
              (Stmt.Sset _t'12
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _co (tptr (Ty.Tstruct _Cookie noattr)))
                    (Ty.Tstruct _Cookie noattr)) _domain (tptr tschar)))
              (Stmt.Sset _t'7
                (Expr.Ecast (Expr.Etempvar _t'12 (tptr tschar)) tbool)))
            (Stmt.Sset _t'7 (Expr.Econst_int (Integers.Int.repr 0) tint)))
          (Stmt.Sifthenelse (Expr.Etempvar _t'7 tint)
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Sset _t'11
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _co (tptr (Ty.Tstruct _Cookie noattr)))
                        (Ty.Tstruct _Cookie noattr)) _domain (tptr tschar)))
                  (Stmt.Scall (some _t'8)
                    (Expr.Evar _Curl_host_is_ipnum (Ty.Tfunction
                                                     [(tptr tschar)] tbool
                                                     cc_default))
                    [(Expr.Etempvar _t'11 (tptr tschar))]))
                (Stmt.Sset _t'6
                  (Expr.Ecast
                    (Expr.Eunop Unop.Onotbool (Expr.Etempvar _t'8 tbool)
                      tint) tbool)))
              (Stmt.Sset _t'6 (Expr.Ecast (Expr.Etempvar _t'6 tint) tbool)))
            (Stmt.Sset _t'6
              (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint) tbool))))
        (Stmt.Sset _t'6 (Expr.Econst_int (Integers.Int.repr 0) tint)))
      (Stmt.Sifthenelse (Expr.Etempvar _t'6 tint)
        (Stmt.Ssequence
          (Stmt.Sset _acceptable
            (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint) tbool))
          (Stmt.Ssequence
            (Stmt.Ssequence
              (Stmt.Scall (some _t'1)
                (Expr.Evar _strlen (Ty.Tfunction [(tptr tschar)] tulong
                                     cc_default))
                [(Expr.Etempvar _domain (tptr tschar))])
              (Stmt.Sset _dlen (Expr.Etempvar _t'1 tulong)))
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Sset _t'10
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _co (tptr (Ty.Tstruct _Cookie noattr)))
                        (Ty.Tstruct _Cookie noattr)) _domain (tptr tschar)))
                  (Stmt.Scall (some _t'2)
                    (Expr.Evar _strlen (Ty.Tfunction [(tptr tschar)] tulong
                                         cc_default))
                    [(Expr.Etempvar _t'10 (tptr tschar))]))
                (Stmt.Sset _clen (Expr.Etempvar _t'2 tulong)))
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                      (Expr.Etempvar _dlen tulong)
                                      (Expr.Esizeof (tarray tschar 256) tulong)
                                      tint)
                    (Stmt.Sset _t'5
                      (Expr.Ecast
                        (Expr.Ebinop Binop.Olt (Expr.Etempvar _clen tulong)
                          (Expr.Esizeof (tarray tschar 256) tulong) tint)
                        tbool))
                    (Stmt.Sset _t'5
                      (Expr.Econst_int (Integers.Int.repr 0) tint)))
                  (Stmt.Sifthenelse (Expr.Etempvar _t'5 tint)
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Scall (some _t'3)
                          (Expr.Evar _Curl_psl_use (Ty.Tfunction
                                                     [(tptr (Ty.Tstruct _Curl_easy noattr))]
                                                     (tptr (Ty.Tstruct _psl_ctx_st noattr))
                                                     cc_default))
                          [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))])
                        (Stmt.Sset _psl
                          (Expr.Etempvar _t'3 (tptr (Ty.Tstruct _psl_ctx_st noattr)))))
                      (Stmt.Sifthenelse (Expr.Etempvar _psl (tptr (Ty.Tstruct _psl_ctx_st noattr)))
                        (Stmt.Ssequence
                          (Stmt.Scall none
                            (Expr.Evar _Curl_strntolower (Ty.Tfunction
                                                           [(tptr tschar),
                                                            (tptr tschar),
                                                            tulong] tvoid
                                                           cc_default))
                            [(Expr.Evar _lcase (tarray tschar 256)),
                             (Expr.Etempvar _domain (tptr tschar)),
                             (Expr.Ebinop Binop.Oadd
                               (Expr.Etempvar _dlen tulong)
                               (Expr.Econst_int (Integers.Int.repr 1) tint)
                               tulong)])
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Sset _t'9
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _co (tptr (Ty.Tstruct _Cookie noattr)))
                                    (Ty.Tstruct _Cookie noattr)) _domain
                                  (tptr tschar)))
                              (Stmt.Scall none
                                (Expr.Evar _Curl_strntolower (Ty.Tfunction
                                                               [(tptr tschar),
                                                                (tptr tschar),
                                                                tulong] tvoid
                                                               cc_default))
                                [(Expr.Evar _lcookie (tarray tschar 256)),
                                 (Expr.Etempvar _t'9 (tptr tschar)),
                                 (Expr.Ebinop Binop.Oadd
                                   (Expr.Etempvar _clen tulong)
                                   (Expr.Econst_int (Integers.Int.repr 1) tint)
                                   tulong)]))
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Scall (some _t'4)
                                  (Expr.Evar _psl_is_cookie_domain_acceptable 
                                  (Ty.Tfunction
                                    [(tptr (Ty.Tstruct _psl_ctx_st noattr)),
                                     (tptr tschar), (tptr tschar)] tint
                                    cc_default))
                                  [(Expr.Etempvar _psl (tptr (Ty.Tstruct _psl_ctx_st noattr))),
                                   (Expr.Evar _lcase (tarray tschar 256)),
                                   (Expr.Evar _lcookie (tarray tschar 256))])
                                (Stmt.Sset _acceptable
                                  (Expr.Ecast (Expr.Etempvar _t'4 tint)
                                    tbool)))
                              (Stmt.Scall none
                                (Expr.Evar _Curl_psl_release (Ty.Tfunction
                                                               [(tptr (Ty.Tstruct _Curl_easy noattr))]
                                                               tvoid
                                                               cc_default))
                                [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))]))))
                        (Stmt.Sloop Stmt.Sskip Stmt.Sbreak)))
                    Stmt.Sskip))
                (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                    (Expr.Etempvar _acceptable tbool) tint)
                  (Stmt.Ssequence
                    (Stmt.Sloop Stmt.Sskip Stmt.Sbreak)
                    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 14) tint))))
                  Stmt.Sskip)))))
        Stmt.Sskip))
    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint)))))
}

def v_deb2026_8924_keep : GlobVar Ty := {
  gvar_info := (tptr (Ty.Tfunction
                       [(tptr (Ty.Tstruct _Curl_easy noattr)),
                        (tptr (Ty.Tstruct _Cookie noattr)), (tptr tschar)]
                       tint cc_default)),
  gvar_init := [(InitData.Init_addrof _is_public_suffix (Integers.Ptrofs.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def composites : List CompositeDef :=
[(CompositeDef.Composite _Cookie SU.Struct
   [(Member.Member_plain _name (tptr tschar)),
    (Member.Member_plain _domain (tptr tschar))]
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
 (_strlen,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "strlen"
                                   (mksignature [XType.Xptr] XType.Xlong
                                     cc_default)) [(tptr tschar)] tulong
     cc_default)),
 (_Curl_host_is_ipnum,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_host_is_ipnum"
                                   (mksignature [XType.Xptr] XType.Xbool
                                     cc_default)) [(tptr tschar)] tbool
     cc_default)),
 (_Curl_psl_use,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_psl_use"
                                   (mksignature [XType.Xptr] XType.Xptr
                                     cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr))]
     (tptr (Ty.Tstruct _psl_ctx_st noattr)) cc_default)),
 (_Curl_psl_release,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_psl_release"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr))] tvoid cc_default)),
 (_Curl_strntolower,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_strntolower"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xlong]
                                     XType.Xvoid cc_default))
     [(tptr tschar), (tptr tschar), tulong] tvoid cc_default)),
 (_psl_is_cookie_domain_acceptable,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "psl_is_cookie_domain_acceptable"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xptr]
                                     XType.Xint cc_default))
     [(tptr (Ty.Tstruct _psl_ctx_st noattr)), (tptr tschar), (tptr tschar)]
     tint cc_default)),
 (_is_public_suffix, GlobDef.Gfun (FunDef.Internal f_is_public_suffix)),
 (_deb2026_8924_keep, GlobDef.Gvar v_deb2026_8924_keep)]

def public_idents : List Ident :=
[_deb2026_8924_keep, _psl_is_cookie_domain_acceptable, _Curl_strntolower,
 _Curl_psl_release, _Curl_psl_use, _Curl_host_is_ipnum, _strlen,
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

end Deb2026_8924_d0

