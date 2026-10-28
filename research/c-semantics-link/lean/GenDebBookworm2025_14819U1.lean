import Clightdefs
open CC

namespace DebBookworm2025_14819_u1

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
  def source_file : String := "debbookworm2025_14819_u1.c"
  def normalized : Bool := true
end Info

def _CAfile : Ident := identOfString "CAfile"
def _Curl_cfilter : Ident := identOfString "Curl_cfilter"
def _Curl_easy : Ident := identOfString "Curl_easy"
def _Curl_ssl_cf_get_config : Ident := identOfString "Curl_ssl_cf_get_config"
def _Curl_ssl_cf_get_primary_config : Ident := identOfString "Curl_ssl_cf_get_primary_config"
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
def _cf : Ident := identOfString "cf"
def _conn_config : Ident := identOfString "conn_config"
def _data : Ident := identOfString "data"
def _debbookworm2025_14819_keep : Ident := identOfString "debbookworm2025_14819_keep"
def _main : Ident := identOfString "main"
def _mb : Ident := identOfString "mb"
def _no_partialchain : Ident := identOfString "no_partialchain"
def _ossl_cached_x509_store_different : Ident := identOfString "ossl_cached_x509_store_different"
def _ossl_x509_share : Ident := identOfString "ossl_x509_share"
def _ssl_config : Ident := identOfString "ssl_config"
def _ssl_config_data : Ident := identOfString "ssl_config_data"
def _ssl_primary_config : Ident := identOfString "ssl_primary_config"
def _strcmp : Ident := identOfString "strcmp"
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

def f_ossl_cached_x509_store_different : Function := {
  fn_return := tbool,
  fn_callconv := cc_default,
  fn_params := [(_cf, (tptr (Ty.Tstruct _Curl_cfilter noattr))),
                (_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_mb, (tptr (Ty.Tstruct _ossl_x509_share noattr)))],
  fn_vars := [],
  fn_temps := [(_conn_config, (tptr (Ty.Tstruct _ssl_primary_config noattr))),
               (_ssl_config, (tptr (Ty.Tstruct _ssl_config_data noattr))),
               (_t'4, tint), (_t'3, tint),
               (_t'2, (tptr (Ty.Tstruct _ssl_config_data noattr))),
               (_t'1, (tptr (Ty.Tstruct _ssl_primary_config noattr))),
               (_t'12, tint), (_t'11, tint), (_t'10, (tptr tschar)),
               (_t'9, (tptr tschar)), (_t'8, (tptr tschar)),
               (_t'7, (tptr tschar)), (_t'6, (tptr tschar)),
               (_t'5, (tptr tschar))],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Ssequence
    (Stmt.Scall (some _t'1)
      (Expr.Evar _Curl_ssl_cf_get_primary_config (Ty.Tfunction
                                                   [(tptr (Ty.Tstruct _Curl_cfilter noattr))]
                                                   (tptr (Ty.Tstruct _ssl_primary_config noattr))
                                                   cc_default))
      [(Expr.Etempvar _cf (tptr (Ty.Tstruct _Curl_cfilter noattr)))])
    (Stmt.Sset _conn_config
      (Expr.Etempvar _t'1 (tptr (Ty.Tstruct _ssl_primary_config noattr)))))
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Scall (some _t'2)
        (Expr.Evar _Curl_ssl_cf_get_config (Ty.Tfunction
                                             [(tptr (Ty.Tstruct _Curl_cfilter noattr)),
                                              (tptr (Ty.Tstruct _Curl_easy noattr))]
                                             (tptr (Ty.Tstruct _ssl_config_data noattr))
                                             cc_default))
        [(Expr.Etempvar _cf (tptr (Ty.Tstruct _Curl_cfilter noattr))),
         (Expr.Ecast
           (Expr.Ecast
             (Expr.Ecast
               (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
               (tptr tvoid)) tulong) (tptr tvoid))])
      (Stmt.Sset _ssl_config
        (Expr.Etempvar _t'2 (tptr (Ty.Tstruct _ssl_config_data noattr)))))
    (Stmt.Ssequence
      (Stmt.Ssequence
        (Stmt.Sset _t'11
          (Expr.Efield
            (Expr.Ederef
              (Expr.Etempvar _mb (tptr (Ty.Tstruct _ossl_x509_share noattr)))
              (Ty.Tstruct _ossl_x509_share noattr)) _no_partialchain tint))
        (Stmt.Ssequence
          (Stmt.Sset _t'12
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _ssl_config (tptr (Ty.Tstruct _ssl_config_data noattr)))
                (Ty.Tstruct _ssl_config_data noattr)) _no_partialchain tint))
          (Stmt.Sifthenelse (Expr.Ebinop Binop.One (Expr.Etempvar _t'11 tint)
                              (Expr.Etempvar _t'12 tint) tint)
            (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 1) tint)))
            Stmt.Sskip)))
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Ssequence
            (Stmt.Sset _t'9
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _mb (tptr (Ty.Tstruct _ossl_x509_share noattr)))
                  (Ty.Tstruct _ossl_x509_share noattr)) _CAfile
                (tptr tschar)))
            (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                (Expr.Etempvar _t'9 (tptr tschar)) tint)
              (Stmt.Sset _t'3 (Expr.Econst_int (Integers.Int.repr 1) tint))
              (Stmt.Ssequence
                (Stmt.Sset _t'10
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _conn_config (tptr (Ty.Tstruct _ssl_primary_config noattr)))
                      (Ty.Tstruct _ssl_primary_config noattr)) _CAfile
                    (tptr tschar)))
                (Stmt.Sset _t'3
                  (Expr.Ecast
                    (Expr.Eunop Unop.Onotbool
                      (Expr.Etempvar _t'10 (tptr tschar)) tint) tbool)))))
          (Stmt.Sifthenelse (Expr.Etempvar _t'3 tint)
            (Stmt.Ssequence
              (Stmt.Sset _t'7
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _mb (tptr (Ty.Tstruct _ossl_x509_share noattr)))
                    (Ty.Tstruct _ossl_x509_share noattr)) _CAfile
                  (tptr tschar)))
              (Stmt.Ssequence
                (Stmt.Sset _t'8
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _conn_config (tptr (Ty.Tstruct _ssl_primary_config noattr)))
                      (Ty.Tstruct _ssl_primary_config noattr)) _CAfile
                    (tptr tschar)))
                (Stmt.Sreturn (some (Expr.Ebinop Binop.One
                                      (Expr.Etempvar _t'7 (tptr tschar))
                                      (Expr.Etempvar _t'8 (tptr tschar))
                                      tint)))))
            Stmt.Sskip))
        (Stmt.Ssequence
          (Stmt.Ssequence
            (Stmt.Sset _t'5
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _mb (tptr (Ty.Tstruct _ossl_x509_share noattr)))
                  (Ty.Tstruct _ossl_x509_share noattr)) _CAfile
                (tptr tschar)))
            (Stmt.Ssequence
              (Stmt.Sset _t'6
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _conn_config (tptr (Ty.Tstruct _ssl_primary_config noattr)))
                    (Ty.Tstruct _ssl_primary_config noattr)) _CAfile
                  (tptr tschar)))
              (Stmt.Scall (some _t'4)
                (Expr.Evar _strcmp (Ty.Tfunction
                                     [(tptr tschar), (tptr tschar)] tint
                                     cc_default))
                [(Expr.Etempvar _t'5 (tptr tschar)),
                 (Expr.Etempvar _t'6 (tptr tschar))])))
          (Stmt.Sreturn (some (Expr.Etempvar _t'4 tint))))))))
}

def v_debbookworm2025_14819_keep : GlobVar Ty := {
  gvar_info := (tptr tvoid),
  gvar_init := [(InitData.Init_addrof _ossl_cached_x509_store_different (Integers.Ptrofs.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def composites : List CompositeDef :=
[(CompositeDef.Composite _ssl_primary_config SU.Struct
   [(Member.Member_plain _CAfile (tptr tschar))]
   noattr),
 (CompositeDef.Composite _ssl_config_data SU.Struct
   [(Member.Member_bitfield _no_partialchain IntSize.I32 Signedness.Unsigned
      noattr 1 false)]
   noattr),
 (CompositeDef.Composite _ossl_x509_share SU.Struct
   [(Member.Member_plain _CAfile (tptr tschar)),
    (Member.Member_bitfield _no_partialchain IntSize.I32 Signedness.Unsigned
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
 (_Curl_ssl_cf_get_primary_config,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_ssl_cf_get_primary_config"
                                   (mksignature [XType.Xptr] XType.Xptr
                                     cc_default))
     [(tptr (Ty.Tstruct _Curl_cfilter noattr))]
     (tptr (Ty.Tstruct _ssl_primary_config noattr)) cc_default)),
 (_Curl_ssl_cf_get_config,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_ssl_cf_get_config"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xptr cc_default))
     [(tptr (Ty.Tstruct _Curl_cfilter noattr)),
      (tptr (Ty.Tstruct _Curl_easy noattr))]
     (tptr (Ty.Tstruct _ssl_config_data noattr)) cc_default)),
 (_strcmp,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "strcmp"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xint cc_default))
     [(tptr tschar), (tptr tschar)] tint cc_default)),
 (_ossl_cached_x509_store_different, GlobDef.Gfun (FunDef.Internal f_ossl_cached_x509_store_different)),
 (_debbookworm2025_14819_keep, GlobDef.Gvar v_debbookworm2025_14819_keep)]

def public_idents : List Ident :=
[_debbookworm2025_14819_keep, _strcmp, _Curl_ssl_cf_get_config,
 _Curl_ssl_cf_get_primary_config, ___builtin_debug, ___builtin_fmin,
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

end DebBookworm2025_14819_u1

