import Clightdefs
open CC

namespace Deb2026_3805_deb_before

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
  def source_file : String := "deb2026_3805_deb_before.c"
  def normalized : Bool := true
end Info

def _Curl_cfree : Ident := identOfString "Curl_cfree"
def _Curl_cstrdup : Ident := identOfString "Curl_cstrdup"
def _Curl_easy : Ident := identOfString "Curl_easy"
def _Curl_failf : Ident := identOfString "Curl_failf"
def _Curl_urldecode : Ident := identOfString "Curl_urldecode"
def _UrlState : Ident := identOfString "UrlState"
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
def _data : Ident := identOfString "data"
def _deb2026_3805_keep : Ident := identOfString "deb2026_3805_keep"
def _main : Ident := identOfString "main"
def _path : Ident := identOfString "path"
def _req : Ident := identOfString "req"
def _result : Ident := identOfString "result"
def _share : Ident := identOfString "share"
def _slash : Ident := identOfString "slash"
def _smb_conn : Ident := identOfString "smb_conn"
def _smb_parse_url_path : Ident := identOfString "smb_parse_url_path"
def _smb_request : Ident := identOfString "smb_request"
def _smbc : Ident := identOfString "smbc"
def _state : Ident := identOfString "state"
def _strchr : Ident := identOfString "strchr"
def _up : Ident := identOfString "up"
def _urlpieces : Ident := identOfString "urlpieces"
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
def _t'3 : Ident := (Positive.ofNat 130)
def _t'4 : Ident := (Positive.ofNat 131)
def _t'5 : Ident := (Positive.ofNat 132)
def _t'6 : Ident := (Positive.ofNat 133)
def _t'7 : Ident := (Positive.ofNat 134)
def _t'8 : Ident := (Positive.ofNat 135)
def _t'9 : Ident := (Positive.ofNat 136)

def v___stringlit_1 : GlobVar Ty := {
  gvar_info := (tarray tschar 34),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 109)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 103)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 115)),
                (InitData.Init_int8 (Integers.Int.repr 104)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 101)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 105)),
                (InitData.Init_int8 (Integers.Int.repr 110)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 85)),
                (InitData.Init_int8 (Integers.Int.repr 82)),
                (InitData.Init_int8 (Integers.Int.repr 76)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 112)),
                (InitData.Init_int8 (Integers.Int.repr 97)),
                (InitData.Init_int8 (Integers.Int.repr 116)),
                (InitData.Init_int8 (Integers.Int.repr 104)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 102)),
                (InitData.Init_int8 (Integers.Int.repr 111)),
                (InitData.Init_int8 (Integers.Int.repr 114)),
                (InitData.Init_int8 (Integers.Int.repr 32)),
                (InitData.Init_int8 (Integers.Int.repr 83)),
                (InitData.Init_int8 (Integers.Int.repr 77)),
                (InitData.Init_int8 (Integers.Int.repr 66)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def f_smb_parse_url_path : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_smbc, (tptr (Ty.Tstruct _smb_conn noattr))),
                (_req, (tptr (Ty.Tstruct _smb_request noattr)))],
  fn_vars := [(_path, (tptr tschar))],
  fn_temps := [(_slash, (tptr tschar)), (_result, tint),
               (_t'7, (tptr tschar)), (_t'6, (tptr tschar)),
               (_t'5, (tptr tschar)), (_t'4, (tptr tschar)),
               (_t'3, (tptr tschar)), (_t'2, tint), (_t'1, tint),
               (_t'21, (tptr tschar)), (_t'20, tschar),
               (_t'19, (tptr tschar)), (_t'18, tschar),
               (_t'17, (tptr tschar)), (_t'16, (tptr tschar)),
               (_t'15, (tptr tschar)), (_t'14, (tptr tschar)),
               (_t'13, (tptr tschar)), (_t'12, (tptr tschar)),
               (_t'11, (tptr tschar)), (_t'10, (tptr tschar)),
               (_t'9, tschar), (_t'8, tschar)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Sset _t'21
        (Expr.Efield
          (Expr.Efield
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                (Ty.Tstruct _Curl_easy noattr)) _state
              (Ty.Tstruct _UrlState noattr)) _up
            (Ty.Tstruct _urlpieces noattr)) _path (tptr tschar)))
      (Stmt.Scall (some _t'1)
        (Expr.Evar _Curl_urldecode (Ty.Tfunction
                                     [(tptr tschar), tulong,
                                      (tptr (tptr tschar)), (tptr tulong),
                                      tint] tint cc_default))
        [(Expr.Etempvar _t'21 (tptr tschar)),
         (Expr.Econst_int (Integers.Int.repr 0) tint),
         (Expr.Eaddrof (Expr.Evar _path (tptr tschar)) (tptr (tptr tschar))),
         (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint)
           (tptr tvoid)), (Expr.Econst_int (Integers.Int.repr 3) tint)]))
    (Stmt.Sset _result (Expr.Etempvar _t'1 tint)))
  (Stmt.Ssequence
    (Stmt.Sifthenelse (Expr.Etempvar _result tint)
      (Stmt.Sreturn (some (Expr.Etempvar _result tint)))
      Stmt.Sskip)
    (Stmt.Ssequence
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Ssequence
            (Stmt.Ssequence
              (Stmt.Sset _t'17 (Expr.Evar _path (tptr tschar)))
              (Stmt.Ssequence
                (Stmt.Sset _t'18
                  (Expr.Ederef (Expr.Etempvar _t'17 (tptr tschar)) tschar))
                (Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq
                                    (Expr.Etempvar _t'18 tschar)
                                    (Expr.Econst_int (Integers.Int.repr 47) tint)
                                    tint)
                  (Stmt.Sset _t'2
                    (Expr.Econst_int (Integers.Int.repr 1) tint))
                  (Stmt.Ssequence
                    (Stmt.Sset _t'19 (Expr.Evar _path (tptr tschar)))
                    (Stmt.Ssequence
                      (Stmt.Sset _t'20
                        (Expr.Ederef (Expr.Etempvar _t'19 (tptr tschar))
                          tschar))
                      (Stmt.Sset _t'2
                        (Expr.Ecast
                          (Expr.Ebinop Binop.Oeq (Expr.Etempvar _t'20 tschar)
                            (Expr.Econst_int (Integers.Int.repr 92) tint)
                            tint) tbool)))))))
            (Stmt.Sifthenelse (Expr.Etempvar _t'2 tint)
              (Stmt.Ssequence
                (Stmt.Sset _t'16 (Expr.Evar _path (tptr tschar)))
                (Stmt.Sset _t'3
                  (Expr.Ecast
                    (Expr.Ebinop Binop.Oadd
                      (Expr.Etempvar _t'16 (tptr tschar))
                      (Expr.Econst_int (Integers.Int.repr 1) tint)
                      (tptr tschar)) (tptr tschar))))
              (Stmt.Ssequence
                (Stmt.Sset _t'15 (Expr.Evar _path (tptr tschar)))
                (Stmt.Sset _t'3
                  (Expr.Ecast (Expr.Etempvar _t'15 (tptr tschar))
                    (tptr tschar))))))
          (Stmt.Scall (some _t'4)
            (Expr.Evar _Curl_cstrdup (Ty.Tfunction [(tptr tschar)]
                                       (tptr tschar) cc_default))
            [(Expr.Etempvar _t'3 (tptr tschar))]))
        (Stmt.Sassign
          (Expr.Efield
            (Expr.Ederef
              (Expr.Etempvar _smbc (tptr (Ty.Tstruct _smb_conn noattr)))
              (Ty.Tstruct _smb_conn noattr)) _share (tptr tschar))
          (Expr.Etempvar _t'4 (tptr tschar))))
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Sset _t'14 (Expr.Evar _path (tptr tschar)))
          (Stmt.Scall none
            (Expr.Evar _Curl_cfree (Ty.Tfunction [(tptr tvoid)] tvoid
                                     cc_default))
            [(Expr.Etempvar _t'14 (tptr tschar))]))
        (Stmt.Ssequence
          (Stmt.Ssequence
            (Stmt.Sset _t'13
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _smbc (tptr (Ty.Tstruct _smb_conn noattr)))
                  (Ty.Tstruct _smb_conn noattr)) _share (tptr tschar)))
            (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                (Expr.Etempvar _t'13 (tptr tschar)) tint)
              (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 27) tint)))
              Stmt.Sskip))
          (Stmt.Ssequence
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Sset _t'12
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _smbc (tptr (Ty.Tstruct _smb_conn noattr)))
                      (Ty.Tstruct _smb_conn noattr)) _share (tptr tschar)))
                (Stmt.Scall (some _t'5)
                  (Expr.Evar _strchr (Ty.Tfunction [(tptr tschar), tint]
                                       (tptr tschar) cc_default))
                  [(Expr.Etempvar _t'12 (tptr tschar)),
                   (Expr.Econst_int (Integers.Int.repr 47) tint)]))
              (Stmt.Sset _slash (Expr.Etempvar _t'5 (tptr tschar))))
            (Stmt.Ssequence
              (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                  (Expr.Etempvar _slash (tptr tschar)) tint)
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Sset _t'11
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _smbc (tptr (Ty.Tstruct _smb_conn noattr)))
                          (Ty.Tstruct _smb_conn noattr)) _share
                        (tptr tschar)))
                    (Stmt.Scall (some _t'6)
                      (Expr.Evar _strchr (Ty.Tfunction [(tptr tschar), tint]
                                           (tptr tschar) cc_default))
                      [(Expr.Etempvar _t'11 (tptr tschar)),
                       (Expr.Econst_int (Integers.Int.repr 92) tint)]))
                  (Stmt.Sset _slash (Expr.Etempvar _t'6 (tptr tschar))))
                Stmt.Sskip)
              (Stmt.Ssequence
                (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                    (Expr.Etempvar _slash (tptr tschar))
                                    tint)
                  (Stmt.Ssequence
                    (Stmt.Sloop
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Sset _t'10
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _smbc (tptr (Ty.Tstruct _smb_conn noattr)))
                                (Ty.Tstruct _smb_conn noattr)) _share
                              (tptr tschar)))
                          (Stmt.Scall none
                            (Expr.Evar _Curl_cfree (Ty.Tfunction
                                                     [(tptr tvoid)] tvoid
                                                     cc_default))
                            [(Expr.Etempvar _t'10 (tptr tschar))]))
                        (Stmt.Sassign
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _smbc (tptr (Ty.Tstruct _smb_conn noattr)))
                              (Ty.Tstruct _smb_conn noattr)) _share
                            (tptr tschar))
                          (Expr.Ecast
                            (Expr.Econst_int (Integers.Int.repr 0) tint)
                            (tptr tvoid))))
                      Stmt.Sbreak)
                    (Stmt.Ssequence
                      (Stmt.Scall none
                        (Expr.Evar _Curl_failf (Ty.Tfunction
                                                 [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                  (tptr tschar)] tvoid
                                                 { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                        [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                         (Expr.Evar ___stringlit_1 (tarray tschar 34))])
                      (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 3) tint)))))
                  Stmt.Sskip)
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sset _t'7 (Expr.Etempvar _slash (tptr tschar)))
                      (Stmt.Sset _slash
                        (Expr.Ebinop Binop.Oadd
                          (Expr.Etempvar _t'7 (tptr tschar))
                          (Expr.Econst_int (Integers.Int.repr 1) tint)
                          (tptr tschar))))
                    (Stmt.Sassign
                      (Expr.Ederef (Expr.Etempvar _t'7 (tptr tschar)) tschar)
                      (Expr.Econst_int (Integers.Int.repr 0) tint)))
                  (Stmt.Ssequence
                    (Stmt.Sassign
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _req (tptr (Ty.Tstruct _smb_request noattr)))
                          (Ty.Tstruct _smb_request noattr)) _path
                        (tptr tschar)) (Expr.Etempvar _slash (tptr tschar)))
                    (Stmt.Ssequence
                      (Stmt.Sloop
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'9
                              (Expr.Ederef
                                (Expr.Etempvar _slash (tptr tschar)) tschar))
                            (Stmt.Sifthenelse (Expr.Etempvar _t'9 tschar)
                              Stmt.Sskip
                              Stmt.Sbreak))
                          (Stmt.Ssequence
                            (Stmt.Sset _t'8
                              (Expr.Ederef
                                (Expr.Etempvar _slash (tptr tschar)) tschar))
                            (Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq
                                                (Expr.Etempvar _t'8 tschar)
                                                (Expr.Econst_int (Integers.Int.repr 47) tint)
                                                tint)
                              (Stmt.Sassign
                                (Expr.Ederef
                                  (Expr.Etempvar _slash (tptr tschar))
                                  tschar)
                                (Expr.Econst_int (Integers.Int.repr 92) tint))
                              Stmt.Sskip)))
                        (Stmt.Sset _slash
                          (Expr.Ebinop Binop.Oadd
                            (Expr.Etempvar _slash (tptr tschar))
                            (Expr.Econst_int (Integers.Int.repr 1) tint)
                            (tptr tschar))))
                      (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint))))))))))))))
}

def v_deb2026_3805_keep : GlobVar Ty := {
  gvar_info := (tptr (Ty.Tfunction
                       [(tptr (Ty.Tstruct _Curl_easy noattr)),
                        (tptr (Ty.Tstruct _smb_conn noattr)),
                        (tptr (Ty.Tstruct _smb_request noattr))] tint
                       cc_default)),
  gvar_init := [(InitData.Init_addrof _smb_parse_url_path (Integers.Ptrofs.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def composites : List CompositeDef :=
[(CompositeDef.Composite _urlpieces SU.Struct
   [(Member.Member_plain _path (tptr tschar))]
   noattr),
 (CompositeDef.Composite _UrlState SU.Struct
   [(Member.Member_plain _up (Ty.Tstruct _urlpieces noattr))]
   noattr),
 (CompositeDef.Composite _Curl_easy SU.Struct
   [(Member.Member_plain _state (Ty.Tstruct _UrlState noattr))]
   noattr),
 (CompositeDef.Composite _smb_conn SU.Struct
   [(Member.Member_plain _share (tptr tschar))]
   noattr),
 (CompositeDef.Composite _smb_request SU.Struct
   [(Member.Member_plain _path (tptr tschar))]
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
 (_Curl_urldecode,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_urldecode"
                                   (mksignature
                                     [XType.Xptr, XType.Xlong, XType.Xptr,
                                      XType.Xptr, XType.Xint] XType.Xint
                                     cc_default))
     [(tptr tschar), tulong, (tptr (tptr tschar)), (tptr tulong), tint] tint
     cc_default)),
 (_Curl_cstrdup,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_cstrdup"
                                   (mksignature [XType.Xptr] XType.Xptr
                                     cc_default)) [(tptr tschar)]
     (tptr tschar) cc_default)),
 (_Curl_cfree,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_cfree"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default)) [(tptr tvoid)] tvoid
     cc_default)),
 (_strchr,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "strchr"
                                   (mksignature [XType.Xptr, XType.Xint]
                                     XType.Xptr cc_default))
     [(tptr tschar), tint] (tptr tschar) cc_default)),
 (_Curl_failf,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_failf"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xvoid
                                     { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar)] tvoid
     { cc_vararg := (some 2), cc_unproto := false, cc_structret := false })),
 (_smb_parse_url_path, GlobDef.Gfun (FunDef.Internal f_smb_parse_url_path)),
 (_deb2026_3805_keep, GlobDef.Gvar v_deb2026_3805_keep)]

def public_idents : List Ident :=
[_deb2026_3805_keep, _Curl_failf, _strchr, _Curl_cfree, _Curl_cstrdup,
 _Curl_urldecode, ___builtin_debug, ___builtin_fmin, ___builtin_fmax,
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

end Deb2026_3805_deb_before

