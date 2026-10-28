import Clightdefs
open CC

namespace Deb2025_14524_u1

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
  def source_file : String := "deb2025_14524_u1.c"
  def normalized : Bool := true
end Info

def _Curl_auth_create_external_message : Ident := identOfString "Curl_auth_create_external_message"
def _Curl_auth_create_login_message : Ident := identOfString "Curl_auth_create_login_message"
def _Curl_auth_create_oauth_bearer_message : Ident := identOfString "Curl_auth_create_oauth_bearer_message"
def _Curl_auth_create_plain_message : Ident := identOfString "Curl_auth_create_plain_message"
def _Curl_auth_create_xoauth_bearer_message : Ident := identOfString "Curl_auth_create_xoauth_bearer_message"
def _Curl_bufref_free : Ident := identOfString "Curl_bufref_free"
def _Curl_bufref_init : Ident := identOfString "Curl_bufref_init"
def _Curl_bufref_len : Ident := identOfString "Curl_bufref_len"
def _Curl_bufref_ptr : Ident := identOfString "Curl_bufref_ptr"
def _Curl_conn_get_current_host : Ident := identOfString "Curl_conn_get_current_host"
def _Curl_easy : Ident := identOfString "Curl_easy"
def _Curl_sasl_start : Ident := identOfString "Curl_sasl_start"
def _SASL : Ident := identOfString "SASL"
def _SASLproto : Ident := identOfString "SASLproto"
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
def _allow_auth_to_other_hosts : Ident := identOfString "allow_auth_to_other_hosts"
def _aptr : Ident := identOfString "aptr"
def _authmechs : Ident := identOfString "authmechs"
def _authused : Ident := identOfString "authused"
def _bufref : Ident := identOfString "bufref"
def _build_message : Ident := identOfString "build_message"
def _cancelauth : Ident := identOfString "cancelauth"
def _conn : Ident := identOfString "conn"
def _connectdata : Ident := identOfString "connectdata"
def _contauth : Ident := identOfString "contauth"
def _contcode : Ident := identOfString "contcode"
def _curmech : Ident := identOfString "curmech"
def _data : Ident := identOfString "data"
def _defmechs : Ident := identOfString "defmechs"
def _dtor : Ident := identOfString "dtor"
def _dynamically_allocated_data : Ident := identOfString "dynamically_allocated_data"
def _enabledmechs : Ident := identOfString "enabledmechs"
def _finalcode : Ident := identOfString "finalcode"
def _flags : Ident := identOfString "flags"
def _force_ir : Ident := identOfString "force_ir"
def _getmessage : Ident := identOfString "getmessage"
def _hostname : Ident := identOfString "hostname"
def _len : Ident := identOfString "len"
def _main : Ident := identOfString "main"
def _maxirlen : Ident := identOfString "maxirlen"
def _mech : Ident := identOfString "mech"
def _memset : Ident := identOfString "memset"
def _mutual_auth : Ident := identOfString "mutual_auth"
def _oauth_bearer : Ident := identOfString "oauth_bearer"
def _params : Ident := identOfString "params"
def _passwd : Ident := identOfString "passwd"
def _port : Ident := identOfString "port"
def _prefmech : Ident := identOfString "prefmech"
def _progress : Ident := identOfString "progress"
def _ptr : Ident := identOfString "ptr"
def _resetprefs : Ident := identOfString "resetprefs"
def _resp : Ident := identOfString "resp"
def _result : Ident := identOfString "result"
def _sasl : Ident := identOfString "sasl"
def _sasl_authzid : Ident := identOfString "sasl_authzid"
def _sasl_choose_external : Ident := identOfString "sasl_choose_external"
def _sasl_choose_login : Ident := identOfString "sasl_choose_login"
def _sasl_choose_oauth : Ident := identOfString "sasl_choose_oauth"
def _sasl_choose_oauth2 : Ident := identOfString "sasl_choose_oauth2"
def _sasl_choose_plain : Ident := identOfString "sasl_choose_plain"
def _sasl_ctx : Ident := identOfString "sasl_ctx"
def _sasl_ir : Ident := identOfString "sasl_ir"
def _sasl_state : Ident := identOfString "sasl_state"
def _sctx : Ident := identOfString "sctx"
def _sendauth : Ident := identOfString "sendauth"
def _service : Ident := identOfString "service"
def _set : Ident := identOfString "set"
def _state : Ident := identOfString "state"
def _state1 : Ident := identOfString "state1"
def _state2 : Ident := identOfString "state2"
def _str : Ident := identOfString "str"
def _strlen : Ident := identOfString "strlen"
def _this_is_a_follow : Ident := identOfString "this_is_a_follow"
def _user : Ident := identOfString "user"
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
def _t'4 : Ident := (Positive.ofNat 131)
def _t'5 : Ident := (Positive.ofNat 132)
def _t'6 : Ident := (Positive.ofNat 133)
def _t'7 : Ident := (Positive.ofNat 134)
def _t'8 : Ident := (Positive.ofNat 135)
def _t'9 : Ident := (Positive.ofNat 136)

def v___stringlit_4 : GlobVar Ty := {
  gvar_info := (tarray tschar 6),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 80)),
                (InitData.Init_int8 (Integers.Int.repr 76)),
                (InitData.Init_int8 (Integers.Int.repr 65)),
                (InitData.Init_int8 (Integers.Int.repr 73)),
                (InitData.Init_int8 (Integers.Int.repr 78)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_3 : GlobVar Ty := {
  gvar_info := (tarray tschar 8),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 88)),
                (InitData.Init_int8 (Integers.Int.repr 79)),
                (InitData.Init_int8 (Integers.Int.repr 65)),
                (InitData.Init_int8 (Integers.Int.repr 85)),
                (InitData.Init_int8 (Integers.Int.repr 84)),
                (InitData.Init_int8 (Integers.Int.repr 72)),
                (InitData.Init_int8 (Integers.Int.repr 50)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_5 : GlobVar Ty := {
  gvar_info := (tarray tschar 6),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 76)),
                (InitData.Init_int8 (Integers.Int.repr 79)),
                (InitData.Init_int8 (Integers.Int.repr 71)),
                (InitData.Init_int8 (Integers.Int.repr 73)),
                (InitData.Init_int8 (Integers.Int.repr 78)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_1 : GlobVar Ty := {
  gvar_info := (tarray tschar 9),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 69)),
                (InitData.Init_int8 (Integers.Int.repr 88)),
                (InitData.Init_int8 (Integers.Int.repr 84)),
                (InitData.Init_int8 (Integers.Int.repr 69)),
                (InitData.Init_int8 (Integers.Int.repr 82)),
                (InitData.Init_int8 (Integers.Int.repr 78)),
                (InitData.Init_int8 (Integers.Int.repr 65)),
                (InitData.Init_int8 (Integers.Int.repr 76)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def v___stringlit_2 : GlobVar Ty := {
  gvar_info := (tarray tschar 12),
  gvar_init := [(InitData.Init_int8 (Integers.Int.repr 79)),
                (InitData.Init_int8 (Integers.Int.repr 65)),
                (InitData.Init_int8 (Integers.Int.repr 85)),
                (InitData.Init_int8 (Integers.Int.repr 84)),
                (InitData.Init_int8 (Integers.Int.repr 72)),
                (InitData.Init_int8 (Integers.Int.repr 66)),
                (InitData.Init_int8 (Integers.Int.repr 69)),
                (InitData.Init_int8 (Integers.Int.repr 65)),
                (InitData.Init_int8 (Integers.Int.repr 82)),
                (InitData.Init_int8 (Integers.Int.repr 69)),
                (InitData.Init_int8 (Integers.Int.repr 82)),
                (InitData.Init_int8 (Integers.Int.repr 0))],
  gvar_readonly := true,
  gvar_volatile := false
}

def f_sasl_choose_external : Function := {
  fn_return := tbool,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_sctx, (tptr (Ty.Tstruct _sasl_ctx noattr)))],
  fn_vars := [],
  fn_temps := [(_t'2, tint), (_t'1, tint), (_t'12, tschar),
               (_t'11, (tptr tschar)),
               (_t'10, (tptr (Ty.Tstruct _connectdata noattr))),
               (_t'9, tushort), (_t'8, (tptr (Ty.Tstruct _SASL noattr))),
               (_t'7, tint), (_t'6, tint),
               (_t'5, (tptr (Ty.Tstruct _SASL noattr))),
               (_t'4, (tptr tschar)),
               (_t'3, (tptr (Ty.Tstruct _connectdata noattr)))],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Sset _t'9
        (Expr.Efield
          (Expr.Ederef
            (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
            (Ty.Tstruct _sasl_ctx noattr)) _enabledmechs tushort))
      (Stmt.Sifthenelse (Expr.Ebinop Binop.Oand (Expr.Etempvar _t'9 tushort)
                          (Expr.Ebinop Binop.Oshl
                            (Expr.Econst_int (Integers.Int.repr 1) tint)
                            (Expr.Econst_int (Integers.Int.repr 5) tint)
                            tint) tint)
        (Stmt.Ssequence
          (Stmt.Sset _t'10
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                (Ty.Tstruct _sasl_ctx noattr)) _conn
              (tptr (Ty.Tstruct _connectdata noattr))))
          (Stmt.Ssequence
            (Stmt.Sset _t'11
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _t'10 (tptr (Ty.Tstruct _connectdata noattr)))
                  (Ty.Tstruct _connectdata noattr)) _passwd (tptr tschar)))
            (Stmt.Ssequence
              (Stmt.Sset _t'12
                (Expr.Ederef
                  (Expr.Ebinop Binop.Oadd (Expr.Etempvar _t'11 (tptr tschar))
                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                    (tptr tschar)) tschar))
              (Stmt.Sset _t'2
                (Expr.Ecast
                  (Expr.Eunop Unop.Onotbool (Expr.Etempvar _t'12 tschar)
                    tint) tbool)))))
        (Stmt.Sset _t'2 (Expr.Econst_int (Integers.Int.repr 0) tint))))
    (Stmt.Sifthenelse (Expr.Etempvar _t'2 tint)
      (Stmt.Ssequence
        (Stmt.Sassign
          (Expr.Efield
            (Expr.Ederef
              (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
              (Ty.Tstruct _sasl_ctx noattr)) _mech (tptr tschar))
          (Expr.Evar ___stringlit_1 (tarray tschar 9)))
        (Stmt.Ssequence
          (Stmt.Sassign
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                (Ty.Tstruct _sasl_ctx noattr)) _state1 tint)
            (Expr.Econst_int (Integers.Int.repr 4) tint))
          (Stmt.Ssequence
            (Stmt.Ssequence
              (Stmt.Sset _t'8
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                    (Ty.Tstruct _sasl_ctx noattr)) _sasl
                  (tptr (Ty.Tstruct _SASL noattr))))
              (Stmt.Sassign
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _t'8 (tptr (Ty.Tstruct _SASL noattr)))
                    (Ty.Tstruct _SASL noattr)) _authused tushort)
                (Expr.Ebinop Binop.Oshl
                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                  (Expr.Econst_int (Integers.Int.repr 5) tint) tint)))
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Sset _t'5
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                        (Ty.Tstruct _sasl_ctx noattr)) _sasl
                      (tptr (Ty.Tstruct _SASL noattr))))
                  (Stmt.Ssequence
                    (Stmt.Sset _t'6
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _t'5 (tptr (Ty.Tstruct _SASL noattr)))
                          (Ty.Tstruct _SASL noattr)) _force_ir tint))
                    (Stmt.Sifthenelse (Expr.Etempvar _t'6 tint)
                      (Stmt.Sset _t'1
                        (Expr.Econst_int (Integers.Int.repr 1) tint))
                      (Stmt.Ssequence
                        (Stmt.Sset _t'7
                          (Expr.Efield
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                (Ty.Tstruct _Curl_easy noattr)) _set
                              (Ty.Tstruct _UserDefined noattr)) _sasl_ir
                            tint))
                        (Stmt.Sset _t'1
                          (Expr.Ecast (Expr.Etempvar _t'7 tint) tbool))))))
                (Stmt.Sifthenelse (Expr.Etempvar _t'1 tint)
                  (Stmt.Ssequence
                    (Stmt.Sset _t'3
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                          (Ty.Tstruct _sasl_ctx noattr)) _conn
                        (tptr (Ty.Tstruct _connectdata noattr))))
                    (Stmt.Ssequence
                      (Stmt.Sset _t'4
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _t'3 (tptr (Ty.Tstruct _connectdata noattr)))
                            (Ty.Tstruct _connectdata noattr)) _user
                          (tptr tschar)))
                      (Stmt.Scall none
                        (Expr.Evar _Curl_auth_create_external_message 
                        (Ty.Tfunction
                          [(tptr tschar), (tptr (Ty.Tstruct _bufref noattr))]
                          tvoid cc_default))
                        [(Expr.Etempvar _t'4 (tptr tschar)),
                         (Expr.Eaddrof
                           (Expr.Efield
                             (Expr.Ederef
                               (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                               (Ty.Tstruct _sasl_ctx noattr)) _resp
                             (Ty.Tstruct _bufref noattr))
                           (tptr (Ty.Tstruct _bufref noattr)))])))
                  Stmt.Sskip))
              (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 1) tint)))))))
      Stmt.Sskip))
  (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint))))
}

def f_sasl_choose_oauth : Function := {
  fn_return := tbool,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_sctx, (tptr (Ty.Tstruct _sasl_ctx noattr)))],
  fn_vars := [(_hostname, (tptr tschar)), (_port, tint)],
  fn_temps := [(_oauth_bearer, (tptr tschar)), (_t'6, tint), (_t'5, tint),
               (_t'4, tint), (_t'3, tint), (_t'2, (tptr tvoid)),
               (_t'1, tint), (_t'19, tint), (_t'18, tint),
               (_t'17, (tptr tschar)), (_t'16, (tptr tschar)),
               (_t'15, tushort), (_t'14, (tptr (Ty.Tstruct _SASL noattr))),
               (_t'13, tint), (_t'12, tint),
               (_t'11, (tptr (Ty.Tstruct _SASL noattr))), (_t'10, tint),
               (_t'9, (tptr tschar)), (_t'8, (tptr tschar)),
               (_t'7, (tptr (Ty.Tstruct _connectdata noattr)))],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Ssequence
        (Stmt.Sset _t'18
          (Expr.Efield
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                (Ty.Tstruct _Curl_easy noattr)) _state
              (Ty.Tstruct _UrlState noattr)) _this_is_a_follow tint))
        (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                            (Expr.Etempvar _t'18 tint) tint)
          (Stmt.Sset _t'1 (Expr.Econst_int (Integers.Int.repr 1) tint))
          (Stmt.Ssequence
            (Stmt.Sset _t'19
              (Expr.Efield
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                    (Ty.Tstruct _Curl_easy noattr)) _set
                  (Ty.Tstruct _UserDefined noattr))
                _allow_auth_to_other_hosts tint))
            (Stmt.Sset _t'1 (Expr.Ecast (Expr.Etempvar _t'19 tint) tbool)))))
      (Stmt.Sifthenelse (Expr.Etempvar _t'1 tint)
        (Stmt.Ssequence
          (Stmt.Sset _t'17
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
          (Stmt.Sset _t'2
            (Expr.Ecast (Expr.Etempvar _t'17 (tptr tschar)) (tptr tvoid))))
        (Stmt.Sset _t'2
          (Expr.Ecast
            (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint)
              (tptr tvoid)) (tptr tvoid)))))
    (Stmt.Sset _oauth_bearer (Expr.Etempvar _t'2 (tptr tvoid))))
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Sset _t'16
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                (Ty.Tstruct _sasl_ctx noattr)) _user (tptr tschar)))
          (Stmt.Sifthenelse (Expr.Etempvar _t'16 (tptr tschar))
            (Stmt.Sset _t'5
              (Expr.Ecast (Expr.Etempvar _oauth_bearer (tptr tschar)) tbool))
            (Stmt.Sset _t'5 (Expr.Econst_int (Integers.Int.repr 0) tint))))
        (Stmt.Sifthenelse (Expr.Etempvar _t'5 tint)
          (Stmt.Ssequence
            (Stmt.Sset _t'15
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                  (Ty.Tstruct _sasl_ctx noattr)) _enabledmechs tushort))
            (Stmt.Sset _t'6
              (Expr.Ecast
                (Expr.Ebinop Binop.Oand (Expr.Etempvar _t'15 tushort)
                  (Expr.Ebinop Binop.Oshl
                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                    (Expr.Econst_int (Integers.Int.repr 8) tint) tint) tint)
                tbool)))
          (Stmt.Sset _t'6 (Expr.Econst_int (Integers.Int.repr 0) tint))))
      (Stmt.Sifthenelse (Expr.Etempvar _t'6 tint)
        (Stmt.Ssequence
          (Stmt.Scall none
            (Expr.Evar _Curl_conn_get_current_host (Ty.Tfunction
                                                     [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                      tint,
                                                      (tptr (tptr tschar)),
                                                      (tptr tint)] tvoid
                                                     cc_default))
            [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
             (Expr.Econst_int (Integers.Int.repr 0) tint),
             (Expr.Eaddrof (Expr.Evar _hostname (tptr tschar))
               (tptr (tptr tschar))),
             (Expr.Eaddrof (Expr.Evar _port tint) (tptr tint))])
          (Stmt.Ssequence
            (Stmt.Sassign
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                  (Ty.Tstruct _sasl_ctx noattr)) _mech (tptr tschar))
              (Expr.Evar ___stringlit_2 (tarray tschar 12)))
            (Stmt.Ssequence
              (Stmt.Sassign
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                    (Ty.Tstruct _sasl_ctx noattr)) _state1 tint)
                (Expr.Econst_int (Integers.Int.repr 13) tint))
              (Stmt.Ssequence
                (Stmt.Sassign
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                      (Ty.Tstruct _sasl_ctx noattr)) _state2 tint)
                  (Expr.Econst_int (Integers.Int.repr 14) tint))
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Sset _t'14
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                          (Ty.Tstruct _sasl_ctx noattr)) _sasl
                        (tptr (Ty.Tstruct _SASL noattr))))
                    (Stmt.Sassign
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _t'14 (tptr (Ty.Tstruct _SASL noattr)))
                          (Ty.Tstruct _SASL noattr)) _authused tushort)
                      (Expr.Ebinop Binop.Oshl
                        (Expr.Econst_int (Integers.Int.repr 1) tint)
                        (Expr.Econst_int (Integers.Int.repr 8) tint) tint)))
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Sset _t'11
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                              (Ty.Tstruct _sasl_ctx noattr)) _sasl
                            (tptr (Ty.Tstruct _SASL noattr))))
                        (Stmt.Ssequence
                          (Stmt.Sset _t'12
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _t'11 (tptr (Ty.Tstruct _SASL noattr)))
                                (Ty.Tstruct _SASL noattr)) _force_ir tint))
                          (Stmt.Sifthenelse (Expr.Etempvar _t'12 tint)
                            (Stmt.Sset _t'4
                              (Expr.Econst_int (Integers.Int.repr 1) tint))
                            (Stmt.Ssequence
                              (Stmt.Sset _t'13
                                (Expr.Efield
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                      (Ty.Tstruct _Curl_easy noattr)) _set
                                    (Ty.Tstruct _UserDefined noattr))
                                  _sasl_ir tint))
                              (Stmt.Sset _t'4
                                (Expr.Ecast (Expr.Etempvar _t'13 tint) tbool))))))
                      (Stmt.Sifthenelse (Expr.Etempvar _t'4 tint)
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'7
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                                  (Ty.Tstruct _sasl_ctx noattr)) _conn
                                (tptr (Ty.Tstruct _connectdata noattr))))
                            (Stmt.Ssequence
                              (Stmt.Sset _t'8
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _t'7 (tptr (Ty.Tstruct _connectdata noattr)))
                                    (Ty.Tstruct _connectdata noattr)) _user
                                  (tptr tschar)))
                              (Stmt.Ssequence
                                (Stmt.Sset _t'9
                                  (Expr.Evar _hostname (tptr tschar)))
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'10 (Expr.Evar _port tint))
                                  (Stmt.Scall (some _t'3)
                                    (Expr.Evar _Curl_auth_create_oauth_bearer_message 
                                    (Ty.Tfunction
                                      [(tptr tschar), (tptr tschar), tlong,
                                       (tptr tschar),
                                       (tptr (Ty.Tstruct _bufref noattr))]
                                      tint cc_default))
                                    [(Expr.Etempvar _t'8 (tptr tschar)),
                                     (Expr.Etempvar _t'9 (tptr tschar)),
                                     (Expr.Etempvar _t'10 tint),
                                     (Expr.Etempvar _oauth_bearer (tptr tschar)),
                                     (Expr.Eaddrof
                                       (Expr.Efield
                                         (Expr.Ederef
                                           (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                                           (Ty.Tstruct _sasl_ctx noattr))
                                         _resp (Ty.Tstruct _bufref noattr))
                                       (tptr (Ty.Tstruct _bufref noattr)))])))))
                          (Stmt.Sassign
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                                (Ty.Tstruct _sasl_ctx noattr)) _result tint)
                            (Expr.Etempvar _t'3 tint)))
                        Stmt.Sskip))
                    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 1) tint)))))))))
        Stmt.Sskip))
    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint)))))
}

def f_sasl_choose_oauth2 : Function := {
  fn_return := tbool,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_sctx, (tptr (Ty.Tstruct _sasl_ctx noattr)))],
  fn_vars := [],
  fn_temps := [(_oauth_bearer, (tptr tschar)), (_t'6, tint), (_t'5, tint),
               (_t'4, tint), (_t'3, tint), (_t'2, (tptr tvoid)),
               (_t'1, tint), (_t'17, tint), (_t'16, tint),
               (_t'15, (tptr tschar)), (_t'14, (tptr tschar)),
               (_t'13, tushort), (_t'12, (tptr (Ty.Tstruct _SASL noattr))),
               (_t'11, tint), (_t'10, tint),
               (_t'9, (tptr (Ty.Tstruct _SASL noattr))),
               (_t'8, (tptr tschar)),
               (_t'7, (tptr (Ty.Tstruct _connectdata noattr)))],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Ssequence
        (Stmt.Sset _t'16
          (Expr.Efield
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                (Ty.Tstruct _Curl_easy noattr)) _state
              (Ty.Tstruct _UrlState noattr)) _this_is_a_follow tint))
        (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                            (Expr.Etempvar _t'16 tint) tint)
          (Stmt.Sset _t'1 (Expr.Econst_int (Integers.Int.repr 1) tint))
          (Stmt.Ssequence
            (Stmt.Sset _t'17
              (Expr.Efield
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                    (Ty.Tstruct _Curl_easy noattr)) _set
                  (Ty.Tstruct _UserDefined noattr))
                _allow_auth_to_other_hosts tint))
            (Stmt.Sset _t'1 (Expr.Ecast (Expr.Etempvar _t'17 tint) tbool)))))
      (Stmt.Sifthenelse (Expr.Etempvar _t'1 tint)
        (Stmt.Ssequence
          (Stmt.Sset _t'15
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
          (Stmt.Sset _t'2
            (Expr.Ecast (Expr.Etempvar _t'15 (tptr tschar)) (tptr tvoid))))
        (Stmt.Sset _t'2
          (Expr.Ecast
            (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint)
              (tptr tvoid)) (tptr tvoid)))))
    (Stmt.Sset _oauth_bearer (Expr.Etempvar _t'2 (tptr tvoid))))
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Sset _t'14
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                (Ty.Tstruct _sasl_ctx noattr)) _user (tptr tschar)))
          (Stmt.Sifthenelse (Expr.Etempvar _t'14 (tptr tschar))
            (Stmt.Sset _t'5
              (Expr.Ecast (Expr.Etempvar _oauth_bearer (tptr tschar)) tbool))
            (Stmt.Sset _t'5 (Expr.Econst_int (Integers.Int.repr 0) tint))))
        (Stmt.Sifthenelse (Expr.Etempvar _t'5 tint)
          (Stmt.Ssequence
            (Stmt.Sset _t'13
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                  (Ty.Tstruct _sasl_ctx noattr)) _enabledmechs tushort))
            (Stmt.Sset _t'6
              (Expr.Ecast
                (Expr.Ebinop Binop.Oand (Expr.Etempvar _t'13 tushort)
                  (Expr.Ebinop Binop.Oshl
                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                    (Expr.Econst_int (Integers.Int.repr 7) tint) tint) tint)
                tbool)))
          (Stmt.Sset _t'6 (Expr.Econst_int (Integers.Int.repr 0) tint))))
      (Stmt.Sifthenelse (Expr.Etempvar _t'6 tint)
        (Stmt.Ssequence
          (Stmt.Sassign
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                (Ty.Tstruct _sasl_ctx noattr)) _mech (tptr tschar))
            (Expr.Evar ___stringlit_3 (tarray tschar 8)))
          (Stmt.Ssequence
            (Stmt.Sassign
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                  (Ty.Tstruct _sasl_ctx noattr)) _state1 tint)
              (Expr.Econst_int (Integers.Int.repr 13) tint))
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Sset _t'12
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                      (Ty.Tstruct _sasl_ctx noattr)) _sasl
                    (tptr (Ty.Tstruct _SASL noattr))))
                (Stmt.Sassign
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _t'12 (tptr (Ty.Tstruct _SASL noattr)))
                      (Ty.Tstruct _SASL noattr)) _authused tushort)
                  (Expr.Ebinop Binop.Oshl
                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                    (Expr.Econst_int (Integers.Int.repr 7) tint) tint)))
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Sset _t'9
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                          (Ty.Tstruct _sasl_ctx noattr)) _sasl
                        (tptr (Ty.Tstruct _SASL noattr))))
                    (Stmt.Ssequence
                      (Stmt.Sset _t'10
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _t'9 (tptr (Ty.Tstruct _SASL noattr)))
                            (Ty.Tstruct _SASL noattr)) _force_ir tint))
                      (Stmt.Sifthenelse (Expr.Etempvar _t'10 tint)
                        (Stmt.Sset _t'4
                          (Expr.Econst_int (Integers.Int.repr 1) tint))
                        (Stmt.Ssequence
                          (Stmt.Sset _t'11
                            (Expr.Efield
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                  (Ty.Tstruct _Curl_easy noattr)) _set
                                (Ty.Tstruct _UserDefined noattr)) _sasl_ir
                              tint))
                          (Stmt.Sset _t'4
                            (Expr.Ecast (Expr.Etempvar _t'11 tint) tbool))))))
                  (Stmt.Sifthenelse (Expr.Etempvar _t'4 tint)
                    (Stmt.Ssequence
                      (Stmt.Ssequence
                        (Stmt.Sset _t'7
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                              (Ty.Tstruct _sasl_ctx noattr)) _conn
                            (tptr (Ty.Tstruct _connectdata noattr))))
                        (Stmt.Ssequence
                          (Stmt.Sset _t'8
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _t'7 (tptr (Ty.Tstruct _connectdata noattr)))
                                (Ty.Tstruct _connectdata noattr)) _user
                              (tptr tschar)))
                          (Stmt.Scall (some _t'3)
                            (Expr.Evar _Curl_auth_create_xoauth_bearer_message 
                            (Ty.Tfunction
                              [(tptr tschar), (tptr tschar),
                               (tptr (Ty.Tstruct _bufref noattr))] tint
                              cc_default))
                            [(Expr.Etempvar _t'8 (tptr tschar)),
                             (Expr.Etempvar _oauth_bearer (tptr tschar)),
                             (Expr.Eaddrof
                               (Expr.Efield
                                 (Expr.Ederef
                                   (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                                   (Ty.Tstruct _sasl_ctx noattr)) _resp
                                 (Ty.Tstruct _bufref noattr))
                               (tptr (Ty.Tstruct _bufref noattr)))])))
                      (Stmt.Sassign
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                            (Ty.Tstruct _sasl_ctx noattr)) _result tint)
                        (Expr.Etempvar _t'3 tint)))
                    Stmt.Sskip))
                (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 1) tint)))))))
        Stmt.Sskip))
    (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint)))))
}

def f_sasl_choose_plain : Function := {
  fn_return := tbool,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_sctx, (tptr (Ty.Tstruct _sasl_ctx noattr)))],
  fn_vars := [],
  fn_temps := [(_t'3, tint), (_t'2, tint), (_t'1, tint), (_t'15, tushort),
               (_t'14, (tptr tschar)),
               (_t'13, (tptr (Ty.Tstruct _SASL noattr))), (_t'12, tint),
               (_t'11, tint), (_t'10, (tptr (Ty.Tstruct _SASL noattr))),
               (_t'9, (tptr tschar)),
               (_t'8, (tptr (Ty.Tstruct _connectdata noattr))),
               (_t'7, (tptr tschar)),
               (_t'6, (tptr (Ty.Tstruct _connectdata noattr))),
               (_t'5, (tptr tschar)),
               (_t'4, (tptr (Ty.Tstruct _connectdata noattr)))],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Sset _t'14
        (Expr.Efield
          (Expr.Ederef
            (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
            (Ty.Tstruct _sasl_ctx noattr)) _user (tptr tschar)))
      (Stmt.Sifthenelse (Expr.Etempvar _t'14 (tptr tschar))
        (Stmt.Ssequence
          (Stmt.Sset _t'15
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                (Ty.Tstruct _sasl_ctx noattr)) _enabledmechs tushort))
          (Stmt.Sset _t'3
            (Expr.Ecast
              (Expr.Ebinop Binop.Oand (Expr.Etempvar _t'15 tushort)
                (Expr.Ebinop Binop.Oshl
                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                  (Expr.Econst_int (Integers.Int.repr 1) tint) tint) tint)
              tbool)))
        (Stmt.Sset _t'3 (Expr.Econst_int (Integers.Int.repr 0) tint))))
    (Stmt.Sifthenelse (Expr.Etempvar _t'3 tint)
      (Stmt.Ssequence
        (Stmt.Sassign
          (Expr.Efield
            (Expr.Ederef
              (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
              (Ty.Tstruct _sasl_ctx noattr)) _mech (tptr tschar))
          (Expr.Evar ___stringlit_4 (tarray tschar 6)))
        (Stmt.Ssequence
          (Stmt.Sassign
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                (Ty.Tstruct _sasl_ctx noattr)) _state1 tint)
            (Expr.Econst_int (Integers.Int.repr 1) tint))
          (Stmt.Ssequence
            (Stmt.Ssequence
              (Stmt.Sset _t'13
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                    (Ty.Tstruct _sasl_ctx noattr)) _sasl
                  (tptr (Ty.Tstruct _SASL noattr))))
              (Stmt.Sassign
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _t'13 (tptr (Ty.Tstruct _SASL noattr)))
                    (Ty.Tstruct _SASL noattr)) _authused tushort)
                (Expr.Ebinop Binop.Oshl
                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                  (Expr.Econst_int (Integers.Int.repr 1) tint) tint)))
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Sset _t'10
                    (Expr.Efield
                      (Expr.Ederef
                        (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                        (Ty.Tstruct _sasl_ctx noattr)) _sasl
                      (tptr (Ty.Tstruct _SASL noattr))))
                  (Stmt.Ssequence
                    (Stmt.Sset _t'11
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _t'10 (tptr (Ty.Tstruct _SASL noattr)))
                          (Ty.Tstruct _SASL noattr)) _force_ir tint))
                    (Stmt.Sifthenelse (Expr.Etempvar _t'11 tint)
                      (Stmt.Sset _t'2
                        (Expr.Econst_int (Integers.Int.repr 1) tint))
                      (Stmt.Ssequence
                        (Stmt.Sset _t'12
                          (Expr.Efield
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                (Ty.Tstruct _Curl_easy noattr)) _set
                              (Ty.Tstruct _UserDefined noattr)) _sasl_ir
                            tint))
                        (Stmt.Sset _t'2
                          (Expr.Ecast (Expr.Etempvar _t'12 tint) tbool))))))
                (Stmt.Sifthenelse (Expr.Etempvar _t'2 tint)
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sset _t'4
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                            (Ty.Tstruct _sasl_ctx noattr)) _conn
                          (tptr (Ty.Tstruct _connectdata noattr))))
                      (Stmt.Ssequence
                        (Stmt.Sset _t'5
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _t'4 (tptr (Ty.Tstruct _connectdata noattr)))
                              (Ty.Tstruct _connectdata noattr)) _sasl_authzid
                            (tptr tschar)))
                        (Stmt.Ssequence
                          (Stmt.Sset _t'6
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                                (Ty.Tstruct _sasl_ctx noattr)) _conn
                              (tptr (Ty.Tstruct _connectdata noattr))))
                          (Stmt.Ssequence
                            (Stmt.Sset _t'7
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _t'6 (tptr (Ty.Tstruct _connectdata noattr)))
                                  (Ty.Tstruct _connectdata noattr)) _user
                                (tptr tschar)))
                            (Stmt.Ssequence
                              (Stmt.Sset _t'8
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                                    (Ty.Tstruct _sasl_ctx noattr)) _conn
                                  (tptr (Ty.Tstruct _connectdata noattr))))
                              (Stmt.Ssequence
                                (Stmt.Sset _t'9
                                  (Expr.Efield
                                    (Expr.Ederef
                                      (Expr.Etempvar _t'8 (tptr (Ty.Tstruct _connectdata noattr)))
                                      (Ty.Tstruct _connectdata noattr))
                                    _passwd (tptr tschar)))
                                (Stmt.Scall (some _t'1)
                                  (Expr.Evar _Curl_auth_create_plain_message 
                                  (Ty.Tfunction
                                    [(tptr tschar), (tptr tschar),
                                     (tptr tschar),
                                     (tptr (Ty.Tstruct _bufref noattr))] tint
                                    cc_default))
                                  [(Expr.Etempvar _t'5 (tptr tschar)),
                                   (Expr.Etempvar _t'7 (tptr tschar)),
                                   (Expr.Etempvar _t'9 (tptr tschar)),
                                   (Expr.Eaddrof
                                     (Expr.Efield
                                       (Expr.Ederef
                                         (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                                         (Ty.Tstruct _sasl_ctx noattr)) _resp
                                       (Ty.Tstruct _bufref noattr))
                                     (tptr (Ty.Tstruct _bufref noattr)))])))))))
                    (Stmt.Sassign
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                          (Ty.Tstruct _sasl_ctx noattr)) _result tint)
                      (Expr.Etempvar _t'1 tint)))
                  Stmt.Sskip))
              (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 1) tint)))))))
      Stmt.Sskip))
  (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint))))
}

def f_sasl_choose_login : Function := {
  fn_return := tbool,
  fn_callconv := cc_default,
  fn_params := [(_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_sctx, (tptr (Ty.Tstruct _sasl_ctx noattr)))],
  fn_vars := [],
  fn_temps := [(_t'2, tint), (_t'1, tint), (_t'10, tushort),
               (_t'9, (tptr tschar)),
               (_t'8, (tptr (Ty.Tstruct _SASL noattr))), (_t'7, tint),
               (_t'6, tint), (_t'5, (tptr (Ty.Tstruct _SASL noattr))),
               (_t'4, (tptr tschar)),
               (_t'3, (tptr (Ty.Tstruct _connectdata noattr)))],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Sset _t'9
        (Expr.Efield
          (Expr.Ederef
            (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
            (Ty.Tstruct _sasl_ctx noattr)) _user (tptr tschar)))
      (Stmt.Sifthenelse (Expr.Etempvar _t'9 (tptr tschar))
        (Stmt.Ssequence
          (Stmt.Sset _t'10
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                (Ty.Tstruct _sasl_ctx noattr)) _enabledmechs tushort))
          (Stmt.Sset _t'2
            (Expr.Ecast
              (Expr.Ebinop Binop.Oand (Expr.Etempvar _t'10 tushort)
                (Expr.Ebinop Binop.Oshl
                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                  (Expr.Econst_int (Integers.Int.repr 0) tint) tint) tint)
              tbool)))
        (Stmt.Sset _t'2 (Expr.Econst_int (Integers.Int.repr 0) tint))))
    (Stmt.Sifthenelse (Expr.Etempvar _t'2 tint)
      (Stmt.Ssequence
        (Stmt.Sassign
          (Expr.Efield
            (Expr.Ederef
              (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
              (Ty.Tstruct _sasl_ctx noattr)) _mech (tptr tschar))
          (Expr.Evar ___stringlit_5 (tarray tschar 6)))
        (Stmt.Ssequence
          (Stmt.Sassign
            (Expr.Efield
              (Expr.Ederef
                (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                (Ty.Tstruct _sasl_ctx noattr)) _state1 tint)
            (Expr.Econst_int (Integers.Int.repr 2) tint))
          (Stmt.Ssequence
            (Stmt.Sassign
              (Expr.Efield
                (Expr.Ederef
                  (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                  (Ty.Tstruct _sasl_ctx noattr)) _state2 tint)
              (Expr.Econst_int (Integers.Int.repr 3) tint))
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Sset _t'8
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                      (Ty.Tstruct _sasl_ctx noattr)) _sasl
                    (tptr (Ty.Tstruct _SASL noattr))))
                (Stmt.Sassign
                  (Expr.Efield
                    (Expr.Ederef
                      (Expr.Etempvar _t'8 (tptr (Ty.Tstruct _SASL noattr)))
                      (Ty.Tstruct _SASL noattr)) _authused tushort)
                  (Expr.Ebinop Binop.Oshl
                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                    (Expr.Econst_int (Integers.Int.repr 0) tint) tint)))
              (Stmt.Ssequence
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Sset _t'5
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                          (Ty.Tstruct _sasl_ctx noattr)) _sasl
                        (tptr (Ty.Tstruct _SASL noattr))))
                    (Stmt.Ssequence
                      (Stmt.Sset _t'6
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _t'5 (tptr (Ty.Tstruct _SASL noattr)))
                            (Ty.Tstruct _SASL noattr)) _force_ir tint))
                      (Stmt.Sifthenelse (Expr.Etempvar _t'6 tint)
                        (Stmt.Sset _t'1
                          (Expr.Econst_int (Integers.Int.repr 1) tint))
                        (Stmt.Ssequence
                          (Stmt.Sset _t'7
                            (Expr.Efield
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                  (Ty.Tstruct _Curl_easy noattr)) _set
                                (Ty.Tstruct _UserDefined noattr)) _sasl_ir
                              tint))
                          (Stmt.Sset _t'1
                            (Expr.Ecast (Expr.Etempvar _t'7 tint) tbool))))))
                  (Stmt.Sifthenelse (Expr.Etempvar _t'1 tint)
                    (Stmt.Ssequence
                      (Stmt.Sset _t'3
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                            (Ty.Tstruct _sasl_ctx noattr)) _conn
                          (tptr (Ty.Tstruct _connectdata noattr))))
                      (Stmt.Ssequence
                        (Stmt.Sset _t'4
                          (Expr.Efield
                            (Expr.Ederef
                              (Expr.Etempvar _t'3 (tptr (Ty.Tstruct _connectdata noattr)))
                              (Ty.Tstruct _connectdata noattr)) _user
                            (tptr tschar)))
                        (Stmt.Scall none
                          (Expr.Evar _Curl_auth_create_login_message 
                          (Ty.Tfunction
                            [(tptr tschar),
                             (tptr (Ty.Tstruct _bufref noattr))] tvoid
                            cc_default))
                          [(Expr.Etempvar _t'4 (tptr tschar)),
                           (Expr.Eaddrof
                             (Expr.Efield
                               (Expr.Ederef
                                 (Expr.Etempvar _sctx (tptr (Ty.Tstruct _sasl_ctx noattr)))
                                 (Ty.Tstruct _sasl_ctx noattr)) _resp
                               (Ty.Tstruct _bufref noattr))
                             (tptr (Ty.Tstruct _bufref noattr)))])))
                    Stmt.Sskip))
                (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 1) tint))))))))
      Stmt.Sskip))
  (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint))))
}

def f_Curl_sasl_start : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_sasl, (tptr (Ty.Tstruct _SASL noattr))),
                (_data, (tptr (Ty.Tstruct _Curl_easy noattr))),
                (_force_ir, tbool), (_progress, (tptr tint))],
  fn_vars := [(_sctx, (Ty.Tstruct _sasl_ctx noattr))],
  fn_temps := [(_t'18, tint), (_t'17, tint), (_t'16, (tptr tschar)),
               (_t'15, tint), (_t'14, tulong), (_t'13, tulong),
               (_t'12, tint), (_t'11, (tptr tschar)), (_t'10, tint),
               (_t'9, tbool), (_t'8, tint), (_t'7, tbool), (_t'6, tint),
               (_t'5, tbool), (_t'4, tint), (_t'3, tbool), (_t'2, tint),
               (_t'1, tbool),
               (_t'38, (tptr (Ty.Tstruct _connectdata noattr))),
               (_t'37, (tptr tschar)), (_t'36, tushort), (_t'35, tushort),
               (_t'34, (tptr tschar)), (_t'33, tint), (_t'32, (tptr tschar)),
               (_t'31, (tptr tschar)), (_t'30, tulong),
               (_t'29, (tptr (Ty.Tstruct _SASLproto noattr))),
               (_t'28, tulong),
               (_t'27, (tptr (Ty.Tstruct _SASLproto noattr))),
               (_t'26, (tptr tschar)),
               (_t'25,
                (tptr (Ty.Tfunction
                        [(tptr (Ty.Tstruct _Curl_easy noattr)),
                         (tptr tschar), (tptr (Ty.Tstruct _bufref noattr))]
                        tint cc_default))),
               (_t'24, (tptr (Ty.Tstruct _SASLproto noattr))), (_t'23, tint),
               (_t'22, tint), (_t'21, tint), (_t'20, tint), (_t'19, tint)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Sassign
    (Expr.Efield
      (Expr.Ederef (Expr.Etempvar _sasl (tptr (Ty.Tstruct _SASL noattr)))
        (Ty.Tstruct _SASL noattr)) _force_ir tint)
    (Expr.Etempvar _force_ir tbool))
  (Stmt.Ssequence
    (Stmt.Sassign
      (Expr.Efield
        (Expr.Ederef (Expr.Etempvar _sasl (tptr (Ty.Tstruct _SASL noattr)))
          (Ty.Tstruct _SASL noattr)) _authused tushort)
      (Expr.Econst_int (Integers.Int.repr 0) tint))
    (Stmt.Ssequence
      (Stmt.Sassign (Expr.Ederef (Expr.Etempvar _progress (tptr tint)) tint)
        (Expr.Econst_int (Integers.Int.repr 0) tint))
      (Stmt.Ssequence
        (Stmt.Scall none
          (Expr.Evar _memset (Ty.Tfunction [(tptr tvoid), tint, tulong]
                               (tptr tvoid) cc_default))
          [(Expr.Eaddrof (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
             (tptr (Ty.Tstruct _sasl_ctx noattr))),
           (Expr.Econst_int (Integers.Int.repr 0) tint),
           (Expr.Esizeof (Ty.Tstruct _sasl_ctx noattr) tulong)])
        (Stmt.Ssequence
          (Stmt.Sassign
            (Expr.Efield (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
              _sasl (tptr (Ty.Tstruct _SASL noattr)))
            (Expr.Etempvar _sasl (tptr (Ty.Tstruct _SASL noattr))))
          (Stmt.Ssequence
            (Stmt.Ssequence
              (Stmt.Sset _t'38
                (Expr.Efield
                  (Expr.Ederef
                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                    (Ty.Tstruct _Curl_easy noattr)) _conn
                  (tptr (Ty.Tstruct _connectdata noattr))))
              (Stmt.Sassign
                (Expr.Efield (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                  _conn (tptr (Ty.Tstruct _connectdata noattr)))
                (Expr.Etempvar _t'38 (tptr (Ty.Tstruct _connectdata noattr)))))
            (Stmt.Ssequence
              (Stmt.Ssequence
                (Stmt.Sset _t'37
                  (Expr.Efield
                    (Expr.Efield
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                          (Ty.Tstruct _Curl_easy noattr)) _state
                        (Ty.Tstruct _UrlState noattr)) _aptr
                      (Ty.Tstruct _dynamically_allocated_data noattr)) _user
                    (tptr tschar)))
                (Stmt.Sassign
                  (Expr.Efield
                    (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr)) _user
                    (tptr tschar)) (Expr.Etempvar _t'37 (tptr tschar))))
              (Stmt.Ssequence
                (Stmt.Scall none
                  (Expr.Evar _Curl_bufref_init (Ty.Tfunction
                                                 [(tptr (Ty.Tstruct _bufref noattr))]
                                                 tvoid cc_default))
                  [(Expr.Eaddrof
                     (Expr.Efield
                       (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr)) _resp
                       (Ty.Tstruct _bufref noattr))
                     (tptr (Ty.Tstruct _bufref noattr)))])
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Sset _t'35
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _sasl (tptr (Ty.Tstruct _SASL noattr)))
                          (Ty.Tstruct _SASL noattr)) _authmechs tushort))
                    (Stmt.Ssequence
                      (Stmt.Sset _t'36
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _sasl (tptr (Ty.Tstruct _SASL noattr)))
                            (Ty.Tstruct _SASL noattr)) _prefmech tushort))
                      (Stmt.Sassign
                        (Expr.Efield
                          (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                          _enabledmechs tushort)
                        (Expr.Ebinop Binop.Oand (Expr.Etempvar _t'35 tushort)
                          (Expr.Etempvar _t'36 tushort) tint))))
                  (Stmt.Ssequence
                    (Stmt.Sassign
                      (Expr.Efield
                        (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                        _state1 tint)
                      (Expr.Econst_int (Integers.Int.repr 0) tint))
                    (Stmt.Ssequence
                      (Stmt.Sassign
                        (Expr.Efield
                          (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                          _state2 tint)
                        (Expr.Econst_int (Integers.Int.repr 17) tint))
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Scall (some _t'1)
                                    (Expr.Evar _sasl_choose_external 
                                    (Ty.Tfunction
                                      [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                       (tptr (Ty.Tstruct _sasl_ctx noattr))]
                                      tbool cc_default))
                                    [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                     (Expr.Eaddrof
                                       (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                       (tptr (Ty.Tstruct _sasl_ctx noattr)))])
                                  (Stmt.Sifthenelse (Expr.Etempvar _t'1 tbool)
                                    (Stmt.Sset _t'2
                                      (Expr.Econst_int (Integers.Int.repr 1) tint))
                                    (Stmt.Ssequence
                                      (Stmt.Scall (some _t'3)
                                        (Expr.Evar _sasl_choose_oauth 
                                        (Ty.Tfunction
                                          [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                           (tptr (Ty.Tstruct _sasl_ctx noattr))]
                                          tbool cc_default))
                                        [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                         (Expr.Eaddrof
                                           (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                           (tptr (Ty.Tstruct _sasl_ctx noattr)))])
                                      (Stmt.Sset _t'2
                                        (Expr.Ecast
                                          (Expr.Etempvar _t'3 tbool) tbool)))))
                                (Stmt.Sifthenelse (Expr.Etempvar _t'2 tint)
                                  (Stmt.Sset _t'4
                                    (Expr.Econst_int (Integers.Int.repr 1) tint))
                                  (Stmt.Ssequence
                                    (Stmt.Scall (some _t'5)
                                      (Expr.Evar _sasl_choose_oauth2 
                                      (Ty.Tfunction
                                        [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                         (tptr (Ty.Tstruct _sasl_ctx noattr))]
                                        tbool cc_default))
                                      [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                       (Expr.Eaddrof
                                         (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                         (tptr (Ty.Tstruct _sasl_ctx noattr)))])
                                    (Stmt.Sset _t'4
                                      (Expr.Ecast (Expr.Etempvar _t'5 tbool)
                                        tbool)))))
                              (Stmt.Sifthenelse (Expr.Etempvar _t'4 tint)
                                (Stmt.Sset _t'6
                                  (Expr.Econst_int (Integers.Int.repr 1) tint))
                                (Stmt.Ssequence
                                  (Stmt.Scall (some _t'7)
                                    (Expr.Evar _sasl_choose_plain (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                    (tptr (Ty.Tstruct _sasl_ctx noattr))]
                                                                    tbool
                                                                    cc_default))
                                    [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                     (Expr.Eaddrof
                                       (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                       (tptr (Ty.Tstruct _sasl_ctx noattr)))])
                                  (Stmt.Sset _t'6
                                    (Expr.Ecast (Expr.Etempvar _t'7 tbool)
                                      tbool)))))
                            (Stmt.Sifthenelse (Expr.Etempvar _t'6 tint)
                              (Stmt.Sset _t'8
                                (Expr.Econst_int (Integers.Int.repr 1) tint))
                              (Stmt.Ssequence
                                (Stmt.Scall (some _t'9)
                                  (Expr.Evar _sasl_choose_login (Ty.Tfunction
                                                                  [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                   (tptr (Ty.Tstruct _sasl_ctx noattr))]
                                                                  tbool
                                                                  cc_default))
                                  [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                   (Expr.Eaddrof
                                     (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                     (tptr (Ty.Tstruct _sasl_ctx noattr)))])
                                (Stmt.Sset _t'8
                                  (Expr.Ecast (Expr.Etempvar _t'9 tbool)
                                    tbool)))))
                          (Stmt.Sifthenelse (Expr.Etempvar _t'8 tint)
                            (Stmt.Sloop Stmt.Sskip Stmt.Sbreak)
                            Stmt.Sskip))
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Sset _t'33
                                (Expr.Efield
                                  (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                  _result tint))
                              (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                                  (Expr.Etempvar _t'33 tint)
                                                  tint)
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'34
                                    (Expr.Efield
                                      (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                      _mech (tptr tschar)))
                                  (Stmt.Sset _t'18
                                    (Expr.Ecast
                                      (Expr.Etempvar _t'34 (tptr tschar))
                                      tbool)))
                                (Stmt.Sset _t'18
                                  (Expr.Econst_int (Integers.Int.repr 0) tint))))
                            (Stmt.Sifthenelse (Expr.Etempvar _t'18 tint)
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'32
                                    (Expr.Efield
                                      (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                      _mech (tptr tschar)))
                                  (Stmt.Sassign
                                    (Expr.Efield
                                      (Expr.Ederef
                                        (Expr.Etempvar _sasl (tptr (Ty.Tstruct _SASL noattr)))
                                        (Ty.Tstruct _SASL noattr)) _curmech
                                      (tptr tschar))
                                    (Expr.Etempvar _t'32 (tptr tschar))))
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Scall (some _t'11)
                                      (Expr.Evar _Curl_bufref_ptr (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _bufref noattr))]
                                                                    (tptr tschar)
                                                                    cc_default))
                                      [(Expr.Eaddrof
                                         (Expr.Efield
                                           (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                           _resp (Ty.Tstruct _bufref noattr))
                                         (tptr (Ty.Tstruct _bufref noattr)))])
                                    (Stmt.Sifthenelse (Expr.Etempvar _t'11 (tptr tschar))
                                      (Stmt.Ssequence
                                        (Stmt.Scall (some _t'10)
                                          (Expr.Evar _build_message (Ty.Tfunction
                                                                    [(tptr (Ty.Tstruct _SASL noattr)),
                                                                    (tptr (Ty.Tstruct _bufref noattr))]
                                                                    tint
                                                                    cc_default))
                                          [(Expr.Etempvar _sasl (tptr (Ty.Tstruct _SASL noattr))),
                                           (Expr.Eaddrof
                                             (Expr.Efield
                                               (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                               _resp
                                               (Ty.Tstruct _bufref noattr))
                                             (tptr (Ty.Tstruct _bufref noattr)))])
                                        (Stmt.Sassign
                                          (Expr.Efield
                                            (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                            _result tint)
                                          (Expr.Etempvar _t'10 tint)))
                                      Stmt.Sskip))
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'27
                                          (Expr.Efield
                                            (Expr.Ederef
                                              (Expr.Etempvar _sasl (tptr (Ty.Tstruct _SASL noattr)))
                                              (Ty.Tstruct _SASL noattr))
                                            _params
                                            (tptr (Ty.Tstruct _SASLproto noattr))))
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'28
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _t'27 (tptr (Ty.Tstruct _SASLproto noattr)))
                                                (Ty.Tstruct _SASLproto noattr))
                                              _maxirlen tulong))
                                          (Stmt.Sifthenelse (Expr.Etempvar _t'28 tulong)
                                            (Stmt.Ssequence
                                              (Stmt.Ssequence
                                                (Stmt.Ssequence
                                                  (Stmt.Sset _t'31
                                                    (Expr.Efield
                                                      (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                                      _mech (tptr tschar)))
                                                  (Stmt.Scall (some _t'13)
                                                    (Expr.Evar _strlen 
                                                    (Ty.Tfunction
                                                      [(tptr tschar)] tulong
                                                      cc_default))
                                                    [(Expr.Etempvar _t'31 (tptr tschar))]))
                                                (Stmt.Scall (some _t'14)
                                                  (Expr.Evar _Curl_bufref_len 
                                                  (Ty.Tfunction
                                                    [(tptr (Ty.Tstruct _bufref noattr))]
                                                    tulong cc_default))
                                                  [(Expr.Eaddrof
                                                     (Expr.Efield
                                                       (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                                       _resp
                                                       (Ty.Tstruct _bufref noattr))
                                                     (tptr (Ty.Tstruct _bufref noattr)))]))
                                              (Stmt.Ssequence
                                                (Stmt.Sset _t'29
                                                  (Expr.Efield
                                                    (Expr.Ederef
                                                      (Expr.Etempvar _sasl (tptr (Ty.Tstruct _SASL noattr)))
                                                      (Ty.Tstruct _SASL noattr))
                                                    _params
                                                    (tptr (Ty.Tstruct _SASLproto noattr))))
                                                (Stmt.Ssequence
                                                  (Stmt.Sset _t'30
                                                    (Expr.Efield
                                                      (Expr.Ederef
                                                        (Expr.Etempvar _t'29 (tptr (Ty.Tstruct _SASLproto noattr)))
                                                        (Ty.Tstruct _SASLproto noattr))
                                                      _maxirlen tulong))
                                                  (Stmt.Sset _t'12
                                                    (Expr.Ecast
                                                      (Expr.Ebinop Binop.Ogt
                                                        (Expr.Ebinop Binop.Oadd
                                                          (Expr.Etempvar _t'13 tulong)
                                                          (Expr.Etempvar _t'14 tulong)
                                                          tulong)
                                                        (Expr.Etempvar _t'30 tulong)
                                                        tint) tbool)))))
                                            (Stmt.Sset _t'12
                                              (Expr.Econst_int (Integers.Int.repr 0) tint)))))
                                      (Stmt.Sifthenelse (Expr.Etempvar _t'12 tint)
                                        (Stmt.Scall none
                                          (Expr.Evar _Curl_bufref_free 
                                          (Ty.Tfunction
                                            [(tptr (Ty.Tstruct _bufref noattr))]
                                            tvoid cc_default))
                                          [(Expr.Eaddrof
                                             (Expr.Efield
                                               (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                               _resp
                                               (Ty.Tstruct _bufref noattr))
                                             (tptr (Ty.Tstruct _bufref noattr)))])
                                        Stmt.Sskip))
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'23
                                          (Expr.Efield
                                            (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                            _result tint))
                                        (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                                            (Expr.Etempvar _t'23 tint)
                                                            tint)
                                          (Stmt.Ssequence
                                            (Stmt.Ssequence
                                              (Stmt.Sset _t'24
                                                (Expr.Efield
                                                  (Expr.Ederef
                                                    (Expr.Etempvar _sasl (tptr (Ty.Tstruct _SASL noattr)))
                                                    (Ty.Tstruct _SASL noattr))
                                                  _params
                                                  (tptr (Ty.Tstruct _SASLproto noattr))))
                                              (Stmt.Ssequence
                                                (Stmt.Sset _t'25
                                                  (Expr.Efield
                                                    (Expr.Ederef
                                                      (Expr.Etempvar _t'24 (tptr (Ty.Tstruct _SASLproto noattr)))
                                                      (Ty.Tstruct _SASLproto noattr))
                                                    _sendauth
                                                    (tptr (Ty.Tfunction
                                                            [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                             (tptr tschar),
                                                             (tptr (Ty.Tstruct _bufref noattr))]
                                                            tint cc_default))))
                                                (Stmt.Ssequence
                                                  (Stmt.Sset _t'26
                                                    (Expr.Efield
                                                      (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                                      _mech (tptr tschar)))
                                                  (Stmt.Scall (some _t'15)
                                                    (Expr.Etempvar _t'25 (tptr 
                                                    (Ty.Tfunction
                                                      [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                       (tptr tschar),
                                                       (tptr (Ty.Tstruct _bufref noattr))]
                                                      tint cc_default)))
                                                    [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                     (Expr.Etempvar _t'26 (tptr tschar)),
                                                     (Expr.Eaddrof
                                                       (Expr.Efield
                                                         (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                                         _resp
                                                         (Ty.Tstruct _bufref noattr))
                                                       (tptr (Ty.Tstruct _bufref noattr)))]))))
                                            (Stmt.Sassign
                                              (Expr.Efield
                                                (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                                _result tint)
                                              (Expr.Etempvar _t'15 tint)))
                                          Stmt.Sskip))
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'20
                                          (Expr.Efield
                                            (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                            _result tint))
                                        (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                                            (Expr.Etempvar _t'20 tint)
                                                            tint)
                                          (Stmt.Ssequence
                                            (Stmt.Sassign
                                              (Expr.Ederef
                                                (Expr.Etempvar _progress (tptr tint))
                                                tint)
                                              (Expr.Econst_int (Integers.Int.repr 1) tint))
                                            (Stmt.Ssequence
                                              (Stmt.Ssequence
                                                (Stmt.Scall (some _t'16)
                                                  (Expr.Evar _Curl_bufref_ptr 
                                                  (Ty.Tfunction
                                                    [(tptr (Ty.Tstruct _bufref noattr))]
                                                    (tptr tschar) cc_default))
                                                  [(Expr.Eaddrof
                                                     (Expr.Efield
                                                       (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                                       _resp
                                                       (Ty.Tstruct _bufref noattr))
                                                     (tptr (Ty.Tstruct _bufref noattr)))])
                                                (Stmt.Sifthenelse (Expr.Etempvar _t'16 (tptr tschar))
                                                  (Stmt.Ssequence
                                                    (Stmt.Sset _t'22
                                                      (Expr.Efield
                                                        (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                                        _state2 tint))
                                                    (Stmt.Sset _t'17
                                                      (Expr.Ecast
                                                        (Expr.Etempvar _t'22 tint)
                                                        tint)))
                                                  (Stmt.Ssequence
                                                    (Stmt.Sset _t'21
                                                      (Expr.Efield
                                                        (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                                        _state1 tint))
                                                    (Stmt.Sset _t'17
                                                      (Expr.Ecast
                                                        (Expr.Etempvar _t'21 tint)
                                                        tint)))))
                                              (Stmt.Scall none
                                                (Expr.Evar _sasl_state 
                                                (Ty.Tfunction
                                                  [(tptr (Ty.Tstruct _SASL noattr)),
                                                   (tptr (Ty.Tstruct _Curl_easy noattr)),
                                                   tint] tvoid cc_default))
                                                [(Expr.Etempvar _sasl (tptr (Ty.Tstruct _SASL noattr))),
                                                 (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                                 (Expr.Etempvar _t'17 tint)])))
                                          Stmt.Sskip))))))
                              Stmt.Sskip))
                          (Stmt.Ssequence
                            (Stmt.Scall none
                              (Expr.Evar _Curl_bufref_free (Ty.Tfunction
                                                             [(tptr (Ty.Tstruct _bufref noattr))]
                                                             tvoid
                                                             cc_default))
                              [(Expr.Eaddrof
                                 (Expr.Efield
                                   (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                   _resp (Ty.Tstruct _bufref noattr))
                                 (tptr (Ty.Tstruct _bufref noattr)))])
                            (Stmt.Ssequence
                              (Stmt.Sset _t'19
                                (Expr.Efield
                                  (Expr.Evar _sctx (Ty.Tstruct _sasl_ctx noattr))
                                  _result tint))
                              (Stmt.Sreturn (some (Expr.Etempvar _t'19 tint))))))))))))))))))
}

def composites : List CompositeDef :=
[(CompositeDef.Composite _bufref SU.Struct
   [(Member.Member_plain _dtor
      (tptr (Ty.Tfunction [(tptr tvoid)] tvoid cc_default))),
    (Member.Member_plain _ptr (tptr tuchar)),
    (Member.Member_plain _len tulong)]
   noattr),
 (CompositeDef.Composite _SASLproto SU.Struct
   [(Member.Member_plain _service (tptr tschar)),
    (Member.Member_plain _sendauth
      (tptr (Ty.Tfunction
              [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar),
               (tptr (Ty.Tstruct _bufref noattr))] tint cc_default))),
    (Member.Member_plain _contauth
      (tptr (Ty.Tfunction
              [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar),
               (tptr (Ty.Tstruct _bufref noattr))] tint cc_default))),
    (Member.Member_plain _cancelauth
      (tptr (Ty.Tfunction
              [(tptr (Ty.Tstruct _Curl_easy noattr)), (tptr tschar)] tint
              cc_default))),
    (Member.Member_plain _getmessage
      (tptr (Ty.Tfunction
              [(tptr (Ty.Tstruct _Curl_easy noattr)),
               (tptr (Ty.Tstruct _bufref noattr))] tint cc_default))),
    (Member.Member_plain _maxirlen tulong),
    (Member.Member_plain _contcode tint),
    (Member.Member_plain _finalcode tint),
    (Member.Member_plain _defmechs tushort),
    (Member.Member_plain _flags tushort)]
   noattr),
 (CompositeDef.Composite _SASL SU.Struct
   [(Member.Member_plain _params (tptr (Ty.Tstruct _SASLproto noattr))),
    (Member.Member_plain _state tint),
    (Member.Member_plain _curmech (tptr tschar)),
    (Member.Member_plain _authmechs tushort),
    (Member.Member_plain _prefmech tushort),
    (Member.Member_plain _authused tushort),
    (Member.Member_bitfield _resetprefs IntSize.I32 Signedness.Unsigned
      noattr 1 false),
    (Member.Member_bitfield _mutual_auth IntSize.I32 Signedness.Unsigned
      noattr 1 false),
    (Member.Member_bitfield _force_ir IntSize.I32 Signedness.Unsigned noattr
      1 false)]
   noattr),
 (CompositeDef.Composite _connectdata SU.Struct
   [(Member.Member_plain _user (tptr tschar)),
    (Member.Member_plain _passwd (tptr tschar)),
    (Member.Member_plain _sasl_authzid (tptr tschar))]
   noattr),
 (CompositeDef.Composite _dynamically_allocated_data SU.Struct
   [(Member.Member_plain _user (tptr tschar))]
   noattr),
 (CompositeDef.Composite _UrlState SU.Struct
   [(Member.Member_plain _aptr
      (Ty.Tstruct _dynamically_allocated_data noattr)),
    (Member.Member_bitfield _this_is_a_follow IntSize.I32 Signedness.Unsigned
      noattr 1 false)]
   noattr),
 (CompositeDef.Composite _UserDefined SU.Struct
   [(Member.Member_plain _str (tarray (tptr tschar) 70)),
    (Member.Member_bitfield _allow_auth_to_other_hosts IntSize.I32
      Signedness.Unsigned noattr 1 false),
    (Member.Member_bitfield _sasl_ir IntSize.I32 Signedness.Unsigned noattr 1
      false)]
   noattr),
 (CompositeDef.Composite _Curl_easy SU.Struct
   [(Member.Member_plain _conn (tptr (Ty.Tstruct _connectdata noattr))),
    (Member.Member_plain _set (Ty.Tstruct _UserDefined noattr)),
    (Member.Member_plain _state (Ty.Tstruct _UrlState noattr))]
   noattr),
 (CompositeDef.Composite _sasl_ctx SU.Struct
   [(Member.Member_plain _sasl (tptr (Ty.Tstruct _SASL noattr))),
    (Member.Member_plain _conn (tptr (Ty.Tstruct _connectdata noattr))),
    (Member.Member_plain _user (tptr tschar)),
    (Member.Member_plain _enabledmechs tushort),
    (Member.Member_plain _mech (tptr tschar)),
    (Member.Member_plain _state1 tint), (Member.Member_plain _state2 tint),
    (Member.Member_plain _resp (Ty.Tstruct _bufref noattr)),
    (Member.Member_plain _result tint)]
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
 (___stringlit_4, GlobDef.Gvar v___stringlit_4),
 (___stringlit_3, GlobDef.Gvar v___stringlit_3),
 (___stringlit_5, GlobDef.Gvar v___stringlit_5),
 (___stringlit_1, GlobDef.Gvar v___stringlit_1),
 (___stringlit_2, GlobDef.Gvar v___stringlit_2),
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
 (_Curl_conn_get_current_host,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_conn_get_current_host"
                                   (mksignature
                                     [XType.Xptr, XType.Xint, XType.Xptr,
                                      XType.Xptr] XType.Xvoid cc_default))
     [(tptr (Ty.Tstruct _Curl_easy noattr)), tint, (tptr (tptr tschar)),
      (tptr tint)] tvoid cc_default)),
 (_Curl_bufref_init,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_bufref_init"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default))
     [(tptr (Ty.Tstruct _bufref noattr))] tvoid cc_default)),
 (_Curl_bufref_ptr,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_bufref_ptr"
                                   (mksignature [XType.Xptr] XType.Xptr
                                     cc_default))
     [(tptr (Ty.Tstruct _bufref noattr))] (tptr tschar) cc_default)),
 (_Curl_bufref_len,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_bufref_len"
                                   (mksignature [XType.Xptr] XType.Xlong
                                     cc_default))
     [(tptr (Ty.Tstruct _bufref noattr))] tulong cc_default)),
 (_Curl_bufref_free,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_bufref_free"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default))
     [(tptr (Ty.Tstruct _bufref noattr))] tvoid cc_default)),
 (_Curl_auth_create_external_message,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_auth_create_external_message"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xvoid cc_default))
     [(tptr tschar), (tptr (Ty.Tstruct _bufref noattr))] tvoid cc_default)),
 (_Curl_auth_create_oauth_bearer_message,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_auth_create_oauth_bearer_message"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xlong,
                                      XType.Xptr, XType.Xptr] XType.Xint
                                     cc_default))
     [(tptr tschar), (tptr tschar), tlong, (tptr tschar),
      (tptr (Ty.Tstruct _bufref noattr))] tint cc_default)),
 (_Curl_auth_create_xoauth_bearer_message,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_auth_create_xoauth_bearer_message"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xptr]
                                     XType.Xint cc_default))
     [(tptr tschar), (tptr tschar), (tptr (Ty.Tstruct _bufref noattr))] tint
     cc_default)),
 (_Curl_auth_create_plain_message,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_auth_create_plain_message"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xptr,
                                      XType.Xptr] XType.Xint cc_default))
     [(tptr tschar), (tptr tschar), (tptr tschar),
      (tptr (Ty.Tstruct _bufref noattr))] tint cc_default)),
 (_Curl_auth_create_login_message,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "Curl_auth_create_login_message"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xvoid cc_default))
     [(tptr tschar), (tptr (Ty.Tstruct _bufref noattr))] tvoid cc_default)),
 (_build_message,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "build_message"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xint cc_default))
     [(tptr (Ty.Tstruct _SASL noattr)), (tptr (Ty.Tstruct _bufref noattr))]
     tint cc_default)),
 (_sasl_state,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "sasl_state"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xint]
                                     XType.Xvoid cc_default))
     [(tptr (Ty.Tstruct _SASL noattr)),
      (tptr (Ty.Tstruct _Curl_easy noattr)), tint] tvoid cc_default)),
 (_memset,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "memset"
                                   (mksignature
                                     [XType.Xptr, XType.Xint, XType.Xlong]
                                     XType.Xptr cc_default))
     [(tptr tvoid), tint, tulong] (tptr tvoid) cc_default)),
 (_strlen,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "strlen"
                                   (mksignature [XType.Xptr] XType.Xlong
                                     cc_default)) [(tptr tschar)] tulong
     cc_default)),
 (_sasl_choose_external, GlobDef.Gfun (FunDef.Internal f_sasl_choose_external)),
 (_sasl_choose_oauth, GlobDef.Gfun (FunDef.Internal f_sasl_choose_oauth)),
 (_sasl_choose_oauth2, GlobDef.Gfun (FunDef.Internal f_sasl_choose_oauth2)),
 (_sasl_choose_plain, GlobDef.Gfun (FunDef.Internal f_sasl_choose_plain)),
 (_sasl_choose_login, GlobDef.Gfun (FunDef.Internal f_sasl_choose_login)),
 (_Curl_sasl_start, GlobDef.Gfun (FunDef.Internal f_Curl_sasl_start))]

def public_idents : List Ident :=
[_Curl_sasl_start, _strlen, _memset, _sasl_state, _build_message,
 _Curl_auth_create_login_message, _Curl_auth_create_plain_message,
 _Curl_auth_create_xoauth_bearer_message,
 _Curl_auth_create_oauth_bearer_message, _Curl_auth_create_external_message,
 _Curl_bufref_free, _Curl_bufref_len, _Curl_bufref_ptr, _Curl_bufref_init,
 _Curl_conn_get_current_host, ___builtin_debug, ___builtin_fmin,
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

end Deb2025_14524_u1

