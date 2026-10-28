/-
CVE-2026-8927: curl 8.14.1 に Debian の CVE-2026-8927.patch を当てた（D1）`create_conn_helper_init_proxy`。

場面 S（cases/CVE-2026-8927.md）の上で、関数は CURLE_OK を返し、戻った時点の所有は `cellsD1 c (sFinD c same q)`
であることを示す（`helper_after`）。U1 と同じく、`Curl_safecmp` が偽なら `proxydigest.nonce` は NULL になる。
8.14.1 では関数の形が上流と違う（`conn->handler`、`conn->http_proxy.host.rawalloc`、Unix ソケットの分岐、
`parse_proxy` の後の `Curl_safefree(proxy)`）ので、U1 の証明を写すのではなく、同じ道具で書き直した。
-/
import Deb2026_8927GenD1
import Deb2026_8927U1
open CC CC.Sep CC.HProp
open Deb2026_8927_d1
open Case4C (call_none IsPtr loadResult_ptr cast_ptr)

set_option maxRecDepth 20000

namespace Deb2026_8927

/-! ## 8.14.1 のセル（`struct connectdata` の並びが上流と違う） -/

def cWD (c : Ctx) (s : St) : Cell := ⟨.Mint32, c.connB, u (f2 c.connO 96 0), .Vint s.w⟩
/-- `conn->http_proxy.host.rawalloc`（`St.hpeer` に入れる。`parse_proxy` が `peerB`・`peerO` にする）。 -/
def cHraw (c : Ctx) (s : St) : Cell := ⟨Mptr, c.connB, u (f1 (f2 c.connO 56 0) 0), s.hpeer⟩
def cHptD (c : Ctx) (s : St) : Cell := ⟨.Mint8unsigned, c.connB, u (f2 c.connO 56 16), .Vint s.hpt⟩
/-- `conn->host.name` -/
def cDName (c : Ctx) : Cell := ⟨Mptr, c.connB, u (f2 c.connO 0 8), .Vptr c.hostB c.hostO⟩
/-- `conn->handler`（`schB`・`schO` を指す。`protocol`・`flags` の位置は上流の `Curl_scheme` と同じ） -/
def cHdl (c : Ctx) : Cell := ⟨Mptr, c.connB, u (f1 c.connO 104), .Vptr c.schB c.schO⟩
def cSraw (c : Ctx) : Cell := ⟨Mptr, c.connB, u (f1 (f2 c.connO 16 0) 0), vnull⟩
def cUnix (c : Ctx) : Cell := ⟨Mptr, c.connB, u (f1 c.connO 112), vnull⟩

abbrev fixD (c : Ctx) : List Cell :=
  [cProxy c, cPre c, cNo c, cNp c, cDName c, cHdl c, cProto c, cFlags c, cP c, cSraw c, cPeer c, cUnix c]

abbrev cellsD1 (c : Ctx) (s : St) : List Cell :=
  cWD c s :: cHraw c s :: cHptD c s :: cEnv1 c s :: cNonce1 c s :: fixD c

/-- 8.14.1 の `conn->bits` の書き込み: httpproxy = 1、socksproxy = 0、proxy = 1 の順。 -/
def dw1 : Integers.Int :=
  Integers.Int.bitfield_insert (Cop.firstBit .I32 0 1).toNat 1 (Integers.Int.repr 0) (Integers.Int.repr 1)
def dw2 : Integers.Int :=
  Integers.Int.bitfield_insert (Cop.firstBit .I32 1 1).toNat 1 dw1 (Integers.Int.repr 0)
def dwFin : Integers.Int :=
  Integers.Int.bitfield_insert (Cop.firstBit .I32 4 1).toNat 1 dw2 (Integers.Int.repr 1)

def sWD (c : Ctx) (same : Bool) (q : Val) (w : Integers.Int) : St :=
  ⟨w, .Vptr c.peerB c.peerO, Integers.Int.repr 0, cond same c.envV q, cond same c.nonce0 vnull⟩

def sFinD (c : Ctx) (same : Bool) (q : Val) : St := sWD c same q dwFin

end Deb2026_8927

namespace Deb2026_8927.D1
open Deb2026_8927

def coOf (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_easy : prog.prog_comp_env.get _Curl_easy = some (coOf _Curl_easy) := rfl
theorem co_ud : prog.prog_comp_env.get _UserDefined = some (coOf _UserDefined) := rfl
theorem co_state : prog.prog_comp_env.get _UrlState = some (coOf _UrlState) := rfl
theorem co_conn : prog.prog_comp_env.get _connectdata = some (coOf _connectdata) := rfl
theorem co_pi : prog.prog_comp_env.get _proxy_info = some (coOf _proxy_info) := rfl
theorem co_hn : prog.prog_comp_env.get _hostname = some (coOf _hostname) := rfl
theorem co_bits : prog.prog_comp_env.get _ConnectBits = some (coOf _ConnectBits) := rfl
theorem co_hdl : prog.prog_comp_env.get _Curl_handler = some (coOf _Curl_handler) := rfl

theorem off_set : fieldOffset prog.prog_comp_env _set (coOf _Curl_easy).co_members = .OK (0, .Full) := by decide
theorem off_state : fieldOffset prog.prog_comp_env _state (coOf _Curl_easy).co_members = .OK (568, .Full) := by decide
theorem off_str : fieldOffset prog.prog_comp_env _str (coOf _UserDefined).co_members = .OK (0, .Full) := by decide
theorem off_envproxy : fieldOffset prog.prog_comp_env _envproxy (coOf _UrlState).co_members = .OK (0, .Full) := by decide
theorem off_proxydigest : fieldOffset prog.prog_comp_env _proxydigest (coOf _UrlState).co_members = .OK (16, .Full) := by decide
theorem off_host : fieldOffset prog.prog_comp_env _host (coOf _connectdata).co_members = .OK (0, .Full) := by decide
theorem off_socks : fieldOffset prog.prog_comp_env _socks_proxy (coOf _connectdata).co_members = .OK (16, .Full) := by decide
theorem off_http : fieldOffset prog.prog_comp_env _http_proxy (coOf _connectdata).co_members = .OK (56, .Full) := by decide
theorem off_bits : fieldOffset prog.prog_comp_env _bits (coOf _connectdata).co_members = .OK (96, .Full) := by decide
theorem off_handler : fieldOffset prog.prog_comp_env _handler (coOf _connectdata).co_members = .OK (104, .Full) := by decide
theorem off_unix : fieldOffset prog.prog_comp_env _unix_domain_socket (coOf _connectdata).co_members = .OK (112, .Full) := by decide
theorem off_pihost : fieldOffset prog.prog_comp_env _host (coOf _proxy_info).co_members = .OK (0, .Full) := by decide
theorem off_proxytype : fieldOffset prog.prog_comp_env _proxytype (coOf _proxy_info).co_members = .OK (16, .Full) := by decide
theorem off_rawalloc : fieldOffset prog.prog_comp_env _rawalloc (coOf _hostname).co_members = .OK (0, .Full) := by decide
theorem off_name : fieldOffset prog.prog_comp_env _name (coOf _hostname).co_members = .OK (8, .Full) := by decide
theorem off_protocol : fieldOffset prog.prog_comp_env _protocol (coOf _Curl_handler).co_members = .OK (0, .Full) := by decide
theorem off_flags : fieldOffset prog.prog_comp_env _flags (coOf _Curl_handler).co_members = .OK (8, .Full) := by decide
theorem off_httpproxy : fieldOffset prog.prog_comp_env _httpproxy (coOf _ConnectBits).co_members = .OK (0, .Bits .I32 .Unsigned 0 1) := by decide
theorem off_socksproxy : fieldOffset prog.prog_comp_env _socksproxy (coOf _ConnectBits).co_members = .OK (0, .Bits .I32 .Unsigned 1 1) := by decide
theorem off_pup : fieldOffset prog.prog_comp_env _proxy_user_passwd (coOf _ConnectBits).co_members = .OK (0, .Bits .I32 .Unsigned 2 1) := by decide
theorem off_proxyb : fieldOffset prog.prog_comp_env _proxy (coOf _ConnectBits).co_members = .OK (0, .Bits .I32 .Unsigned 4 1) := by decide

/-- `p->f1.f2.f3` の左辺値（`f1`・`f2` は構造体）。 -/
theorem lv_f3 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {p sid sid1 sid2 f1 f2 f3 : Ident}
    {ty : Ty} {co co1 co2 : Composite} {b : Block} {o : Integers.Ptrofs} {d1 d2 d3 : Z}
    (hle : le.get p = some (.Vptr b o)) (hco : ge.genv_cenv.get sid = some co)
    (hf1 : fieldOffset ge.genv_cenv f1 co.co_members = .OK (d1, .Full))
    (hco1 : ge.genv_cenv.get sid1 = some co1)
    (hf2 : fieldOffset ge.genv_cenv f2 co1.co_members = .OK (d2, .Full))
    (hco2 : ge.genv_cenv.get sid2 = some co2)
    (hf3 : fieldOffset ge.genv_cenv f3 co2.co_members = .OK (d3, .Full)) :
    EvalLvalue ge e le m
      (.Efield (.Efield (.Efield (.Ederef (.Etempvar p (tptr (.Tstruct sid noattr))) (.Tstruct sid noattr))
        f1 (.Tstruct sid1 noattr)) f2 (.Tstruct sid2 noattr)) f3 ty)
      b (Integers.Ptrofs.add (Integers.Ptrofs.add (Integers.Ptrofs.add o (Integers.Ptrofs.repr d1))
        (Integers.Ptrofs.repr d2)) (Integers.Ptrofs.repr d3)) .Full :=
  EvalLvalue.Efield_struct _ f3 ty b _ sid2 co2 noattr d3 .Full
    (EvalExpr.Elvalue _ _ _ .Full _ (lv_f2 hle hco hf1 hco1 hf2) (DerefLoc.copy rfl)) rfl hco2 hf3

theorem cast_vptr_bool {b : Block} {o : Integers.Ptrofs} {t : Ty} {m : Mem}
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.semCast (.Vptr b o) (tptr t) tbool m = some (Val.ofBool true) := by
  unfold Cop.semCast
  simp [Cop.classifyCast, tptr, tbool, hv, Archi.ptr64, Val.ofBool] <;> rfl

/-- `PROTO_FAMILY_HTTP` の値（`(1<<0 | 1<<1 | 1<<30) | ((curl_prot_t)1 << 31)`）。 -/
def famHttp : Integers.Int64 := Integers.Int64.repr 3221225475

def famExpr : Expr :=
  Expr.Ebinop Binop.Oor
    (Expr.Ebinop Binop.Oor
      (Expr.Ebinop Binop.Oor
        (Expr.Ebinop Binop.Oshl (Expr.Econst_long (Integers.Int64.repr 1) tlong)
          (Expr.Econst_int (Integers.Int.repr 0) tint) tlong)
        (Expr.Ebinop Binop.Oshl (Expr.Econst_long (Integers.Int64.repr 1) tlong)
          (Expr.Econst_int (Integers.Int.repr 1) tint) tlong) tlong)
      (Expr.Ebinop Binop.Oshl (Expr.Econst_long (Integers.Int64.repr 1) tlong)
        (Expr.Econst_int (Integers.Int.repr 30) tint) tlong) tlong)
    (Expr.Ebinop Binop.Oshl (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 1) tint) tlong)
      (Expr.Econst_int (Integers.Int.repr 31) tint) tlong) tlong

theorem eval_fam {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} :
    EvalExpr ge e le m famExpr (.Vlong famHttp) :=
  EvalExpr.Ebinop _ _ _ _ _ _ _
    (EvalExpr.Ebinop _ _ _ _ _ _ _
      (EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_long _ _) (EvalExpr.Econst_int _ _) rfl)
        (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_long _ _) (EvalExpr.Econst_int _ _) rfl) rfl)
      (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_long _ _) (EvalExpr.Econst_int _ _) rfl) rfl)
    (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)
      (EvalExpr.Econst_int _ _) rfl) rfl

/-! ## 仕様 -/

def helperSpecA (c : Ctx) (same : Bool) (q : Val) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _connectdata noattr)]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dataB c.dataO, .Vptr c.connB c.connO]
    ∧ Cells c.pm (cellsD1 c (s0 c)) hp
  post := fun v hp => v = .Vint (Integers.Int.repr 0) ∧ Cells c.pm (cellsD1 c (sFinD c same q)) hp
  measure := fun _ => 0

/-- `parse_proxy(data, conn, proxy, ptype)`: CURLE_OK を返し、`conn->http_proxy.host.rawalloc` を
    `peerB`・`peerO` に、`proxytype` を 0 にする。ほかのセルは変えない（引数は問わない）。 -/
def parseSpec (c : Ctx) (s : St) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _connectdata noattr), tptr tschar, tint]
  tyres := tint
  cc := cc_default
  pre := fun _ hp => Cells c.pm (cellsD1 c s) hp
  post := fun v hp => v = .Vint (Integers.Int.repr 0) ∧
    Cells c.pm (cellsD1 c { s with hpeer := .Vptr c.peerB c.peerO, hpt := Integers.Int.repr 0 }) hp
  measure := fun _ => 0

def digestSpec (c : Ctx) (s : St) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _digestdata noattr)]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dataB (f2 c.dataO 568 16)] ∧ Cells c.pm (cellsD1 c s) hp
  post := fun _ hp => Cells c.pm (cellsD1 c { s with nonce := vnull }) hp
  measure := fun _ => 0

theorem entry_wf :
    listNorepet (varNames f_create_conn_helper_init_proxy.fn_vars)
    ∧ listNorepet (varNames f_create_conn_helper_init_proxy.fn_params)
    ∧ listDisjoint (varNames f_create_conn_helper_init_proxy.fn_params)
        (varNames f_create_conn_helper_init_proxy.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxHeartbeats 4000000 in
theorem helper_after (ge : CGenv) (c : Ctx) (same : Bool) (q : Val)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hpc : Integers.Int.eq (Integers.Int.sign_ext 8 c.pc) Integers.Int.zero = false)
    (hfl : Integers.Int.eq (Integers.Int.and c.flags
      (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 4))) Integers.Int.zero = true)
    (hproto : Integers.Int64.eq (Integers.Int64.and c.proto famHttp) Integers.Int64.zero = false)
    (henv : IsPtr c.envV) (hq : IsPtr q)
    (bNo bDet bFree bParse bCmp bDg bDup : Block)
    (fdNo fdDet fdFree fdParse fdCmp fdDg fdDup : FunDef)
    (hsNo : Genv.findSymbol ge.genv_genv _Curl_check_noproxy = some bNo)
    (hsDet : Genv.findSymbol ge.genv_genv _detect_proxy = some bDet)
    (hsFree : Genv.findSymbol ge.genv_genv _Curl_cfree = some bFree)
    (hsParse : Genv.findSymbol ge.genv_genv _parse_proxy = some bParse)
    (hsCmp : Genv.findSymbol ge.genv_genv _Curl_safecmp = some bCmp)
    (hsDg : Genv.findSymbol ge.genv_genv _Curl_auth_digest_cleanup = some bDg)
    (hsDup : Genv.findSymbol ge.genv_genv _Curl_cstrdup = some bDup)
    (hfNo : FuncPtr ge bNo fdNo) (hfDet : FuncPtr ge bDet fdDet) (hfFree : FuncPtr ge bFree fdFree)
    (hfParse : FuncPtr ge bParse fdParse) (hfCmp : FuncPtr ge bCmp fdCmp)
    (hfDg : FuncPtr ge bDg fdDg) (hfDup : FuncPtr ge bDup fdDup)
    (htyNo : typeOfFundef fdNo = .Tfunction [tptr tschar, tptr tschar] tbool cc_default)
    (htyDet : typeOfFundef fdDet = .Tfunction [tptr (Ty.Tstruct _Curl_easy noattr),
      tptr (Ty.Tstruct _connectdata noattr)] (tptr tschar) cc_default)
    (htyFree : typeOfFundef fdFree = .Tfunction [tptr tvoid] tvoid cc_default)
    (htyParse : typeOfFundef fdParse = .Tfunction [tptr (Ty.Tstruct _Curl_easy noattr),
      tptr (Ty.Tstruct _connectdata noattr), tptr tschar, tint] tint cc_default)
    (htyCmp : typeOfFundef fdCmp = .Tfunction [tptr tschar, tptr tschar] tbool cc_default)
    (htyDg : typeOfFundef fdDg = .Tfunction [tptr (Ty.Tstruct _digestdata noattr)] tvoid cc_default)
    (htyDup : typeOfFundef fdDup = .Tfunction [tptr tschar] (tptr tschar) cc_default)
    (hNo : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdNo
      (retSpec [tptr tschar, tptr tschar] tbool (Val.ofBool false)) vs)
    (hDet : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdDet
      (retSpec [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _connectdata noattr)]
        (tptr tschar) (.Vptr c.pB c.pO)) vs)
    (hFree : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdFree (retSpec [tptr tvoid] tvoid .Vundef) vs)
    (hParse : ∀ s vs, SatisfiesAt ge (FunctionEntry2 ge) fdParse (parseSpec c s) vs)
    (hCmp : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCmp
      (retSpec [tptr tschar, tptr tschar] tbool (Val.ofBool same)) vs)
    (hDg : ∀ s vs, SatisfiesAt ge (FunctionEntry2 ge) fdDg (digestSpec c s) vs)
    (hDup : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdDup
      (retSpec [tptr tschar] (tptr tschar) q) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_create_conn_helper_init_proxy)
      (helperSpecA c same q) vs := by
  by_cases hvs : vs = [.Vptr c.dataB c.dataO, .Vptr c.connB c.connO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := entry_wf
  have henvl : IsPtr (Val.loadResult Mptr c.envV) := by rw [loadResult_ptr henv]; exact henv
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_create_conn_helper_init_proxy _ _
    (LocalSt emptyEnv [(_conn, .Vptr c.connB c.connO), (_data, .Vptr c.dataB c.dataO)]
      (Cells c.pm (cellsD1 c (s0 c))))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _conn (.Vptr c.connB c.connO)
              (PTree.set _data (.Vptr c.dataB c.dataO)
                (createUndefTemps f_create_conn_helper_init_proxy.fn_temps)),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_nil _)), hpre.2⟩
    exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
  -- proxy = NULL; socksproxy = NULL; no_proxy = NULL; result = CURLE_OK;
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _proxy _ vnull
    (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _socksproxy _ vnull
    (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _no_proxy _ vnull
    (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _result _
    (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  -- if(conn->bits.proxy_user_passwd) …: 0
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'55 _
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned 2 1 (Integers.Int.repr 0))) (fun le m hp hT hH hag =>
        eval_lv_bit (lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_bits)
          (hcenv ▸ co_bits) (hcenv ▸ off_pup)) (by decide) (by decide) (ldc 0 (cWD c (s0 c)))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
      (triple_skip ge _ _ _))) ?_
  -- if(data->set.str[STRING_PROXY]) … : NULL
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'53 _ vnull (fun le m hp hT hH hag =>
      eval_lv_load (lv_arr (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
        (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc 5 (cProxy c))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_null⟩)
      (triple_skip ge _ _ _))) ?_
  -- if(data->set.str[STRING_PRE_PROXY]) … : NULL
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'51 _ vnull (fun le m hp hT hH hag =>
      eval_lv_load (lv_arr (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
        (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc 6 (cPre c))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_null⟩)
      (triple_skip ge _ _ _))) ?_
  -- if(!data->set.str[STRING_NOPROXY]) … : NULL でない
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'50 _ (.Vptr c.npB c.npO) (fun le m hp hT hH hag =>
      eval_lv_load (lv_arr (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
        (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc 7 (cNo c))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Eunop _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
        (notbool_vptr (cells_weakValid hpn hH hag (c := cNp c) (mem_idx 8 rfl) Nat.one_pos)), rfl⟩)
      (triple_skip ge _ _ _))) ?_
  -- Curl_check_noproxy(conn->host.name, …) は偽 → proxy = detect_proxy(data, conn);
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'48 _ (.Vptr c.npB c.npO)
          (fun le m hp hT hH hag =>
            eval_lv_load (lv_arr (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
              (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc 7 (cNo c))))
        (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
          (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
            boolVal_vptr (cells_weakValid hpn hH hag (c := cNp c) (mem_idx 8 rfl) Nat.one_pos)⟩)
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'49 _ (.Vptr c.npB c.npO)
              (fun le m hp hT hH hag =>
                eval_lv_load (lv_arr (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
                  (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc 7 (cNo c))))
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'8 _ (.Vptr c.npB c.npO)
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl)))))
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'47 _ (.Vptr c.hostB c.hostO)
          (fun le m hp hT hH hag =>
            eval_lv_load (lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_host)
              (hcenv ▸ co_hn) (hcenv ▸ off_name)) rfl (ldc 9 (cDName c))))
        (call_ret ge _ _ _ _ _ _t'9 _ _ emptyEnv _ _ [.Vptr c.hostB c.hostO, .Vptr c.npB c.npO]
          bNo fdNo hNo hfNo htyNo rfl (fun _ _ _ => eval_callee_global rfl hsNo rfl)
          (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.hostB c.hostO))) rfl
            (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.npB c.npO))) rfl
              EvalExprlist.nil)))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
        boolVal_ofBool false tbool m (.inr rfl)⟩)
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (tget vnull)) notbool_null, rfl⟩)
          (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'7 _ (.Vint (Integers.Int.repr 1))
            (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (tget vnull)) notbool_null) rfl)))
        (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (call_ret ge _ _ _ _ _ _t'6 _ _ emptyEnv _ _ [.Vptr c.dataB c.dataO, .Vptr c.connB c.connO]
              bDet fdDet hDet hfDet htyDet rfl (fun _ _ _ => eval_callee_global rfl hsDet rfl)
              (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.dataB c.dataO))) rfl
                (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.connB c.connO))) rfl
                  EvalExprlist.nil)))
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _proxy _ (.Vptr c.pB c.pO)
              (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))))))) ?_
  -- Curl_safefree(no_proxy);
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_once ge _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (call_none ge _ _ _ _ _ emptyEnv _ _ [vnull] bFree fdFree hFree hfFree htyFree rfl
      (fun _ _ _ => eval_callee_global rfl hsFree rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (tget vnull)) rfl EvalExprlist.nil)
      (fun _ h => h) (fun _ _ h => h.2))
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _no_proxy _ vnull
      (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)))) ?_
  -- if(proxy && conn->unix_domain_socket) …: NULL
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO)),
        boolVal_vptr (cells_weakValid hpn hH hag (c := cP c) (mem_idx 13 rfl) Nat.one_pos)⟩)
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'46 _ vnull (fun le m hp hT hH hag =>
          eval_lv_load (lv_f1 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_unix))
            rfl (ldc 16 (cUnix c))))
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'10 _ (.Vint (Integers.Int.repr 0))
          (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
      (triple_skip ge _ _ _))) ?_
  -- if(proxy && (!*proxy || (conn->handler->flags & PROTOPT_NONETWORK))) …: どちらも偽
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO)),
        boolVal_vptr (cells_weakValid hpn hH hag (c := cP c) (mem_idx 13 rfl) Nat.one_pos)⟩)
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'43 _ (.Vint (Integers.Int.sign_ext 8 c.pc))
          (fun le m hp hT hH hag =>
            eval_deref_scalar (tget (.Vptr c.pB c.pO)) rfl (ldc 13 (cP c))))
        (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl,
            by simp [Cop.boolVal, Cop.classifyBool, Val.ofBool, hpc]; rfl⟩)
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'44 _ (.Vptr c.schB c.schO)
                (fun le m hp hT hH hag =>
                  eval_lv_load (lv_f1 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_handler))
                    rfl (ldc 10 (cHdl c))))
              (triple_seq_fwd ge _ _ _ _ _ _ _
                (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'45 _ (.Vint c.flags)
                  (fun le m hp hT hH hag =>
                    eval_lv_load (lv_f1 (tget (.Vptr c.schB c.schO)) (hcenv ▸ co_hdl) (hcenv ▸ off_flags))
                      rfl (ldc 12 (cFlags c))))
                (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'11 _ (.Vint (Integers.Int.repr 0))
                  (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                    (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                      (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _)
                        (EvalExpr.Econst_int _ _) rfl) rfl)
                    (by simp [Cop.semCast, Cop.classifyCast, hfl]; rfl)))))
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'11 _ (.Vint (Integers.Int.repr 0))
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl))))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
      (triple_skip ge _ _ _))) ?_
  -- if(socksproxy && …): socksproxy は NULL
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget vnull), boolVal_null⟩)
      (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'12 _ (.Vint (Integers.Int.repr 0))
        (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
      (triple_skip ge _ _ _))) ?_
  -- if(proxy || socksproxy) { … }
  apply triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO)),
        boolVal_vptr (cells_weakValid hpn hH hag (c := cP c) (mem_idx 13 rfl) Nat.one_pos)⟩)
      (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'19 _ (.Vint (Integers.Int.repr 1))
        (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)))
    ?if19)
  case if19 =>
    refine triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
    -- ptype = conn->http_proxy.proxytype;
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'39 _ (.Vint (Integers.Int.zero_ext 8 c.hpt0)) (fun le m hp hT hH hag =>
        eval_lv_load (lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_http)
          (hcenv ▸ co_pi) (hcenv ▸ off_proxytype)) rfl (ldc 2 (cHptD c (s0 c)))))
      (triple_set_local_fwd ge _ _ emptyEnv _ _ _ptype _ (.Vint (Integers.Int.zero_ext 8 c.hpt0))
        (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
          (EvalExpr.Etempvar _ _ _ (tget (.Vint (Integers.Int.zero_ext 8 c.hpt0)))) rfl))) ?_
    -- if(proxy) { result = parse_proxy(…); <Debian の検査>; Curl_safefree(proxy); if(result) goto out; }
    apply triple_seq_fwd ge _ _ _ _ _ _ _ ?ifproxy
    case ifproxy =>
      refine triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
        (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO)),
          boolVal_vptr (cells_weakValid hpn hH hag (c := cP c) (mem_idx 13 rfl) Nat.one_pos)⟩) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
        (call_set_cells ge _ _ (parseSpec c (s0 c)) _t'13 _ _ emptyEnv _ _ _
          [.Vptr c.dataB c.dataO, .Vptr c.connB c.connO, .Vptr c.pB c.pO, .Vint (Integers.Int.zero_ext 8 c.hpt0)]
          (.Vint (Integers.Int.repr 0)) bParse fdParse (hParse _) hfParse htyParse rfl
          (fun _ _ _ => eval_callee_global rfl hsParse rfl)
          (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.dataB c.dataO))) rfl
            (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.connB c.connO))) rfl
              (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO))) rfl
                (EvalExprlist.cons _ _ _ _ _ _ _
                  (EvalExpr.Etempvar _ _ _ (tget (.Vint (Integers.Int.zero_ext 8 c.hpt0)))) rfl
                  EvalExprlist.nil))))
          (fun _ h => h) (fun _ _ h => h))
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _result _ (.Vint (Integers.Int.repr 0))
          (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
      refine triple_seq_fwd ge _ _ _
        (LocalSt emptyEnv [(_t'15, Val.ofBool same), (_proxy, .Vptr c.pB c.pO), (_socksproxy, vnull),
          (_result, .Vint (Integers.Int.repr 0)), (_conn, .Vptr c.connB c.connO),
          (_data, .Vptr c.dataB c.dataO)] (Cells c.pm (cellsD1 c (sWD c same q (Integers.Int.repr 0)))))
        _ _ _ ?join ?after
      case join =>
        -- t'16 = !result && conn->http_proxy.host.rawalloc;  （真）
        refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (tget (.Vint (Integers.Int.repr 0)))) rfl, rfl⟩)
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'38 _ (.Vptr c.peerB c.peerO)
              (fun le m hp hT hH hag =>
                eval_lv_load (lv_f3 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_http)
                  (hcenv ▸ co_pi) (hcenv ▸ off_pihost) (hcenv ▸ co_hn) (hcenv ▸ off_rawalloc)) rfl
                  (ldc 1 (cHraw c (s1 c)))))
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'16 _ (Val.ofBool true)
              (fun le m hp hT hH hag => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                (cast_vptr_bool (cells_weakValid hpn hH hag (c := cPeer c) (mem_idx 15 rfl) Nat.one_pos))))))
          ?_
        refine triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
        -- t'37 = data->state.envproxy; t'15 = Curl_safecmp(t'37, proxy);
        refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'37 _ (Val.loadResult Mptr c.envV)
            (fun le m hp hT hH hag =>
              eval_lv_load (lv_f2 (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_state)
                (hcenv ▸ co_state) (hcenv ▸ off_envproxy)) rfl (ldc 3 (cEnv1 c (s1 c)))))
          (call_ret ge _ _ _ _ _ _t'15 _ _ emptyEnv _ _
            [Val.loadResult Mptr c.envV, .Vptr c.pB c.pO] bCmp fdCmp hCmp hfCmp htyCmp rfl
            (fun _ _ _ => eval_callee_global rfl hsCmp rfl)
            (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (tget (Val.loadResult Mptr c.envV))) (cast_ptr henvl _ _ m)
              (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO))) rfl
                EvalExprlist.nil)))) ?_
        refine triple_pre_sub ge _ _ emptyEnv _ [(_t'15, Val.ofBool same), (_proxy, .Vptr c.pB c.pO),
          (_socksproxy, vnull), (_result, .Vint (Integers.Int.repr 0)), (_conn, .Vptr c.connB c.connO),
          (_data, .Vptr c.dataB c.dataO)] _ _ _ ?sub ?_
        case sub =>
          intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> temps_get
        refine triple_if_local ge _ _ emptyEnv _ _ _ (!same) _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (tget (Val.ofBool same))) (Case5C.notbool_ofBool same m),
            Case5C.boolVal_ofBool_tint _ m⟩) ?_
        cases same
        case true =>
          exact triple_skip ge _ _ _
        case false =>
          apply triple_post_sub ge _ _ _ emptyEnv _ _ _ _ ?sub2 ?main
          case main =>
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (call_void_cells ge _ _ (digestSpec c (s1 c)) _ _ emptyEnv _ _ _
                [.Vptr c.dataB (f2 c.dataO 568 16)]
                bDg fdDg (hDg _) hfDg htyDg rfl (fun _ _ _ => eval_callee_global rfl hsDg rfl)
                (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                  (EvalExpr.Eaddrof _ _ _ _ (lv_f2 (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy)
                    (hcenv ▸ off_state) (hcenv ▸ co_state) (hcenv ▸ off_proxydigest))) rfl
                  EvalExprlist.nil)
                (fun _ h => ⟨rfl, h⟩) (fun _ _ h => h)) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'36 _ (Val.loadResult Mptr c.envV)
                (fun le m hp hT hH hag =>
                  eval_lv_load (lv_f2 (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_state)
                    (hcenv ▸ co_state) (hcenv ▸ off_envproxy)) rfl (ldc 3 (cEnv1 c (s2 c)))))
              (call_none ge _ _ _ _ _ emptyEnv _ _ [Val.loadResult Mptr c.envV] bFree fdFree hFree hfFree
                htyFree rfl (fun _ _ _ => eval_callee_global rfl hsFree rfl)
                (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                  (EvalExpr.Etempvar _ _ _ (tget (Val.loadResult Mptr c.envV))) (cast_ptr henvl _ _ m)
                  EvalExprlist.nil)
                (fun _ h => h) (fun _ _ h => h.2))) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (call_ret ge _ _ _ _ _ _t'14 _ _ emptyEnv _ _ [.Vptr c.pB c.pO] bDup fdDup hDup hfDup htyDup
                rfl (fun _ _ _ => eval_callee_global rfl hsDup rfl)
                (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                  (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO))) rfl EvalExprlist.nil)) ?_
            exact assign_at ge _ _ emptyEnv _ c.pm _ (cellsD1 c (sWD c false q (Integers.Int.repr 0)))
              (List.take 3 (cellsD1 c (s2 c))) (List.drop 4 (cellsD1 c (s2 c))) (cEnv1 c (s2 c))
              _ _ (f2 c.dataO 568 0) q rfl rfl hpw rfl rfl
              (fun le m hp hT _ _ => lv_f2 (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy)
                (hcenv ▸ off_state) (hcenv ▸ co_state) (hcenv ▸ off_envproxy))
              (fun le m hp hT _ _ => ⟨q, EvalExpr.Etempvar _ _ _ (tget q), cast_ptr hq _ _ m⟩)
          case sub2 =>
            intro p hp
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> temps_get
      case after =>
        -- Curl_safefree(proxy); if(result) goto out;
        refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_once ge _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
          (call_none ge _ _ _ _ _ emptyEnv _ _ [.Vptr c.pB c.pO] bFree fdFree hFree hfFree htyFree rfl
            (fun _ _ _ => eval_callee_global rfl hsFree rfl)
            (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO))) rfl EvalExprlist.nil)
            (fun _ h => h) (fun _ _ h => h.2))
          (triple_set_local_fwd ge _ _ emptyEnv _ _ _proxy _ vnull
            (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)))) ?_
        exact triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget (.Vint (Integers.Int.repr 0))), rfl⟩)
          (triple_skip ge _ _ _)
    -- if(socksproxy) …: NULL
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget vnull), boolVal_null⟩)
      (triple_skip ge _ _ _)) ?_
    -- if(conn->http_proxy.host.rawalloc) { …; conn->bits.httpproxy = TRUE; }
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'30 _
      (.Vptr c.peerB c.peerO) (fun le m hp hT hH hag =>
        eval_lv_load (lv_f3 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_http)
          (hcenv ▸ co_pi) (hcenv ▸ off_pihost) (hcenv ▸ co_hn) (hcenv ▸ off_rawalloc)) rfl
          (ldc 1 (cHraw c (sWD c same q (Integers.Int.repr 0))))))
    (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
        boolVal_vptr (cells_weakValid hpn hH hag (c := cPeer c) (mem_idx 15 rfl) Nat.one_pos)⟩)
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'31 _ (.Vptr c.schB c.schO)
            (fun le m hp hT hH hag =>
              eval_lv_load (lv_f1 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_handler))
                rfl (ldc 10 (cHdl c))))
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'32 _ (.Vlong c.proto)
              (fun le m hp hT hH hag =>
                eval_lv_load (lv_f1 (tget (.Vptr c.schB c.schO)) (hcenv ▸ co_hdl) (hcenv ▸ off_protocol))
                  rfl (ldc 11 (cProto c))))
            (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
              (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
                (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget (.Vlong c.proto))) eval_fam rfl)
                notbool_long, by rw [hproto]; rfl⟩)
              (triple_skip ge _ _ _))))
        (assign_bits_at ge _ _ emptyEnv _ c.pm (cellsD1 c (sWD c same q (Integers.Int.repr 0)))
          (cellsD1 c (sWD c same q dw1)) [] (List.drop 1 (cellsD1 c (sWD c same q (Integers.Int.repr 0))))
          (cWD c (sWD c same q (Integers.Int.repr 0))) (Integers.Int.repr 0) _ _ (f2 c.connO 96 0) 0
          (Integers.Int.repr 1) rfl rfl hpw hpr rfl (by decide) (by decide) ⟨rfl, rfl⟩ rfl
          (fun le m hp hT _ _ => lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_bits)
            (hcenv ▸ co_bits) (hcenv ▸ off_httpproxy))
          (fun _ _ _ _ _ _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩))))) ?_
    -- if(conn->socks_proxy.host.rawalloc) … else conn->bits.socksproxy = FALSE;
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'24 _ vnull
      (fun le m hp hT hH hag =>
        eval_lv_load (lv_f3 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_socks)
          (hcenv ▸ co_pi) (hcenv ▸ off_pihost) (hcenv ▸ co_hn) (hcenv ▸ off_rawalloc)) rfl
          (ldc 14 (cSraw c)))) ?_
    exact triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_null⟩)
      (assign_bits_at ge _ _ emptyEnv _ c.pm (cellsD1 c (sWD c same q dw1))
        (cellsD1 c (sWD c same q dw2)) [] (List.drop 1 (cellsD1 c (sWD c same q dw1)))
        (cWD c (sWD c same q dw1)) dw1 _ _ (f2 c.connO 96 0) 1 (Integers.Int.repr 0)
        rfl rfl hpw hpr rfl (by decide) (by decide) ⟨rfl, rfl⟩ rfl
        (fun le m hp hT _ _ => lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_bits)
          (hcenv ▸ co_bits) (hcenv ▸ off_socksproxy))
        (fun _ _ _ _ _ _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩))
  -- conn->bits.proxy = conn->bits.httpproxy || conn->bits.socksproxy;
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'22 _
        (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 dw2)) (fun le m hp hT hH hag =>
          eval_lv_bit (lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_bits)
            (hcenv ▸ co_bits) (hcenv ▸ off_httpproxy)) (by decide) (by decide)
            (ldc 0 (cWD c (sWD c same q dw2)))))
      (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'20 _ (.Vint (Integers.Int.repr 1))
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))))
    (assign_bits_at ge _ _ emptyEnv _ c.pm (cellsD1 c (sWD c same q dw2))
      (cellsD1 c (sWD c same q dwFin)) [] (List.drop 1 (cellsD1 c (sWD c same q dw2)))
      (cWD c (sWD c same q dw2)) dw2 _ _ (f2 c.connO 96 0) 4 (Integers.Int.repr 1)
      rfl rfl hpw hpr rfl (by decide) (by decide) ⟨rfl, rfl⟩ rfl
      (fun le m hp hT _ _ => lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_bits)
        (hcenv ▸ co_bits) (hcenv ▸ off_proxyb))
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩))) ?_
  -- if(!conn->bits.proxy) …: 立っているので通らない
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'21 _
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned 4 1 dwFin)) (fun le m hp hT hH hag =>
        eval_lv_bit (lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_bits)
          (hcenv ▸ co_bits) (hcenv ▸ off_proxyb)) (by decide) (by decide)
          (ldc 0 (cWD c (sWD c same q dwFin)))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl, rfl⟩)
      (triple_skip ge _ _ _))) ?_
  -- out: free(socksproxy); free(proxy); return result;  （どちらも NULL）
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_label ge _ _ _ _ _ _
    (call_none ge _ _ _ _ _ emptyEnv _ _ [vnull] bFree fdFree hFree hfFree htyFree rfl
      (fun _ _ _ => eval_callee_global rfl hsFree rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (tget vnull)) rfl EvalExprlist.nil)
      (fun _ h => h) (fun _ _ h => h.2))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (call_none ge _ _ _ _ _ emptyEnv _ _ [vnull] bFree fdFree hFree hfFree htyFree rfl
      (fun _ _ _ => eval_callee_global rfl hsFree rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (tget vnull)) rfl EvalExprlist.nil)
      (fun _ h => h) (fun _ _ h => h.2)) ?_
  exact triple_return_local ge _ _ _ _ _ _ (.Vint (Integers.Int.repr 0)) (.Vint (Integers.Int.repr 0))
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (tget (.Vint (Integers.Int.repr 0))))
    (fun _ => rfl) (fun hp hH => ⟨rfl, hH⟩)

end Deb2026_8927.D1
