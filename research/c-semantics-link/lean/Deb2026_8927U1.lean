/-
CVE-2026-8927（`research/backport-proof-debian/cases/CVE-2026-8927.md`）: 上流の修正後（U1、curl 5c225384b8）の
`url_set_conn_proxies`。

場面 S（cases/CVE-2026-8927.md）の上で、関数は CURLE_OK を返し、戻った時点の所有は `cellsU1 c (sFin c same q)`
（`same` は `Curl_safecmp` の戻り値、`q` は `curlx_strdup` の戻り値）であることを示す（`setproxies_after`）。
`sFin` は `same` が偽なら `proxydigest.nonce` を NULL にする。
-/
import Deb2026_8927GenU1
import Deb2026_8927Cells
open CC CC.Sep CC.HProp
open Deb2026_8927_u1
open Case4C (call_none IsPtr loadResult_ptr cast_ptr)

set_option maxRecDepth 20000

namespace Deb2026_8927

/-! ## 読み書きするメモリ（上流の2版で共通） -/

/-- 場面 S で関数が読むメモリの置き場所と、変わらない値。 -/
structure Ctx where
  pm : Permission
  dataB : Block
  dataO : Integers.Ptrofs
  connB : Block
  connO : Integers.Ptrofs
  npB : Block               -- data->set.str[STRING_NOPROXY]（NULL でない）
  npO : Integers.Ptrofs
  np0 : Integers.Int        -- その先頭の1バイト（ポインタが有効であることを言うためだけに所有する）
  orgB : Block              -- conn->origin
  orgO : Integers.Ptrofs
  hostB : Block             -- conn->origin->hostname
  hostO : Integers.Ptrofs
  schB : Block              -- conn->scheme
  schO : Integers.Ptrofs
  proto : Integers.Int64    -- conn->scheme->protocol
  flags : Integers.Int      -- conn->scheme->flags
  pB : Block                -- url_detect_proxy が返す文字列
  pO : Integers.Ptrofs
  pc : Integers.Int         -- その先頭の1バイト
  peerB : Block             -- parse_proxy が conn->http_proxy.peer に書く値
  peerO : Integers.Ptrofs
  peer0 : Integers.Int      -- その先頭の1バイト（有効なポインタであることを言うため）
  hpeer0 : Val              -- conn->http_proxy.peer の元の値
  hpt0 : Integers.Int       -- conn->http_proxy.proxytype の元の値
  envV : Val                -- data->state.envproxy の元の値（U1 だけが読む）
  nonce0 : Val              -- data->state.proxydigest.nonce の元の値

/-- 関数の実行で変わる値。 -/
structure St where
  w : Integers.Int          -- conn->bits（httpproxy・socksproxy・tunnel_proxy・proxy の 32 bit の単位）
  hpeer : Val
  hpt : Integers.Int
  env : Val
  nonce : Val

def vnull : Val := .Vlong (Integers.Int64.repr 0)

def u (o : Integers.Ptrofs) : Z := Integers.Ptrofs.unsigned o
def f1 (o : Integers.Ptrofs) (d : Z) : Integers.Ptrofs := Integers.Ptrofs.add o (Integers.Ptrofs.repr d)
def f2 (o : Integers.Ptrofs) (d1 d2 : Z) : Integers.Ptrofs := f1 (f1 o d1) d2

/-- `data->set.str[k]` の番地（`Efield`・`Oadd` が計算するのと同じ式）。 -/
def strAt (o : Integers.Ptrofs) (k : Z) : Integers.Ptrofs :=
  Integers.Ptrofs.add (f2 o 0 0)
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr 8) (Cop.ptrofsOfInt .Signed (Integers.Int.repr k)))

/-! ## セル（並びの先頭5つが書き換わる） -/

def cW (c : Ctx) (s : St) : Cell := ⟨.Mint32, c.connB, u (f2 c.connO 40 0), .Vint s.w⟩
def cHpeer (c : Ctx) (s : St) : Cell := ⟨Mptr, c.connB, u (f2 c.connO 24 0), s.hpeer⟩
def cHpt (c : Ctx) (s : St) : Cell := ⟨.Mint8unsigned, c.connB, u (f2 c.connO 24 8), .Vint s.hpt⟩
def cProxy (c : Ctx) : Cell := ⟨Mptr, c.dataB, u (strAt c.dataO 38), vnull⟩
def cPre (c : Ctx) : Cell := ⟨Mptr, c.dataB, u (strAt c.dataO 39), vnull⟩
def cNo (c : Ctx) : Cell := ⟨Mptr, c.dataB, u (strAt c.dataO 50), .Vptr c.npB c.npO⟩
def cNp (c : Ctx) : Cell := ⟨.Mint8signed, c.npB, u c.npO, .Vint c.np0⟩
def cOrg (c : Ctx) : Cell := ⟨Mptr, c.connB, u (f1 c.connO 0), .Vptr c.orgB c.orgO⟩
def cHost (c : Ctx) : Cell := ⟨Mptr, c.orgB, u (f1 c.orgO 0), .Vptr c.hostB c.hostO⟩
def cSch (c : Ctx) : Cell := ⟨Mptr, c.connB, u (f1 c.connO 48), .Vptr c.schB c.schO⟩
def cProto (c : Ctx) : Cell := ⟨.Mint64, c.schB, u (f1 c.schO 0), .Vlong c.proto⟩
def cFlags (c : Ctx) : Cell := ⟨.Mint32, c.schB, u (f1 c.schO 8), .Vint c.flags⟩
def cP (c : Ctx) : Cell := ⟨.Mint8signed, c.pB, u c.pO, .Vint c.pc⟩
def cSpeer (c : Ctx) : Cell := ⟨Mptr, c.connB, u (f2 c.connO 8 0), vnull⟩
def cPeer (c : Ctx) : Cell := ⟨.Mint8signed, c.peerB, u c.peerO, .Vint c.peer0⟩

/-- 変わらないセル（上流の2版で共通）。 -/
abbrev fixU (c : Ctx) : List Cell :=
  [cProxy c, cPre c, cNo c, cNp c, cOrg c, cHost c, cSch c, cProto c, cFlags c, cP c, cSpeer c, cPeer c]

/-! ## U1 の並び -/

def cEnv1 (c : Ctx) (s : St) : Cell := ⟨Mptr, c.dataB, u (f2 c.dataO 568 0), s.env⟩
def cNonce1 (c : Ctx) (s : St) : Cell := ⟨Mptr, c.dataB, u (f1 (f2 c.dataO 568 16) 0), s.nonce⟩

abbrev cellsU1 (c : Ctx) (s : St) : List Cell :=
  cW c s :: cHpeer c s :: cHpt c s :: cEnv1 c s :: cNonce1 c s :: fixU c

def s0 (c : Ctx) : St := ⟨Integers.Int.repr 0, c.hpeer0, c.hpt0, c.envV, c.nonce0⟩

/-- `parse_proxy` の後の状態。 -/
def s1 (c : Ctx) : St := ⟨Integers.Int.repr 0, .Vptr c.peerB c.peerO, Integers.Int.repr 0, c.envV, c.nonce0⟩
/-- `Curl_auth_digest_cleanup` の後の状態（U1 で `Curl_safecmp` が偽のとき）。 -/
def s2 (c : Ctx) : St := ⟨Integers.Int.repr 0, .Vptr c.peerB c.peerO, Integers.Int.repr 0, c.envV, vnull⟩

/-- `conn->bits` の最後の値: socksproxy = 0、httpproxy = 1、proxy = 1 の順に書く。 -/
def wFin : Integers.Int :=
  Integers.Int.bitfield_insert (Cop.firstBit .I32 3 1).toNat 1
    (Integers.Int.bitfield_insert (Cop.firstBit .I32 0 1).toNat 1
      (Integers.Int.bitfield_insert (Cop.firstBit .I32 1 1).toNat 1 (Integers.Int.repr 0)
        (Integers.Int.repr 0)) (Integers.Int.repr 1)) (Integers.Int.repr 1)

def sFin1 (c : Ctx) (same : Bool) (q : Val) : St :=
  ⟨wFin, .Vptr c.peerB c.peerO, Integers.Int.repr 0, cond same c.envV q, cond same c.nonce0 vnull⟩

end Deb2026_8927

namespace Deb2026_8927.U1
open Deb2026_8927

/-! ## 構造体のレイアウト -/

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
theorem co_bits : prog.prog_comp_env.get _ConnectBits = some (coOf _ConnectBits) := rfl
theorem co_peer : prog.prog_comp_env.get _Curl_peer = some (coOf _Curl_peer) := rfl
theorem co_sch : prog.prog_comp_env.get _Curl_scheme = some (coOf _Curl_scheme) := rfl

theorem off_set : fieldOffset prog.prog_comp_env _set (coOf _Curl_easy).co_members = .OK (0, .Full) := by decide
theorem off_state : fieldOffset prog.prog_comp_env _state (coOf _Curl_easy).co_members = .OK (568, .Full) := by decide
theorem off_str : fieldOffset prog.prog_comp_env _str (coOf _UserDefined).co_members = .OK (0, .Full) := by decide
theorem off_envproxy : fieldOffset prog.prog_comp_env _envproxy (coOf _UrlState).co_members = .OK (0, .Full) := by decide
theorem off_proxydigest : fieldOffset prog.prog_comp_env _proxydigest (coOf _UrlState).co_members = .OK (16, .Full) := by decide
theorem off_origin : fieldOffset prog.prog_comp_env _origin (coOf _connectdata).co_members = .OK (0, .Full) := by decide
theorem off_socks : fieldOffset prog.prog_comp_env _socks_proxy (coOf _connectdata).co_members = .OK (8, .Full) := by decide
theorem off_http : fieldOffset prog.prog_comp_env _http_proxy (coOf _connectdata).co_members = .OK (24, .Full) := by decide
theorem off_bits : fieldOffset prog.prog_comp_env _bits (coOf _connectdata).co_members = .OK (40, .Full) := by decide
theorem off_scheme : fieldOffset prog.prog_comp_env _scheme (coOf _connectdata).co_members = .OK (48, .Full) := by decide
theorem off_peer : fieldOffset prog.prog_comp_env _peer (coOf _proxy_info).co_members = .OK (0, .Full) := by decide
theorem off_proxytype : fieldOffset prog.prog_comp_env _proxytype (coOf _proxy_info).co_members = .OK (8, .Full) := by decide
theorem off_hostname : fieldOffset prog.prog_comp_env _hostname (coOf _Curl_peer).co_members = .OK (0, .Full) := by decide
theorem off_protocol : fieldOffset prog.prog_comp_env _protocol (coOf _Curl_scheme).co_members = .OK (0, .Full) := by decide
theorem off_flags : fieldOffset prog.prog_comp_env _flags (coOf _Curl_scheme).co_members = .OK (8, .Full) := by decide
theorem off_httpproxy : fieldOffset prog.prog_comp_env _httpproxy (coOf _ConnectBits).co_members = .OK (0, .Bits .I32 .Unsigned 0 1) := by decide
theorem off_socksproxy : fieldOffset prog.prog_comp_env _socksproxy (coOf _ConnectBits).co_members = .OK (0, .Bits .I32 .Unsigned 1 1) := by decide
theorem off_proxyb : fieldOffset prog.prog_comp_env _proxy (coOf _ConnectBits).co_members = .OK (0, .Bits .I32 .Unsigned 3 1) := by decide

/-! ## 式の評価（この関数に出る形） -/

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

/-- 関数の仕様（場面 S）。戻り値は CURLE_OK、所有は `sFin1`。 -/
def setSpecA (c : Ctx) (same : Bool) (q : Val) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _connectdata noattr)]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dataB c.dataO, .Vptr c.connB c.connO]
    ∧ Cells c.pm (cellsU1 c (s0 c)) hp
  post := fun v hp => v = .Vint (Integers.Int.repr 0) ∧ Cells c.pm (cellsU1 c (sFin1 c same q)) hp
  measure := fun _ => 0

/-- `parse_proxy(data, proxy, FALSE, &conn->http_proxy)`: CURLE_OK を返し、`http_proxy.peer` を
    `peerB`・`peerO` に、`proxytype` を CURLPROXY_HTTP（0）にする。ほかのセルは変えない。 -/
def parseSpec (c : Ctx) (s : St) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr tschar, tbool,
             tptr (Ty.Tstruct _proxy_info noattr)]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr c.dataB c.dataO, .Vptr c.pB c.pO, .Vint (Integers.Int.repr 0),
             .Vptr c.connB (f1 c.connO 24)] ∧ Cells c.pm (cellsU1 c s) hp
  post := fun v hp => v = .Vint (Integers.Int.repr 0) ∧
    Cells c.pm (cellsU1 c { s with hpeer := .Vptr c.peerB c.peerO, hpt := Integers.Int.repr 0 }) hp
  measure := fun _ => 0

/-- `Curl_auth_digest_cleanup(&data->state.proxydigest)`: `proxydigest.nonce` を NULL にする。 -/
def digestSpec (c : Ctx) (s : St) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _digestdata noattr)]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dataB (f2 c.dataO 568 16)] ∧ Cells c.pm (cellsU1 c s) hp
  post := fun _ hp => Cells c.pm (cellsU1 c { s with nonce := vnull }) hp
  measure := fun _ => 0

/-- `if(!Curl_safecmp(...))` の後の状態。 -/
def sMid (c : Ctx) (same : Bool) (q : Val) : St :=
  ⟨Integers.Int.repr 0, .Vptr c.peerB c.peerO, Integers.Int.repr 0, cond same c.envV q,
   cond same c.nonce0 vnull⟩

def w1 : Integers.Int :=
  Integers.Int.bitfield_insert (Cop.firstBit .I32 1 1).toNat 1 (Integers.Int.repr 0) (Integers.Int.repr 0)
def w2 : Integers.Int :=
  Integers.Int.bitfield_insert (Cop.firstBit .I32 0 1).toNat 1 w1 (Integers.Int.repr 1)

/-- `sMid` の `conn->bits` だけを `w` にしたもの。 -/
def sW (c : Ctx) (same : Bool) (q : Val) (w : Integers.Int) : St :=
  ⟨w, .Vptr c.peerB c.peerO, Integers.Int.repr 0, cond same c.envV q, cond same c.nonce0 vnull⟩

theorem entry_wf :
    listNorepet (varNames f_url_set_conn_proxies.fn_vars)
    ∧ listNorepet (varNames f_url_set_conn_proxies.fn_params)
    ∧ listDisjoint (varNames f_url_set_conn_proxies.fn_params)
        (varNames f_url_set_conn_proxies.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option hygiene false in
/-- 並びの中のセル `X` を読む（`hpr`・`hH`・`hag` は文脈の名前）。 -/
macro "ldc " i:num x:term:max : term => `(ld hpr hH hag (x := $x) (mem_idx $i rfl) rfl)

set_option hygiene false in
/-- 一時変数の値を読む（値を先に決めて、`temps_get` に渡す）。 -/
macro "tget " v:term:max : term => `(TempsHold.get hT (v := $v) (by temps_get))

set_option maxHeartbeats 4000000 in
theorem setproxies_after (ge : CGenv) (c : Ctx) (same : Bool) (q : Val)
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
    (hsDet : Genv.findSymbol ge.genv_genv _url_detect_proxy = some bDet)
    (hsFree : Genv.findSymbol ge.genv_genv _curlx_free = some bFree)
    (hsParse : Genv.findSymbol ge.genv_genv _parse_proxy = some bParse)
    (hsCmp : Genv.findSymbol ge.genv_genv _Curl_safecmp = some bCmp)
    (hsDg : Genv.findSymbol ge.genv_genv _Curl_auth_digest_cleanup = some bDg)
    (hsDup : Genv.findSymbol ge.genv_genv _curlx_strdup = some bDup)
    (hfNo : FuncPtr ge bNo fdNo) (hfDet : FuncPtr ge bDet fdDet) (hfFree : FuncPtr ge bFree fdFree)
    (hfParse : FuncPtr ge bParse fdParse) (hfCmp : FuncPtr ge bCmp fdCmp)
    (hfDg : FuncPtr ge bDg fdDg) (hfDup : FuncPtr ge bDup fdDup)
    (htyNo : typeOfFundef fdNo = .Tfunction [tptr tschar, tptr tschar] tbool cc_default)
    (htyDet : typeOfFundef fdDet = .Tfunction [tptr (Ty.Tstruct _Curl_easy noattr),
      tptr (Ty.Tstruct _connectdata noattr)] (tptr tschar) cc_default)
    (htyFree : typeOfFundef fdFree = .Tfunction [tptr tvoid] tvoid cc_default)
    (htyParse : typeOfFundef fdParse = .Tfunction [tptr (Ty.Tstruct _Curl_easy noattr), tptr tschar,
      tbool, tptr (Ty.Tstruct _proxy_info noattr)] tint cc_default)
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
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_url_set_conn_proxies) (setSpecA c same q) vs := by
  by_cases hvs : vs = [.Vptr c.dataB c.dataO, .Vptr c.connB c.connO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := entry_wf
  have henvl : IsPtr (Val.loadResult Mptr c.envV) := by rw [loadResult_ptr henv]; exact henv
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_url_set_conn_proxies _ _
    (LocalSt emptyEnv [(_conn, .Vptr c.connB c.connO), (_data, .Vptr c.dataB c.dataO)]
      (Cells c.pm (cellsU1 c (s0 c))))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _conn (.Vptr c.connB c.connO)
              (PTree.set _data (.Vptr c.dataB c.dataO)
                (createUndefTemps f_url_set_conn_proxies.fn_temps)),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_nil _)), hpre.2⟩
    exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
  -- proxy = NULL; pre_proxy = NULL; no_proxy = NULL; result = CURLE_OK;
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _proxy _ vnull
    (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _pre_proxy _ vnull
    (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _no_proxy _ vnull
    (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _result _
    (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  -- if(data->set.str[STRING_PROXY]) … : NULL
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'46 _ vnull (fun le m hp hT hH hag =>
      eval_lv_load (lv_arr (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
        (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc 5 (cProxy c))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_null⟩)
      (triple_skip ge _ _ _))) ?_
  -- if(data->set.str[STRING_PRE_PROXY]) … : NULL
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'44 _ vnull (fun le m hp hT hH hag =>
      eval_lv_load (lv_arr (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
        (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc 6 (cPre c))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_null⟩)
      (triple_skip ge _ _ _))) ?_
  -- if(!data->set.str[STRING_NOPROXY]) … : NULL でない
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'43 _ (.Vptr c.npB c.npO) (fun le m hp hT hH hag =>
      eval_lv_load (lv_arr (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
        (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc 7 (cNo c))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Eunop _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
        (notbool_vptr (cells_weakValid hpn hH hag (c := cNp c) (mem_idx 8 rfl) Nat.one_pos)), rfl⟩)
      (triple_skip ge _ _ _))) ?_
  -- t'7 = data->set.str[STRING_NOPROXY]; t'8 = Curl_check_noproxy(conn->origin->hostname, t'7);
  -- if(t'8) … else { t'6 = !proxy && !pre_proxy; if(t'6) proxy = url_detect_proxy(data, conn); }
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'41 _ (.Vptr c.npB c.npO)
          (fun le m hp hT hH hag =>
            eval_lv_load (lv_arr (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
              (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc 7 (cNo c))))
        (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
          (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
            boolVal_vptr (cells_weakValid hpn hH hag (c := cNp c) (mem_idx 8 rfl) Nat.one_pos)⟩)
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'42 _ (.Vptr c.npB c.npO)
              (fun le m hp hT hH hag =>
                eval_lv_load (lv_arr (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
                  (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc 7 (cNo c))))
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'7 _ (.Vptr c.npB c.npO)
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl)))))
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'39 _ (.Vptr c.orgB c.orgO)
          (fun le m hp hT hH hag =>
            eval_lv_load (lv_f1 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_origin)) rfl
              (ldc 9 (cOrg c))))
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'40 _ (.Vptr c.hostB c.hostO)
            (fun le m hp hT hH hag =>
              eval_lv_load (lv_f1 (tget (.Vptr c.orgB c.orgO)) (hcenv ▸ co_peer) (hcenv ▸ off_hostname))
                rfl (ldc 10 (cHost c))))
          (call_ret ge _ _ _ _ _ _t'8 _ _ emptyEnv _ _ [.Vptr c.hostB c.hostO, .Vptr c.npB c.npO]
            bNo fdNo hNo hfNo htyNo rfl (fun _ _ _ => eval_callee_global rfl hsNo rfl)
            (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.hostB c.hostO))) rfl
              (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.npB c.npO))) rfl
                EvalExprlist.nil))))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
        boolVal_ofBool false tbool m (.inr rfl)⟩)
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) notbool_null, rfl⟩)
          (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'6 _ (.Vint (Integers.Int.repr 1))
            (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) notbool_null) rfl)))
        (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (call_ret ge _ _ _ _ _ _t'5 _ _ emptyEnv _ _ [.Vptr c.dataB c.dataO, .Vptr c.connB c.connO]
              bDet fdDet hDet hfDet htyDet rfl (fun _ _ _ => eval_callee_global rfl hsDet rfl)
              (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.dataB c.dataO))) rfl
                (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.connB c.connO))) rfl
                  EvalExprlist.nil)))
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _proxy _ (.Vptr c.pB c.pO)
              (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))))))) ?_
  -- curlx_safefree(no_proxy);
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_once ge _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (call_none ge _ _ _ _ _ emptyEnv _ _ [vnull] bFree fdFree hFree hfFree htyFree rfl
      (fun _ _ _ => eval_callee_global rfl hsFree rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (tget vnull)) rfl EvalExprlist.nil)
      (fun _ h => h) (fun _ _ h => h.2))
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _no_proxy _ vnull
      (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)))) ?_
  -- if(proxy && (!*proxy || (conn->scheme->flags & PROTOPT_NONETWORK))) …: どちらも偽
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
        boolVal_vptr (cells_weakValid hpn hH hag (c := cP c) (mem_idx 14 rfl) Nat.one_pos)⟩)
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'36 _ (.Vint (Integers.Int.sign_ext 8 c.pc))
          (fun le m hp hT hH hag =>
            eval_deref_scalar (tget (.Vptr c.pB c.pO)) rfl (ldc 14 (cP c))))
        (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl,
            by simp [Cop.boolVal, Cop.classifyBool, Val.ofBool, hpc]; rfl⟩)
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'37 _ (.Vptr c.schB c.schO)
                (fun le m hp hT hH hag =>
                  eval_lv_load (lv_f1 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_scheme))
                    rfl (ldc 11 (cSch c))))
              (triple_seq_fwd ge _ _ _ _ _ _ _
                (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'38 _ (.Vint c.flags)
                  (fun le m hp hT hH hag =>
                    eval_lv_load (lv_f1 (tget (.Vptr c.schB c.schO)) (hcenv ▸ co_sch) (hcenv ▸ off_flags))
                      rfl (ldc 13 (cFlags c))))
                (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'9 _ (.Vint (Integers.Int.repr 0))
                  (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                    (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                      (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _)
                        (EvalExpr.Econst_int _ _) rfl) rfl)
                    (by simp [Cop.semCast, Cop.classifyCast, hfl]; rfl)))))
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'9 _ (.Vint (Integers.Int.repr 0))
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl))))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
      (triple_skip ge _ _ _))) ?_
  -- if(pre_proxy && …): pre_proxy は NULL
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget vnull), boolVal_null⟩)
      (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'10 _ (.Vint (Integers.Int.repr 0))
        (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
      (triple_skip ge _ _ _))) ?_
  -- if(proxy || pre_proxy) { … }
  apply triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO)),
        boolVal_vptr (cells_weakValid hpn hH hag (c := cP c) (mem_idx 14 rfl) Nat.one_pos)⟩)
      (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'16 _ (.Vint (Integers.Int.repr 1))
        (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)))
    ?if16)
  case if16 =>
    refine triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
    -- if(pre_proxy) …: NULL
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget vnull), boolVal_null⟩)
      (triple_skip ge _ _ _)) ?_
    -- if(proxy) { result = parse_proxy(…); if(result) goto out; switch(proxytype) … }
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO)),
        boolVal_vptr (cells_weakValid hpn hH hag (c := cP c) (mem_idx 14 rfl) Nat.one_pos)⟩)
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (call_set_cells ge _ _ (parseSpec c (s0 c)) _t'12 _ _ emptyEnv _ _ _
            [.Vptr c.dataB c.dataO, .Vptr c.pB c.pO, .Vint (Integers.Int.repr 0),
             .Vptr c.connB (f1 c.connO 24)] (.Vint (Integers.Int.repr 0)) bParse fdParse
            (hParse _) hfParse htyParse rfl (fun _ _ _ => eval_callee_global rfl hsParse rfl)
            (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.dataB c.dataO))) rfl
              (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO))) rfl
                (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl
                  (EvalExprlist.cons _ _ _ _ _ _ _
                    (EvalExpr.Eaddrof _ _ _ _ (lv_f1 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn)
                      (hcenv ▸ off_http))) rfl EvalExprlist.nil))))
            (fun _ h => ⟨rfl, h⟩) (fun _ _ h => h))
          (triple_set_local_fwd ge _ _ emptyEnv _ _ _result _ (.Vint (Integers.Int.repr 0))
            (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))))
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
            (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
            (triple_skip ge _ _ _))
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'31 _
              (.Vint (Integers.Int.zero_ext 8 (Integers.Int.repr 0)))
              (fun le m hp hT hH hag =>
                eval_lv_load (lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_http)
                  (hcenv ▸ co_pi) (hcenv ▸ off_proxytype)) rfl
                  (ldc 2 (cHpt c (s1 c)))))
            (triple_switch_const ge _ _ _ _ _ _ 0
              (break_seq ge _ _ _ _ _ (fun _ _ _ x => x))
              (fun e le hp m hP _ => ⟨_, EvalExpr.Etempvar _ _ _ (hP.2.1.get (by temps_get)), by decide⟩)))))) ?_
    -- t'23 = conn->http_proxy.peer; if(t'23) { … }
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'23 _
      (.Vptr c.peerB c.peerO) (fun le m hp hT hH hag =>
        eval_lv_load (lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_http)
          (hcenv ▸ co_pi) (hcenv ▸ off_peer)) rfl
          (ldc 1 (cHpeer c (s1 c)))))
      ?_
    refine triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
        boolVal_vptr (cells_weakValid hpn hH hag (c := cPeer c) (mem_idx 16 rfl) Nat.one_pos)⟩) ?_
    refine triple_seq_fwd ge _ _ _
      (LocalSt emptyEnv [(_t'14, Val.ofBool same), (_proxy, .Vptr c.pB c.pO), (_pre_proxy, vnull),
        (_result, .Vint (Integers.Int.repr 0)), (_conn, .Vptr c.connB c.connO),
        (_data, .Vptr c.dataB c.dataO)] (Cells c.pm (cellsU1 c (sMid c same q)))) _ _ _ ?join ?after
    case join =>
      -- t'30 = data->state.envproxy; t'14 = Curl_safecmp(t'30, proxy);
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'30 _ (Val.loadResult Mptr c.envV)
          (fun le m hp hT hH hag =>
            eval_lv_load (lv_f2 (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_state)
              (hcenv ▸ co_state) (hcenv ▸ off_envproxy)) rfl
              (ldc 3 (cEnv1 c (s1 c)))))
        (call_ret ge _ _ _ _ _ _t'14 _ _ emptyEnv _ _
          [Val.loadResult Mptr c.envV, .Vptr c.pB c.pO] bCmp fdCmp hCmp hfCmp htyCmp rfl
          (fun _ _ _ => eval_callee_global rfl hsCmp rfl)
          (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (tget (Val.loadResult Mptr c.envV))) (cast_ptr henvl _ _ m)
            (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO))) rfl
              EvalExprlist.nil)))) ?_
      refine triple_pre_sub ge _ _ emptyEnv _ [(_t'14, Val.ofBool same), (_proxy, .Vptr c.pB c.pO),
        (_pre_proxy, vnull), (_result, .Vint (Integers.Int.repr 0)), (_conn, .Vptr c.connB c.connO),
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
          -- Curl_auth_digest_cleanup(&data->state.proxydigest);
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (call_void_cells ge _ _ (digestSpec c (s1 c)) _ _ emptyEnv _ _ _ [.Vptr c.dataB (f2 c.dataO 568 16)]
              bDg fdDg (hDg _) hfDg htyDg rfl (fun _ _ _ => eval_callee_global rfl hsDg rfl)
              (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Eaddrof _ _ _ _ (lv_f2 (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy)
                  (hcenv ▸ off_state) (hcenv ▸ co_state) (hcenv ▸ off_proxydigest))) rfl
                EvalExprlist.nil)
              (fun _ h => ⟨rfl, h⟩) (fun _ _ h => h)) ?_
          -- curlx_free(data->state.envproxy);
          refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'29 _ (Val.loadResult Mptr c.envV)
              (fun le m hp hT hH hag =>
                eval_lv_load (lv_f2 (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_state)
                  (hcenv ▸ co_state) (hcenv ▸ off_envproxy)) rfl
                  (ldc 3 (cEnv1 c (s2 c)))))
            (call_none ge _ _ _ _ _ emptyEnv _ _ [Val.loadResult Mptr c.envV] bFree fdFree hFree hfFree
              htyFree rfl (fun _ _ _ => eval_callee_global rfl hsFree rfl)
              (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ _ (tget (Val.loadResult Mptr c.envV))) (cast_ptr henvl _ _ m)
                EvalExprlist.nil)
              (fun _ h => h) (fun _ _ h => h.2))) ?_
          -- data->state.envproxy = curlx_strdup(proxy);
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (call_ret ge _ _ _ _ _ _t'13 _ _ emptyEnv _ _ [.Vptr c.pB c.pO] bDup fdDup hDup hfDup htyDup
              rfl (fun _ _ _ => eval_callee_global rfl hsDup rfl)
              (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO))) rfl EvalExprlist.nil)) ?_
          exact assign_at ge _ _ emptyEnv _ c.pm _ (cellsU1 c (sMid c false q))
            (List.take 3 (cellsU1 c (s2 c)))
            (List.drop 4 (cellsU1 c (s2 c)))
            (cEnv1 c (s2 c))
            _ _ (f2 c.dataO 568 0) q rfl rfl hpw rfl rfl
            (fun le m hp hT _ _ => lv_f2 (tget (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy)
              (hcenv ▸ off_state) (hcenv ▸ co_state) (hcenv ▸ off_envproxy))
            (fun le m hp hT _ _ => ⟨q, EvalExpr.Etempvar _ _ _ (tget q), cast_ptr hq _ _ m⟩)
        case sub2 =>
          intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> temps_get
    case after =>
      -- if(!(conn->scheme->protocol & PROTO_FAMILY_HTTP)) …: HTTP の族なので通らない
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'24 _
        (.Vptr c.schB c.schO) (fun le m hp hT hH hag =>
          eval_lv_load (lv_f1 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_scheme))
            rfl (ldc 11 (cSch c)))) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'25 _
        (.Vlong c.proto) (fun le m hp hT hH hag =>
          eval_lv_load (lv_f1 (tget (.Vptr c.schB c.schO)) (hcenv ▸ co_sch) (hcenv ▸ off_protocol))
            rfl (ldc 12 (cProto c)))) ?_
      refine triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
          (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget (.Vlong c.proto))) eval_fam rfl)
          notbool_long, by rw [hproto]; rfl⟩) ?_
      exact triple_skip ge _ _ _
  -- conn->bits.socksproxy = !!conn->socks_proxy.peer;  (NULL)
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'22 _ vnull (fun le m hp hT hH hag =>
      eval_lv_load (lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_socks)
        (hcenv ▸ co_pi) (hcenv ▸ off_peer)) rfl (ldc 15 (cSpeer c))))
    (assign_bits_at ge _ _ emptyEnv _ c.pm (cellsU1 c (sMid c same q))
      (cellsU1 c (sW c same q w1)) [] (List.drop 1 (cellsU1 c (sMid c same q)))
      (cW c (sMid c same q)) (Integers.Int.repr 0) _ _ (f2 c.connO 40 0) 1 (Integers.Int.repr 0)
      rfl rfl hpw hpr rfl (by decide) (by decide) ⟨rfl, rfl⟩ rfl
      (fun le m hp hT _ _ => lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_bits)
        (hcenv ▸ co_bits) (hcenv ▸ off_socksproxy))
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Eunop _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (tget vnull)) notbool_null) rfl, rfl⟩))) ?_
  -- conn->bits.httpproxy = !!conn->http_proxy.peer;  (NULL でない)
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'21 _ (.Vptr c.peerB c.peerO) (fun le m hp hT hH hag =>
      eval_lv_load (lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_http)
        (hcenv ▸ co_pi) (hcenv ▸ off_peer)) rfl (ldc 1 (cHpeer c (sW c same q w1)))))
    (assign_bits_at ge _ _ emptyEnv _ c.pm (cellsU1 c (sW c same q w1))
      (cellsU1 c (sW c same q w2)) [] (List.drop 1 (cellsU1 c (sW c same q w1)))
      (cW c (sW c same q w1)) w1 _ _ (f2 c.connO 40 0) 0 (Integers.Int.repr 1)
      rfl rfl hpw hpr rfl (by decide) (by decide) ⟨rfl, rfl⟩ rfl
      (fun le m hp hT _ _ => lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_bits)
        (hcenv ▸ co_bits) (hcenv ▸ off_httpproxy))
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Eunop _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.peerB c.peerO)))
        (notbool_vptr (cells_weakValid hpn hH hag (c := cPeer c) (mem_idx 16 rfl) Nat.one_pos))) rfl,
        rfl⟩))) ?_
  -- conn->bits.proxy = conn->bits.httpproxy || conn->bits.socksproxy;
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'19 _
        (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 w2)) (fun le m hp hT hH hag =>
          eval_lv_bit (lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_bits)
            (hcenv ▸ co_bits) (hcenv ▸ off_httpproxy)) (by decide) (by decide)
            (ldc 0 (cW c (sW c same q w2)))))
      (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'17 _ (.Vint (Integers.Int.repr 1))
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))))
    (assign_bits_at ge _ _ emptyEnv _ c.pm (cellsU1 c (sW c same q w2))
      (cellsU1 c (sW c same q wFin)) [] (List.drop 1 (cellsU1 c (sW c same q w2)))
      (cW c (sW c same q w2)) w2 _ _ (f2 c.connO 40 0) 3 (Integers.Int.repr 1)
      rfl rfl hpw hpr rfl (by decide) (by decide) ⟨rfl, rfl⟩ rfl
      (fun le m hp hT _ _ => lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_bits)
        (hcenv ▸ co_bits) (hcenv ▸ off_proxyb))
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩))) ?_
  -- if(!conn->bits.proxy) …: 立っているので通らない
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'18 _
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned 3 1 wFin)) (fun le m hp hT hH hag =>
        eval_lv_bit (lv_f2 (tget (.Vptr c.connB c.connO)) (hcenv ▸ co_conn) (hcenv ▸ off_bits)
          (hcenv ▸ co_bits) (hcenv ▸ off_proxyb)) (by decide) (by decide)
          (ldc 0 (cW c (sW c same q wFin)))))
    (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl, rfl⟩)
      (triple_skip ge _ _ _))) ?_
  -- out: curlx_free(pre_proxy); curlx_free(proxy); return result;
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_label ge _ _ _ _ _ _
    (call_none ge _ _ _ _ _ emptyEnv _ _ [vnull] bFree fdFree hFree hfFree htyFree rfl
      (fun _ _ _ => eval_callee_global rfl hsFree rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (tget vnull)) rfl EvalExprlist.nil)
      (fun _ h => h) (fun _ _ h => h.2))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (call_none ge _ _ _ _ _ emptyEnv _ _ [.Vptr c.pB c.pO] bFree fdFree hFree hfFree htyFree rfl
      (fun _ _ _ => eval_callee_global rfl hsFree rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (tget (.Vptr c.pB c.pO))) rfl EvalExprlist.nil)
      (fun _ h => h) (fun _ _ h => h.2)) ?_
  exact triple_return_local ge _ _ _ _ _ _ (.Vint (Integers.Int.repr 0)) (.Vint (Integers.Int.repr 0))
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (tget (.Vint (Integers.Int.repr 0))))
    (fun _ => rfl) (fun hp hH => ⟨rfl, hH⟩)

end Deb2026_8927.U1
