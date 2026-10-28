/-
Case 5（CURL-CVE-2026-86411）: 修正前・修正後の両方の証明で共通に使う部分。

- `Ctx`: 関数が読むメモリの中身と置き場所。`H` はその所有（読み出しだけの8つのセル）
- `input`: C の関数が読む値を、H5 のモデルの入力（`H5.Case5.Input`）に写す
- 呼ばれる側の仕様: `Curl_conn_is_ssl`・`Curl_ssl_conn_config_match`（外部関数。仕様は定理の仮定として与える）、
  `get_protocol_family`（同じ翻訳単位の関数。ここで証明する）
-/
import GenCase5After
import H5Case5
import CCLib
open CC CC.Sep CC.HProp
open Case5_after

set_option maxRecDepth 20000

namespace Case5C

/-! ## 読むメモリ -/

/-- 対象の関数が読むメモリ。`url_match_ssl_use` / `url_match_ssl_config` の引数 `conn`・`m` から辿れるもの。 -/
structure Ctx where
  connB : Block
  connO : Integers.Ptrofs
  mB : Block
  mO : Integers.Ptrofs
  dataB : Block              -- m->data
  dataO : Integers.Ptrofs
  ndlB : Block               -- m->needle
  ndlO : Integers.Ptrofs
  nschB : Block              -- m->needle->scheme
  nschO : Integers.Ptrofs
  cschB : Block              -- conn->scheme
  cschO : Integers.Ptrofs
  bits : Integers.Int        -- m の may_tls・require_tls を入れた 32 bit の単位
  flags : Integers.Int       -- m->needle->scheme->flags
  proto : Integers.Int64     -- m->needle->scheme->protocol
  fam : Integers.Int64       -- conn->scheme->family
  pm : Permission

/-- フィールドの番地。`Efield` が計算するのと同じ式で書く（桁あふれの場合分けを避ける）。 -/
def addr (o : Integers.Ptrofs) (d : Z) : Z :=
  Integers.Ptrofs.unsigned (Integers.Ptrofs.add o (Integers.Ptrofs.repr d))

/-- 読むセルの所有。並びは `m` → `needle` → `needle->scheme` → `conn` → `conn->scheme`。
    `needle->scheme` と `conn->scheme` が同じ構造体でもよい（読むフィールドが重ならないため）。 -/
def H (c : Ctx) : HProp :=
  mapsto Mptr c.pm c.mB (addr c.mO 0) (.Vptr c.dataB c.dataO) ∗
  (mapsto Mptr c.pm c.mB (addr c.mO 8) (.Vptr c.ndlB c.ndlO) ∗
  (mapsto .Mint32 c.pm c.mB (addr c.mO 16) (.Vint c.bits) ∗
  (mapsto Mptr c.pm c.ndlB (addr c.ndlO 0) (.Vptr c.nschB c.nschO) ∗
  (mapsto .Mint64 c.pm c.nschB (addr c.nschO 0) (.Vlong c.proto) ∗
  (mapsto .Mint32 c.pm c.nschB (addr c.nschO 16) (.Vint c.flags) ∗
  (mapsto Mptr c.pm c.connB (addr c.connO 0) (.Vptr c.cschB c.cschO) ∗
   mapsto .Mint64 c.pm c.cschB (addr c.cschO 8) (.Vlong c.fam)))))))

/-- `H` から読み出せること（8つの load）。 -/
structure Loads (c : Ctx) (m : Mem) : Prop where
  data : Mem.load Mptr m c.mB (addr c.mO 0) = some (.Vptr c.dataB c.dataO)
  needle : Mem.load Mptr m c.mB (addr c.mO 8) = some (.Vptr c.ndlB c.ndlO)
  bits : Mem.load .Mint32 m c.mB (addr c.mO 16) = some (.Vint c.bits)
  nsch : Mem.load Mptr m c.ndlB (addr c.ndlO 0) = some (.Vptr c.nschB c.nschO)
  proto : Mem.load .Mint64 m c.nschB (addr c.nschO 0) = some (.Vlong c.proto)
  flags : Mem.load .Mint32 m c.nschB (addr c.nschO 16) = some (.Vint c.flags)
  csch : Mem.load Mptr m c.connB (addr c.connO 0) = some (.Vptr c.cschB c.cschO)
  fam : Mem.load .Mint64 m c.cschB (addr c.cschO 8) = some (.Vlong c.fam)

theorem sep_l {P Q : HProp} {h : Heap} {m : Mem} (hs : (P ∗ Q) h) (hag : Heap.Agrees h m) :
    ∃ h1, P h1 ∧ Heap.Agrees h1 m := by
  obtain ⟨h1, h2, _, rfl, hp, _⟩ := hs
  exact ⟨h1, hp, Heap.Agrees_union_left hag⟩

theorem sep_r {P Q : HProp} {h : Heap} {m : Mem} (hs : (P ∗ Q) h) (hag : Heap.Agrees h m) :
    ∃ h2, Q h2 ∧ Heap.Agrees h2 m := by
  obtain ⟨h1, h2, hd, rfl, _, hq⟩ := hs
  exact ⟨h2, hq, Heap.Agrees_union_right hd hag⟩

theorem H_loads {c : Ctx} {hp : Heap} {m : Mem} (hpr : permOrder c.pm .Readable = true)
    (hH : H c hp) (hag : Heap.Agrees hp m) : Loads c m := by
  obtain ⟨h1, c1, a1⟩ := sep_l hH hag
  obtain ⟨r1, d1, b1⟩ := sep_r hH hag
  obtain ⟨h2, c2, a2⟩ := sep_l d1 b1
  obtain ⟨r2, d2, b2⟩ := sep_r d1 b1
  obtain ⟨h3, c3, a3⟩ := sep_l d2 b2
  obtain ⟨r3, d3, b3⟩ := sep_r d2 b2
  obtain ⟨h4, c4, a4⟩ := sep_l d3 b3
  obtain ⟨r4, d4, b4⟩ := sep_r d3 b3
  obtain ⟨h5, c5, a5⟩ := sep_l d4 b4
  obtain ⟨r5, d5, b5⟩ := sep_r d4 b4
  obtain ⟨h6, c6, a6⟩ := sep_l d5 b5
  obtain ⟨r6, d6, b6⟩ := sep_r d5 b5
  obtain ⟨h7, c7, a7⟩ := sep_l d6 b6
  obtain ⟨h8, c8, a8⟩ := sep_r d6 b6
  exact ⟨mapsto_load hpr c1 a1, mapsto_load hpr c2 a2, mapsto_load hpr c3 a3,
         mapsto_load hpr c4 a4, mapsto_load hpr c5 a5, mapsto_load hpr c6 a6,
         mapsto_load hpr c7 a7, mapsto_load hpr c8 a8⟩

/-! ## 構造体のレイアウト（生成された composite 環境から計算する） -/

theorem co_scheme :
    prog.prog_comp_env.get _Curl_scheme = some
      { co_su := SU.Struct,
        co_members := [Member.Member_plain _protocol tlong, Member.Member_plain _family tlong,
                       Member.Member_plain _flags tuint],
        co_attr := noattr, co_sizeof := 24, co_alignof := 8, co_rank := 0 } := by decide

theorem co_conn :
    prog.prog_comp_env.get _connectdata = some
      { co_su := SU.Struct,
        co_members := [Member.Member_plain _scheme (tptr (Ty.Tstruct _Curl_scheme noattr))],
        co_attr := noattr, co_sizeof := 8, co_alignof := 8, co_rank := 0 } := by decide

def matchMembers : List Member :=
  [Member.Member_plain _data (tptr (Ty.Tstruct _Curl_easy noattr)),
   Member.Member_plain _needle (tptr (Ty.Tstruct _connectdata noattr)),
   Member.Member_bitfield _may_tls IntSize.I32 Signedness.Unsigned noattr 1 false,
   Member.Member_bitfield _require_tls IntSize.I32 Signedness.Unsigned noattr 1 false]

theorem co_match :
    prog.prog_comp_env.get _url_conn_match = some
      { co_su := SU.Struct, co_members := matchMembers,
        co_attr := noattr, co_sizeof := 24, co_alignof := 8, co_rank := 0 } := by decide

theorem off_protocol : fieldOffset prog.prog_comp_env _protocol
    [Member.Member_plain _protocol tlong, Member.Member_plain _family tlong,
     Member.Member_plain _flags tuint] = .OK (0, .Full) := by decide
theorem off_family : fieldOffset prog.prog_comp_env _family
    [Member.Member_plain _protocol tlong, Member.Member_plain _family tlong,
     Member.Member_plain _flags tuint] = .OK (8, .Full) := by decide
theorem off_flags : fieldOffset prog.prog_comp_env _flags
    [Member.Member_plain _protocol tlong, Member.Member_plain _family tlong,
     Member.Member_plain _flags tuint] = .OK (16, .Full) := by decide
theorem off_scheme : fieldOffset prog.prog_comp_env _scheme
    [Member.Member_plain _scheme (tptr (Ty.Tstruct _Curl_scheme noattr))] = .OK (0, .Full) := by
  decide
theorem off_data : fieldOffset prog.prog_comp_env _data matchMembers = .OK (0, .Full) := by
  decide
theorem off_needle : fieldOffset prog.prog_comp_env _needle matchMembers = .OK (8, .Full) := by
  decide
theorem off_may_tls : fieldOffset prog.prog_comp_env _may_tls matchMembers
    = .OK (16, .Bits .I32 .Unsigned 0 1) := by decide
theorem off_require_tls : fieldOffset prog.prog_comp_env _require_tls matchMembers
    = .OK (16, .Bits .I32 .Unsigned 1 1) := by decide

/-! ## 式の評価 -/

/-- `p->fld`（`p` は一時変数、`fld` はビットフィールドでないスカラー）。 -/
theorem eval_field {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {p sid fld : Ident} {ty : Ty} {co : Composite} {chunk : Chunk}
    {b : Block} {o : Integers.Ptrofs} {delta : Z} {v : Val}
    (hle : le.get p = some (.Vptr b o))
    (hco : ge.genv_cenv.get sid = some co)
    (hfld : fieldOffset ge.genv_cenv fld co.co_members = .OK (delta, .Full))
    (hacc : accessMode ty = .By_value chunk)
    (hload : Mem.load chunk m b (addr o delta) = some v) :
    EvalExpr ge e le m
      (.Efield (.Ederef (.Etempvar p (tptr (.Tstruct sid noattr))) (.Tstruct sid noattr)) fld ty)
      v :=
  EvalExpr.Elvalue _ b (Integers.Ptrofs.add o (Integers.Ptrofs.repr delta)) .Full v
    (EvalLvalue.Efield_struct _ fld ty b o sid co noattr delta .Full
      (EvalExpr.Elvalue _ b o .Full _
        (EvalLvalue.Ederef _ _ b o (EvalExpr.Etempvar p _ _ hle)) (DerefLoc.copy rfl))
      rfl hco hfld)
    (DerefLoc.value chunk v hacc hload)

/-- `p->fld`（`fld` は `unsigned int fld:1` のビットフィールド）。読んだ値の型は `int`。 -/
theorem eval_bitfield {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {p sid fld : Ident} {co : Composite}
    {b : Block} {o : Integers.Ptrofs} {delta pos : Z} {c : Integers.Int}
    (hle : le.get p = some (.Vptr b o))
    (hco : ge.genv_cenv.get sid = some co)
    (hfld : fieldOffset ge.genv_cenv fld co.co_members = .OK (delta, .Bits .I32 .Unsigned pos 1))
    (hpos0 : 0 ≤ pos) (hpos : pos + 1 ≤ 32)
    (hload : Mem.load .Mint32 m b (addr o delta) = some (.Vint c)) :
    EvalExpr ge e le m
      (.Efield (.Ederef (.Etempvar p (tptr (.Tstruct sid noattr))) (.Tstruct sid noattr)) fld tint)
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned pos 1 c)) :=
  EvalExpr.Elvalue _ b (Integers.Ptrofs.add o (Integers.Ptrofs.repr delta))
    (.Bits .I32 .Unsigned pos 1) _
    (EvalLvalue.Efield_struct _ fld tint b o sid co noattr delta _
      (EvalExpr.Elvalue _ b o .Full _
        (EvalLvalue.Ederef _ _ b o (EvalExpr.Etempvar p _ _ hle)) (DerefLoc.copy rfl))
      rfl hco hfld)
    (DerefLoc.bitfield .I32 .Unsigned pos 1 _
      (Cop.LoadBitfield.intro .I32 .Signed noattr .Unsigned pos 1 m _ c hpos0 (by decide)
        (by decide) hpos (by decide) hload))

/-! ## H5 のモデルへの写像

C の関数が読む値から、H5 のモデルの入力を作る。`connSSL`・`cfgMatch` は外部関数の戻り値。 -/

def flagBit (flags : Integers.Int) (k : Z) : Bool :=
  !Integers.Int.eq (Integers.Int.and flags (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr k)))
    Integers.Int.zero

def bitOf (bits : Integers.Int) (pos : Z) : Bool :=
  !Integers.Int.eq (Cop.bitfieldExtract .I32 .Unsigned pos 1 bits) Integers.Int.zero

def input (c : Ctx) (ssl cfg : Bool) : H5.Case5.Input where
  needleSSL := flagBit c.flags 0       -- PROTOPT_SSL = 1 << 0
  connSSL := ssl
  reuseOk := flagBit c.flags 15        -- PROTOPT_SSL_REUSE = 1 << 15
  sameFamily := Integers.Int64.eq c.fam c.proto
  requireTls := bitOf c.bits 1         -- m->require_tls
  mayTls := bitOf c.bits 0             -- m->may_tls
  cfgMatch := cfg

/-! ## 呼ばれる側の仕様 -/

/-- `Curl_conn_is_ssl(conn, FIRSTSOCKET)` は `ssl` を返し、メモリを変えない。
    `ssl` は任意（何を返してもよい）。ただし同じ `conn` に対しては毎回同じ値を返す。 -/
def sslSpec (c : Ctx) (ssl : Bool) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _connectdata noattr), tschar]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.connB c.connO, .Vint (Integers.Int.repr 0)] ∧ emp hp
  post := fun v hp => v = Val.ofBool ssl ∧ emp hp
  measure := fun _ => 0

/-- `Curl_ssl_conn_config_match(data, conn, FALSE)` は `cfg` を返し、メモリを変えない。`cfg` は任意。 -/
def cfgSpec (c : Ctx) (cfg : Bool) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _connectdata noattr), tbool]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr c.dataB c.dataO, .Vptr c.connB c.connO, .Vint (Integers.Int.repr 0)] ∧ emp hp
  post := fun v hp => v = Val.ofBool cfg ∧ emp hp
  measure := fun _ => 0

/-- `get_protocol_family(conn->scheme)` の仕様。下で本体から証明する。 -/
def gpfSpec (c : Ctx) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_scheme noattr)]
  tyres := tlong
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.cschB c.cschO] ∧ H c hp
  post := fun v hp => v = .Vlong c.fam ∧ H c hp
  measure := fun _ => 0

/-! ## `DEBUGASSERT(x)` = `do {} while(0)` -/

theorem triple_nop_loop (ge fe f) (P : Sep.Assn) :
    Triple ge fe f P (.Sloop .Sskip .Sbreak) (.only P) :=
  triple_loop ge fe f (.only P) (fun _ => P) (fun _ => P) .Sskip .Sbreak
    (fun _ => triple_conseq ge fe f (triple_skip ge fe f P) (fun _ _ _ x => x)
      (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
      (fun _ _ x => False.elim x))
    (fun _ => triple_conseq ge fe f (triple_break ge fe f P) (fun _ _ _ x => x)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x))
    0

/-! ## `get_protocol_family` -/

theorem gpf_entry_wf :
    listNorepet (varNames f_get_protocol_family.fn_vars)
    ∧ listNorepet (varNames f_get_protocol_family.fn_params)
    ∧ listDisjoint (varNames f_get_protocol_family.fn_params)
        (varNames f_get_protocol_family.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem gpf_satisfies (ge : CGenv) (c : Ctx) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_get_protocol_family) (gpfSpec c) vs := by
  by_cases hvs : vs = [.Vptr c.cschB c.cschO]
  · subst hvs
    obtain ⟨hnv, hnp, hdisj⟩ := gpf_entry_wf
    refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_get_protocol_family _ _
      (LocalSt emptyEnv [(_s, .Vptr c.cschB c.cschO)] (H c)) (fun m => ?_) ?_
    · refine ⟨PTree.set _s (.Vptr c.cschB c.cschO)
                (createUndefTemps f_get_protocol_family.fn_temps),
              FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
              fun hp hpre => ?_⟩
      exact ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_nil _), hpre.2⟩
    · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_nop_loop ge _ _ _) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_nop_loop ge _ _ _) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'1 _ (.Vlong c.fam)
          (fun le m hp hT hH hag =>
            eval_field (hT.get (by temps_mem)) (hcenv ▸ co_scheme) (hcenv ▸ off_family) rfl
              (H_loads hpr hH hag).fam)) ?_
      exact triple_return_local ge _ _ _ (H c) _ _ (.Vlong c.fam) (.Vlong c.fam)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
        (fun _ => rfl) (fun hp hH => ⟨rfl, hH⟩)
  · intro k m hp hf _ hpre
    exact absurd hpre.1 hvs

/-! ## 式・文の規則（この関数の形に合わせたもの） -/

theorem boolVal_ofBool_tint (b : Bool) (m : Mem) : Cop.boolVal (Val.ofBool b) tint m = some b := by
  cases b <;> rfl

theorem boolVal_ofBool_tbool (b : Bool) (m : Mem) : Cop.boolVal (Val.ofBool b) tbool m = some b := by
  cases b <;> rfl

theorem notbool_ofBool (b : Bool) (m : Mem) :
    Cop.semUnaryOperation .Onotbool (Val.ofBool b) tbool m = some (Val.ofBool (!b)) := by
  cases b <;> rfl

theorem boolVal_flag0 (fl : Integers.Int) (m : Mem) :
    Cop.boolVal (.Vint (Integers.Int.and fl
      (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 0)))) tuint m
      = some (flagBit fl 0) := rfl

/-- `t & (1 << 0)` -/
theorem eval_flag0 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {t : Ident} {fl : Integers.Int}
    (hle : le.get t = some (.Vint fl)) :
    EvalExpr ge e le m
      (.Ebinop .Oand (.Etempvar t tuint)
        (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tint) (.Econst_int (Integers.Int.repr 0) tint) tint)
        tuint)
      (.Vint (Integers.Int.and fl (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 0)))) :=
  EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hle)
    (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl) rfl

/-- `t & (1 << 15)` -/
theorem eval_flag15 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {t : Ident} {fl : Integers.Int}
    (hle : le.get t = some (.Vint fl)) :
    EvalExpr ge e le m
      (.Ebinop .Oand (.Etempvar t tuint)
        (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tint) (.Econst_int (Integers.Int.repr 15) tint) tint)
        tuint)
      (.Vint (Integers.Int.and fl (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 15)))) :=
  EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hle)
    (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl) rfl

/-- `!(t & (1 << 15))` -/
theorem eval_notflag15 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {t : Ident} {fl : Integers.Int}
    (hle : le.get t = some (.Vint fl)) :
    EvalExpr ge e le m
      (.Eunop .Onotbool
        (.Ebinop .Oand (.Etempvar t tuint)
          (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tint) (.Econst_int (Integers.Int.repr 15) tint) tint)
          tuint) tint)
      (Val.ofBool (!flagBit fl 15)) :=
  EvalExpr.Eunop _ _ _ _ _ (eval_flag15 hle) rfl

/-- `(_Bool)(t3 != t16)`（`long` どうしの比較） -/
theorem eval_ne_cast {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {t1 t2 : Ident}
    {x y : Integers.Int64}
    (h1 : le.get t1 = some (.Vlong x)) (h2 : le.get t2 = some (.Vlong y)) :
    EvalExpr ge e le m
      (.Ecast (.Ebinop .One (.Etempvar t1 tlong) (.Etempvar t2 tlong) tint) tbool)
      (Val.ofBool (!Integers.Int64.eq x y)) := by
  have hne : Integers.Int64.cmp .Cne x y = !Integers.Int64.eq x y := rfl
  refine EvalExpr.Ecast _ _ (Val.ofBool (Integers.Int64.cmp .Cne x y)) _
    (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ h1) (EvalExpr.Etempvar _ _ _ h2) rfl) ?_
  rw [hne]
  cases Integers.Int64.eq x y <;> rfl

/-- 呼び出しの規則。`triple_call_local` を、所有の形の等式で包んだもの。 -/
theorem call_fwd (ge fe f) (S : FunSpec) (id : Ident) (callee : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (Hpre Hkeep Hpost H0 H1 : HProp)
    (vargs : List Val) (vret : Val) (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs)
    (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof callee) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le →
                 EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, Hpre h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → v = vret ∧ Hpost h)
    (h0 : H0 = Hpre ∗ Hkeep) (h1 : Hpost ∗ Hkeep = H1) :
    Triple ge fe f (LocalSt E l H0) (.Scall (some id) callee al)
      (.only (LocalSt E (setLocal l id vret) H1)) := by
  subst h0 h1
  exact triple_call_local ge fe f S id callee al E l (dropId id l) Hpre Hkeep Hpost vargs vret
    fb fd hspec hfind hty hclass (fun _ hq => (mem_dropId hq).1) (fun _ hq => (mem_dropId hq).2)
    hcallee hargs hpre hpost

/-- 戻り値が決まっている出口の条件。`normal` だけを入れ替えて使う。 -/
abbrev RR (Ret : Val → HProp) (Q : Sep.Assn) : Sep.ExitConds :=
  { normal := Q, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := Ret }

/-- `return n;`（`n` は `int` の定数）。 -/
theorem return_const (ge fe f) (l : List (Ident × Val)) (Hh : HProp) (n : Integers.Int)
    (Ret : Val → HProp) (Q : Sep.Assn) (v' : Val)
    (hcast : ∀ m : Mem, Cop.semCast (.Vint n) tint f.fn_return m = some v')
    (hret : ∀ hp, Hh hp → Ret v' hp) :
    Triple ge fe f (LocalSt emptyEnv l Hh) (.Sreturn (some (.Econst_int n tint))) (RR Ret Q) :=
  triple_conseq ge fe f
    (triple_return_local ge fe f l Hh _ Ret (.Vint n) v'
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) hcast hret)
    (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ x => x)

/-- 何もせずに抜ける枝。抜けた先の条件 `φ` はこの枝で成り立つことを示す。 -/
theorem skip_end (ge fe f) (l : List (Ident × Val)) (Hh : HProp) (Ret : Val → HProp) (φ : Prop)
    (hφ : φ) :
    Triple ge fe f (LocalSt emptyEnv l Hh) .Sskip
      (RR Ret (fun e _ hp => e = emptyEnv ∧ φ ∧ Hh hp)) :=
  triple_conseq ge fe f (triple_skip ge fe f _) (fun _ _ _ x => x)
    (fun _ _ _ ⟨he, _, hH⟩ => ⟨he, hφ, hH⟩) (fun _ _ _ x => False.elim x)
    (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

end Case5C
