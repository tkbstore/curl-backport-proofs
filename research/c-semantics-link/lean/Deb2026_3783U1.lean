/-
CVE-2026-3783（research/backport-proof-debian/cases/CVE-2026-3783.md）: 上流の修正後（U1、curl e3d7401a32）の
`output_auth_headers`。構成は `deb2026_3783/prelude.h`。

証明すること（`oah_after`、P1）: `authstatus->picked == CURLAUTH_BEARER` で `Curl_auth_allowed_to_host(data)` が偽を返すなら、
`proxy` と `data->set.str[STRING_BEARER]` の値によらず、戻り値は CURLE_OK（0）。
`http_output_bearer`・`Curl_checkheaders` には仕様を与えない（呼ぶ経路があれば証明が通らない）。
-/
import GenDeb2026_3783U1
import Case4debAfter
import Case3Cells
open CC CC.Sep CC.HProp
open Deb2026_3783_u1
open Case5C (addr call_fwd RR skip_fall)
open Case4debC (lv_field eval_deref_temp return_temp mapsto_weakValid)
open Case3C (CellD cellH Cells whole_pick cell_load3 assign_bit3)

set_option maxRecDepth 20000

namespace Deb2026_3783U

/-! ## 読み書きするメモリ -/

structure Ctx where
  dB : Block                 -- data
  dO : Integers.Ptrofs
  aB : Block                 -- authstatus
  aO : Integers.Ptrofs
  connV : Val                -- conn・request・path（この経路では読まない）
  reqV : Val
  pathV : Val
  bset : Bool                -- data->set.str[STRING_BEARER] が NULL でないか
  bB : Block                 -- そのときの文字列の先頭
  bO : Integers.Ptrofs
  ch : Integers.Int          -- 文字列の先頭のバイト（ポインタが有効であることを言うために所有する）
  pm : Permission

/-- `data->set.str[STRING_BEARER]` の値。 -/
def bearerV (c : Ctx) : Val :=
  if c.bset then .Vptr c.bB c.bO else .Vlong (Integers.Int64.repr 0)

/-- `data->set.str[STRING_BEARER]` の番地（`Efield`・`Oadd` が計算するのと同じ式。添字 56）。 -/
def strOfs (o : Integers.Ptrofs) : Integers.Ptrofs :=
  Integers.Ptrofs.add
    (Integers.Ptrofs.add (Integers.Ptrofs.add o (Integers.Ptrofs.repr 0)) (Integers.Ptrofs.repr 0))
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr 8) (Cop.ptrofsOfInt .Signed (Integers.Int.repr 56)))

/-- 値を追うセル: `picked`（= CURLAUTH_BEARER）、`done`・`multipass` を入れた 32 bit の単位、
    `str[STRING_BEARER]`、Bearer の文字列の先頭のバイト。 -/
abbrev cells (c : Ctx) (w : Integers.Int) : List CellD :=
  [(.Mint32, c.pm, c.aB, addr c.aO 4, .Vint (Integers.Int.repr 64)),
   (.Mint32, c.pm, c.aB, addr c.aO 12, .Vint w),
   (Mptr, c.pm, c.dB, Integers.Ptrofs.unsigned (strOfs c.dO), bearerV c),
   (.Mint8unsigned, c.pm, c.bB, Integers.Ptrofs.unsigned c.bO, .Vint c.ch)]

def H (c : Ctx) (w : Integers.Int) : HProp := Cells (cells c w) ∗ emp

def args (c : Ctx) (proxy : Bool) : List Val :=
  [.Vptr c.dB c.dO, c.connV, .Vptr c.aB c.aO, c.reqV, c.pathV, Val.ofBool proxy]

/-- P1 の仕様: 戻り値は CURLE_OK。`done`・`multipass` の単位は書き換わる。 -/
def oahSpecA (c : Ctx) (proxy : Bool) (w : Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _connectdata noattr),
             tptr (Ty.Tstruct _auth noattr), tptr tschar, tptr tschar, tbool]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = args c proxy ∧ H c w hp
  post := fun v hp => v = .Vint (Integers.Int.repr 0) ∧ ∃ w', H c w' hp
  measure := fun _ => 0

/-- `Curl_auth_allowed_to_host(data)` は `b` を返す。 -/
def allowedSpec (b : Bool) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun v hp => v = Val.ofBool b ∧ emp hp
  measure := fun _ => 0

/-! ## 構造体のレイアウト -/

def coOf (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_auth : prog.prog_comp_env.get _auth = some (coOf _auth) := rfl
theorem co_easy : prog.prog_comp_env.get _Curl_easy = some (coOf _Curl_easy) := rfl
theorem co_ud : prog.prog_comp_env.get _UserDefined = some (coOf _UserDefined) := rfl

theorem off_picked : fieldOffset prog.prog_comp_env _picked (coOf _auth).co_members
    = .OK (4, .Full) := by decide
theorem off_done : fieldOffset prog.prog_comp_env _done (coOf _auth).co_members
    = .OK (12, .Bits .I32 .Unsigned 0 1) := by decide
theorem off_multipass : fieldOffset prog.prog_comp_env _multipass (coOf _auth).co_members
    = .OK (12, .Bits .I32 .Unsigned 1 1) := by decide
theorem off_set : fieldOffset prog.prog_comp_env _set (coOf _Curl_easy).co_members
    = .OK (0, .Full) := by decide
theorem off_str : fieldOffset prog.prog_comp_env _str (coOf _UserDefined).co_members
    = .OK (0, .Full) := by decide

/-! ## 式の評価 -/

theorem load_cell {c : Ctx} {w : Integers.Int} {hp : Heap} {m : Mem} (k : Nat)
    (hk : k < (cells c w).length) {ch : Chunk} {b : Block} {o : Z} {v : Val}
    (hl : (cells c w)[k]'hk = (ch, c.pm, b, o, v))
    (hpr : permOrder c.pm .Readable = true) (hH : H c w hp) (hag : Heap.Agrees hp m) :
    Mem.load ch m b o = some (Val.loadResult ch v) :=
  cell_load3 hl hpr hH hag

/-- `authstatus->picked` -/
theorem eval_picked {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {c : Ctx} {w : Integers.Int}
    {hp : Heap} (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpr : permOrder c.pm .Readable = true)
    (hle : le.get _authstatus = some (.Vptr c.aB c.aO)) (hH : H c w hp) (hag : Heap.Agrees hp m) :
    EvalExpr ge e le m
      (.Efield (.Ederef (.Etempvar _authstatus (tptr (Ty.Tstruct _auth noattr)))
        (Ty.Tstruct _auth noattr)) _picked tuint)
      (.Vint (Integers.Int.repr 64)) :=
  EvalExpr.Elvalue _ _ _ .Full _
    (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_auth) (hcenv ▸ off_picked))
    (DerefLoc.value .Mint32 _ rfl (load_cell 0 (by show (0 : Nat) < 4; decide) rfl hpr hH hag))

/-- `data->set.str[STRING_BEARER]` -/
theorem eval_bearer {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {c : Ctx} {w : Integers.Int}
    {hp : Heap} (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpr : permOrder c.pm .Readable = true)
    (hle : le.get _data = some (.Vptr c.dB c.dO)) (hH : H c w hp) (hag : Heap.Agrees hp m) :
    EvalExpr ge e le m
      (.Ederef
        (.Ebinop .Oadd
          (.Efield (.Efield (.Ederef (.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
              (Ty.Tstruct _Curl_easy noattr)) _set (Ty.Tstruct _UserDefined noattr)) _str
            (tarray (tptr tschar) 70))
          (.Econst_int (Integers.Int.repr 56) tint) (tptr (tptr tschar))) (tptr tschar))
      (bearerV c) := by
  have hl : Mem.load Mptr m c.dB (Integers.Ptrofs.unsigned (strOfs c.dO))
      = some (Val.loadResult Mptr (bearerV c)) :=
    load_cell 2 (by show (2 : Nat) < 4; decide) rfl hpr hH hag
  have hv : Val.loadResult Mptr (bearerV c) = bearerV c := by
    unfold bearerV; cases c.bset <;> rfl
  rw [hv] at hl
  exact EvalExpr.Elvalue _ _ _ .Full _
    (EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Elvalue _ _ _ .Full _
          (lv_field (EvalExpr.Elvalue _ _ _ .Full _
              (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_easy) (hcenv ▸ off_set))
              (DerefLoc.copy rfl))
            rfl (hcenv ▸ co_ud) (hcenv ▸ off_str))
          (DerefLoc.reference rfl))
        (EvalExpr.Econst_int _ _)
        (semAdd_ptr_int _ _ _ _ _ rfl)))
    (DerefLoc.value Mptr _ rfl hl)

/-- Bearer の文字列の先頭は有効なポインタ。 -/
theorem bearer_valid {c : Ctx} {w : Integers.Int} {hp : Heap} {m : Mem}
    (hpn : permOrder c.pm .Nonempty = true) (hH : H c w hp) (hag : Heap.Agrees hp m) :
    Mem.weakValidPointer m c.bB (Integers.Ptrofs.unsigned c.bO) = true := by
  unfold H at hH
  rw [whole_pick (cells c w) emp 3 (by show (3 : Nat) < 4; decide)] at hH
  obtain ⟨h1, h2, _, rfl, hm, _⟩ := hH
  exact mapsto_weakValid hpn hm (Heap.Agrees_union_left hag)
    (by show 0 < sizeChunkNat .Mint8unsigned; decide)

theorem cast_bool_ptr {b : Block} {o : Integers.Ptrofs} {m : Mem}
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.semCast (.Vptr b o) (tptr tschar) tbool m = some (.Vint Integers.Int.one) := by
  simp only [Cop.semCast, hv]
  rfl

/-- `(bool)t'22`（`t'22` は Bearer の値）は `bset`。 -/
theorem cast_bool_bearer {c : Ctx} {m : Mem}
    (hv : c.bset = true → Mem.weakValidPointer m c.bB (Integers.Ptrofs.unsigned c.bO) = true) :
    Cop.semCast (bearerV c) (tptr tschar) tbool m = some (Val.ofBool c.bset) := by
  unfold bearerV
  cases hb : c.bset
  · rfl
  · rw [if_pos rfl]; exact cast_bool_ptr (hv hb)

theorem boolVal_ofBool_int (b : Bool) (m : Mem) : Cop.boolVal (Val.ofBool b) tint m = some b := by
  cases b <;> rfl

/-! ## 補助 -/

/-- 追っている一時変数の一部を捨てる。 -/
theorem weaken (ge fe f) {P : Sep.Assn} {s : Stmt} {E : Env} {l l' : List (Ident × Val)} {Hh : HProp}
    (h : Triple ge fe f P s (.only (LocalSt E l Hh))) (hsub : ∀ p ∈ l', p ∈ l) :
    Triple ge fe f P s (.only (LocalSt E l' Hh)) :=
  triple_conseq ge fe f h (fun _ _ _ x => x)
    (fun _ _ _ ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono hsub hT, hH⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

/-- `done`・`multipass` の単位の値は問わない。 -/
def Hx (c : Ctx) : HProp := fun hp => ∃ w', H c w' hp

theorem local_ex (ge fe f) {E : Env} {l : List (Ident × Val)} {s : Stmt} {R : Sep.ExitConds}
    {Hf : Integers.Int → HProp}
    (h : ∀ w, Triple ge fe f (LocalSt E l (Hf w)) s R) :
    Triple ge fe f (LocalSt E l (fun hp => ∃ w, Hf w hp)) s R :=
  triple_conseq ge fe f (triple_exists ge fe f (fun w => LocalSt E l (Hf w)) s R h)
    (fun _ _ _ ⟨he, hT, w, hH⟩ => ⟨w, he, hT, hH⟩) (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ _ x => x) (fun _ _ x => x)

/-- `∀ p ∈ l', p ∈ l`（`l'` は具体的な短い並び、`l` は `setLocal` の連鎖）。 -/
macro "sub_tac" : tactic =>
  `(tactic| (intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp;
             rcases hp with h | h | h | h | h <;> (subst_vars; temps_get)))

/-- `auth = NULL` の値。 -/
abbrev v0 : Val := .Vlong (Integers.Int64.repr 0)

/-- Bearer の分岐のあとで使う一時変数。 -/
abbrev Lx (c : Ctx) : List (Ident × Val) :=
  [(_auth__1, v0), (_result, .Vint (Integers.Int.repr 0)), (_authstatus, .Vptr c.aB c.aO)]

theorem oah_entry_wf :
    listNorepet (varNames f_output_auth_headers.fn_vars)
    ∧ listNorepet (varNames f_output_auth_headers.fn_params)
    ∧ listDisjoint (varNames f_output_auth_headers.fn_params)
        (varNames f_output_auth_headers.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

macro "ptree_get" : tactic =>
  `(tactic| repeat (first
      | exact PTree.gss _ _ _
      | refine (PTree.gso _ _ _ _ (by decide)).trans ?_))

/-! ## P1 -/

theorem oah_after (ge : CGenv) (c : Ctx) (proxy : Bool) (w : Integers.Int)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (bAl : Block) (fdAl : FunDef)
    (hsAl : Genv.findSymbol ge.genv_genv _Curl_auth_allowed_to_host = some bAl)
    (hfAl : FuncPtr ge bAl fdAl)
    (htyAl : typeOfFundef fdAl
      = .Tfunction (allowedSpec false).tyargs (allowedSpec false).tyres (allowedSpec false).cc)
    (hAl : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdAl (allowedSpec false) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_output_auth_headers) (oahSpecA c proxy w) vs := by
  by_cases hvs : vs = args c proxy
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := oah_entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_output_auth_headers _ _
    (LocalSt emptyEnv [(_proxy, Val.ofBool proxy), (_path, c.pathV), (_request, c.reqV),
                       (_authstatus, .Vptr c.aB c.aO), (_conn, c.connV),
                       (_data, .Vptr c.dB c.dO)] (H c w))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _proxy (Val.ofBool proxy) (PTree.set _path c.pathV
              (PTree.set _request c.reqV (PTree.set _authstatus (.Vptr c.aB c.aO)
                (PTree.set _conn c.connV (PTree.set _data (.Vptr c.dB c.dO)
                  (createUndefTemps f_output_auth_headers.fn_temps)))))),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ⟨rfl, ?_, hpre.2⟩⟩
    refine TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_cons ?_
      (TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_nil _)))))) <;> ptree_get
  -- auth = NULL; result = CURLE_OK;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ v0
      (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vint (Integers.Int.repr 0))
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  -- Basic の分岐: picked は CURLAUTH_BASIC でない
  refine triple_seq ge _ _ _ ?Qb _ _ _ ?b1 ?b2
  case b1 =>
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vint (Integers.Int.repr 64))
        (fun le m hp hT hH hag => eval_picked hcenv hpr (hT.get (by temps_get)) hH hag)) ?_
    refine triple_if_local ge _ _ emptyEnv _ (H c w) _ false _ _ _
      (fun le m hp hT _ _ =>
        ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
              (EvalExpr.Ebinop _ _ _ _ _ _ _
                (EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl) (EvalExpr.Econst_int _ _) rfl)
              rfl, rfl⟩) ?_
    rw [if_neg Bool.false_ne_true]
    exact skip_fall ge _ _ _ _
  case b2 =>
  -- Bearer の分岐
  refine triple_seq ge _ _ _ (LocalSt emptyEnv (Lx c) (Hx c)) _ _ _ ?e1 ?e2
  case e1 =>
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vint (Integers.Int.repr 64))
        (fun le m hp hT hH hag => eval_picked hcenv hpr (hT.get (by temps_get)) hH hag)) ?_
    refine triple_if_local ge _ _ emptyEnv _ (H c w) _ true _ _ _
      (fun le m hp hT _ _ =>
        ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
              (EvalExpr.Ebinop _ _ _ _ _ _ _
                (EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl) (EvalExpr.Econst_int _ _) rfl)
              rfl, rfl⟩) ?_
    rw [if_pos rfl]
    refine Sep.triple_fallthrough ge _ _ _ _ _ _ ?_ (fun _ _ _ x => x)
    -- 条件の評価（3つの経路）のあと、done = TRUE
    refine triple_seq_fwd ge _ _ _ (LocalSt emptyEnv (Lx c) (H c w)) _ _ _ ?x ?done
    case done =>
      refine triple_conseq ge _ _
        (assign_bit3 ge _ _ emptyEnv (Lx c) (cells c w) emp 1 (by show (1 : Nat) < 4; decide)
          c.pm c.aB (Integers.Ptrofs.add c.aO (Integers.Ptrofs.repr 12)) 0 w (Integers.Int.repr 1)
          rfl _ _ hpw hpr rfl (by decide) (by decide)
          (fun le m hT => EvalLvalue.Efield_struct _ _ _ _ _ _ _ _ _ _
            (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_auth) (hcenv ▸ off_done))
          (fun le m hT => ⟨_, EvalExpr.Econst_int _ _, rfl⟩))
        (fun _ _ _ x => x)
        (fun _ _ _ ⟨he, hT, hH⟩ =>
          ⟨he, hT, ⟨Integers.Int.bitfield_insert (Cop.firstBit .I32 0 1).toNat 1 w
            (Integers.Int.repr 1), hH⟩⟩)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    case x =>
    refine triple_seq_fwd ge _ _ _ (LocalSt emptyEnv ((_t'12, .Vint (Integers.Int.repr 0)) :: Lx c) (H c w))
      _ _ _ ?x1 ?x2
    case x2 =>
      -- if (t'12) … else skip（t'12 = 0）
      refine triple_if_local ge _ _ emptyEnv _ (H c w) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0))
          (hT.get (by temps_mem)), rfl⟩) ?_
      rw [if_neg Bool.false_ne_true]
      exact weaken ge _ _ (triple_skip ge _ _ _) (fun p hp => List.mem_cons_of_mem _ hp)
    case x1 =>
    refine triple_seq_fwd ge _ _ _ (LocalSt emptyEnv ((_t'10, .Vint (Integers.Int.repr 0)) :: Lx c) (H c w))
      _ _ _ ?y1 ?y2
    case y2 =>
      -- if (t'10) … else t'12 = 0（t'10 = 0。Curl_checkheaders は呼ばない）
      refine triple_if_local ge _ _ emptyEnv _ (H c w) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0))
          (hT.get (by temps_mem)), rfl⟩) ?_
      rw [if_neg Bool.false_ne_true]
      exact weaken ge _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vint (Integers.Int.repr 0))
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) (by sub_tac)
    case y1 =>
    cases proxy
    · -- proxy が偽: t'22 = str[STRING_BEARER]; t'9 = (bool)t'22;
      refine triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_if_local ge _ _ emptyEnv _ (H c w) _ true _ _ _
          (fun le m hp hT _ _ =>
            ⟨_, EvalExpr.Eunop _ _ _ _ _
              (EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get))) rfl, rfl⟩)
          (by
            rw [if_pos rfl]
            exact triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (bearerV c)
                (fun le m hp hT hH hag => eval_bearer hcenv hpr (hT.get (by temps_get)) hH hag))
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (Val.ofBool c.bset)
                (fun le m hp hT hH hag => EvalExpr.Ecast _ _ _ _
                  (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                  (cast_bool_bearer (fun _ => bearer_valid hpn hH hag)))))) ?_
      cases hb : c.bset
      · -- Bearer が NULL: t'10 = 0
        refine triple_if_local ge _ _ emptyEnv _ (H c w) _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false)
            (hT.get (by temps_get)), rfl⟩) ?_
        rw [if_neg Bool.false_ne_true]
        exact weaken ge _ _
          (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vint (Integers.Int.repr 0))
            (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) (by sub_tac)
      · -- Bearer が設定されている: t'11 = Curl_auth_allowed_to_host(data)（偽）; t'10 = (bool)t'11;
        refine triple_if_local ge _ _ emptyEnv _ (H c w) _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true)
            (hT.get (by temps_get)), rfl⟩) ?_
        rw [if_pos rfl]
        exact weaken ge _ _
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (call_fwd ge _ _ (allowedSpec false) _ _ _ emptyEnv _ emp (H c w) emp (H c w) (H c w)
              [.Vptr c.dB c.dO] (Val.ofBool false) bAl fdAl hAl hfAl htyAl rfl
              (fun _ _ _ => eval_callee_global rfl hsAl rfl)
              (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get))) rfl EvalExprlist.nil)
              (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vint (Integers.Int.repr 0))
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get))) rfl)))
          (by sub_tac)
    · -- proxy が真: t'9 = 0; t'10 = 0
      refine triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_if_local ge _ _ emptyEnv _ (H c w) _ false _ _ _
          (fun le m hp hT _ _ =>
            ⟨_, EvalExpr.Eunop _ _ _ _ _
              (EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get))) rfl, rfl⟩)
          (by
            rw [if_neg Bool.false_ne_true]
            exact triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vint (Integers.Int.repr 0))
              (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))) ?_
      refine triple_if_local ge _ _ emptyEnv _ (H c w) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0))
          (hT.get (by temps_get)), rfl⟩) ?_
      rw [if_neg Bool.false_ne_true]
      exact weaken ge _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vint (Integers.Int.repr 0))
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) (by sub_tac)
  case e2 =>
  -- if (auth) … else multipass = FALSE;（auth は NULL）  return result;
  refine local_ex ge _ _ (fun w1 => ?_)
  refine triple_seq_fwd ge _ _ _ (LocalSt emptyEnv (Lx c)
    (H c (Integers.Int.bitfield_insert (Cop.firstBit .I32 1 1).toNat 1 w1 (Integers.Int.repr 0))))
    _ _ _ ?f1 ?f2
  case f1 =>
    refine triple_if_local ge _ _ emptyEnv _ (H c w1) _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ v0 (hT.get (by temps_mem)), rfl⟩) ?_
    rw [if_neg Bool.false_ne_true]
    exact assign_bit3 ge _ _ emptyEnv (Lx c) (cells c w1) emp 1 (by show (1 : Nat) < 4; decide)
      c.pm c.aB (Integers.Ptrofs.add c.aO (Integers.Ptrofs.repr 12)) 1 w1 (Integers.Int.repr 0)
      rfl _ _ hpw hpr rfl (by decide) (by decide)
      (fun le m hT => EvalLvalue.Efield_struct _ _ _ _ _ _ _ _ _ _
        (eval_deref_temp (hT.get (by temps_mem))) rfl (hcenv ▸ co_auth) (hcenv ▸ off_multipass))
      (fun le m hT => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)
  case f2 =>
    exact return_temp ge _ _ _ _ _result (Integers.Int.repr 0) _ _ (by temps_mem) rfl
      (fun hp hH => ⟨rfl, Integers.Int.bitfield_insert (Cop.firstBit .I32 1 1).toNat 1 w1
        (Integers.Int.repr 0), hH⟩)

end Deb2026_3783U
