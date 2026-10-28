/-
CVE-2025-14819: 上流の修正前（be3c226bb0）の `ossl_cached_x509_store_different`（U0）と P0。

証明すること（`different_before`）: `mb->CAfile` と `conn_config->CAfile` がともに NULL なら、戻り値は FALSE（0）。
関数は `ssl_config->no_partialchain` を読まないので、その値が 1（部分的な鎖を禁じる）でも、キャッシュは使われる。
-/
import GenDeb2025_14819UpBefore
import Case5Witness
import Case4debCommon
open CC CC.Sep CC.HProp
open Deb2025_14819_up_before
open Case5C (addr call_fwd RR return_const boolVal_ofBool_tint sep_l sep_r bitOf cell mapsto_disj agrees_union)
open Case4debC (IsPtr cast_ptr)

set_option maxRecDepth 20000

namespace Deb2025_14819C

def nullV : Val := .Vlong Integers.Int64.zero

structure CtxB where
  cfV : Val
  mbB : Block
  mbO : Integers.Ptrofs
  cpB : Block                -- Curl_ssl_cf_get_primary_config(cf) の戻り値（conn_config）
  cpO : Integers.Ptrofs
  cfgB : Block               -- ssl_config（この関数は読まない。性質を述べるためだけに所有に入れる）
  cfgO : Integers.Ptrofs
  cfgWord : Integers.Int
  pm : Permission

def HB (c : CtxB) : HProp :=
  mapsto Mptr c.pm c.mbB (addr c.mbO 0) nullV ∗
  (mapsto Mptr c.pm c.cpB (addr c.cpO 0) nullV ∗
   mapsto .Mint32 c.pm c.cfgB (addr c.cfgO 0) (.Vint c.cfgWord))

def coOfB (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_shareB : prog.prog_comp_env.get _ossl_x509_share = some (coOfB _ossl_x509_share) := rfl
theorem co_pcB : prog.prog_comp_env.get _ssl_primary_config = some (coOfB _ssl_primary_config) := rfl
theorem off_ca_share : fieldOffset prog.prog_comp_env _CAfile (coOfB _ossl_x509_share).co_members
    = .OK (0, .Full) := by decide
theorem off_ca_pc : fieldOffset prog.prog_comp_env _CAfile (coOfB _ssl_primary_config).co_members
    = .OK (0, .Full) := by decide

def getSpecB (cp : Val) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_cfilter noattr)]
  tyres := tptr (Ty.Tstruct _ssl_primary_config noattr)
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun v hp => v = cp ∧ emp hp
  measure := fun _ => 0

def dfSpecB (c : CtxB) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_cfilter noattr), tptr (Ty.Tstruct _ossl_x509_share noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [c.cfV, .Vptr c.mbB c.mbO] ∧ HB c hp
  post := fun v hp => v = .Vint Integers.Int.zero ∧ HB c hp
  measure := fun _ => 0

theorem dfB_entry_wf :
    listNorepet (varNames f_ossl_cached_x509_store_different.fn_vars)
    ∧ listNorepet (varNames f_ossl_cached_x509_store_different.fn_params)
    ∧ listDisjoint (varNames f_ossl_cached_x509_store_different.fn_params)
        (varNames f_ossl_cached_x509_store_different.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem load_null {pm : Permission} {b : Block} {o : Z} {h : Heap} {m : Mem}
    (hpr : permOrder pm .Readable = true) (hm : mapsto Mptr pm b o nullV h) (hag : Heap.Agrees h m) :
    Mem.load Mptr m b o = some nullV := by
  rw [mapsto_load hpr hm hag]; rfl

theorem different_before (ge : CGenv) (c : CtxB)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hcf : IsPtr c.cfV)
    (bGet : Block) (fdGet : FunDef)
    (hsGet : Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_primary_config = some bGet)
    (hfGet : FuncPtr ge bGet fdGet)
    (htyGet : typeOfFundef fdGet = .Tfunction (getSpecB (.Vptr c.cpB c.cpO)).tyargs
      (getSpecB (.Vptr c.cpB c.cpO)).tyres (getSpecB (.Vptr c.cpB c.cpO)).cc)
    (hGet : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpecB (.Vptr c.cpB c.cpO)) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_ossl_cached_x509_store_different)
      (dfSpecB c) vs := by
  by_cases hvs : vs = [c.cfV, .Vptr c.mbB c.mbO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := dfB_entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_ossl_cached_x509_store_different _ _
    (LocalSt emptyEnv [(_mb, .Vptr c.mbB c.mbO), (_cf, c.cfV)] (HB c)) (fun m => ?_) ?_
  · refine ⟨PTree.set _mb (.Vptr c.mbB c.mbO)
              (PTree.set _cf c.cfV (createUndefTemps f_ossl_cached_x509_store_different.fn_temps)),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_nil _)), hpre.2⟩
    exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
  have hmbL : ∀ hp m, HB c hp → Heap.Agrees hp m → Mem.load Mptr m c.mbB (addr c.mbO 0) = some nullV :=
    fun hp m hH hag => by obtain ⟨h1, c1, a1⟩ := sep_l hH hag; exact load_null hpr c1 a1
  have hcpL : ∀ hp m, HB c hp → Heap.Agrees hp m → Mem.load Mptr m c.cpB (addr c.cpO 0) = some nullV :=
    fun hp m hH hag => by
      obtain ⟨r1, d1, b1⟩ := sep_r hH hag
      obtain ⟨h2, c2, a2⟩ := sep_l d1 b1
      exact load_null hpr c2 a2
  -- conn_config = Curl_ssl_cf_get_primary_config(cf);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (getSpecB (.Vptr c.cpB c.cpO)) _t'1 _ _ emptyEnv _ emp (HB c) emp (HB c) (HB c)
        [c.cfV] (.Vptr c.cpB c.cpO) bGet fdGet hGet hfGet htyGet rfl
        (fun _ _ _ => eval_callee_global rfl hsGet rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ c.cfV (hT.get (by temps_get))) (cast_ptr hcf _ _ m)
          EvalExprlist.nil)
        (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
      (triple_set_local_fwd ge _ _ emptyEnv _ (HB c) _conn_config _ (.Vptr c.cpB c.cpO)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  -- t'9 = mb->CAfile; if (!t'9) t'3 = 1; else ...; if (t'3) { ... return t'7 != t'8; }
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ emptyEnv _ (HB c) _t'8 _ nullV
        (fun le m hp hT hH hag => Case5C.eval_field (b := c.mbB) (o := c.mbO)
          (hT.get (by temps_get)) (hcenv ▸ co_shareB) (hcenv ▸ off_ca_share) rfl (hmbL hp m hH hag)))
      (triple_if_local ge _ _ emptyEnv _ (HB c) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
            rfl, boolVal_ofBool_tint true m⟩)
        (triple_set_local_fwd ge _ _ emptyEnv _ (HB c) _t'2 _ (.Vint (Integers.Int.repr 1))
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)))) ?_
  refine triple_if_local ge _ _ emptyEnv _ (HB c) _ true _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
  rw [if_pos rfl]
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (HB c) _t'6 _ nullV
      (fun le m hp hT hH hag => Case5C.eval_field (b := c.mbB) (o := c.mbO)
        (hT.get (by temps_get)) (hcenv ▸ co_shareB) (hcenv ▸ off_ca_share) rfl (hmbL hp m hH hag))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (HB c) _t'7 _ nullV
      (fun le m hp hT hH hag => Case5C.eval_field (b := c.cpB) (o := c.cpO)
        (hT.get (by temps_get)) (hcenv ▸ co_pcB) (hcenv ▸ off_ca_pc) rfl (hcpL hp m hH hag))) ?_
  refine triple_conseq ge _ _
    (triple_return_local ge _ _ _ (HB c) _ _ (.Vint Integers.Int.zero) (.Vint Integers.Int.zero)
      (fun le m hp hT _ _ => EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
        rfl)
      (fun _ => rfl) (fun hp hH => ⟨rfl, hH⟩))
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

/-! ## 前提を満たす具体的なメモリ（1つのブロック、24 バイト）

  オフセット  中身
   0  mb->CAfile = NULL
   8  conn_config->CAfile = NULL
  16  ssl_config の no_partialchain を入れた単位 = 1（部分的な鎖を禁じる）
-/

def bwB : Block := Mem.empty.nextblock
def m0B : Mem := (Mem.alloc Mem.empty 0 24).1

def storesB : Option Mem := do
  let m ← Mem.store Mptr m0B bwB 0 nullV
  let m ← Mem.store Mptr m bwB 8 nullV
  Mem.store .Mint32 m bwB 16 (.Vint (Integers.Int.repr 1))

theorem storesB_isSome : storesB.isSome = true := by decide

def mWB : Mem := storesB.get storesB_isSome

def cWB : CtxB where
  cfV := nullV
  mbB := bwB
  mbO := Integers.Ptrofs.repr 0
  cpB := bwB
  cpO := Integers.Ptrofs.repr 8
  cfgB := bwB
  cfgO := Integers.Ptrofs.repr 16
  cfgWord := Integers.Int.repr 1
  pm := .Freeable

theorem cWB_cells : addr cWB.mbO 0 = 0 ∧ addr cWB.cpO 0 = 8 ∧ addr cWB.cfgO 0 = 16 := by decide

theorem HB_cWB_satisfiable : ∃ hp, HB cWB hp ∧ Heap.Agrees hp mWB := by
  obtain ⟨a0, a8, a16⟩ := cWB_cells
  obtain ⟨h1, m1, g1⟩ := cell (chunk := Mptr) (b := bwB) (ofs := 0) (v := nullV) (m := mWB)
    (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := cell (chunk := Mptr) (b := bwB) (ofs := 8) (v := nullV) (m := mWB)
    (by decide) (by decide)
  obtain ⟨h3, m3, g3⟩ := cell (chunk := .Mint32) (b := bwB) (ofs := 16)
    (v := .Vint (Integers.Int.repr 1)) (m := mWB) (by decide) (by decide)
  have d23 := mapsto_disj m2 m3 (by decide)
  have d1 : Heap.disjoint h1 (Heap.union h2 h3) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m2 (by decide), mapsto_disj m1 m3 (by decide)⟩
  refine ⟨_, ?_, agrees_union g1 (agrees_union g2 g3)⟩
  unfold HB
  rw [a0, a8, a16]
  exact ⟨_, _, d1, rfl, m1, _, _, d23, rfl, m2, m3⟩

/-- **P0（C）: 修正前の関数には、部分的な鎖を禁じた設定でもキャッシュを使う入力がある。**

    `mb->CAfile`・`conn_config->CAfile` がともに NULL（既定の CA）で、`ssl_config->no_partialchain` が 1 の状態（`cWB`、`mWB`）で、
    戻り値は FALSE（キャッシュの CA ストアを使う）。修正前の `struct ossl_x509_share` には、ストアを作ったときの設定が無い。 -/
theorem P0_C :
    ∃ c : CtxB, (∃ hp m, HB c hp ∧ Heap.Agrees hp m) ∧ permOrder c.pm .Readable = true ∧ IsPtr c.cfV
      ∧ bitOf c.cfgWord 0 = true
      ∧ ∀ (ge : CGenv) (bGet : Block) (fdGet : FunDef),
          ge.genv_cenv = prog.prog_comp_env →
          Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_primary_config = some bGet →
          FuncPtr ge bGet fdGet →
          typeOfFundef fdGet = .Tfunction (getSpecB (.Vptr c.cpB c.cpO)).tyargs
            (getSpecB (.Vptr c.cpB c.cpO)).tyres (getSpecB (.Vptr c.cpB c.cpO)).cc →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpecB (.Vptr c.cpB c.cpO)) vs) →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_ossl_cached_x509_store_different)
            (dfSpecB c) vs := by
  obtain ⟨hp, hH, hag⟩ := HB_cWB_satisfiable
  refine ⟨cWB, ⟨hp, mWB, hH, hag⟩, rfl, Or.inr ⟨_, rfl⟩, by decide, ?_⟩
  intro ge bGet fdGet hcenv hsGet hfGet htyGet hGet vs
  exact different_before ge cWB hcenv rfl (Or.inr ⟨_, rfl⟩) bGet fdGet hsGet hfGet htyGet hGet vs

end Deb2025_14819C

#print axioms Deb2025_14819C.different_before
#print axioms Deb2025_14819C.P0_C
#print axioms Deb2025_14819C.HB_cWB_satisfiable
