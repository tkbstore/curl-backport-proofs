/-
CVE-2025-14819: P0 を修正後の関数（U1・D1）の上で述べ直して証明する（PROTOCOL-auto §3.10 の確かめ）。

P0（`Deb2025_14819Before.lean` の `P0_C`）は「`mb->CAfile`・`conn_config->CAfile` がともに NULL で、`ssl_config->no_partialchain` が 1 の
入力があって、戻り値は FALSE（キャッシュを使う）」と述べる。修正後の関数にだけある引数（`data`）とメモリ（`mb->no_partialchain`）は
∃ の側に入れて述べ直す。ここでは `mb->no_partialchain` も 1 を選ぶと、修正後の関数も FALSE を返す。
つまり P0 は修正後の関数でも成り立ち、修正の前と後を見分けない。
-/
import GenDeb2025_14819UpAfter
import GenDeb2025_14819DebAfter
import Case5Witness
import Case4debCommon
import Deb2025_14819After
open CC CC.Sep CC.HProp
open Deb2025_14819_up_after
open Case5C (addr call_fwd RR boolVal_ofBool_tint sep_l sep_r eval_bitfield bitOf cell mapsto_disj
  agrees_union)
open Case4debC (IsPtr cast_ptr)

set_option maxRecDepth 20000

namespace Deb2025_14819X
open Deb2025_14819C (getSpec cfgSpec co_share co_cfg off_npc_share off_npc_cfg df_entry_wf cmp_ne coOf)

def nullV : Val := .Vlong Integers.Int64.zero

/-- 修正後の関数が読むメモリ。P0 の `CtxB` に、修正後にだけある `data` と `mb->no_partialchain` を足したもの。 -/
structure CtxX where
  cfV : Val
  dataB : Block
  dataO : Integers.Ptrofs
  mbB : Block
  mbO : Integers.Ptrofs
  cpB : Block
  cpO : Integers.Ptrofs
  cfgB : Block
  cfgO : Integers.Ptrofs
  mbWord : Integers.Int      -- mb->no_partialchain を入れた単位（オフセット 8）
  cfgWord : Integers.Int     -- ssl_config->no_partialchain を入れた単位（オフセット 0）
  pm : Permission

def HX (c : CtxX) : HProp :=
  mapsto Mptr c.pm c.mbB (addr c.mbO 0) nullV ∗
  (mapsto .Mint32 c.pm c.mbB (addr c.mbO 8) (.Vint c.mbWord) ∗
  (mapsto Mptr c.pm c.cpB (addr c.cpO 0) nullV ∗
   mapsto .Mint32 c.pm c.cfgB (addr c.cfgO 0) (.Vint c.cfgWord)))

theorem off_ca_share : fieldOffset prog.prog_comp_env _CAfile (coOf _ossl_x509_share).co_members
    = .OK (0, .Full) := by decide
theorem co_pc : prog.prog_comp_env.get _ssl_primary_config = some (coOf _ssl_primary_config) := rfl
theorem off_ca_pc : fieldOffset prog.prog_comp_env _CAfile (coOf _ssl_primary_config).co_members
    = .OK (0, .Full) := by decide

/-- 事後条件は P0 と同じ（戻り値は FALSE）。 -/
def dfSpecX (c : CtxX) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_cfilter noattr), tptr (Ty.Tstruct _Curl_easy noattr),
             tptr (Ty.Tstruct _ossl_x509_share noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [c.cfV, .Vptr c.dataB c.dataO, .Vptr c.mbB c.mbO] ∧ HX c hp
  post := fun v hp => v = .Vint Integers.Int.zero ∧ HX c hp
  measure := fun _ => 0

theorem load_null {pm : Permission} {b : Block} {o : Z} {h : Heap} {m : Mem}
    (hpr : permOrder pm .Readable = true) (hm : mapsto Mptr pm b o nullV h) (hag : Heap.Agrees h m) :
    Mem.load Mptr m b o = some nullV := by
  rw [mapsto_load hpr hm hag]; rfl

theorem eq_self (a : Integers.Int) : Integers.Int.eq a a = true := by
  simp [Integers.Int.eq, Integers.MI.eq]

/-- 記録と今の設定が等しく、CA ファイルがどちらも NULL なら、修正後の関数も FALSE を返す。 -/
theorem same_after (ge : CGenv) (c : CtxX)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hcf : IsPtr c.cfV)
    (heq : c.mbWord = c.cfgWord)
    (bGet bCfg : Block) (fdGet fdCfg : FunDef)
    (hsGet : Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_primary_config = some bGet)
    (hsCfg : Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_config = some bCfg)
    (hfGet : FuncPtr ge bGet fdGet) (hfCfg : FuncPtr ge bCfg fdCfg)
    (htyGet : typeOfFundef fdGet = .Tfunction (getSpec (.Vptr c.cpB c.cpO)).tyargs
      (getSpec (.Vptr c.cpB c.cpO)).tyres (getSpec (.Vptr c.cpB c.cpO)).cc)
    (htyCfg : typeOfFundef fdCfg = .Tfunction (cfgSpec c.cfgB c.cfgO).tyargs
      (cfgSpec c.cfgB c.cfgO).tyres (cfgSpec c.cfgB c.cfgO).cc)
    (hGet : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpec (.Vptr c.cpB c.cpO)) vs)
    (hCfg : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCfg (cfgSpec c.cfgB c.cfgO) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_ossl_cached_x509_store_different)
      (dfSpecX c) vs := by
  by_cases hvs : vs = [c.cfV, .Vptr c.dataB c.dataO, .Vptr c.mbB c.mbO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := df_entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_ossl_cached_x509_store_different _ _
    (LocalSt emptyEnv [(_mb, .Vptr c.mbB c.mbO), (_data, .Vptr c.dataB c.dataO), (_cf, c.cfV)] (HX c))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _mb (.Vptr c.mbB c.mbO)
              (PTree.set _data (.Vptr c.dataB c.dataO)
                (PTree.set _cf c.cfV (createUndefTemps f_ossl_cached_x509_store_different.fn_temps))),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_cons ?_
      (TempsHold_nil _))), hpre.2⟩
    · exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
    · exact (PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans
        (PTree.gss _ _ _))
  have hmbCA : ∀ hp m, HX c hp → Heap.Agrees hp m → Mem.load Mptr m c.mbB (addr c.mbO 0) = some nullV :=
    fun hp m hH hag => by obtain ⟨h1, c1, a1⟩ := sep_l hH hag; exact load_null hpr c1 a1
  have hmbW : ∀ hp m, HX c hp → Heap.Agrees hp m →
      Mem.load .Mint32 m c.mbB (addr c.mbO 8) = some (.Vint c.mbWord) :=
    fun hp m hH hag => by
      obtain ⟨r1, d1, b1⟩ := sep_r hH hag
      obtain ⟨h2, c2, a2⟩ := sep_l d1 b1
      exact mapsto_load hpr c2 a2
  have hcpCA : ∀ hp m, HX c hp → Heap.Agrees hp m → Mem.load Mptr m c.cpB (addr c.cpO 0) = some nullV :=
    fun hp m hH hag => by
      obtain ⟨r1, d1, b1⟩ := sep_r hH hag
      obtain ⟨r2, d2, b2⟩ := sep_r d1 b1
      obtain ⟨h3, c3, a3⟩ := sep_l d2 b2
      exact load_null hpr c3 a3
  have hcfgW : ∀ hp m, HX c hp → Heap.Agrees hp m →
      Mem.load .Mint32 m c.cfgB (addr c.cfgO 0) = some (.Vint c.cfgWord) :=
    fun hp m hH hag => by
      obtain ⟨r1, d1, b1⟩ := sep_r hH hag
      obtain ⟨r2, d2, b2⟩ := sep_r d1 b1
      obtain ⟨h4, c4, a4⟩ := sep_r d2 b2
      exact mapsto_load hpr c4 a4
  -- conn_config = Curl_ssl_cf_get_primary_config(cf);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (getSpec (.Vptr c.cpB c.cpO)) _t'1 _ _ emptyEnv _ emp (HX c) emp (HX c) (HX c)
        [c.cfV] (.Vptr c.cpB c.cpO) bGet fdGet hGet hfGet htyGet rfl
        (fun _ _ _ => eval_callee_global rfl hsGet rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ c.cfV (hT.get (by temps_get))) (cast_ptr hcf _ _ m)
          EvalExprlist.nil)
        (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
      (triple_set_local_fwd ge _ _ emptyEnv _ (HX c) _conn_config _ (.Vptr c.cpB c.cpO)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  -- ssl_config = Curl_ssl_cf_get_config(cf, CURL_UNCONST(data));
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (cfgSpec c.cfgB c.cfgO) _t'2 _ _ emptyEnv _ emp (HX c) emp (HX c) (HX c)
        [c.cfV, .Vptr c.dataB c.dataO] (.Vptr c.cfgB c.cfgO) bCfg fdCfg hCfg hfCfg htyCfg rfl
        (fun _ _ _ => eval_callee_global rfl hsCfg rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ c.cfV (hT.get (by temps_get))) (cast_ptr hcf _ _ m)
          (EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Ecast _ _ _ _
              (EvalExpr.Ecast _ _ _ _
                (EvalExpr.Ecast _ _ _ _
                  (EvalExpr.Etempvar _ _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))) rfl)
                rfl) rfl)
            rfl EvalExprlist.nil))
        (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
      (triple_set_local_fwd ge _ _ emptyEnv _ (HX c) _ssl_config _ (.Vptr c.cfgB c.cfgO)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  -- t'11 = mb->no_partialchain; t'12 = ssl_config->no_partialchain; if (t'11 != t'12) …（等しいので抜ける）
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ emptyEnv _ (HX c) _t'11 _
        (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.mbWord))
        (fun le m hp hT hH hag => eval_bitfield (b := c.mbB) (o := c.mbO) (hT.get (by temps_get))
          (hcenv ▸ co_share) (hcenv ▸ off_npc_share) (by decide) (by decide) (hmbW hp m hH hag)))
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ (HX c) _t'12 _
          (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.cfgWord))
          (fun le m hp hT hH hag => eval_bitfield (b := c.cfgB) (o := c.cfgO) (hT.get (by temps_get))
            (hcenv ▸ co_cfg) (hcenv ▸ off_npc_cfg) (by decide) (by decide) (hcfgW hp m hH hag)))
        (triple_if_local ge _ _ emptyEnv _ (HX c) _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
              (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (cmp_ne _ _ _ m),
            by rw [heq, eq_self]; exact boolVal_ofBool_tint false m⟩)
          (triple_skip ge _ _ _)))) ?_
  -- t'9 = mb->CAfile; if (!t'9) t'3 = 1; else …; if (t'3) { return t'7 != t'8; }
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ emptyEnv _ (HX c) _t'9 _ nullV
        (fun le m hp hT hH hag => Case5C.eval_field (b := c.mbB) (o := c.mbO)
          (hT.get (by temps_get)) (hcenv ▸ co_share) (hcenv ▸ off_ca_share) rfl (hmbCA hp m hH hag)))
      (triple_if_local ge _ _ emptyEnv _ (HX c) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
            rfl, boolVal_ofBool_tint true m⟩)
        (triple_set_local_fwd ge _ _ emptyEnv _ (HX c) _t'3 _ (.Vint (Integers.Int.repr 1))
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)))) ?_
  refine triple_if_local ge _ _ emptyEnv _ (HX c) _ true _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
  rw [if_pos rfl]
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (HX c) _t'7 _ nullV
      (fun le m hp hT hH hag => Case5C.eval_field (b := c.mbB) (o := c.mbO)
        (hT.get (by temps_get)) (hcenv ▸ co_share) (hcenv ▸ off_ca_share) rfl (hmbCA hp m hH hag))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (HX c) _t'8 _ nullV
      (fun le m hp hT hH hag => Case5C.eval_field (b := c.cpB) (o := c.cpO)
        (hT.get (by temps_get)) (hcenv ▸ co_pc) (hcenv ▸ off_ca_pc) rfl (hcpCA hp m hH hag))) ?_
  refine triple_conseq ge _ _
    (triple_return_local ge _ _ _ (HX c) _ _ (.Vint Integers.Int.zero) (.Vint Integers.Int.zero)
      (fun le m hp hT _ _ => EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
        rfl)
      (fun _ => rfl) (fun hp hH => ⟨rfl, hH⟩))
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

/-! ## 前提を満たす具体的なメモリ（1つのブロック、32 バイト）

  オフセット  中身
   0  mb->CAfile = NULL
   8  mb->no_partialchain を入れた単位 = 1（∃ の側で選ぶ）
  16  conn_config->CAfile = NULL
  24  ssl_config の no_partialchain を入れた単位 = 1（部分的な鎖を禁じる）
-/

def bwX : Block := Mem.empty.nextblock
def m0X : Mem := (Mem.alloc Mem.empty 0 32).1

def storesX : Option Mem := do
  let m ← Mem.store Mptr m0X bwX 0 nullV
  let m ← Mem.store .Mint32 m bwX 8 (.Vint (Integers.Int.repr 1))
  let m ← Mem.store Mptr m bwX 16 nullV
  Mem.store .Mint32 m bwX 24 (.Vint (Integers.Int.repr 1))

theorem storesX_isSome : storesX.isSome = true := by decide

def mWX : Mem := storesX.get storesX_isSome

def cWX : CtxX where
  cfV := nullV
  dataB := bwX
  dataO := Integers.Ptrofs.repr 0
  mbB := bwX
  mbO := Integers.Ptrofs.repr 0
  cpB := bwX
  cpO := Integers.Ptrofs.repr 16
  cfgB := bwX
  cfgO := Integers.Ptrofs.repr 24
  mbWord := Integers.Int.repr 1
  cfgWord := Integers.Int.repr 1
  pm := .Freeable

theorem cWX_cells : addr cWX.mbO 0 = 0 ∧ addr cWX.mbO 8 = 8 ∧ addr cWX.cpO 0 = 16
    ∧ addr cWX.cfgO 0 = 24 := by decide

theorem HX_cWX_satisfiable : ∃ hp, HX cWX hp ∧ Heap.Agrees hp mWX := by
  obtain ⟨a0, a8, a16, a24⟩ := cWX_cells
  obtain ⟨h1, m1, g1⟩ := cell (chunk := Mptr) (b := bwX) (ofs := 0) (v := nullV) (m := mWX)
    (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := cell (chunk := .Mint32) (b := bwX) (ofs := 8)
    (v := .Vint (Integers.Int.repr 1)) (m := mWX) (by decide) (by decide)
  obtain ⟨h3, m3, g3⟩ := cell (chunk := Mptr) (b := bwX) (ofs := 16) (v := nullV) (m := mWX)
    (by decide) (by decide)
  obtain ⟨h4, m4, g4⟩ := cell (chunk := .Mint32) (b := bwX) (ofs := 24)
    (v := .Vint (Integers.Int.repr 1)) (m := mWX) (by decide) (by decide)
  have d34 := mapsto_disj m3 m4 (by decide)
  have d2 : Heap.disjoint h2 (Heap.union h3 h4) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m3 (by decide), mapsto_disj m2 m4 (by decide)⟩
  have d1 : Heap.disjoint h1 (Heap.union h2 (Heap.union h3 h4)) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m2 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m3 (by decide), mapsto_disj m1 m4 (by decide)⟩⟩
  refine ⟨_, ?_, agrees_union g1 (agrees_union g2 (agrees_union g3 g4))⟩
  unfold HX
  rw [a0, a8, a16, a24]
  exact ⟨_, _, d1, rfl, m1, _, _, d2, rfl, m2, _, _, d34, rfl, m3, m4⟩

/-- **P0 を修正後の関数（U1）で述べ直したもの。成り立つ。**

    `P0_C` と同じく、`mb->CAfile`・`conn_config->CAfile` がともに NULL で `ssl_config->no_partialchain` が 1 の入力で、
    戻り値は FALSE（キャッシュを使う）。修正後にだけある `mb->no_partialchain` は 1 を選んだ。 -/
theorem P0_on_after :
    ∃ c : CtxX, (∃ hp m, HX c hp ∧ Heap.Agrees hp m) ∧ permOrder c.pm .Readable = true ∧ IsPtr c.cfV
      ∧ bitOf c.cfgWord 0 = true
      ∧ ∀ (ge : CGenv) (bGet bCfg : Block) (fdGet fdCfg : FunDef),
          ge.genv_cenv = prog.prog_comp_env →
          Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_primary_config = some bGet →
          Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_config = some bCfg →
          FuncPtr ge bGet fdGet → FuncPtr ge bCfg fdCfg →
          typeOfFundef fdGet = .Tfunction (getSpec (.Vptr c.cpB c.cpO)).tyargs
            (getSpec (.Vptr c.cpB c.cpO)).tyres (getSpec (.Vptr c.cpB c.cpO)).cc →
          typeOfFundef fdCfg = .Tfunction (cfgSpec c.cfgB c.cfgO).tyargs
            (cfgSpec c.cfgB c.cfgO).tyres (cfgSpec c.cfgB c.cfgO).cc →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpec (.Vptr c.cpB c.cpO)) vs) →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCfg (cfgSpec c.cfgB c.cfgO) vs) →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_ossl_cached_x509_store_different)
            (dfSpecX c) vs := by
  obtain ⟨hp, hH, hag⟩ := HX_cWX_satisfiable
  refine ⟨cWX, ⟨hp, mWX, hH, hag⟩, rfl, Or.inr ⟨_, rfl⟩, by decide, ?_⟩
  intro ge bGet bCfg fdGet fdCfg hcenv hsGet hsCfg hfGet hfCfg htyGet htyCfg hGet hCfg vs
  exact same_after ge cWX hcenv rfl (Or.inr ⟨_, rfl⟩) rfl bGet bCfg fdGet fdCfg hsGet hsCfg
    hfGet hfCfg htyGet htyCfg hGet hCfg vs

/-- **D1 でも同じ**（Debian のバックポートを当てた 8.14.1。関数と構造体の環境は U1 と同じ: `Deb2025_14819Deb`）。 -/
theorem P0_on_debian_after :
    ∃ c : CtxX, (∃ hp m, HX c hp ∧ Heap.Agrees hp m) ∧ permOrder c.pm .Readable = true ∧ IsPtr c.cfV
      ∧ bitOf c.cfgWord 0 = true
      ∧ ∀ (ge : CGenv) (bGet bCfg : Block) (fdGet fdCfg : FunDef),
          ge.genv_cenv = Deb2025_14819_deb_after.prog.prog_comp_env →
          Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_primary_config = some bGet →
          Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_config = some bCfg →
          FuncPtr ge bGet fdGet → FuncPtr ge bCfg fdCfg →
          typeOfFundef fdGet = .Tfunction (getSpec (.Vptr c.cpB c.cpO)).tyargs
            (getSpec (.Vptr c.cpB c.cpO)).tyres (getSpec (.Vptr c.cpB c.cpO)).cc →
          typeOfFundef fdCfg = .Tfunction (cfgSpec c.cfgB c.cfgO).tyargs
            (cfgSpec c.cfgB c.cfgO).tyres (cfgSpec c.cfgB c.cfgO).cc →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpec (.Vptr c.cpB c.cpO)) vs) →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCfg (cfgSpec c.cfgB c.cfgO) vs) →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge)
            (.Internal Deb2025_14819_deb_after.f_ossl_cached_x509_store_different) (dfSpecX c) vs := by
  obtain ⟨c, hsat, hpr, hcf, hbit, h⟩ := P0_on_after
  refine ⟨c, hsat, hpr, hcf, hbit, fun ge bGet bCfg fdGet fdCfg hcenv hs1 hs2 hf1 hf2 ht1 ht2 hG hC vs => ?_⟩
  have hfn : Deb2025_14819_deb_after.f_ossl_cached_x509_store_different
      = f_ossl_cached_x509_store_different := rfl
  have hce : Deb2025_14819_deb_after.prog.prog_comp_env = prog.prog_comp_env := rfl
  rw [hfn]
  exact h ge bGet bCfg fdGet fdCfg (hcenv.trans hce) hs1 hs2 hf1 hf2 ht1 ht2 hG hC vs

end Deb2025_14819X

#print axioms Deb2025_14819X.P0_on_after
#print axioms Deb2025_14819X.P0_on_debian_after
