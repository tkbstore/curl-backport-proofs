/-
CVE-2025-14819: 上流の修正後（cd046f6c93）の `ossl_cached_x509_store_different`（U1）。

証明すること（`different_after`、P1）: `mb->no_partialchain` と `ssl_config->no_partialchain` が違えば、戻り値は TRUE（1）。
CA ファイルの名前（`CAfile`）は読まれない。
-/
import GenDeb2025_14819UpAfter
import Case5Common
import Case4debCommon
open CC CC.Sep CC.HProp
open Deb2025_14819_up_after
open Case5C (addr call_fwd RR return_const eval_bitfield bitOf boolVal_ofBool_tint sep_l sep_r)
open Case4debC (IsPtr cast_ptr)

set_option maxRecDepth 20000

namespace Deb2025_14819C

/-- 関数が読むメモリと、外部関数の戻り値。 -/
structure Ctx where
  cfV : Val                  -- cf（外部関数に渡すだけ）
  dataB : Block              -- data
  dataO : Integers.Ptrofs
  mbB : Block                -- mb
  mbO : Integers.Ptrofs
  cfgB : Block               -- Curl_ssl_cf_get_config(cf, data) の戻り値（ssl_config）
  cfgO : Integers.Ptrofs
  cpV : Val                  -- Curl_ssl_cf_get_primary_config(cf) の戻り値（この経路では読まない）
  mbWord : Integers.Int      -- mb->no_partialchain を入れた 32 bit の単位（オフセット 8）
  cfgWord : Integers.Int     -- ssl_config->no_partialchain を入れた 32 bit の単位（オフセット 0）
  pm : Permission

def HA (c : Ctx) : HProp :=
  mapsto .Mint32 c.pm c.mbB (addr c.mbO 8) (.Vint c.mbWord) ∗
  mapsto .Mint32 c.pm c.cfgB (addr c.cfgO 0) (.Vint c.cfgWord)

/-! ## 構造体のレイアウト -/

def coOf (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_share : prog.prog_comp_env.get _ossl_x509_share = some (coOf _ossl_x509_share) := rfl
theorem co_cfg : prog.prog_comp_env.get _ssl_config_data = some (coOf _ssl_config_data) := rfl
theorem off_npc_share : fieldOffset prog.prog_comp_env _no_partialchain (coOf _ossl_x509_share).co_members
    = .OK (8, .Bits .I32 .Unsigned 0 1) := by decide
theorem off_npc_cfg : fieldOffset prog.prog_comp_env _no_partialchain (coOf _ssl_config_data).co_members
    = .OK (0, .Bits .I32 .Unsigned 0 1) := by decide

/-! ## 外部関数の仕様（どれもメモリを変えない） -/

/-- `Curl_ssl_cf_get_primary_config(cf)` は `cp` を返す。 -/
def getSpec (cp : Val) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_cfilter noattr)]
  tyres := tptr (Ty.Tstruct _ssl_primary_config noattr)
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun v hp => v = cp ∧ emp hp
  measure := fun _ => 0

/-- `Curl_ssl_cf_get_config(cf, data)` は `ssl_config` を指すポインタを返す。 -/
def cfgSpec (b : Block) (o : Integers.Ptrofs) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_cfilter noattr), tptr (Ty.Tstruct _Curl_easy noattr)]
  tyres := tptr (Ty.Tstruct _ssl_config_data noattr)
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun v hp => v = .Vptr b o ∧ emp hp
  measure := fun _ => 0

def dfSpecA (c : Ctx) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_cfilter noattr), tptr (Ty.Tstruct _Curl_easy noattr),
             tptr (Ty.Tstruct _ossl_x509_share noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [c.cfV, .Vptr c.dataB c.dataO, .Vptr c.mbB c.mbO] ∧ HA c hp
  post := fun v hp => v = .Vint (Integers.Int.repr 1) ∧ HA c hp
  measure := fun _ => 0

theorem df_entry_wf :
    listNorepet (varNames f_ossl_cached_x509_store_different.fn_vars)
    ∧ listNorepet (varNames f_ossl_cached_x509_store_different.fn_params)
    ∧ listDisjoint (varNames f_ossl_cached_x509_store_different.fn_params)
        (varNames f_ossl_cached_x509_store_different.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- 2つのビットが違えば、取り出した値も違う。 -/
theorem extract_ne {a b : Integers.Int} (h : bitOf a 0 ≠ bitOf b 0) :
    Integers.Int.eq (Cop.bitfieldExtract .I32 .Unsigned 0 1 a)
      (Cop.bitfieldExtract .I32 .Unsigned 0 1 b) = false := by
  cases he : Integers.Int.eq (Cop.bitfieldExtract .I32 .Unsigned 0 1 a)
      (Cop.bitfieldExtract .I32 .Unsigned 0 1 b)
  · rfl
  · exfalso; apply h
    have : Cop.bitfieldExtract .I32 .Unsigned 0 1 a = Cop.bitfieldExtract .I32 .Unsigned 0 1 b := by
      simpa [Integers.Int.eq, Integers.MI.eq] using he
    simp only [bitOf, this]

theorem cmp_ne (ce : CompositeEnv) (x y : Integers.Int) (m : Mem) :
    Cop.semBinaryOperation ce .One (.Vint x) tint (.Vint y) tint m
      = some (Val.ofBool (!Integers.Int.eq x y)) := rfl

theorem different_after (ge : CGenv) (c : Ctx)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hcf : IsPtr c.cfV)
    (hne : bitOf c.mbWord 0 ≠ bitOf c.cfgWord 0)
    (bGet bCfg : Block) (fdGet fdCfg : FunDef)
    (hsGet : Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_primary_config = some bGet)
    (hsCfg : Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_config = some bCfg)
    (hfGet : FuncPtr ge bGet fdGet) (hfCfg : FuncPtr ge bCfg fdCfg)
    (htyGet : typeOfFundef fdGet = .Tfunction (getSpec c.cpV).tyargs (getSpec c.cpV).tyres
      (getSpec c.cpV).cc)
    (htyCfg : typeOfFundef fdCfg = .Tfunction (cfgSpec c.cfgB c.cfgO).tyargs
      (cfgSpec c.cfgB c.cfgO).tyres (cfgSpec c.cfgB c.cfgO).cc)
    (hGet : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpec c.cpV) vs)
    (hCfg : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCfg (cfgSpec c.cfgB c.cfgO) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_ossl_cached_x509_store_different)
      (dfSpecA c) vs := by
  by_cases hvs : vs = [c.cfV, .Vptr c.dataB c.dataO, .Vptr c.mbB c.mbO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := df_entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_ossl_cached_x509_store_different _ _
    (LocalSt emptyEnv [(_mb, .Vptr c.mbB c.mbO), (_data, .Vptr c.dataB c.dataO), (_cf, c.cfV)] (HA c))
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
  -- conn_config = Curl_ssl_cf_get_primary_config(cf);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (getSpec c.cpV) _t'1 _ _ emptyEnv _ emp (HA c) emp (HA c) (HA c)
        [c.cfV] c.cpV bGet fdGet hGet hfGet htyGet rfl
        (fun _ _ _ => eval_callee_global rfl hsGet rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ c.cfV (hT.get (by temps_get))) (cast_ptr hcf _ _ m)
          EvalExprlist.nil)
        (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
      (triple_set_local_fwd ge _ _ emptyEnv _ (HA c) _conn_config _ c.cpV
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  -- ssl_config = Curl_ssl_cf_get_config(cf, CURL_UNCONST(data));
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (cfgSpec c.cfgB c.cfgO) _t'2 _ _ emptyEnv _ emp (HA c) emp (HA c) (HA c)
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
      (triple_set_local_fwd ge _ _ emptyEnv _ (HA c) _ssl_config _ (.Vptr c.cfgB c.cfgO)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  -- t'11 = mb->no_partialchain; t'12 = ssl_config->no_partialchain; if (t'11 != t'12) return TRUE;
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (HA c) _t'11 _
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.mbWord))
      (fun le m hp hT hH hag => eval_bitfield (b := c.mbB) (o := c.mbO) (hT.get (by temps_get)) (hcenv ▸ co_share)
        (hcenv ▸ off_npc_share) (by decide) (by decide)
        (by obtain ⟨h1, c1, a1⟩ := sep_l hH hag; exact mapsto_load hpr c1 a1))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (HA c) _t'12 _
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.cfgWord))
      (fun le m hp hT hH hag => eval_bitfield (b := c.cfgB) (o := c.cfgO) (hT.get (by temps_get)) (hcenv ▸ co_cfg)
        (hcenv ▸ off_npc_cfg) (by decide) (by decide)
        (by obtain ⟨h1, c1, a1⟩ := sep_r hH hag; exact mapsto_load hpr c1 a1))) ?_
  refine triple_if_local ge _ _ emptyEnv _ (HA c) _ true _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (cmp_ne _ _ _ m),
      by rw [extract_ne hne]; exact boolVal_ofBool_tint true m⟩) ?_
  rw [if_pos rfl]
  exact return_const ge _ _ _ _ _ _ _ (.Vint (Integers.Int.repr 1)) (fun _ => rfl)
    (fun hp hH => ⟨rfl, hH⟩)

end Deb2025_14819C

#print axioms Deb2025_14819C.different_after
