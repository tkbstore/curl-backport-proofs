/-
CVE-2025-14819 bookworm: Debian のバックポート（D1: curl 7.88.1 に CVE-2025-14819.patch を当てたもの）の `cached_x509_store_different` の上の P1。

trixie の件の `Deb2025_14819C.different_after`（上流の修正後）の証明を写したもの。7.88.1 では構造体の名前（`multi_ssl_backend_data`）と
関数の名前（`cached_x509_store_different`）が違い、`CURL_UNCONST(data)`（3段のキャスト）が `(struct Curl_easy *)data`（1段）になっている。
そのため関数の構文木は上流のものと同じにならず、等式での書き換えはできない。証明の形は同じで、違うのはその3点に当たる行だけ。
-/
import GenDebBookworm2025_14819D1
import Deb2025_14819After
open CC CC.Sep CC.HProp
open DebBookworm2025_14819_d1
open Case5C (addr call_fwd RR return_const eval_bitfield bitOf boolVal_ofBool_tint sep_l sep_r)
open Case4debC (IsPtr cast_ptr)

set_option maxRecDepth 20000

namespace DebBookworm2025_14819C
open Deb2025_14819C (Ctx HA getSpec cfgSpec extract_ne cmp_ne)

def coOfD1 (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_mb : prog.prog_comp_env.get _multi_ssl_backend_data = some (coOfD1 _multi_ssl_backend_data) := rfl
theorem co_cfgD1 : prog.prog_comp_env.get _ssl_config_data = some (coOfD1 _ssl_config_data) := rfl
theorem off_npc_mb : fieldOffset prog.prog_comp_env _no_partialchain (coOfD1 _multi_ssl_backend_data).co_members
    = .OK (8, .Bits .I32 .Unsigned 0 1) := by decide
theorem off_npc_cfgD1 : fieldOffset prog.prog_comp_env _no_partialchain (coOfD1 _ssl_config_data).co_members
    = .OK (0, .Bits .I32 .Unsigned 0 1) := by decide

def dfSpecD1 (c : Ctx) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_cfilter noattr), tptr (Ty.Tstruct _Curl_easy noattr),
             tptr (Ty.Tstruct _multi_ssl_backend_data noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [c.cfV, .Vptr c.dataB c.dataO, .Vptr c.mbB c.mbO] ∧ HA c hp
  post := fun v hp => v = .Vint (Integers.Int.repr 1) ∧ HA c hp
  measure := fun _ => 0

theorem dfD1_entry_wf :
    listNorepet (varNames f_cached_x509_store_different.fn_vars)
    ∧ listNorepet (varNames f_cached_x509_store_different.fn_params)
    ∧ listDisjoint (varNames f_cached_x509_store_different.fn_params)
        (varNames f_cached_x509_store_different.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **D1（P1）**: Debian のバックポートを当てた 7.88.1 の関数は、記録された `no_partialchain` と今の設定が違えば真を返す。 -/
theorem P1_D1 (ge : CGenv) (c : Ctx)
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
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_cached_x509_store_different)
      (dfSpecD1 c) vs := by
  by_cases hvs : vs = [c.cfV, .Vptr c.dataB c.dataO, .Vptr c.mbB c.mbO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := dfD1_entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_cached_x509_store_different _ _
    (LocalSt emptyEnv [(_mb, .Vptr c.mbB c.mbO), (_data, .Vptr c.dataB c.dataO), (_cf, c.cfV)] (HA c))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _mb (.Vptr c.mbB c.mbO)
              (PTree.set _data (.Vptr c.dataB c.dataO)
                (PTree.set _cf c.cfV (createUndefTemps f_cached_x509_store_different.fn_temps))),
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
  -- ssl_config = Curl_ssl_cf_get_config(cf, (struct Curl_easy *)data);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (cfgSpec c.cfgB c.cfgO) _t'2 _ _ emptyEnv _ emp (HA c) emp (HA c) (HA c)
        [c.cfV, .Vptr c.dataB c.dataO] (.Vptr c.cfgB c.cfgO) bCfg fdCfg hCfg hfCfg htyCfg rfl
        (fun _ _ _ => eval_callee_global rfl hsCfg rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ c.cfV (hT.get (by temps_get))) (cast_ptr hcf _ _ m)
          (EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Ecast _ _ _ _
              (EvalExpr.Etempvar _ _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))) rfl)
            rfl EvalExprlist.nil))
        (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
      (triple_set_local_fwd ge _ _ emptyEnv _ (HA c) _ssl_config _ (.Vptr c.cfgB c.cfgO)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  -- t'11 = mb->no_partialchain; t'12 = ssl_config->no_partialchain; if (t'11 != t'12) return true;
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (HA c) _t'11 _
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.mbWord))
      (fun le m hp hT hH hag => eval_bitfield (b := c.mbB) (o := c.mbO) (hT.get (by temps_get)) (hcenv ▸ co_mb)
        (hcenv ▸ off_npc_mb) (by decide) (by decide)
        (by obtain ⟨h1, c1, a1⟩ := sep_l hH hag; exact mapsto_load hpr c1 a1))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (HA c) _t'12 _
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.cfgWord))
      (fun le m hp hT hH hag => eval_bitfield (b := c.cfgB) (o := c.cfgO) (hT.get (by temps_get)) (hcenv ▸ co_cfgD1)
        (hcenv ▸ off_npc_cfgD1) (by decide) (by decide)
        (by obtain ⟨h1, c1, a1⟩ := sep_r hH hag; exact mapsto_load hpr c1 a1))) ?_
  refine triple_if_local ge _ _ emptyEnv _ (HA c) _ true _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (cmp_ne _ _ _ m),
      by rw [extract_ne hne]; exact boolVal_ofBool_tint true m⟩) ?_
  rw [if_pos rfl]
  exact return_const ge _ _ _ _ _ _ _ (.Vint (Integers.Int.repr 1)) (fun _ => rfl)
    (fun hp hH => ⟨rfl, hH⟩)

end DebBookworm2025_14819C

#print axioms DebBookworm2025_14819C.P1_D1
#check @DebBookworm2025_14819C.P1_D1
