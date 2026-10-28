/-
CVE-2025-14819 bookworm: 修正前（D0: curl 7.88.1。series でこのパッチの前に当たるものは無い）の `cached_x509_store_different` の上の P0。

trixie の件の `Deb2025_14819C.different_before`・`Deb2025_14819C.P0_C`（上流の修正前）の証明を写したもの。7.88.1 では構造体の名前
（`multi_ssl_backend_data`）と関数の名前（`cached_x509_store_different`）が違うので、等式での書き換えはできない。
前提を満たす具体的なメモリ（`cWB`・`mWB`・`HB_cWB_satisfiable`）は構文木によらないので、trixie の件のものを使う。
-/
import GenDebBookworm2025_14819D0
import Deb2025_14819Before
open CC CC.Sep CC.HProp
open DebBookworm2025_14819_d0
open Case5C (addr call_fwd RR return_const boolVal_ofBool_tint sep_l sep_r bitOf)
open Case4debC (IsPtr cast_ptr)

set_option maxRecDepth 20000

namespace DebBookworm2025_14819C
open Deb2025_14819C (nullV CtxB HB getSpecB load_null cWB mWB HB_cWB_satisfiable)

def coOfD0 (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_mbD0 : prog.prog_comp_env.get _multi_ssl_backend_data = some (coOfD0 _multi_ssl_backend_data) := rfl
theorem co_pcD0 : prog.prog_comp_env.get _ssl_primary_config = some (coOfD0 _ssl_primary_config) := rfl
theorem off_ca_mbD0 : fieldOffset prog.prog_comp_env _CAfile (coOfD0 _multi_ssl_backend_data).co_members
    = .OK (0, .Full) := by decide
theorem off_ca_pcD0 : fieldOffset prog.prog_comp_env _CAfile (coOfD0 _ssl_primary_config).co_members
    = .OK (0, .Full) := by decide

def dfSpecD0 (c : CtxB) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_cfilter noattr), tptr (Ty.Tstruct _multi_ssl_backend_data noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [c.cfV, .Vptr c.mbB c.mbO] ∧ HB c hp
  post := fun v hp => v = .Vint Integers.Int.zero ∧ HB c hp
  measure := fun _ => 0

theorem dfD0_entry_wf :
    listNorepet (varNames f_cached_x509_store_different.fn_vars)
    ∧ listNorepet (varNames f_cached_x509_store_different.fn_params)
    ∧ listDisjoint (varNames f_cached_x509_store_different.fn_params)
        (varNames f_cached_x509_store_different.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem different_before_D0 (ge : CGenv) (c : CtxB)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hcf : IsPtr c.cfV)
    (bGet : Block) (fdGet : FunDef)
    (hsGet : Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_primary_config = some bGet)
    (hfGet : FuncPtr ge bGet fdGet)
    (htyGet : typeOfFundef fdGet = .Tfunction (getSpecB (.Vptr c.cpB c.cpO)).tyargs
      (getSpecB (.Vptr c.cpB c.cpO)).tyres (getSpecB (.Vptr c.cpB c.cpO)).cc)
    (hGet : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpecB (.Vptr c.cpB c.cpO)) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_cached_x509_store_different)
      (dfSpecD0 c) vs := by
  by_cases hvs : vs = [c.cfV, .Vptr c.mbB c.mbO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := dfD0_entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_cached_x509_store_different _ _
    (LocalSt emptyEnv [(_mb, .Vptr c.mbB c.mbO), (_cf, c.cfV)] (HB c)) (fun m => ?_) ?_
  · refine ⟨PTree.set _mb (.Vptr c.mbB c.mbO)
              (PTree.set _cf c.cfV (createUndefTemps f_cached_x509_store_different.fn_temps)),
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
          (hT.get (by temps_get)) (hcenv ▸ co_mbD0) (hcenv ▸ off_ca_mbD0) rfl (hmbL hp m hH hag)))
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
        (hT.get (by temps_get)) (hcenv ▸ co_mbD0) (hcenv ▸ off_ca_mbD0) rfl (hmbL hp m hH hag))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (HB c) _t'7 _ nullV
      (fun le m hp hT hH hag => Case5C.eval_field (b := c.cpB) (o := c.cpO)
        (hT.get (by temps_get)) (hcenv ▸ co_pcD0) (hcenv ▸ off_ca_pcD0) rfl (hcpL hp m hH hag))) ?_
  refine triple_conseq ge _ _
    (triple_return_local ge _ _ _ (HB c) _ _ (.Vint Integers.Int.zero) (.Vint Integers.Int.zero)
      (fun le m hp hT _ _ => EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
        rfl)
      (fun _ => rfl) (fun hp hH => ⟨rfl, hH⟩))
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

theorem P0_D0 :
    ∃ c : CtxB, (∃ hp m, HB c hp ∧ Heap.Agrees hp m) ∧ permOrder c.pm .Readable = true ∧ IsPtr c.cfV
      ∧ bitOf c.cfgWord 0 = true
      ∧ ∀ (ge : CGenv) (bGet : Block) (fdGet : FunDef),
          ge.genv_cenv = prog.prog_comp_env →
          Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_primary_config = some bGet →
          FuncPtr ge bGet fdGet →
          typeOfFundef fdGet = .Tfunction (getSpecB (.Vptr c.cpB c.cpO)).tyargs
            (getSpecB (.Vptr c.cpB c.cpO)).tyres (getSpecB (.Vptr c.cpB c.cpO)).cc →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpecB (.Vptr c.cpB c.cpO)) vs) →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_cached_x509_store_different)
            (dfSpecD0 c) vs := by
  obtain ⟨hp, hH, hag⟩ := HB_cWB_satisfiable
  refine ⟨cWB, ⟨hp, mWB, hH, hag⟩, rfl, Or.inr ⟨_, rfl⟩, by decide, ?_⟩
  intro ge bGet fdGet hcenv hsGet hfGet htyGet hGet vs
  exact different_before_D0 ge cWB hcenv rfl (Or.inr ⟨_, rfl⟩) bGet fdGet hsGet hfGet htyGet hGet vs

end DebBookworm2025_14819C

#print axioms DebBookworm2025_14819C.different_before_D0
#print axioms DebBookworm2025_14819C.P0_D0
#check @DebBookworm2025_14819C.P0_D0
