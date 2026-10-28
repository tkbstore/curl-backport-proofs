/-
CVE-2026-3784: 上流の修正前（U0、curl e47b6e657a） の `proxy_info_matches`。生成: `research/c-semantics-link/deb2026_3784/proof_gen/gen.py`。

すべての入力について、戻り値は `res`（下の定義）で、メモリは変えない（`matches_before`）。
-/
import Deb2026_3784GenU0
import Deb2026_3784Common
open CC CC.Sep CC.HProp
open Deb2026_3784_u0
open Deb2026_8927 (Cell Cells mem_idx ld lv_f1 lv_f2 eval_lv_load retSpec call_ret boolVal_ofBool)
open Case4C (IsPtr loadResult_ptr cast_ptr)

set_option maxRecDepth 20000

namespace Deb2026_3784.U0
open Deb2026_3784

def coOf (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_pi : prog.prog_comp_env.get _proxy_info = some (coOf _proxy_info) := rfl
theorem co_hn : prog.prog_comp_env.get _hostname = some (coOf _hostname) := rfl
theorem off_host : fieldOffset prog.prog_comp_env _host (coOf _proxy_info).co_members = .OK (0, .Full) := by decide
theorem off_port : fieldOffset prog.prog_comp_env _port (coOf _proxy_info).co_members = .OK (8, .Full) := by decide
theorem off_pt : fieldOffset prog.prog_comp_env _proxytype (coOf _proxy_info).co_members = .OK (10, .Full) := by decide
theorem off_user : fieldOffset prog.prog_comp_env _user (coOf _proxy_info).co_members = .OK (16, .Full) := by decide
theorem off_passwd : fieldOffset prog.prog_comp_env _passwd (coOf _proxy_info).co_members = .OK (24, .Full) := by decide
theorem off_name : fieldOffset prog.prog_comp_env _name (coOf _hostname).co_members = .OK (0, .Full) := by decide

def lay : Lay := ⟨.Mint16unsigned, 8, 10⟩

def res (c : Ctx) (se : Integers.Int) : Val :=
  Val.ofBool (Integers.Int.eq (Integers.Int.zero_ext 8 c.ptD) (Integers.Int.zero_ext 8 c.ptN) && Integers.Int.eq (Integers.Int.zero_ext 16 c.portD) (Integers.Int.zero_ext 16 c.portN) && !Integers.Int.eq se Integers.Int.zero)

def spec (c : Ctx) (se : Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _proxy_info noattr), tptr (Ty.Tstruct _proxy_info noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dB c.dO, .Vptr c.nB c.nO] ∧ Cells .Freeable (cells lay c) hp
  post := fun v hp => v = res c se ∧ Cells .Freeable (cells lay c) hp
  measure := fun _ => 0

theorem entry_wf :
    listNorepet (varNames f_proxy_info_matches.fn_vars) ∧ listNorepet (varNames f_proxy_info_matches.fn_params)
    ∧ listDisjoint (varNames f_proxy_info_matches.fn_params) (varNames f_proxy_info_matches.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxHeartbeats 8000000 in
theorem matches_before (ge : CGenv) (c : Ctx) (se : Integers.Int)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hnd : IsPtr (Val.loadResult Mptr c.nameD)) (hnn : IsPtr (Val.loadResult Mptr c.nameN))
    (bSe : Block) (fdSe : FunDef) (hsSe : Genv.findSymbol ge.genv_genv _curl_strequal = some bSe)
    (hfSe : FuncPtr ge bSe fdSe)
    (htySe : typeOfFundef fdSe = .Tfunction [tptr tschar, tptr tschar] tint cc_default)
    (hSe : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdSe (retSpec [tptr tschar, tptr tschar] tint (.Vint se)) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_proxy_info_matches) (spec c se) vs := by
  by_cases hvs : vs = [.Vptr c.dB c.dO, .Vptr c.nB c.nO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hpr : permOrder Permission.Freeable .Readable = true := rfl
  obtain ⟨hnv, hnp, hdisj⟩ := entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_proxy_info_matches _ _
    (LocalSt emptyEnv [(_needle, .Vptr c.nB c.nO), (_data, .Vptr c.dB c.dO)] (Cells .Freeable (cells lay c)))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _needle (.Vptr c.nB c.nO)
              (PTree.set _data (.Vptr c.dB c.dO) (createUndefTemps f_proxy_info_matches.fn_temps)),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_nil _)), hpre.2⟩
    exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
  cases hb1 : Integers.Int.eq (Integers.Int.zero_ext 8 c.ptD) (Integers.Int.zero_ext 8 c.ptN)
  case false =>
    apply triple_seq_fwd ge _ _ _ _ _ _ _ ?X
    case X =>
      apply triple_seq_fwd ge _ _ _ _ _ _ _ ?AB
      case AB =>
        apply triple_seq_fwd ge _ _ _ _ _ _ _ ?A
        case A =>
          refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'6 _ (.Vint (Integers.Int.zero_ext 8 c.ptD)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.dB c.dO)) (hcenv ▸ co_pi) (hcenv ▸ off_pt)) rfl (ldc3 0 (cPtD lay c)))) ?_
          refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'7 _ (.Vint (Integers.Int.zero_ext 8 c.ptN)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.nB c.nO)) (hcenv ▸ co_pi) (hcenv ▸ off_pt)) rfl (ldc3 1 (cPtN lay c)))) ?_
          exact triple_if_local ge _ _ emptyEnv _ _ _ (Integers.Int.eq (Integers.Int.zero_ext 8 c.ptD) (Integers.Int.zero_ext 8 c.ptN)) _ _ _ (fun le m hp hT _ _ => ⟨Val.ofBool (Integers.Int.eq (Integers.Int.zero_ext 8 c.ptD) (Integers.Int.zero_ext 8 c.ptN)), EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 8 c.ptD)))) (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 8 c.ptN)))) rfl, boolVal_ofBool _ _ m (.inl rfl)⟩) (if_false_triple hb1 (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'1 _ (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)))
        exact triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.repr 0))), rfl⟩) ((triple_set_local_fwd ge _ _ emptyEnv _ _ _t'2 _ (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)))
      exact triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.repr 0))), rfl⟩) ((triple_skip ge _ _ _))
    exact (triple_return_local ge _ _ _ _ _ _ (.Vint (Integers.Int.repr 0)) (Val.ofBool false) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl) (fun hp hH => ⟨by simp only [res, hb1, Bool.true_and, Bool.false_and, Bool.and_false, Bool.and_true, Bool.not_true, Bool.not_false], hH⟩))
  case true =>
    cases hb2 : Integers.Int.eq (Integers.Int.zero_ext 16 c.portD) (Integers.Int.zero_ext 16 c.portN)
    case false =>
      apply triple_seq_fwd ge _ _ _ _ _ _ _ ?X
      case X =>
        apply triple_seq_fwd ge _ _ _ _ _ _ _ ?AB
        case AB =>
          apply triple_seq_fwd ge _ _ _ _ _ _ _ ?A
          case A =>
            refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'6 _ (.Vint (Integers.Int.zero_ext 8 c.ptD)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.dB c.dO)) (hcenv ▸ co_pi) (hcenv ▸ off_pt)) rfl (ldc3 0 (cPtD lay c)))) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'7 _ (.Vint (Integers.Int.zero_ext 8 c.ptN)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.nB c.nO)) (hcenv ▸ co_pi) (hcenv ▸ off_pt)) rfl (ldc3 1 (cPtN lay c)))) ?_
            exact triple_if_local ge _ _ emptyEnv _ _ _ (Integers.Int.eq (Integers.Int.zero_ext 8 c.ptD) (Integers.Int.zero_ext 8 c.ptN)) _ _ _ (fun le m hp hT _ _ => ⟨Val.ofBool (Integers.Int.eq (Integers.Int.zero_ext 8 c.ptD) (Integers.Int.zero_ext 8 c.ptN)), EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 8 c.ptD)))) (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 8 c.ptN)))) rfl, boolVal_ofBool _ _ m (.inl rfl)⟩) (if_true_triple hb1 (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'8 _ (.Vint (Integers.Int.zero_ext 16 c.portD)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.dB c.dO)) (hcenv ▸ co_pi) (hcenv ▸ off_port)) rfl (ldc3 2 (cPortD lay c)))) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'9 _ (.Vint (Integers.Int.zero_ext 16 c.portN)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.nB c.nO)) (hcenv ▸ co_pi) (hcenv ▸ off_port)) rfl (ldc3 3 (cPortN lay c)))) (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'1 _ (Val.ofBool (Integers.Int.eq (Integers.Int.zero_ext 16 c.portD) (Integers.Int.zero_ext 16 c.portN))) (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 16 c.portD)))) (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 16 c.portN)))) rfl) (Deb2026_7168.cast_ofBool_int_bool _ m))))))
          exact triple_if_local ge _ _ emptyEnv _ _ _ (Integers.Int.eq (Integers.Int.zero_ext 16 c.portD) (Integers.Int.zero_ext 16 c.portN)) _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget3 (Val.ofBool (Integers.Int.eq (Integers.Int.zero_ext 16 c.portD) (Integers.Int.zero_ext 16 c.portN)))), boolVal_ofBool _ _ m (.inl rfl)⟩) (if_false_triple hb2 (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'2 _ (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)))
        exact triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.repr 0))), rfl⟩) ((triple_skip ge _ _ _))
      exact (triple_return_local ge _ _ _ _ _ _ (.Vint (Integers.Int.repr 0)) (Val.ofBool false) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl) (fun hp hH => ⟨by simp only [res, hb1, hb2, Bool.true_and, Bool.false_and, Bool.and_false, Bool.and_true, Bool.not_true, Bool.not_false], hH⟩))
    case true =>
      cases hb3 : Integers.Int.eq se Integers.Int.zero
      case false =>
        refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?X (triple_vacuous ge _ _ _ _)
        case X =>
          apply triple_seq_fwd ge _ _ _ _ _ _ _ ?AB
          case AB =>
            apply triple_seq_fwd ge _ _ _ _ _ _ _ ?A
            case A =>
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'6 _ (.Vint (Integers.Int.zero_ext 8 c.ptD)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.dB c.dO)) (hcenv ▸ co_pi) (hcenv ▸ off_pt)) rfl (ldc3 0 (cPtD lay c)))) ?_
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'7 _ (.Vint (Integers.Int.zero_ext 8 c.ptN)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.nB c.nO)) (hcenv ▸ co_pi) (hcenv ▸ off_pt)) rfl (ldc3 1 (cPtN lay c)))) ?_
              exact triple_if_local ge _ _ emptyEnv _ _ _ (Integers.Int.eq (Integers.Int.zero_ext 8 c.ptD) (Integers.Int.zero_ext 8 c.ptN)) _ _ _ (fun le m hp hT _ _ => ⟨Val.ofBool (Integers.Int.eq (Integers.Int.zero_ext 8 c.ptD) (Integers.Int.zero_ext 8 c.ptN)), EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 8 c.ptD)))) (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 8 c.ptN)))) rfl, boolVal_ofBool _ _ m (.inl rfl)⟩) (if_true_triple hb1 (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'8 _ (.Vint (Integers.Int.zero_ext 16 c.portD)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.dB c.dO)) (hcenv ▸ co_pi) (hcenv ▸ off_port)) rfl (ldc3 2 (cPortD lay c)))) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'9 _ (.Vint (Integers.Int.zero_ext 16 c.portN)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.nB c.nO)) (hcenv ▸ co_pi) (hcenv ▸ off_port)) rfl (ldc3 3 (cPortN lay c)))) (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'1 _ (Val.ofBool (Integers.Int.eq (Integers.Int.zero_ext 16 c.portD) (Integers.Int.zero_ext 16 c.portN))) (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 16 c.portD)))) (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 16 c.portN)))) rfl) (Deb2026_7168.cast_ofBool_int_bool _ m))))))
            exact triple_if_local ge _ _ emptyEnv _ _ _ (Integers.Int.eq (Integers.Int.zero_ext 16 c.portD) (Integers.Int.zero_ext 16 c.portN)) _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget3 (Val.ofBool (Integers.Int.eq (Integers.Int.zero_ext 16 c.portD) (Integers.Int.zero_ext 16 c.portN)))), boolVal_ofBool _ _ m (.inl rfl)⟩) (if_true_triple hb2 (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'4 _ (Val.loadResult Mptr c.nameD) (fun le m hp hT hH hag => eval_lv_load (lv_f2 (tget3 (.Vptr c.dB c.dO)) (hcenv ▸ co_pi) (hcenv ▸ off_host) (hcenv ▸ co_hn) (hcenv ▸ off_name)) rfl (ldc3 4 (cNameD c)))) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'5 _ (Val.loadResult Mptr c.nameN) (fun le m hp hT hH hag => eval_lv_load (lv_f2 (tget3 (.Vptr c.nB c.nO)) (hcenv ▸ co_pi) (hcenv ▸ off_host) (hcenv ▸ co_hn) (hcenv ▸ off_name)) rfl (ldc3 5 (cNameN c)))) (call_ret ge _ _ _ _ _ _t'3 _ _ emptyEnv _ _ [Val.loadResult Mptr c.nameD, Val.loadResult Mptr c.nameN] bSe fdSe hSe hfSe htySe rfl (fun _ _ _ => eval_callee_global rfl hsSe rfl) (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (Val.loadResult Mptr c.nameD))) (cast_ptr hnd _ _ m) (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (Val.loadResult Mptr c.nameN))) (cast_ptr hnn _ _ m) EvalExprlist.nil))))) (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'2 _ (Val.ofBool (!Integers.Int.eq se Integers.Int.zero)) (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (.Vint se))) (cast_int_bool se m)))))
          exact triple_if_local ge _ _ emptyEnv _ _ _ (!Integers.Int.eq se Integers.Int.zero) _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget3 (Val.ofBool (!Integers.Int.eq se Integers.Int.zero))), boolVal_ofBool _ _ m (.inl rfl)⟩) (if_true_triple (by rw [hb3]; rfl) (triple_return_local ge _ _ _ _ _ _ (.Vint (Integers.Int.repr 1)) (Val.ofBool true) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl) (fun hp hH => ⟨by simp only [res, hb1, hb2, hb3, Bool.true_and, Bool.false_and, Bool.and_false, Bool.and_true, Bool.not_true, Bool.not_false], hH⟩)))
      case true =>
        apply triple_seq_fwd ge _ _ _ _ _ _ _ ?X
        case X =>
          apply triple_seq_fwd ge _ _ _ _ _ _ _ ?AB
          case AB =>
            apply triple_seq_fwd ge _ _ _ _ _ _ _ ?A
            case A =>
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'6 _ (.Vint (Integers.Int.zero_ext 8 c.ptD)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.dB c.dO)) (hcenv ▸ co_pi) (hcenv ▸ off_pt)) rfl (ldc3 0 (cPtD lay c)))) ?_
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'7 _ (.Vint (Integers.Int.zero_ext 8 c.ptN)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.nB c.nO)) (hcenv ▸ co_pi) (hcenv ▸ off_pt)) rfl (ldc3 1 (cPtN lay c)))) ?_
              exact triple_if_local ge _ _ emptyEnv _ _ _ (Integers.Int.eq (Integers.Int.zero_ext 8 c.ptD) (Integers.Int.zero_ext 8 c.ptN)) _ _ _ (fun le m hp hT _ _ => ⟨Val.ofBool (Integers.Int.eq (Integers.Int.zero_ext 8 c.ptD) (Integers.Int.zero_ext 8 c.ptN)), EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 8 c.ptD)))) (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 8 c.ptN)))) rfl, boolVal_ofBool _ _ m (.inl rfl)⟩) (if_true_triple hb1 (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'8 _ (.Vint (Integers.Int.zero_ext 16 c.portD)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.dB c.dO)) (hcenv ▸ co_pi) (hcenv ▸ off_port)) rfl (ldc3 2 (cPortD lay c)))) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'9 _ (.Vint (Integers.Int.zero_ext 16 c.portN)) (fun le m hp hT hH hag => eval_lv_load (lv_f1 (tget3 (.Vptr c.nB c.nO)) (hcenv ▸ co_pi) (hcenv ▸ off_port)) rfl (ldc3 3 (cPortN lay c)))) (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'1 _ (Val.ofBool (Integers.Int.eq (Integers.Int.zero_ext 16 c.portD) (Integers.Int.zero_ext 16 c.portN))) (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 16 c.portD)))) (EvalExpr.Etempvar _ _ _ (tget3 (.Vint (Integers.Int.zero_ext 16 c.portN)))) rfl) (Deb2026_7168.cast_ofBool_int_bool _ m))))))
            exact triple_if_local ge _ _ emptyEnv _ _ _ (Integers.Int.eq (Integers.Int.zero_ext 16 c.portD) (Integers.Int.zero_ext 16 c.portN)) _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget3 (Val.ofBool (Integers.Int.eq (Integers.Int.zero_ext 16 c.portD) (Integers.Int.zero_ext 16 c.portN)))), boolVal_ofBool _ _ m (.inl rfl)⟩) (if_true_triple hb2 (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'4 _ (Val.loadResult Mptr c.nameD) (fun le m hp hT hH hag => eval_lv_load (lv_f2 (tget3 (.Vptr c.dB c.dO)) (hcenv ▸ co_pi) (hcenv ▸ off_host) (hcenv ▸ co_hn) (hcenv ▸ off_name)) rfl (ldc3 4 (cNameD c)))) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'5 _ (Val.loadResult Mptr c.nameN) (fun le m hp hT hH hag => eval_lv_load (lv_f2 (tget3 (.Vptr c.nB c.nO)) (hcenv ▸ co_pi) (hcenv ▸ off_host) (hcenv ▸ co_hn) (hcenv ▸ off_name)) rfl (ldc3 5 (cNameN c)))) (call_ret ge _ _ _ _ _ _t'3 _ _ emptyEnv _ _ [Val.loadResult Mptr c.nameD, Val.loadResult Mptr c.nameN] bSe fdSe hSe hfSe htySe rfl (fun _ _ _ => eval_callee_global rfl hsSe rfl) (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (Val.loadResult Mptr c.nameD))) (cast_ptr hnd _ _ m) (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (Val.loadResult Mptr c.nameN))) (cast_ptr hnn _ _ m) EvalExprlist.nil))))) (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'2 _ (Val.ofBool (!Integers.Int.eq se Integers.Int.zero)) (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (.Vint se))) (cast_int_bool se m)))))
          exact triple_if_local ge _ _ emptyEnv _ _ _ (!Integers.Int.eq se Integers.Int.zero) _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget3 (Val.ofBool (!Integers.Int.eq se Integers.Int.zero))), boolVal_ofBool _ _ m (.inl rfl)⟩) (if_false_triple (by rw [hb3]; rfl) (triple_skip ge _ _ _))
        exact (triple_return_local ge _ _ _ _ _ _ (.Vint (Integers.Int.repr 0)) (Val.ofBool false) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl) (fun hp hH => ⟨by simp only [res, hb1, hb2, hb3, Bool.true_and, Bool.false_and, Bool.and_false, Bool.and_true, Bool.not_true, Bool.not_false], hH⟩))

end Deb2026_3784.U0
