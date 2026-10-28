/-
CVE-2026-7168: @DESC@

証明すること（`cases/CVE-2026-7168.md` の場面）: `option` が `CURLOPT_PROXY` のとき、関数は `Curl_setstropt` の戻り値を返し、
戻った時点の所有は `cells @LAY@ c (sBefore c sv)`。プロキシが変わっても `proxydigest.nonce`・`authproxy.picked` は元のまま。
-/
import @GEN@
import Deb2026_7168Common
open CC CC.Sep CC.HProp
open @GENNS@
open Deb2026_8927 (Cell Cells cells_weakValid mem_idx ld lv_f1 lv_f2 lv_arr eval_lv_load retSpec call_ret
  call_set_cells call_void_cells boolVal_vptr boolVal_ofBool vnull u f1 f2)
open Case4C (call_none)

set_option maxRecDepth 20000

namespace Deb2026_7168.@NS@
open Deb2026_7168

def coOf (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_easy : prog.prog_comp_env.get _Curl_easy = some (coOf _Curl_easy) := rfl
theorem co_ud : prog.prog_comp_env.get _UserDefined = some (coOf _UserDefined) := rfl
theorem co_state : prog.prog_comp_env.get _UrlState = some (coOf _UrlState) := rfl
theorem off_set : fieldOffset prog.prog_comp_env _set (coOf _Curl_easy).co_members = .OK (0, .Full) := by decide
theorem off_state : fieldOffset prog.prog_comp_env _state (coOf _Curl_easy).co_members = .OK (@STOFF@, .Full) := by decide
theorem off_str : fieldOffset prog.prog_comp_env _str (coOf _UserDefined).co_members = .OK (@STRB@, .Full) := by decide
theorem off_proxydigest : fieldOffset prog.prog_comp_env _proxydigest (coOf _UrlState).co_members = .OK (0, .Full) := by decide
theorem off_authproxy : fieldOffset prog.prog_comp_env _authproxy (coOf _UrlState).co_members = .OK (8, .Full) := by decide

/-! ## 仕様 -/

def cptrSpecB (c : Ctx) (rs : Integers.Int) (sv : Val) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tint, tptr tschar]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dataB c.dataO, .Vint (Integers.Int.repr 10004), .Vptr c.pB c.pO]
    ∧ Cells .Freeable (cells @LAY@ c (s0 c)) hp
  post := fun v hp => v = .Vint rs ∧ Cells .Freeable (cells @LAY@ c (sBefore c sv)) hp
  measure := fun _ => 0

/-- `Curl_setstropt(&data->set.str[STRING_PROXY], ptr)`: 任意の `rs` を返し、`str[STRING_PROXY]` を任意の `sv` にする。 -/
def setstrSpec (c : Ctx) (s : St) (rs : Integers.Int) (sv : Val) : FunSpec where
  tyargs := [tptr (tptr tschar), tptr tschar]
  tyres := tint
  cc := cc_default
  pre := fun _ hp => Cells .Freeable (cells @LAY@ c s) hp
  post := fun v hp => v = .Vint rs ∧ Cells .Freeable (cells @LAY@ c { s with str := sv }) hp
  measure := fun _ => 0

set_option hygiene false in
macro "ldc7 " i:num x:term:max : term => `(ld hpr hH hag (x := $x) (mem_idx $i rfl) rfl)
set_option hygiene false in
macro "tget7 " v:term:max : term => `(TempsHold.get hT (v := $v) (by temps_get))

theorem blocks_UP (ge : CGenv) (b1 b2 : Block) (hne : b1 ≠ b2) :
    (∀ blk ∈ blocksOfEnv ge.genv_cenv (envUP _u _p b1 b2), blk = (b1, 0, 8) ∨ blk = (b2, 0, 8))
    ∧ (blocksOfEnv ge.genv_cenv (envUP _u _p b1 b2)).Pairwise (fun a b => a.1 ≠ b.1) := by
  first
  | (have e : blocksOfEnv ge.genv_cenv (envUP _u _p b1 b2) = [(b1, 0, 8), (b2, 0, 8)] := rfl
     rw [e]
     exact ⟨fun blk hb => by simp at hb; exact hb, by simp [hne]⟩)
  | (have e : blocksOfEnv ge.genv_cenv (envUP _u _p b1 b2) = [(b2, 0, 8), (b1, 0, 8)] := rfl
     rw [e]
     exact ⟨fun blk hb => by simp at hb; exact hb.symm, by simp [Ne.symm hne]⟩)

theorem cptr_entry_wf :
    listNorepet (varNames @FN@.fn_vars) ∧ listNorepet (varNames @FN@.fn_params)
    ∧ listDisjoint (varNames @FN@.fn_params) (varNames @FN@.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxHeartbeats 8000000 in
/-- **`@FNC@(data, CURLOPT_PROXY, ptr)`**（修正前）: `Curl_setstropt` を呼んでその値を返す。認証の状態には触れない。 -/
theorem @THM@ (ge : CGenv) (c : Ctx) (rs : Integers.Int) (sv : Val)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (bSet : Block) (fdSet : FunDef) (hsSet : Genv.findSymbol ge.genv_genv _Curl_setstropt = some bSet)
    (hfSet : FuncPtr ge bSet fdSet)
    (htySet : typeOfFundef fdSet = .Tfunction [tptr (tptr tschar), tptr tschar] tint cc_default)
    (hSet : ∀ s vs, SatisfiesAt ge (FunctionEntry2 ge) fdSet (setstrSpec c s rs sv) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal @FN@) (cptrSpecB c rs sv) vs := by
  by_cases hvs : vs = [.Vptr c.dataB c.dataO, .Vint (Integers.Int.repr 10004), .Vptr c.pB c.pO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := cptr_entry_wf
  refine satisfies_locals2 ge @FN@ _ _ _u _p
    (PTree.set _ptr (.Vptr c.pB c.pO) (PTree.set _option (.Vint (Integers.Int.repr 10004))
      (PTree.set _data (.Vptr c.dataB c.dataO) (createUndefTemps @FN@.fn_temps))))
    (cells @LAY@ c (s0 c)) rfl hnv hnp hdisj rfl (fun _ h => h.2) (fun b1 b2 hne => ?_)
  obtain ⟨hbl, hbp⟩ := blocks_UP ge b1 b2 hne
  refine triple_pre ge _ _ (P := LocalSt (envUP _u _p b1 b2)
      [(_ptr, .Vptr c.pB c.pO), (_option, .Vint (Integers.Int.repr 10004)), (_data, .Vptr c.dataB c.dataO)]
      (Cells .Freeable (cells @LAY@ c (s0 c) ++ [lcell b1, lcell b2])))
    (fun e le hp ⟨he, hle, hH⟩ => ⟨he, ?_, hH⟩) ?_
  · subst hle
    refine TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_nil _)))
    · exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
    · exact (PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _))
  @PRE@
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
  refine triple_switch_const ge _ _ _ _ _ _ 10004 ?_
    (fun e le hp m hP _ => ⟨_, EvalExpr.Etempvar _ _ _ (hP.2.1.get (v := .Vint (Integers.Int.repr 10004)) (by temps_get)), by decide⟩)
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (Case5C.call_fwd ge _ _ (setstrSpec c (s0 c) rs sv) @TSP@ _ _ (envUP _u _p b1 b2) _
      (Cells .Freeable (cells @LAY@ c (s0 c))) (Cells .Freeable [lcell b1, lcell b2])
      (Cells .Freeable (cells @LAY@ c (sBefore c sv))) _ _
      [_, .Vptr c.pB c.pO] (.Vint rs) bSet fdSet (hSet _) hfSet htySet rfl
      (fun _ _ _ => eval_callee_global (envUP_none _ _ _ _ _ (by decide) (by decide)) hsSet rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Elvalue _ _ _ .Full _ @STRLV@ (DerefLoc.reference rfl))
          (EvalExpr.Econst_int _ _) (semAdd_ptr_int _ _ _ _ _ rfl)) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget7 (.Vptr c.pB c.pO))) rfl
          EvalExprlist.nil))
      (fun _ h => h) (fun _ _ h => h) (cells_append _ _ _) (cells_append _ _ _).symm) ?_
  refine return_locals2 ge _ _ _u _p b1 b2 _ _ _ _ (.Vint rs)
    (.Vint rs) hne hbl hbp
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) ?_ (fun hp hH => ⟨rfl, hH⟩)
  intro m
  rfl

end Deb2026_7168.@NS@
