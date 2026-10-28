/-
CVE-2025-14524: 上流の修正後（U1）の `sasl_choose_*` の仕様を、本体から導く（仮定しない）。

前提（P1）: `this_is_a_follow` が 1、`allow_auth_to_other_hosts` が 0、`enabledmechs` は EXTERNAL・PLAIN・LOGIN のビットを含まない。
どの関数も偽を返し、メモリを変えない。`sasl_choose_oauth`・`sasl_choose_oauth2` は、修正で Bearer が NULL になるので偽を返す。
-/
import Deb2025_14524UC
open CC CC.Sep CC.HProp
open Deb2025_14524_u1
open Deb2025_14524
open Case5C (addr RR return_const eval_field bitOf)
open Case3C (CellD cellH Cells cell_load3 Locs)

set_option maxRecDepth 20000

namespace Deb2025_14524U

/-- `W1` の `k` 番目のセルを読む。 -/
theorem ldW {c : Ctx} {fir : Bool} {xB : Block} {X : HProp} {hp : Heap} {m : Mem} (k : Nat)
    (hk : k < (sctxS c xB ++ outer c (Integers.Int.repr 0)).length)
    {ch : Chunk} {p : Permission} {b : Block} {o : Z} {v : Val}
    (hl : (sctxS c xB ++ outer c (Integers.Int.repr 0))[k]'hk = (ch, p, b, o, v))
    (hpr : permOrder p .Readable = true) (hH : (W1 c fir xB ∗ X) hp) (hag : Heap.Agrees hp m) :
    Mem.load ch m b o = some (Val.loadResult ch v) := by
  unfold W1 at hH
  rw [sep_assoc_eq] at hH
  exact cell_load3 hl hpr hH hag

theorem validW {c : Ctx} {fir : Bool} {xB : Block} {X : HProp} {hp : Heap} {m : Mem} (k : Nat)
    (hk : k < (sctxS c xB ++ outer c (Integers.Int.repr 0)).length)
    {p : Permission} {b : Block} {o : Integers.Ptrofs} {v : Val}
    (hl : (sctxS c xB ++ outer c (Integers.Int.repr 0))[k]'hk
      = (.Mint8unsigned, p, b, Integers.Ptrofs.unsigned o, v))
    (hpn : permOrder p .Nonempty = true) (hH : (W1 c fir xB ∗ X) hp) (hag : Heap.Agrees hp m) :
    Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true := by
  unfold W1 at hH
  rw [sep_assoc_eq] at hH
  exact cell_valid hl hpn hH hag

theorem W1_emp {c : Ctx} {fir : Bool} {xB : Block} {hp : Heap} (hH : W1 c fir xB hp) :
    (W1 c fir xB ∗ emp) hp := by rw [sep_emp_eq]; exact hH

theorem freeable_r : permOrder Permission.Freeable .Readable = true := rfl

theorem cast_bool_zero {x : Integers.Int} (hx : Integers.Int.eq x Integers.Int.zero = true) (m : Mem) :
    Cop.semCast (.Vint x) tint tbool m = some (Val.ofBool false) := by
  show some (.Vint (if Integers.Int.eq x Integers.Int.zero then Integers.Int.zero else Integers.Int.one))
    = some (Val.ofBool false)
  rw [hx]; rfl

theorem notbool_nz {x : Integers.Int} (hx : Integers.Int.eq x Integers.Int.zero = false) (m : Mem) :
    Cop.semUnaryOperation .Onotbool (.Vint x) tint m = some (Val.ofBool false) := by
  show (Cop.boolVal (.Vint x) tint m).map (fun b => Val.ofBool (!b)) = _
  rw [show Cop.boolVal (.Vint x) tint m = some (!Integers.Int.eq x Integers.Int.zero) from rfl, hx]
  rfl

/-- `(bool)((t & k))` が偽になる。 -/
theorem cast_and_zero {x k : Integers.Int} (hx : Integers.Int.and x k = Integers.Int.zero) (m : Mem) :
    Cop.semCast (.Vint (Integers.Int.and x k)) tint tbool m = some (Val.ofBool false) := by
  rw [hx]; rfl

theorem bitOf_true {w : Integers.Int} (h : bitOf w 0 = true) :
    Integers.Int.eq (Cop.bitfieldExtract .I32 .Unsigned 0 1 w) Integers.Int.zero = false := by
  unfold bitOf at h; revert h; cases Integers.Int.eq _ _ <;> simp

theorem bitOf_false {w : Integers.Int} (h : bitOf w 0 = false) :
    Integers.Int.eq (Cop.bitfieldExtract .I32 .Unsigned 0 1 w) Integers.Int.zero = true := by
  unfold bitOf at h; revert h; cases Integers.Int.eq _ _ <;> simp

/-- 入口（局所変数なし）: `data`・`sctx` の2つの引数。 -/
theorem entry2 (ge : CGenv) (f : Function) (c : Ctx) (xB : Block) (W : HProp) (Wpost : HProp)
    (ret : Bool) (hnv : listNorepet (varNames f.fn_vars)) (hvars : f.fn_vars = [])
    (hnp : listNorepet (varNames f.fn_params)) (hdisj : listDisjoint (varNames f.fn_params) (varNames f.fn_temps))
    (hpar : f.fn_params = [(_data, tptr (Ty.Tstruct _Curl_easy noattr)),
                           (_sctx, tptr (Ty.Tstruct _sasl_ctx noattr))])
    (body : Triple ge (FunctionEntry2 ge) f
      (LocalSt emptyEnv [(_sctx, .Vptr xB Integers.Ptrofs.zero), (_data, .Vptr c.dB c.dO)] W)
      f.fn_body (RR (chooseSpec c xB W Wpost ret).post Sep.Assn.no))
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f) (chooseSpec c xB W Wpost ret) vs := by
  by_cases hvs : vs = [.Vptr c.dB c.dO, .Vptr xB Integers.Ptrofs.zero]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f _ _ _ (fun m => ?_) body
  refine ⟨PTree.set _sctx (.Vptr xB Integers.Ptrofs.zero) (PTree.set _data (.Vptr c.dB c.dO)
            (createUndefTemps f.fn_temps)),
          FunctionEntry2.intro hnv hnp hdisj (by rw [hvars]; exact AllocVariables.nil _ _)
            (by rw [hpar]; rfl),
          fun hp hpre => ⟨rfl, ?_, hpre.2⟩⟩
  exact TempsHold_cons (PTree.gss _ _ _)
    (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)) (TempsHold_nil _))

/-! ## `sasl_choose_external` -/

theorem ext_after (ge : CGenv) (c : Ctx) (fir : Bool) (xB : Block)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hE : Integers.Int.and (em c) (Integers.Int.repr 32) = Integers.Int.zero) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sasl_choose_external)
      (chooseSpec c xB (W1 c fir xB) (W1 c fir xB) false) vs := by
  refine entry2 ge _ c xB _ _ false (by decide) rfl (by decide) (by decide) rfl ?_ vs
  have hx : Integers.Int.and (Integers.Int.zero_ext 16 (em c))
      (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 5)) = Integers.Int.zero := by
    rw [zext_em]; exact hE
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _
          (.Vint (Integers.Int.zero_ext 16 (em c)))
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_ctx)
            (hcenv ▸ offx_em) rfl (ldW (X := emp) 3 (by simp) rfl freeable_r (W1_emp hH) hag)))
        (triple_if_local ge _ _ emptyEnv _ (W1 c fir xB) _ false _ _ _
          (fun le m hp hT _ _ =>
            ⟨.Vint (Integers.Int.and (Integers.Int.zero_ext 16 (em c))
                (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 5))),
             EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
              (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl)
              rfl,
             cond_and_false _ _ hx m⟩)
          (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _ (.Vint (Integers.Int.repr 0))
            (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))))
      (triple_if_local ge _ _ emptyEnv _ (W1 c fir xB) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0))
          (hT.get (by temps_get)), rfl⟩)
        (triple_skip ge _ _ _))) ?_
  exact return_const ge _ _ _ _ (Integers.Int.repr 0) _ _ (Val.ofBool false) (fun _ => rfl)
    (fun hp hH => ⟨rfl, hH⟩)

/-! ## `sasl_choose_plain`・`sasl_choose_login` -/

theorem plain_after (ge : CGenv) (c : Ctx) (fir : Bool) (xB : Block)
    (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpn : permOrder c.pm .Nonempty = true)
    (hP : Integers.Int.and (em c) (Integers.Int.repr 2) = Integers.Int.zero) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sasl_choose_plain)
      (chooseSpec c xB (W1 c fir xB) (W1 c fir xB) false) vs := by
  refine entry2 ge _ c xB _ _ false (by decide) rfl (by decide) (by decide) rfl ?_ vs
  have hx : Integers.Int.and (Integers.Int.zero_ext 16 (em c))
      (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 1)) = Integers.Int.zero := by
    rw [zext_em]; exact hP
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _ (.Vptr c.uB c.uO)
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_ctx)
            (hcenv ▸ offx_user) rfl (ldW (X := emp) 2 (by simp) rfl freeable_r (W1_emp hH) hag)))
        (triple_if_local ge _ _ emptyEnv _ (W1 c fir xB) _ true _ _ _
          (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.uB c.uO) (hT.get (by temps_get)),
            boolVal_ptr _ rfl (validW (X := emp) 23 (by simp) rfl hpn (W1_emp hH) hag)⟩)
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _
              (.Vint (Integers.Int.zero_ext 16 (em c)))
              (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_ctx)
                (hcenv ▸ offx_em) rfl (ldW (X := emp) 3 (by simp) rfl freeable_r (W1_emp hH) hag)))
            (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _ (Val.ofBool false)
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _
                (.Vint (Integers.Int.and (Integers.Int.zero_ext 16 (em c))
                  (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 1)))) _
                (EvalExpr.Ebinop _ _ _ _ _ _ _
                  (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                  (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl)
                  rfl)
                (cast_and_zero hx m))))))
      (triple_if_local ge _ _ emptyEnv _ (W1 c fir xB) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false)
          (hT.get (by temps_get)), rfl⟩)
        (triple_skip ge _ _ _))) ?_
  exact return_const ge _ _ _ _ (Integers.Int.repr 0) _ _ (Val.ofBool false) (fun _ => rfl)
    (fun hp hH => ⟨rfl, hH⟩)

theorem login_after (ge : CGenv) (c : Ctx) (fir : Bool) (xB : Block)
    (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpn : permOrder c.pm .Nonempty = true)
    (hL : Integers.Int.and (em c) (Integers.Int.repr 1) = Integers.Int.zero) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sasl_choose_login)
      (chooseSpec c xB (W1 c fir xB) (W1 c fir xB) false) vs := by
  refine entry2 ge _ c xB _ _ false (by decide) rfl (by decide) (by decide) rfl ?_ vs
  have hx : Integers.Int.and (Integers.Int.zero_ext 16 (em c))
      (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 0)) = Integers.Int.zero := by
    rw [zext_em]; exact hL
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _ (.Vptr c.uB c.uO)
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_ctx)
            (hcenv ▸ offx_user) rfl (ldW (X := emp) 2 (by simp) rfl freeable_r (W1_emp hH) hag)))
        (triple_if_local ge _ _ emptyEnv _ (W1 c fir xB) _ true _ _ _
          (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.uB c.uO) (hT.get (by temps_get)),
            boolVal_ptr _ rfl (validW (X := emp) 23 (by simp) rfl hpn (W1_emp hH) hag)⟩)
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _
              (.Vint (Integers.Int.zero_ext 16 (em c)))
              (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_ctx)
                (hcenv ▸ offx_em) rfl (ldW (X := emp) 3 (by simp) rfl freeable_r (W1_emp hH) hag)))
            (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _ (Val.ofBool false)
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _
                (.Vint (Integers.Int.and (Integers.Int.zero_ext 16 (em c))
                  (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 0)))) _
                (EvalExpr.Ebinop _ _ _ _ _ _ _
                  (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                  (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl)
                  rfl)
                (cast_and_zero hx m))))))
      (triple_if_local ge _ _ emptyEnv _ (W1 c fir xB) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false)
          (hT.get (by temps_get)), rfl⟩)
        (triple_skip ge _ _ _))) ?_
  exact return_const ge _ _ _ _ (Integers.Int.repr 0) _ _ (Val.ofBool false) (fun _ => rfl)
    (fun hp hH => ⟨rfl, hH⟩)

/-! ## `sasl_choose_oauth2` -/

/-- `oauth_bearer` を求める部分（修正後）: リダイレクトのあとで許可が無いので NULL。 -/
theorem oauth2_after (ge : CGenv) (c : Ctx) (fir : Bool) (xB : Block)
    (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpn : permOrder c.pm .Nonempty = true)
    (hpr : permOrder c.pm .Readable = true)
    (hfollow : bitOf c.stw 0 = true) (hallow : bitOf c.setw 0 = false) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sasl_choose_oauth2)
      (chooseSpec c xB (W1 c fir xB) (W1 c fir xB) false) vs := by
  refine entry2 ge _ c xB _ _ false (by decide) rfl (by decide) (by decide) rfl ?_ vs
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _
            (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.stw))
            (fun le m hp hT hH hag => eval_bit2 (hT.get (by temps_get)) (hcenv ▸ co_easy)
              (hcenv ▸ off_state) (hcenv ▸ co_us) (hcenv ▸ off_follow) (by decide) (by decide)
              (ldW (X := emp) 21 (by simp) rfl hpr (W1_emp hH) hag)))
          (triple_if_local ge _ _ emptyEnv _ (W1 c fir xB) _ false _ _ _
            (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_nz (bitOf_true hfollow) m),
              rfl⟩)
            (triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _
                (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.setw))
                (fun le m hp hT hH hag => eval_bit2 (hT.get (by temps_get)) (hcenv ▸ co_easy)
                  (hcenv ▸ off_set) (hcenv ▸ co_ud) (hcenv ▸ off_allow) (by decide) (by decide)
                  (ldW (X := emp) 19 (by simp) rfl hpr (W1_emp hH) hag)))
              (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _ (Val.ofBool false)
                (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                  (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (cast_bool_zero (bitOf_false hallow) m))))))
        (triple_if_local ge _ _ emptyEnv _ (W1 c fir xB) _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get)), rfl⟩)
          (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _ z64
            (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _
              (EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl) rfl))))
      (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _ z64
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _ (.Vptr c.uB c.uO)
            (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_ctx)
              (hcenv ▸ offx_user) rfl (ldW (X := emp) 2 (by simp) rfl freeable_r (W1_emp hH) hag)))
          (triple_if_local ge _ _ emptyEnv _ (W1 c fir xB) _ true _ _ _
            (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.uB c.uO) (hT.get (by temps_get)),
              boolVal_ptr _ rfl (validW (X := emp) 23 (by simp) rfl hpn (W1_emp hH) hag)⟩)
            (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _ (Val.ofBool false)
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Etempvar _ _ z64 (hT.get (by temps_get))) rfl))))
        (triple_if_local ge _ _ emptyEnv _ (W1 c fir xB) _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get)), rfl⟩)
          (triple_set_local_fwd ge _ _ emptyEnv _ (W1 c fir xB) _ _ (.Vint (Integers.Int.repr 0))
            (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))))
      (triple_if_local ge _ _ emptyEnv _ (W1 c fir xB) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0))
          (hT.get (by temps_get)), rfl⟩)
        (triple_skip ge _ _ _))) ?_
  exact return_const ge _ _ _ _ (Integers.Int.repr 0) _ _ (Val.ofBool false) (fun _ => rfl)
    (fun hp hH => ⟨rfl, hH⟩)

/-! ## `sasl_choose_oauth`（局所変数 `hostname`・`port` がある） -/

def envO (b1 b2 : Block) : Env :=
  (emptyEnv.set _hostname (b1, tptr tschar)).set _port (b2, tint)

abbrev LO (b1 b2 : Block) : List (Block × Nat) := [(b1, 8), (b2, 4)]

def PbodyO (c : Ctx) (fir : Bool) (xB : Block) : Sep.Assn := fun e le hp =>
  ∃ bs : Block × Block, bs.1 ≠ bs.2 ∧
    LocalSt (envO bs.1 bs.2) [(_sctx, .Vptr xB Integers.Ptrofs.zero), (_data, .Vptr c.dB c.dO)]
      (W1 c fir xB ∗ Locs (LO bs.1 bs.2)) e le hp

theorem blocks_envO (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (b1 b2 : Block) :
    blocksOfEnv ge.genv_cenv (envO b1 b2) = [(b2, 0, 4), (b1, 0, 8)] := by
  rw [hcenv]
  rfl

theorem oauth_body_after (ge : CGenv) (c : Ctx) (fir : Bool) (xB : Block)
    (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpn : permOrder c.pm .Nonempty = true)
    (hpr : permOrder c.pm .Readable = true)
    (hfollow : bitOf c.stw 0 = true) (hallow : bitOf c.setw 0 = false) :
    Triple ge (FunctionEntry2 ge) f_sasl_choose_oauth (PbodyO c fir xB) f_sasl_choose_oauth.fn_body
      (RR (chooseSpec c xB (W1 c fir xB) (W1 c fir xB) false).post Sep.Assn.no) := by
  refine Sep.triple_exists ge _ _ _ _ _ (fun bs => ?_)
  obtain ⟨b1, b2⟩ := bs
  refine Case1C.triple_pure ge _ _ _ _ _ _ (fun hne => ?_)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _
            (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.stw))
            (fun le m hp hT hH hag => eval_bit2 (hT.get (by temps_get)) (hcenv ▸ co_easy)
              (hcenv ▸ off_state) (hcenv ▸ co_us) (hcenv ▸ off_follow) (by decide) (by decide)
              (ldW 21 (by simp) rfl hpr hH hag)))
          (triple_if_local ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ false _ _ _
            (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_nz (bitOf_true hfollow) m),
              rfl⟩)
            (triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _
                (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.setw))
                (fun le m hp hT hH hag => eval_bit2 (hT.get (by temps_get)) (hcenv ▸ co_easy)
                  (hcenv ▸ off_set) (hcenv ▸ co_ud) (hcenv ▸ off_allow) (by decide) (by decide)
                  (ldW 19 (by simp) rfl hpr hH hag)))
              (triple_set_local_fwd ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _ (Val.ofBool false)
                (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                  (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (cast_bool_zero (bitOf_false hallow) m))))))
        (triple_if_local ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get)), rfl⟩)
          (triple_set_local_fwd ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _ z64
            (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _
              (EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl) rfl))))
      (triple_set_local_fwd ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _ z64
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _ (.Vptr c.uB c.uO)
            (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_ctx)
              (hcenv ▸ offx_user) rfl (ldW 2 (by simp) rfl freeable_r hH hag)))
          (triple_if_local ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ true _ _ _
            (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.uB c.uO) (hT.get (by temps_get)),
              boolVal_ptr _ rfl (validW 23 (by simp) rfl hpn hH hag)⟩)
            (triple_set_local_fwd ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _ (Val.ofBool false)
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Etempvar _ _ z64 (hT.get (by temps_get))) rfl))))
        (triple_if_local ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get)), rfl⟩)
          (triple_set_local_fwd ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _ (.Vint (Integers.Int.repr 0))
            (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))))
      (triple_if_local ge _ _ (envO b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0))
          (hT.get (by temps_get)), rfl⟩)
        (triple_skip ge _ _ _))) ?_
  refine Case3C.ret_locs ge _ _ (envO b1 b2) _ (W1 c fir xB) (LO b1 b2) _ (.Vint (Integers.Int.repr 0))
    (Val.ofBool false) _ (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl) ?_ ?_
    (fun hp hH => ⟨rfl, hH⟩)
  · rw [blocks_envO ge hcenv]
    intro x hx'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
    rcases hx' with rfl | rfl
    · exact ⟨b2, 4, rfl, by simp⟩
    · exact ⟨b1, 8, rfl, by simp⟩
  · rw [blocks_envO ge hcenv]
    simp [Ne.symm hne]

theorem oauth_after (ge : CGenv) (c : Ctx) (fir : Bool) (xB : Block)
    (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpn : permOrder c.pm .Nonempty = true)
    (hpr : permOrder c.pm .Readable = true)
    (hfollow : bitOf c.stw 0 = true) (hallow : bitOf c.setw 0 = false) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sasl_choose_oauth)
      (chooseSpec c xB (W1 c fir xB) (W1 c fir xB) false) vs := by
  by_cases hvs : vs = [.Vptr c.dB c.dO, .Vptr xB Integers.Ptrofs.zero]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hnv : listNorepet (varNames f_sasl_choose_oauth.fn_vars) := by decide
  have hnp : listNorepet (varNames f_sasl_choose_oauth.fn_params) := by decide
  have hdisj : listDisjoint (varNames f_sasl_choose_oauth.fn_params)
      (varNames f_sasl_choose_oauth.fn_temps) := by decide
  refine satisfies_internal ge (FunctionEntry2 ge) f_sasl_choose_oauth _ _ (PbodyO c fir xB)
    (fun m hp hf hpre hd hag => ?_) (oauth_body_after ge c fir xB hcenv hpn hpr hfollow hallow)
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (tptr tschar))
  let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv tint)
  have hav : AllocVariables ge.genv_cenv emptyEnv m f_sasl_choose_oauth.fn_vars (envO a1.2 a2.2) a2.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _))
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [f_sasl_choose_oauth, List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl <;> rw [hcenv] <;> decide)
    (Heap.union hp hf) hag
  have hL : Locs (LO a1.2 a2.2) hl := by
    have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv] at this
    exact this
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envO a1.2 a2.2,
    PTree.set _sctx (.Vptr xB Integers.Ptrofs.zero) (PTree.set _data (.Vptr c.dB c.dO)
      (createUndefTemps f_sasl_choose_oauth.fn_temps)),
    a2.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · have hne : a1.2 ≠ a2.2 := by
      obtain ⟨h1, r1, d1, rfl, x1, h2, r2, d2, rfl, x2, _⟩ := hL
      exact Case3C.anyBytes_ne x1 x2 (by
        rw [Heap.disjoint_union_right] at d1; exact d1.1) (by decide) (by decide)
    refine ⟨(a1.2, a2.2), hne, rfl, ?_, ⟨hp, hl, dph, rfl, hpre.2, hL⟩⟩
    exact TempsHold_cons (PTree.gss _ _ _)
      (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)) (TempsHold_nil _))

end Deb2025_14524U
