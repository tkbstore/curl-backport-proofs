/-
CVE-2026-7168: @DESC@

証明すること（`cases/CVE-2026-7168.md` の場面）: `option` が `CURLOPT_PROXY` のとき、関数は `setproxy` の戻り値を返し、
戻った時点の所有は `cells @LAY@ c (sAfter @LAY@ c same sv)`（`same` は `strcmp` が 0 を返したか）。
`same` が偽なら `proxydigest.nonce` は NULL、`authproxy.picked` は 0 になる。
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

/-- `strcmp` の戻り値 `r` が 0 か（`same`）。 -/
def retv (same : Bool) (rs : Integers.Int) : Val := cond same (.Vint (Integers.Int.repr 0)) (.Vint rs)

def spSpec (c : Ctx) (same : Bool) (rs : Integers.Int) (sv : Val) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr tschar]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dataB c.dataO, .Vptr c.pB c.pO]
    ∧ Cells .Freeable (cells @LAY@ c (s0 c)) hp
  post := fun v hp => v = retv same rs ∧ Cells .Freeable (cells @LAY@ c (sAfter @LAY@ c same sv)) hp
  measure := fun _ => 0

def cptrSpec (c : Ctx) (same : Bool) (rs : Integers.Int) (sv : Val) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tint, tptr tschar]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dataB c.dataO, .Vint (Integers.Int.repr 10004), .Vptr c.pB c.pO]
    ∧ Cells .Freeable (cells @LAY@ c (s0 c)) hp
  post := (spSpec c same rs sv).post
  measure := fun _ => 0

/-- `Curl_auth_digest_cleanup(&data->state.proxydigest)`: `nonce` を NULL にする。 -/
def digestSpec (c : Ctx) (s : St) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _digestdata noattr)]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => (∃ rest, vargs = .Vptr c.dataB (f2 c.dataO @STOFF@ 0) :: rest)
    ∧ Cells .Freeable (cells @LAY@ c s) hp
  post := fun _ hp => Cells .Freeable (cells @LAY@ c { s with nonce := vnull }) hp
  measure := fun _ => 0

/-- `memset(&data->state.authproxy, 0, sizeof(...))`: `picked` を 0 にする（減らした構造体は `picked` だけ）。 -/
def memsetSpec (c : Ctx) (s : St) : FunSpec where
  tyargs := [tptr tvoid, tint, tulong]
  tyres := tptr tvoid
  cc := cc_default
  pre := fun vargs hp => (∃ rest, vargs = .Vptr c.dataB (f2 c.dataO @STOFF@ 8) :: rest)
    ∧ Cells .Freeable (cells @LAY@ c s) hp
  post := fun _ hp => Cells .Freeable (cells @LAY@ c { s with picked := @LAY@.pzero }) hp
  measure := fun _ => 0

/-- `Curl_setstropt(&data->set.str[STRING_PROXY], ptr)`: 任意の `rs` を返し、`str[STRING_PROXY]` を任意の `sv` にする。 -/
def setstrSpec (c : Ctx) (s : St) (rs : Integers.Int) (sv : Val) : FunSpec where
  tyargs := [tptr (tptr tschar), tptr tschar]
  tyres := tint
  cc := cc_default
  pre := fun _ hp => Cells .Freeable (cells @LAY@ c s) hp
  post := fun v hp => v = .Vint rs ∧ Cells .Freeable (cells @LAY@ c { s with str := sv }) hp
  measure := fun _ => 0

def sN (c : Ctx) : St := ⟨.Vptr c.oldB c.oldO, vnull, c.picked0⟩
def sNP (c : Ctx) : St := ⟨.Vptr c.oldB c.oldO, vnull, @LAY@.pzero⟩

set_option hygiene false in
macro "ldc7 " i:num x:term:max : term => `(ld hpr hH hag (x := $x) (mem_idx $i rfl) rfl)
set_option hygiene false in
macro "tget7 " v:term:max : term => `(TempsHold.get hT (v := $v) (by temps_get))

theorem cast_vptr_bool {b : Block} {o : Integers.Ptrofs} {t : Ty} {m : Mem}
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.semCast (.Vptr b o) (tptr t) tbool m = some (Val.ofBool true) := by
  unfold Cop.semCast
  simp [Cop.classifyCast, tptr, tbool, hv, Archi.ptr64, Val.ofBool] <;> rfl

theorem sp_entry_wf :
    listNorepet (varNames f_setproxy.fn_vars) ∧ listNorepet (varNames f_setproxy.fn_params)
    ∧ listDisjoint (varNames f_setproxy.fn_params) (varNames f_setproxy.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxHeartbeats 4000000 in
/-- **`setproxy`**（Debian と上流で本体は同じ）。 -/
theorem setproxy_ok (ge : CGenv) (c : Ctx) (r rs : Integers.Int) (same : Bool) (sv : Val)
    (hrs : Integers.Int.eq r Integers.Int.zero = same)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (bCmp bDg bMs bSet : Block) (fdCmp fdDg fdMs fdSet : FunDef)
    (hsCmp : Genv.findSymbol ge.genv_genv _strcmp = some bCmp)
    (hsDg : Genv.findSymbol ge.genv_genv _Curl_auth_digest_cleanup = some bDg)
    (hsMs : Genv.findSymbol ge.genv_genv _memset = some bMs)
    (hsSet : Genv.findSymbol ge.genv_genv _Curl_setstropt = some bSet)
    (hfCmp : FuncPtr ge bCmp fdCmp) (hfDg : FuncPtr ge bDg fdDg) (hfMs : FuncPtr ge bMs fdMs)
    (hfSet : FuncPtr ge bSet fdSet)
    (htyCmp : typeOfFundef fdCmp = .Tfunction [tptr tschar, tptr tschar] tint cc_default)
    (htyDg : typeOfFundef fdDg = .Tfunction [tptr (Ty.Tstruct _digestdata noattr)] tvoid cc_default)
    (htyMs : typeOfFundef fdMs = .Tfunction [tptr tvoid, tint, tulong] (tptr tvoid) cc_default)
    (htySet : typeOfFundef fdSet = .Tfunction [tptr (tptr tschar), tptr tschar] tint cc_default)
    (hCmp : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCmp
      (retSpec [tptr tschar, tptr tschar] tint (.Vint r)) vs)
    (hDg : ∀ s vs, SatisfiesAt ge (FunctionEntry2 ge) fdDg (digestSpec c s) vs)
    (hMs : ∀ s vs, SatisfiesAt ge (FunctionEntry2 ge) fdMs (memsetSpec c s) vs)
    (hSet : ∀ s vs, SatisfiesAt ge (FunctionEntry2 ge) fdSet (setstrSpec c s rs sv) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_setproxy) (spSpec c same rs sv) vs := by
  by_cases hvs : vs = [.Vptr c.dataB c.dataO, .Vptr c.pB c.pO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hpr : permOrder Permission.Freeable .Readable = true := rfl
  have hpn : permOrder Permission.Freeable .Nonempty = true := rfl
  obtain ⟨hnv, hnp, hdisj⟩ := sp_entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_setproxy _ _
    (LocalSt emptyEnv [(_proxy, .Vptr c.pB c.pO), (_data, .Vptr c.dataB c.dataO)]
      (Cells .Freeable (cells @LAY@ c (s0 c))))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _proxy (.Vptr c.pB c.pO)
              (PTree.set _data (.Vptr c.dataB c.dataO) (createUndefTemps f_setproxy.fn_temps)),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_nil _)), hpre.2⟩
    exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
  cases same
  case true =>
    -- 同じプロキシ: return CURLE_OK;
    refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'6 _ (.Vptr c.oldB c.oldO) (fun le m hp hT hH hag =>
          eval_lv_load (lv_arr (tget7 (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
            (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc7 0 (cStr @LAY@ c (s0 c)))))
        (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
          (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
            boolVal_vptr (cells_weakValid hpn hH hag (c := cOld c) (mem_idx 3 rfl) Nat.one_pos)⟩)
          (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'1 _ (Val.ofBool true) (fun le m hp hT hH hag =>
            EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget7 (.Vptr c.pB c.pO)))
              (cast_vptr_bool (cells_weakValid hpn hH hag (c := cPtr c) (mem_idx 4 rfl) Nat.one_pos))))))
      (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'5 _ (.Vptr c.oldB c.oldO) (fun le m hp hT hH hag =>
              eval_lv_load (lv_arr (tget7 (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
                (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc7 0 (cStr @LAY@ c (s0 c)))))
            (call_ret ge _ _ _ _ _ _t'3 _ _ emptyEnv _ _ [.Vptr c.oldB c.oldO, .Vptr c.pB c.pO]
              bCmp fdCmp hCmp hfCmp htyCmp rfl (fun _ _ _ => eval_callee_global rfl hsCmp rfl)
              (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ _ (tget7 (.Vptr c.oldB c.oldO))) rfl
                (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget7 (.Vptr c.pB c.pO))) rfl
                  EvalExprlist.nil))))
          (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'2 _ (Val.ofBool (Integers.Int.eq r Integers.Int.zero))
            (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (tget7 (.Vint r))) notbool_int) (cast_ofBool_int_bool _ m)))))) ?_
    exact triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget7 (Val.ofBool (Integers.Int.eq r Integers.Int.zero))),
        by rw [hrs]; rfl⟩)
      (triple_return_local ge _ _ _ _ _ _ (.Vint (Integers.Int.repr 0)) (.Vint (Integers.Int.repr 0))
        (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl) (fun hp hH => ⟨rfl, hH⟩))
  case false =>
    -- 違うプロキシ: Digest の状態を消し、authproxy を 0 にして、新しい文字列を入れる
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'6 _ (.Vptr c.oldB c.oldO) (fun le m hp hT hH hag =>
          eval_lv_load (lv_arr (tget7 (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
            (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc7 0 (cStr @LAY@ c (s0 c)))))
        (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
          (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
            boolVal_vptr (cells_weakValid hpn hH hag (c := cOld c) (mem_idx 3 rfl) Nat.one_pos)⟩)
          (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'1 _ (Val.ofBool true) (fun le m hp hT hH hag =>
            EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget7 (.Vptr c.pB c.pO)))
              (cast_vptr_bool (cells_weakValid hpn hH hag (c := cPtr c) (mem_idx 4 rfl) Nat.one_pos))))))
      (triple_if_local ge _ _ emptyEnv _ _ _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'5 _ (.Vptr c.oldB c.oldO) (fun le m hp hT hH hag =>
              eval_lv_load (lv_arr (tget7 (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy) (hcenv ▸ off_set)
                (hcenv ▸ co_ud) (hcenv ▸ off_str) rfl) rfl (ldc7 0 (cStr @LAY@ c (s0 c)))))
            (call_ret ge _ _ _ _ _ _t'3 _ _ emptyEnv _ _ [.Vptr c.oldB c.oldO, .Vptr c.pB c.pO]
              bCmp fdCmp hCmp hfCmp htyCmp rfl (fun _ _ _ => eval_callee_global rfl hsCmp rfl)
              (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ _ (tget7 (.Vptr c.oldB c.oldO))) rfl
                (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget7 (.Vptr c.pB c.pO))) rfl
                  EvalExprlist.nil))))
          (triple_set_local_fwd ge _ _ emptyEnv _ _ _t'2 _ (Val.ofBool (Integers.Int.eq r Integers.Int.zero))
            (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (tget7 (.Vint r))) notbool_int) (cast_ofBool_int_bool _ m))))))
      (triple_if_local ge _ _ emptyEnv _ _ _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget7 (Val.ofBool (Integers.Int.eq r Integers.Int.zero))),
          by rw [hrs]; rfl⟩)
        (triple_skip ge _ _ _))) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (call_void_cells ge _ _ (digestSpec c (s0 c)) _ _ emptyEnv _ _ _ [.Vptr c.dataB (f2 c.dataO @STOFF@ 0)]
        bDg fdDg (hDg _) hfDg htyDg rfl (fun _ _ _ => eval_callee_global rfl hsDg rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Eaddrof _ _ _ _ (lv_f2 (tget7 (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy)
            (hcenv ▸ off_state) (hcenv ▸ co_state) (hcenv ▸ off_proxydigest))) rfl EvalExprlist.nil)
        (fun _ h => ⟨⟨[], rfl⟩, h⟩) (fun _ _ h => h)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (call_void_cells ge _ _ (memsetSpec c (sN c)) _ _ emptyEnv _ _ _
        [.Vptr c.dataB (f2 c.dataO @STOFF@ 8), .Vint (Integers.Int.repr 0), _]
        bMs fdMs (hMs _) hfMs htyMs rfl (fun _ _ _ => eval_callee_global rfl hsMs rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Eaddrof _ _ _ _ (lv_f2 (tget7 (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy)
            (hcenv ▸ off_state) (hcenv ▸ co_state) (hcenv ▸ off_authproxy))) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl
            (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Esizeof _ _) rfl EvalExprlist.nil)))
        (fun _ h => ⟨⟨_, rfl⟩, h⟩) (fun _ _ h => h)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (call_set_cells ge _ _ (setstrSpec c (sNP c) rs sv)
        _t'4 _ _ emptyEnv _ _ _ [_, .Vptr c.pB c.pO] (.Vint rs) bSet fdSet (hSet _) hfSet htySet rfl
        (fun _ _ _ => eval_callee_global rfl hsSet rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Elvalue _ _ _ .Full _ (lv_f2 (tget7 (.Vptr c.dataB c.dataO)) (hcenv ▸ co_easy)
              (hcenv ▸ off_set) (hcenv ▸ co_ud) (hcenv ▸ off_str)) (DerefLoc.reference rfl))
            (EvalExpr.Econst_int _ _) (semAdd_ptr_int _ _ _ _ _ rfl)) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget7 (.Vptr c.pB c.pO))) rfl
            EvalExprlist.nil))
        (fun _ h => h) (fun _ _ h => h)) ?_
    exact triple_return_local ge _ _ _ _ _ _ (.Vint rs) (.Vint rs)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (tget7 (.Vint rs))) (fun _ => rfl)
      (fun hp hH => ⟨rfl, hH⟩)

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
/-- **`@FNC@(data, CURLOPT_PROXY, ptr)`**: `setproxy` を呼んでその値を返す。 -/
theorem @THM@ (ge : CGenv) (c : Ctx) (same : Bool) (rs : Integers.Int) (sv : Val)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (bSp : Block) (hsSp : Genv.findSymbol ge.genv_genv _setproxy = some bSp)
    (hfSp : FuncPtr ge bSp (.Internal f_setproxy))
    (hSp : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_setproxy) (spSpec c same rs sv) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal @FN@) (cptrSpec c same rs sv) vs := by
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
    (Case5C.call_fwd ge _ _ (spSpec c same rs sv) @TSP@ _ _ (envUP _u _p b1 b2) _
      (Cells .Freeable (cells @LAY@ c (s0 c))) (Cells .Freeable [lcell b1, lcell b2])
      (Cells .Freeable (cells @LAY@ c (sAfter @LAY@ c same sv))) _ _
      [.Vptr c.dataB c.dataO, .Vptr c.pB c.pO] (retv same rs)
      bSp _ hSp hfSp rfl rfl
      (fun _ _ _ => eval_callee_global (envUP_none _ _ _ _ _ (by decide) (by decide)) hsSp rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (tget7 (.Vptr c.dataB c.dataO))) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget7 (.Vptr c.pB c.pO))) rfl
          EvalExprlist.nil))
      (fun _ h => ⟨rfl, h⟩) (fun _ _ h => h) (cells_append _ _ _) (cells_append _ _ _).symm) ?_
  refine return_locals2 ge _ _ _u _p b1 b2 _ _ _ _ (retv same rs)
    (retv same rs) hne hbl hbp
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) ?_ (fun hp hH => ⟨rfl, hH⟩)
  intro m
  cases same <;> rfl

end Deb2026_7168.@NS@
