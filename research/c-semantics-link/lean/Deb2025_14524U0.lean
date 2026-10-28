/-
CVE-2025-14524: 上流の修正前（U0、curl bb134bba29）の `Curl_sasl_start`。

証明すること（`start_before`、P0）: Bearer が設定され、利用者名があり、`enabledmechs` が OAUTHBEARER を含み EXTERNAL を含まず、
`force_ir` が真のとき、戻り値は `Curl_auth_create_oauth_bearer_message` の戻り値 `r`（0 でない任意の値）。
その仕様は「4番目の引数が Bearer の値なら `r` を返す」なので、Bearer を渡して呼んでいる（リダイレクトのあとかどうかを見ない）。
`Curl_sasl_start` 自体は修正の前後で同じ関数（`start_same`）なので、U1 と同じ入口・前半の証明を使う。
-/
import Deb2025_14524UH0
open CC CC.Sep CC.HProp
open Deb2025_14524_u1
open Deb2025_14524
open Case5C (addr RR call_fwd eval_field bitOf triple_nop_loop)
open Case4debC (lv_field eval_deref_temp)
open Case3C (CellD cellH Cells cell_load3 assign_cell3 Locs)

set_option maxRecDepth 20000

namespace Deb2025_14524U

/-- P0 の仕様: 戻り値は `r`。 -/
def startSpecB (c : Ctx) (r : Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _SASL noattr), tptr (Ty.Tstruct _Curl_easy noattr), tbool, tptr tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = argsS c true ∧ Hs c hp
  post := fun v hp => v = .Vint r ∧
    (Cells (outer c (Integers.Int.repr 0)) ∗ SW3 c true) hp
  measure := fun _ => 0

/-- 呼ばれる側（U0）。 -/
structure ExtU0 (ge : CGenv) (c : Ctx) (bL : Block) (hv : Val) (pv : Integers.Int) (rd rp rl : Val)
    (r : Integers.Int) where
  fdMs : FunDef
  ms : Callee ge _memset fdMs
  tMs : typeOfFundef fdMs = .Tfunction msTy (tptr tvoid) cc_default
  sMs : ∀ xB vs, SatisfiesAt ge (FunctionEntry2 ge) fdMs
    (specK msTy (tptr tvoid) cc_default (Kms c true xB) (Kms' c true xB) none) vs
  fdIn : FunDef
  bin : Callee ge _Curl_bufref_init fdIn
  tIn : typeOfFundef fdIn = .Tfunction brTy tvoid cc_default
  sIn : ∀ xB vs, SatisfiesAt ge (FunctionEntry2 ge) fdIn
    (specK brTy tvoid cc_default (Win c true xB) (Win c true xB) none) vs
  fdFr : FunDef
  bfr : Callee ge _Curl_bufref_free fdFr
  tFr : typeOfFundef fdFr = .Tfunction brTy tvoid cc_default
  sFr : ∀ xB vs, SatisfiesAt ge (FunctionEntry2 ge) fdFr
    (specK brTy tvoid cc_default (W2 c true xB bL rd rp rl r) (W2 c true xB bL rd rp rl r) none) vs
  ext : Callee ge _sasl_choose_external (.Internal Deb2025_14524_u0.f_sasl_choose_external)
  oa : Callee ge _sasl_choose_oauth (.Internal Deb2025_14524_u0.f_sasl_choose_oauth)
  inner : ∀ xB, ExtO ge c true xB bL hv pv rd rp rl r

theorem w2_ret {c : Ctx} {fir : Bool} {xB bL : Block} {rd rp rl : Val} {r : Integers.Int} {hp : Heap}
    (hH : W2 c fir xB bL rd rp rl r hp) :
    ((Cells (outer c (Integers.Int.repr 0)) ∗ SW3 c fir) ∗ Locs [(xB, 80)]) hp := by
  unfold W2 at hH
  rw [cells_append, sep_assoc_eq, sep_comm_eq, sep_assoc_eq] at hH
  rw [sep_assoc_eq]
  obtain ⟨h1, h2, d, rfl, ho, h2'⟩ := hH
  obtain ⟨h3, h4, d', rfl, hsw, hs⟩ := h2'
  refine ⟨h1, Heap.union h3 h4, d, rfl, ho, h3, h4, d', rfl, hsw, ?_⟩
  show (anyBytes .Freeable xB 0 80 ∗ emp) h4
  rw [sep_emp_eq]
  exact sctx_any hs

/-- `sasl_choose_*` を呼ぶ（前後のメモリと戻り値を一般にしたもの）。 -/
theorem call_choose2 (ge : CGenv) (c : Ctx) (xB : Block) (l : List (Ident × Val)) (Wpre Wpost : HProp)
    (ret : Bool) (id fid : Ident) (fn : Function) (cal : Callee ge fid (.Internal fn))
    (hpar : typeOfFundef (.Internal fn) = .Tfunction
      [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _sasl_ctx noattr)] tbool cc_default)
    (hS : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal fn) (chooseSpec c xB Wpre Wpost ret) vs)
    (hd : (_data, Val.Vptr c.dB c.dO) ∈ l) (hne : fid ≠ _sctx) :
    Triple ge (FunctionEntry2 ge) f_Curl_sasl_start (LocalSt (envS xB) l Wpre)
      (.Scall (some id) (.Evar fid (Ty.Tfunction
          [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _sasl_ctx noattr)] tbool cc_default))
        [.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)),
         .Eaddrof (.Evar _sctx (Ty.Tstruct _sasl_ctx noattr)) (tptr (Ty.Tstruct _sasl_ctx noattr))])
      (.only (LocalSt (envS xB) (setLocal l id (Val.ofBool ret)) Wpost)) :=
  callS_some ge _ _ _ Wpre Wpost (Val.ofBool ret) id _ _ (envS xB) l
    [.Vptr c.dB c.dO, .Vptr xB Integers.Ptrofs.zero] cal.b (.Internal fn) hS cal.fp hpar rfl
    (fun _ _ _ => eval_callee_global (envS_get hne) cal.sym rfl)
    (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get hd)) rfl
      (EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (PTree.gss _ _ _))) rfl
        EvalExprlist.nil))
    (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h)

set_option maxHeartbeats 4000000 in
theorem start_body_before (ge : CGenv) (c : Ctx) (bL : Block) (hv : Val) (pv : Integers.Int)
    (rd rp rl : Val) (r : Integers.Int)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hE : Integers.Int.and (em c) (Integers.Int.repr 32) = Integers.Int.zero)
    (hr : Integers.Int.eq r Integers.Int.zero = false)
    (hbset : c.bset = true)
    (hO : Integers.Int.eq (Integers.Int.and (em c) (Integers.Int.repr 256)) Integers.Int.zero = false)
    (hsir : bitOf c.setw 1 = true) (hal : addr c.sO 28 % 4 = 0)
    (hcu : Case4debC.IsPtr c.cuV) (hhv : Case4debC.IsPtr hv)
    (X : ExtU0 ge c bL hv pv rd rp rl r) :
    Triple ge (FunctionEntry2 ge) f_Curl_sasl_start (PbodyS c true) f_Curl_sasl_start.fn_body
      (RR (startSpecB c r).post Sep.Assn.no) := by
  refine Sep.triple_exists ge _ _ _ _ _ (fun xB => ?_)
  refine pre_conv ge _ _ (H2 := mapsto .Mint32 c.pm c.sB (addr c.sO 28) (.Vint c.sw)
    ∗ (Cells (outer c c.prv) ∗ Locs [(xB, 80)])) (fun hp h => by unfold Hs at h; rwa [sep_assoc_eq] at h) ?_
  -- sasl->force_ir = force_ir;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (bitstore_front ge _ _ (envS xB) _ _ c.pm c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 28))
      18 c.sw (if true then Integers.Int.one else Integers.Int.zero) _ _ hpw hpr rfl (by decide) (by decide)
      (fun le m hT => EvalLvalue.Efield_struct _ _ _ _ _ _ _ _ _ _
        (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_sasl) (hcenv ▸ off_fir))
      (fun le m hT => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)),
        rfl⟩)) ?_
  -- sasl->authused = 0;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (store16_word ge _ _ (envS xB) _ _ c.pm c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 28))
      (swF c true) (.Vint (Integers.Int.repr 0)) _ _ hpw rfl
      (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_sasl)
        (hcenv ▸ off_au))
      (fun le m hT => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  refine pre_conv ge _ _ (H2 := Cells (outer c c.prv) ∗ (SW2 c true (Integers.Int.repr 0) ∗ Locs [(xB, 80)]))
    (fun hp h => by
      unfold SW2
      rw [sep_assoc_eq] at h
      rw [sep_left_comm_eq, sep_assoc_eq]
      exact h) ?_
  -- *progress = SASL_IDLE;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell3 ge _ _ (envS xB) _ (outer c c.prv) _ 2 (by simp) .Mint32 c.pm c.pB c.pO
      (.Vint c.prv) (.Vint (Integers.Int.repr 0)) rfl _ _ hpw rfl
      (fun le m hT => EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))
      (fun _ _ _ _ _ _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  -- memset(&sctx, 0, sizeof(sctx));
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ msTy (tptr tvoid) cc_default (Kms c true xB) (Kms' c true xB) none _ _ (envS xB) _
      _ X.ms.b X.fdMs (X.sMs xB) X.ms.fp X.tMs rfl
      (fun _ _ _ => eval_callee_global (envS_get (by decide)) X.ms.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (PTree.gss _ _ _))) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Esizeof _ _) rfl EvalExprlist.nil)))) ?_
  -- sctx.sasl = sasl;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell3 ge _ _ (envS xB) _ (sctxZ xB ++ outer c (Integers.Int.repr 0)) _ 0 (by simp) Mptr
      .Freeable xB _ z64 (.Vptr c.sB c.sO) rfl _ _ rfl rfl
      (fun le m hT => lvx hcenv offx_sasl)
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.sB c.sO) (hT.get (by temps_get)), rfl⟩)) ?_
  -- sctx.conn = data->conn;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envS xB) _ _ _ _ (.Vptr c.cB c.cO)
        (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_easy)
          (hcenv ▸ off_conn) rfl (ldC hH hag 17 (by simp) rfl hpr)))
      (assign_cell3 ge _ _ (envS xB) _ _ _ 1 (by simp) Mptr .Freeable xB _ z64 (.Vptr c.cB c.cO) rfl
        _ _ rfl rfl (fun le m hT => lvx hcenv offx_conn)
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩))) ?_
  -- sctx.user = data->state.aptr.user;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envS xB) _ _ _ _ (.Vptr c.uB c.uO)
        (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _
          (lv_field (EvalExpr.Elvalue _ _ _ .Full _
              (lv_field (EvalExpr.Elvalue _ _ _ .Full _
                  (lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_easy)
                    (hcenv ▸ off_state)) (DerefLoc.copy rfl))
                rfl (hcenv ▸ co_us) (hcenv ▸ off_aptr)) (DerefLoc.copy rfl))
            rfl (hcenv ▸ co_aptr) (hcenv ▸ off_auser))
          (DerefLoc.value Mptr _ rfl (ldC hH hag 20 (by simp) rfl hpr))))
      (assign_cell3 ge _ _ (envS xB) _ _ _ 2 (by simp) Mptr .Freeable xB _ z64 (.Vptr c.uB c.uO) rfl
        _ _ rfl rfl (fun le m hT => lvx hcenv offx_user)
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩))) ?_
  -- Curl_bufref_init(&sctx.resp);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ brTy tvoid cc_default (Win c true xB) (Win c true xB) none _ _ (envS xB) _
      _ X.bin.b X.fdIn (X.sIn xB) X.bin.fp X.tIn rfl
      (fun _ _ _ => eval_callee_global (envS_get (by decide)) X.bin.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (lvx hcenv offx_resp)) rfl EvalExprlist.nil)) ?_
  -- sctx.enabledmechs = sasl->authmechs & sasl->prefmech;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envS xB) _ _ _ _ (.Vint (Integers.Int.zero_ext 16 c.am))
        (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_sasl)
          (hcenv ▸ off_am) rfl (ldC hH hag 14 (by simp) rfl hpr)))
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envS xB) _ _ _ _ (.Vint (Integers.Int.zero_ext 16 c.pf))
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_sasl)
            (hcenv ▸ off_pf) rfl (ldC hH hag 15 (by simp) rfl hpr)))
        (assign_cell3 ge _ _ (envS xB) _ _ _ 3 (by simp) .Mint16unsigned .Freeable xB _
          (.Vint (Integers.Int.repr 0)) (.Vint (em c)) rfl _ _ rfl rfl
          (fun le m hT => lvx hcenv offx_em)
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl, rfl⟩)))) ?_
  -- sctx.state1 = SASL_STOP; sctx.state2 = SASL_FINAL;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell3 ge _ _ (envS xB) _ _ _ 7 (by simp) .Mint32 .Freeable xB _
      (.Vint (Integers.Int.repr 0)) (.Vint (Integers.Int.repr 0)) rfl _ _ rfl rfl
      (fun le m hT => lvx hcenv offx_s1) (fun _ _ _ _ _ _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell3 ge _ _ (envS xB) _ _ _ 8 (by simp) .Mint32 .Freeable xB _
      (.Vint (Integers.Int.repr 0)) (.Vint (Integers.Int.repr 17)) rfl _ _ rfl rfl
      (fun le m hT => lvx hcenv offx_s2) (fun _ _ _ _ _ _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  refine pre_conv ge _ _ (H2 := W1 c true xB) (fun hp h => h) ?_
  -- sasl_choose_external(…) は偽、sasl_choose_oauth(…) は真（ここで選ばれる）
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_seq_fwd ge _ _ _ _ _ _ _
              (call_choose2 ge c xB _ _ _ false _ _ _ X.ext rfl
                (by rw [ext_same]; exact ext_after ge c true xB hcenv hE) (by temps_get) (by decide))
              (triple_if_local ge _ _ (envS xB) _ (W1 c true xB) _ false _ _ _
                (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false)
                  (hT.get (by temps_get)), rfl⟩)
                (triple_seq_fwd ge _ _ _ _ _ _ _
                  (call_choose2 ge c xB _ _ _ true _ _ _ X.oa rfl
                    (oauth_before ge c true xB bL hv pv rd rp rl r hcenv hpn hpr hpw hbset hO hsir hal
                      hcu hhv (X.inner xB)) (by temps_get) (by decide))
                  (triple_set_local_fwd ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ _ (Val.ofBool true)
                    (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                      (EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get))) rfl)))))
            (triple_if_local ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ true _ _ _
              (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true)
                (hT.get (by temps_get)), rfl⟩)
              (triple_set_local_fwd ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ _
                (.Vint (Integers.Int.repr 1)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))))
          (triple_if_local ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ true _ _ _
            (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 1))
              (hT.get (by temps_get)), rfl⟩)
            (triple_set_local_fwd ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ _
              (.Vint (Integers.Int.repr 1)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))))
        (triple_if_local ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 1))
            (hT.get (by temps_get)), rfl⟩)
          (triple_set_local_fwd ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ _
            (.Vint (Integers.Int.repr 1)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))))
      (triple_if_local ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 1))
          (hT.get (by temps_get)), rfl⟩)
        (triple_nop_loop ge _ _ _))) ?_
  -- if(!sctx.result && sctx.mech) …（result は r で 0 でないので通らない）
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ _ (.Vint r)
          (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _ (lvx hcenv offx_res)
            (DerefLoc.value .Mint32 _ rfl (by unfold W2 at hH; exact ldC hH hag 12 (by simp) rfl freeable_r))))
        (triple_if_local ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ (.Vint r) (hT.get (by temps_get))) (notbool_nz hr m), rfl⟩)
          (triple_set_local_fwd ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ _
            (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))))
      (triple_if_local ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0))
          (hT.get (by temps_get)), rfl⟩)
        (triple_skip ge _ _ _))) ?_
  -- Curl_bufref_free(&sctx.resp);  return sctx.result;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ brTy tvoid cc_default (W2 c true xB bL rd rp rl r) (W2 c true xB bL rd rp rl r)
      none _ _ (envS xB) _ _ X.bfr.b X.fdFr (X.sFr xB) X.bfr.fp X.tFr rfl
      (fun _ _ _ => eval_callee_global (envS_get (by decide)) X.bfr.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (lvx hcenv offx_resp)) rfl EvalExprlist.nil)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envS xB) _ (W2 c true xB bL rd rp rl r) _ _ (.Vint r)
      (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _ (lvx hcenv offx_res)
        (DerefLoc.value .Mint32 _ rfl (by unfold W2 at hH; exact ldC hH hag 12 (by simp) rfl freeable_r)))) ?_
  refine pre_conv ge _ _ (fun _ h => w2_ret h) ?_
  refine Case3C.ret_locs ge _ _ (envS xB) _ _ [(xB, 80)] _ (.Vint r) (.Vint r) _
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ (.Vint r) (hT.get (by temps_get)))
    (fun _ => rfl) ?_ ?_ (fun hp hH => ⟨rfl, hH⟩)
  · rw [blocks_envS ge hcenv]
    intro x hx'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
    subst hx'
    exact ⟨xB, 80, rfl, by simp⟩
  · rw [blocks_envS ge hcenv]
    simp

end Deb2025_14524U
