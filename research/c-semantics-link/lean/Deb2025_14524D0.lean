/-
CVE-2025-14524: curl 8.14.1（D0、パッチを当てる前）の `Curl_sasl_start`。

証明すること（`start_before`、P0）: U0 の `Deb2025_14524U.start_before` と同じ形（仕様 `startSpecB` も同じ）。
Bearer が設定され、利用者名があり、`enabledmechs` が OAUTHBEARER を含み EXTERNAL を含まず、`force_ir` が真のとき、
`Curl_auth_create_oauth_bearer_message` を 4番目の引数を Bearer の値にして呼び、その戻り値 `r`（0 でない）を返す。
-/
import Deb2025_14524D1Main
open CC CC.Sep CC.HProp
open Deb2025_14524_d0
open Deb2025_14524
open Case5C (addr RR eval_field bitOf sep_l sep_r)
open Case4debC (lv_field eval_deref_temp)
open Case3C (CellD cellH Cells cell_load3 assign_cell3 Locs)
open Deb2025_14524U (eval_bit2 ldC notbool_nz cast_bool_zero bitOf_true bitOf_false Callee cond_and_false
  msTy brTy Hs argsS startSpecB z64 SW3 crTy crSpec freeable_r)

set_option maxRecDepth 20000

namespace Deb2025_14524D

/-- 局所変数のうち `hostname`・`port` に値が入った形（`Curl_conn_get_host` のあと）。 -/
def LH (bs : Block × Block × Block × Block × Block) (hv : Val) (pv : Integers.Int) : HProp :=
  anyBytes .Freeable bs.1 0 24 ∗
    (mapsto Mptr .Freeable bs.2.1 (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) hv ∗
    (anyBytes .Freeable bs.2.2.1 0 8 ∗
    (mapsto .Mint32 .Freeable bs.2.2.2.1 (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) (.Vint pv) ∗
    (anyBytes .Freeable bs.2.2.2.2 0 24 ∗ emp))))

theorem LH_locs {bs : Block × Block × Block × Block × Block} {hv : Val} {pv : Integers.Int} {h : Heap}
    (hH : LH bs hv pv h) : Locs (LD bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2) h := by
  obtain ⟨h1, r1, d1, rfl, a1, h2, r2, d2, rfl, m2, h3, r3, d3, rfl, a3, h4, r4, d4, rfl, m4, h5⟩ := hH
  exact ⟨h1, _, d1, rfl, a1, h2, _, d2, rfl, Case3C.mapsto_anyBytes m2, h3, _, d3, rfl, a3,
    h4, _, d4, rfl, Case3C.mapsto_anyBytes m4, h5⟩

def WDh (c : Ctx) (bs : Block × Block × Block × Block × Block) (hv : Val) (pv : Integers.Int) : HProp :=
  Cells (outer c c.prv) ∗ (mapsto .Mint32 c.pm c.sB (addr c.sO 28) (.Vint c.sw) ∗ LH bs hv pv)

def WE1 (c : Ctx) (bs : Block × Block × Block × Block × Block) (hv : Val) (pv : Integers.Int) : HProp :=
  Cells (outer c (Integers.Int.repr 0)) ∗ (SW2 c true (Integers.Int.repr 0) ∗ LH bs hv pv)

def WE2 (c : Ctx) (bs : Block × Block × Block × Block × Block) (hv : Val) (pv : Integers.Int) : HProp :=
  Cells (outer c (Integers.Int.repr 0)) ∗ (SW3 c true ∗ LH bs hv pv)

theorem WE2_loads {c : Ctx} {bs : Block × Block × Block × Block × Block} {hv : Val} {pv : Integers.Int}
    {hp : Heap} {m : Mem} (hhv : Case4debC.IsPtr hv) (hH : WE2 c bs hv pv hp) (hag : Heap.Agrees hp m) :
    Mem.load Mptr m bs.2.1 (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) = some hv
    ∧ Mem.load .Mint32 m bs.2.2.2.1 (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) = some (.Vint pv) := by
  obtain ⟨h1, c1, a1⟩ := sep_r hH hag
  obtain ⟨h2, c2, a2⟩ := sep_r c1 a1
  obtain ⟨h3, c3, a3⟩ := sep_r c2 a2
  obtain ⟨h4, c4, a4⟩ := sep_l c3 a3
  obtain ⟨h5, c5, a5⟩ := sep_r c3 a3
  obtain ⟨h6, c6, a6⟩ := sep_r c5 a5
  obtain ⟨h7, c7, a7⟩ := sep_l c6 a6
  exact ⟨by rw [mapsto_load freeable_r c4 a4, Case4debC.loadResult_ptr hhv], mapsto_load freeable_r c7 a7⟩

/-- 呼ばれる側（D0）。 -/
structure ExtD0 (ge : CGenv) (c : Ctx) (bL : Block) (hv : Val) (pv r : Integers.Int) where
  fdG : FunDef
  gh : Callee ge _Curl_conn_get_host fdG
  tG : typeOfFundef fdG = .Tfunction ghTy tvoid cc_default
  sG : ∀ bs vs, SatisfiesAt ge (FunctionEntry2 ge) fdG
    (specK ghTy tvoid cc_default (WD0 c bs) (WDh c bs hv pv) none) vs
  fdIn : FunDef
  bin : Callee ge _Curl_bufref_init fdIn
  tIn : typeOfFundef fdIn = .Tfunction brTy tvoid cc_default
  sIn : ∀ bs vs, SatisfiesAt ge (FunctionEntry2 ge) fdIn
    (specK brTy tvoid cc_default (WDh c bs hv pv) (WDh c bs hv pv) none) vs
  fdC : FunDef
  cr : Callee ge _Curl_auth_create_oauth_bearer_message fdC
  tC : typeOfFundef fdC = .Tfunction crTy tint cc_default
  sC : ∀ bs vs, SatisfiesAt ge (FunctionEntry2 ge) fdC (crSpec c (WE2 c bs hv pv) (WE2 c bs hv pv) r) vs
  fdFr : FunDef
  bfr : Callee ge _Curl_bufref_free fdFr
  tFr : typeOfFundef fdFr = .Tfunction brTy tvoid cc_default
  sFr : ∀ bs vs, SatisfiesAt ge (FunctionEntry2 ge) fdFr
    (specK brTy tvoid cc_default (WE2 c bs hv pv) (WE2 c bs hv pv) none) vs
  lit : Genv.findSymbol ge.genv_genv ___stringlit_4 = some bL

abbrev lSD0 (c : Ctx) (fir : Bool) : List (Ident × Val) :=
  [(_progress, .Vptr c.pB c.pO), (_force_ir, Val.ofBool fir), (_data, .Vptr c.dB c.dO),
   (_sasl, .Vptr c.sB c.sO)]

def envD0 (b1 b2 b3 b4 b5 : Block) : Env :=
  ((((emptyEnv.set _resp (b1, Ty.Tstruct _bufref noattr)).set _hostname (b2, tptr tschar)).set
    _disp_hostname (b3, tptr tschar)).set _port (b4, tint)).set _nullmsg (b5, Ty.Tstruct _bufref noattr)

def envB0 (bs : Block × Block × Block × Block × Block) : Env :=
  envD0 bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2

def PbodyD0 (c : Ctx) (fir : Bool) : Sep.Assn := fun e le hp =>
  ∃ bs : Block × Block × Block × Block × Block,
    ((LD bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2).map Prod.fst).Pairwise (· ≠ ·) ∧
    LocalSt (envB0 bs) (lSD0 c fir) (Hs c ∗ Locs (LD bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2)) e le hp

theorem blocks_envB0 (ge : CGenv) (hcenv : ge.genv_cenv = Deb2025_14524_d1.prog.prog_comp_env)
    (bs : Block × Block × Block × Block × Block) :
    blocksOfEnv ge.genv_cenv (envB0 bs)
      = [(bs.2.2.2.1, 0, 4), (bs.2.1, 0, 8), (bs.2.2.1, 0, 8), (bs.1, 0, 24), (bs.2.2.2.2, 0, 24)] := by
  rw [hcenv]; rfl

macro "envget0" : tactic =>
  `(tactic| (unfold envB0 envD0; repeat (first
      | exact PTree.gss _ _ _
      | exact PTree.gempty _
      | refine (PTree.gso _ _ _ _ (by decide)).trans ?_)))

set_option maxHeartbeats 40000000 in
theorem start_body_before (ge : CGenv) (c : Ctx) (bL : Block) (hv : Val) (pv r : Integers.Int)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hE : Integers.Int.and (em c) (Integers.Int.repr 32) = Integers.Int.zero)
    (hr : Integers.Int.eq r Integers.Int.zero = false)
    (hbset : c.bset = true)
    (hO : Integers.Int.eq (Integers.Int.and (em c) (Integers.Int.repr 256)) Integers.Int.zero = false)
    (hcu : Case4debC.IsPtr c.cuV) (hhv : Case4debC.IsPtr hv)
    (X : ExtD0 ge c bL hv pv r) :
    Triple ge (FunctionEntry2 ge) f_Curl_sasl_start (PbodyD0 c true) f_Curl_sasl_start.fn_body
      (RR (startSpecB c r).post Sep.Assn.no) := by
  have hcenv1 := hcenv.trans cenv_same
  refine Sep.triple_exists ge _ _ _ _ _ (fun bs => ?_)
  refine Case1C.triple_pure ge _ _ _ _ _ _ (fun hnd => ?_)
  refine pre_conv ge _ _ (H2 := WD0 c bs) (fun hp h => by
    unfold WD0 Hs at *; rw [sep_comm_eq (mapsto _ _ _ _ _) (Cells _), sep_assoc_eq] at h; exact h) ?_
  -- result = CURLE_OK; conn = data->conn; mech = NULL; state1 = SASL_STOP; state2 = SASL_FINAL;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envB0 bs) _ (WD0 c bs) _ _ (.Vint (Integers.Int.repr 0))
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envB0 bs) _ (WD0 c bs) _ _ (.Vptr c.cB c.cO)
      (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv1 ▸ co_easy)
        (hcenv1 ▸ off_conn) rfl (ldC hH hag 3 (by simp) rfl hpr))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envB0 bs) _ (WD0 c bs) _ _ z64
      (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envB0 bs) _ (WD0 c bs) _ _ (.Vint (Integers.Int.repr 0))
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envB0 bs) _ (WD0 c bs) _ _ (.Vint (Integers.Int.repr 17))
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  -- oauth_bearer = data->set.str[STRING_BEARER];（修正前は条件なし）
  have hbv : bearerV c = .Vptr c.bB c.bO := by unfold bearerV; rw [hbset]; rfl
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envB0 bs) _ (WD0 c bs) _ _ (bearerV c)
      (fun le m hp hT hH hag => by
        have hl := ldC hH hag 4 (by simp) rfl hpr
        rw [hbv] at hl ⊢
        exact EvalExpr.Elvalue _ _ _ .Full _
          (EvalLvalue.Ederef _ _ _ _
            (EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Elvalue _ _ _ .Full _
                (lv_field (EvalExpr.Elvalue _ _ _ .Full _
                    (lv_field (eval_deref_temp (hT.get (by temps_get))) rfl
                      (hcenv1 ▸ co_easy) (hcenv1 ▸ off_set))
                    (DerefLoc.copy rfl))
                  rfl (hcenv1 ▸ co_ud) (hcenv1 ▸ off_str))
                (DerefLoc.reference rfl))
              (EvalExpr.Econst_int _ _)
              (semAdd_ptr_int _ _ _ _ _ rfl)))
          (DerefLoc.value Mptr _ rfl hl))) ?_
  -- Curl_conn_get_host(...); Curl_bufref_init(&nullmsg); Curl_bufref_init(&resp);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ ghTy tvoid cc_default (WD0 c bs) (WDh c bs hv pv) none _ _ (envB0 bs) _ _
      X.gh.b X.fdG (X.sG bs) X.gh.fp X.tG rfl
      (fun _ _ _ => eval_callee_global (by envget0) X.gh.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get))) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (by envget0))) rfl
            (EvalExprlist.cons _ _ _ _ _ _ _
              (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (by envget0))) rfl
              (EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (by envget0))) rfl
                EvalExprlist.nil)))))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ brTy tvoid cc_default (WDh c bs hv pv) (WDh c bs hv pv) none _ _ (envB0 bs) _ _
      X.bin.b X.fdIn (X.sIn bs) X.bin.fp X.tIn rfl
      (fun _ _ _ => eval_callee_global (by envget0) X.bin.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (by envget0))) rfl EvalExprlist.nil)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ brTy tvoid cc_default (WDh c bs hv pv) (WDh c bs hv pv) none _ _ (envB0 bs) _ _
      X.bin.b X.fdIn (X.sIn bs) X.bin.fp X.tIn rfl
      (fun _ _ _ => eval_callee_global (by envget0) X.bin.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (by envget0))) rfl EvalExprlist.nil)) ?_
  -- sasl->force_ir = force_ir; sasl->authused = 0;
  refine pre_conv ge _ _ (H2 := mapsto .Mint32 c.pm c.sB (addr c.sO 28) (.Vint c.sw)
    ∗ (Cells (outer c c.prv) ∗ LH bs hv pv))
    (fun hp h => by unfold WDh at h; rwa [sep_left_comm_eq] at h) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (bitstore_front ge _ _ (envB0 bs) _ _ c.pm c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 28))
      18 c.sw (if true then Integers.Int.one else Integers.Int.zero) _ _ hpw hpr rfl (by decide) (by decide)
      (fun le m hT => EvalLvalue.Efield_struct _ _ _ _ _ _ _ _ _ _
        (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv1 ▸ co_sasl) (hcenv1 ▸ off_fir))
      (fun le m hT => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)),
        rfl⟩)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (store16_word ge _ _ (envB0 bs) _ _ c.pm c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 28))
      (swF c true) (.Vint (Integers.Int.repr 0)) _ _ hpw rfl
      (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv1 ▸ co_sasl)
        (hcenv1 ▸ off_au))
      (fun le m hT => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  refine pre_conv ge _ _ (H2 := Cells (outer c c.prv) ∗ (SW2 c true (Integers.Int.repr 0)
      ∗ LH bs hv pv))
    (fun hp h => by
      unfold SW2
      rw [sep_assoc_eq] at h
      rw [sep_left_comm_eq, sep_assoc_eq]
      exact h) ?_
  -- enabledmechs = sasl->authmechs & sasl->prefmech;  *progress = SASL_IDLE;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envB0 bs) _ _ _ _ (.Vint (Integers.Int.zero_ext 16 c.am))
        (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv1 ▸ co_sasl)
          (hcenv1 ▸ off_am) rfl (ldC hH hag 0 (by simp) rfl hpr)))
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envB0 bs) _ _ _ _ (.Vint (Integers.Int.zero_ext 16 c.pf))
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv1 ▸ co_sasl)
            (hcenv1 ▸ off_pf) rfl (ldC hH hag 1 (by simp) rfl hpr)))
        (triple_set_local_fwd ge _ _ (envB0 bs) _ _ _ _ (.Vint (em c))
          (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
            (EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ (.Vint (Integers.Int.zero_ext 16 c.am)) (hT.get (by temps_get)))
              (EvalExpr.Etempvar _ _ (.Vint (Integers.Int.zero_ext 16 c.pf)) (hT.get (by temps_get))) rfl)
            rfl)))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell3 ge _ _ (envB0 bs) _ (outer c c.prv) _ 2 (by simp) .Mint32 c.pm c.pB c.pO
      (.Vint c.prv) (.Vint (Integers.Int.repr 0)) rfl _ _ hpw rfl
      (fun le m hT => EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))
      (fun _ _ _ _ _ _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  refine pre_conv ge _ _ (H2 := WE1 c bs hv pv) (fun hp h => h) ?_
  -- 方式の選択: EXTERNAL でない、利用者名あり、OAUTHBEARER を選ぶ
  refine triple_seq_fwd ge _ _ _ (LocalSt (envB0 bs)
    [(_result, .Vint r), (_mech, .Vptr bL Integers.Ptrofs.zero)] (WE2 c bs hv pv)) _ _ _ ?ch ?tail
  case ch =>
    have h5 : Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 5))
        = Integers.Int.zero := hE
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_if_local ge _ _ (envB0 bs) _ (WE1 c bs hv pv) _ false _ _ _
        (fun le m hp hT _ _ => ⟨.Vint (Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1)
            (Integers.Int.repr 5))), EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vint (em c)) (hT.get (by temps_get)))
          (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl)
          rfl, cond_and_false _ _ h5 m⟩)
        (triple_set_local_fwd ge _ _ (envB0 bs) _ (WE1 c bs hv pv) _ _ (.Vint (Integers.Int.repr 0))
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))) ?_
    refine triple_if_local ge _ _ (envB0 bs) _ (WE1 c bs hv pv) _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0))
        (hT.get (by temps_get)), rfl⟩) ?_
    rw [if_neg Bool.false_ne_true]
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envB0 bs) _ (WE1 c bs hv pv) _ _ (.Vptr c.uB c.uO)
        (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _
          (lv_field (EvalExpr.Elvalue _ _ _ .Full _
              (lv_field (EvalExpr.Elvalue _ _ _ .Full _
                  (lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv1 ▸ co_easy)
                    (hcenv1 ▸ off_state)) (DerefLoc.copy rfl))
                rfl (hcenv1 ▸ co_us) (hcenv1 ▸ off_aptr)) (DerefLoc.copy rfl))
            rfl (hcenv1 ▸ co_aptr) (hcenv1 ▸ off_auser))
          (DerefLoc.value Mptr _ rfl (ldC hH hag 6 (by simp) rfl hpr)))) ?_
    refine triple_if_local ge _ _ (envB0 bs) _ (WE1 c bs hv pv) _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.uB c.uO) (hT.get (by temps_get)),
        boolVal_ptr _ rfl (validC hH hag 9 (by simp) rfl hpn)⟩) ?_
    rw [if_pos rfl]
    -- (enabledmechs & OAUTHBEARER) && oauth_bearer: 真
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_if_local ge _ _ (envB0 bs) _ (WE1 c bs hv pv) _ true _ _ _
        (fun le m hp hT _ _ => ⟨.Vint (Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1)
            (Integers.Int.repr 8))), EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vint (em c)) (hT.get (by temps_get)))
          (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl)
          rfl, (boolVal_vint _ m).trans (by rw [show Integers.Int.shl (Integers.Int.repr 1)
            (Integers.Int.repr 8) = Integers.Int.repr 256 from rfl, hO]; rfl)⟩)
        (triple_set_local_fwd ge _ _ (envB0 bs) _ (WE1 c bs hv pv) _ _ (Val.ofBool true)
          (fun le m hp hT hH hag => EvalExpr.Ecast _ tbool _ _
            (EvalExpr.Etempvar _oauth_bearer (tptr tschar) (bearerV c) (hT.get (by temps_get)))
            (by rw [hbv]; exact cast_bool_ptr (validC hH hag 10 (by simp) rfl hpn))))) ?_
    refine triple_if_local ge _ _ (envB0 bs) _ (WE1 c bs hv pv) _ true _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩) ?_
    rw [if_pos rfl]
    -- mech = "OAUTHBEARER"; state1 = SASL_OAUTH2; state2 = SASL_OAUTH2_RESP; sasl->authused = OAUTHBEARER;
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envB0 bs) _ (WE1 c bs hv pv) _ _ (.Vptr bL Integers.Ptrofs.zero)
        (fun _ _ _ _ _ _ => eval_callee_global (by envget0) X.lit rfl)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envB0 bs) _ (WE1 c bs hv pv) _ _ (.Vint (Integers.Int.repr 13))
        (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envB0 bs) _ (WE1 c bs hv pv) _ _ (.Vint (Integers.Int.repr 14))
        (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (store_in_R ge _ _ (envB0 bs) _ _ _ _ .Mint16unsigned c.pm c.sB
        (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 28)) (.Vint (Integers.Int.repr 0))
        (.Vint (Integers.Int.repr 256)) _ _ hpw rfl
        (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl
          (hcenv1 ▸ co_sasl) (hcenv1 ▸ off_au))
        (fun le m hT => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _)
          (EvalExpr.Econst_int _ _) rfl, rfl⟩)) ?_
    refine pre_conv ge _ _ (H2 := WE2 c bs hv pv) (fun hp h => h) ?_
    -- if(force_ir || data->set.sasl_ir)（force_ir が真）
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_if_local ge _ _ (envB0 bs) _ (WE2 c bs hv pv) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩)
        (triple_set_local_fwd ge _ _ (envB0 bs) _ (WE2 c bs hv pv) _ _ (Val.ofBool true)
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int (Integers.Int.repr 1) tint))) ?_
    refine triple_if_local ge _ _ (envB0 bs) _ (WE2 c bs hv pv) _ true _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩) ?_
    rw [if_pos rfl]
    -- result = Curl_auth_create_oauth_bearer_message(conn->user, hostname, port, oauth_bearer, &resp);
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envB0 bs) _ (WE2 c bs hv pv) _ _ c.cuV
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv1 ▸ co_conn)
            (hcenv1 ▸ off_cuser) rfl (by
              rw [← Case4debC.loadResult_ptr hcu]
              exact ldC hH hag 8 (by simp) rfl hpr)))
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ (envB0 bs) _ (WE2 c bs hv pv) _ _ hv
            (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _
              (EvalLvalue.Evar_local _ _ _ (by envget0))
              (DerefLoc.value Mptr _ rfl (WE2_loads hhv hH hag).1)))
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ (envB0 bs) _ (WE2 c bs hv pv) _ _ (.Vint pv)
              (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _
                (EvalLvalue.Evar_local _ _ _ (by envget0))
                (DerefLoc.value .Mint32 _ rfl (WE2_loads hhv hH hag).2)))
            (callS_some ge _ _ _ _ _ (.Vint r) _ _ _ (envB0 bs) _ _ X.cr.b X.fdC (X.sC bs)
              X.cr.fp X.tC rfl
              (fun _ _ _ => eval_callee_global (by envget0) X.cr.sym rfl)
              (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ (tptr tschar) c.cuV (hT.get (by temps_get)))
                (Case4debC.cast_ptr hcu _ _ m)
                (EvalExprlist.cons _ _ _ _ _ _ _
                  (EvalExpr.Etempvar _ (tptr tschar) hv (hT.get (by temps_get)))
                  (Case4debC.cast_ptr hhv _ _ m)
                  (EvalExprlist.cons _ _ _ _ _ _ _
                    (EvalExpr.Etempvar _ tint (.Vint pv) (hT.get (by temps_get))) rfl
                    (EvalExprlist.cons _ _ _ _ _ _ _
                      (EvalExpr.Etempvar _oauth_bearer (tptr tschar) (bearerV c) (hT.get (by temps_get)))
                      (show Cop.semCast (bearerV c) (tptr tschar) (tptr tschar) m = some (bearerV c) by
                        rw [hbv]; rfl)
                      (EvalExprlist.cons _ _ _ _ _ _ _
                        (EvalExpr.Eaddrof _ (tptr (Ty.Tstruct _bufref noattr)) _ _
                          (EvalLvalue.Evar_local _ _ _ (by envget0))) rfl EvalExprlist.nil)))))
              (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h))))) ?_
    exact weaken ge _ _ (triple_set_local_fwd ge _ _ (envB0 bs) _ (WE2 c bs hv pv) _ _ (.Vint r)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ (.Vint r) (hT.get (by temps_get)))) (by subt)
  case tail =>
  -- if(!result && mech) …（result は r）  Curl_bufref_free(&resp);  return result;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_if_local ge _ _ (envB0 bs) _ (WE2 c bs hv pv) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vint r) (hT.get (by temps_get))) (notbool_nz hr m), rfl⟩)
        (triple_set_local_fwd ge _ _ (envB0 bs) _ (WE2 c bs hv pv) _ _ (.Vint (Integers.Int.repr 0))
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)))
      (triple_if_local ge _ _ (envB0 bs) _ (WE2 c bs hv pv) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0))
          (hT.get (by temps_get)), rfl⟩)
        (triple_skip ge _ _ _))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ brTy tvoid cc_default (WE2 c bs hv pv) (WE2 c bs hv pv) none _ _ (envB0 bs) _ _
      X.bfr.b X.fdFr (X.sFr bs) X.bfr.fp X.tFr rfl
      (fun _ _ _ => eval_callee_global (by envget0) X.bfr.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (by envget0))) rfl EvalExprlist.nil)) ?_
  refine pre_conv ge _ _ (H2 := (Cells (outer c (Integers.Int.repr 0)) ∗ SW3 c true)
      ∗ Locs (LD bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2))
    (fun hp h => by
      unfold WE2 at h; rw [← sep_assoc_eq] at h
      exact sep_mono (fun _ x => x) (fun _ x => LH_locs x) hp h) ?_
  obtain ⟨b1, b2, b3, b4, b5⟩ := bs
  refine Case3C.ret_locs ge _ _ _ _ _ _ _ (.Vint r) (.Vint r) _
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ (.Vint r) (hT.get (by temps_get)))
    (fun _ => rfl) ?_ ?_ (fun hp hH => ⟨rfl, hH⟩)
  · rw [blocks_envB0 ge hcenv1]
    intro x hx'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
    rcases hx' with rfl | rfl | rfl | rfl | rfl
    · exact ⟨b4, 4, rfl, by simp⟩
    · exact ⟨b2, 8, rfl, by simp⟩
    · exact ⟨b3, 8, rfl, by simp⟩
    · exact ⟨b1, 24, rfl, by simp⟩
    · exact ⟨b5, 24, rfl, by simp⟩
  · rw [blocks_envB0 ge hcenv1]
    exact pw_reorder hnd

end Deb2025_14524D
