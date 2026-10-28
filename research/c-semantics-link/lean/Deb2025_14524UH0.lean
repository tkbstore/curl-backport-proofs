/-
CVE-2025-14524: 上流の修正前（U0、curl bb134bba29）の `sasl_choose_oauth` の仕様を、本体から導く。

P0 の経路: Bearer が設定され（NULL でない）、利用者名があり、`enabledmechs` が OAUTHBEARER のビットを含む。
`sasl_choose_oauth` は、リダイレクトのあとかどうかを見ずに OAUTHBEARER を選び、`Curl_auth_create_oauth_bearer_message` を
4番目の引数を Bearer の値にして呼び、その戻り値 `r` を `sctx->result` に入れて真を返す。
`sasl_choose_external` は修正の前後で同じ関数（`ext_same`）なので、U1 の証明を使う。
-/
import Deb2025_14524U1
open CC CC.Sep CC.HProp
open Deb2025_14524_u0
open Deb2025_14524
open Case5C (addr RR return_const eval_field eval_bitfield bitOf sep_l sep_r)
open Case3C (CellD cellH Cells cell_load3 assign_cell3 Locs)

set_option maxRecDepth 20000

namespace Deb2025_14524U

theorem ext_same : Deb2025_14524_u0.f_sasl_choose_external = Deb2025_14524_u1.f_sasl_choose_external := rfl
theorem start_same : Deb2025_14524_u0.f_Curl_sasl_start = Deb2025_14524_u1.f_Curl_sasl_start := rfl

/-- `authused` に OAUTHBEARER（256）を書いたあとの 28 番地の単位。 -/
def SW3 (c : Ctx) (fir : Bool) : HProp :=
  mapsto .Mint16unsigned c.pm c.sB (addr c.sO 28) (.Vint (Integers.Int.repr 256))
    ∗ hi2 c.pm c.sB (addr c.sO 28) (swF c fir)

/-- 局所変数 `hostname`・`port` に値が入った形。 -/
def HL (b1 b2 : Block) (hv : Val) (pv : Integers.Int) : HProp :=
  mapsto Mptr .Freeable b1 (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) hv
    ∗ (mapsto .Mint32 .Freeable b2 (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) (.Vint pv) ∗ emp)

theorem HL_locs {b1 b2 : Block} {hv : Val} {pv : Integers.Int} {h : Heap} (hH : HL b1 b2 hv pv h) :
    Locs (LO b1 b2) h := by
  obtain ⟨h1, h2, d, rfl, m1, h3, h4, d', rfl, m2, he⟩ := hH
  exact ⟨h1, Heap.union h3 h4, d, rfl, Case3C.mapsto_anyBytes m1, h3, h4, d', rfl,
    Case3C.mapsto_anyBytes m2, he⟩

/-- OAUTHBEARER を選んだあとの `sctx`（`mech`・`state1`・`state2`、`resp` の中身 `rd rp rl`、`result`）。 -/
abbrev sctxO (c : Ctx) (xB bL : Block) (rd rp rl : Val) (res : Integers.Int) : List CellD :=
  sctxL xB (.Vptr c.sB c.sO) (.Vptr c.cB c.cO) (.Vptr c.uB c.uO) (em c) (.Vptr bL Integers.Ptrofs.zero)
    (Integers.Int.repr 13) (Integers.Int.repr 14) rd rp rl res

/-- `sasl_choose_oauth` が返したあとのメモリ。 -/
def W2 (c : Ctx) (fir : Bool) (xB bL : Block) (rd rp rl : Val) (r : Integers.Int) : HProp :=
  Cells (sctxO c xB bL rd rp rl r ++ outer c (Integers.Int.repr 0)) ∗ SW3 c fir

def gchTy : List Ty := [tptr (Ty.Tstruct _Curl_easy noattr), tint, tptr (tptr tschar), tptr tint]
def crTy : List Ty := [tptr tschar, tptr tschar, tlong, tptr tschar, tptr (Ty.Tstruct _bufref noattr)]

/-- `Curl_auth_create_oauth_bearer_message(user, host, port, bearer, &sctx->resp)`:
    4番目の引数が Bearer の値なら `r` を返し、`resp` を `rd rp rl` にする。 -/
def crSpec (c : Ctx) (K K' : HProp) (r : Integers.Int) : FunSpec where
  tyargs := crTy
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs[3]? = some (bearerV c) ∧ K hp
  post := fun v hp => v = .Vint r ∧ K' hp
  measure := fun _ => 0

/-- 呼ばれる側（`sasl_choose_oauth` の中）。局所変数のブロックについて全称。 -/
structure ExtO (ge : CGenv) (c : Ctx) (fir : Bool) (xB bL : Block) (hv : Val) (pv : Integers.Int)
    (rd rp rl : Val) (r : Integers.Int) where
  fdG : FunDef
  gch : Callee ge _Curl_conn_get_current_host fdG
  tG : typeOfFundef fdG = .Tfunction gchTy tvoid cc_default
  sG : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdG
    (specK gchTy tvoid cc_default (W1 c fir xB ∗ Locs (LO b1 b2)) (W1 c fir xB ∗ HL b1 b2 hv pv) none) vs
  fdC : FunDef
  cr : Callee ge _Curl_auth_create_oauth_bearer_message fdC
  tC : typeOfFundef fdC = .Tfunction crTy tint cc_default
  sC : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdC
    (crSpec c
      (Cells (sctxO c xB bL z64 z64 z64 (Integers.Int.repr 0) ++ outer c (Integers.Int.repr 0))
        ∗ (SW3 c fir ∗ HL b1 b2 hv pv))
      (Cells (sctxO c xB bL rd rp rl (Integers.Int.repr 0) ++ outer c (Integers.Int.repr 0))
        ∗ (SW3 c fir ∗ HL b1 b2 hv pv)) r) vs
  lit : Genv.findSymbol ge.genv_genv ___stringlit_2 = some bL

def envO0 (b1 b2 : Block) : Env :=
  (emptyEnv.set _hostname (b1, tptr tschar)).set _port (b2, tint)

def PbodyO0 (c : Ctx) (fir : Bool) (xB : Block) : Sep.Assn := fun e le hp =>
  ∃ bs : Block × Block, bs.1 ≠ bs.2 ∧
    LocalSt (envO0 bs.1 bs.2) [(_sctx, .Vptr xB Integers.Ptrofs.zero), (_data, .Vptr c.dB c.dO)]
      (W1 c fir xB ∗ Locs (LO bs.1 bs.2)) e le hp

theorem blocks_envO0 (ge : CGenv) (hcenv : ge.genv_cenv = Deb2025_14524_u1.prog.prog_comp_env)
    (b1 b2 : Block) : blocksOfEnv ge.genv_cenv (envO0 b1 b2) = [(b2, 0, 4), (b1, 0, 8)] := by
  rw [hcenv]; rfl

abbrev Wc (c : Ctx) (fir : Bool) (xB bL b1 b2 : Block) (hv : Val) (pv : Integers.Int) : HProp :=
  Cells (sctxO c xB bL z64 z64 z64 (Integers.Int.repr 0) ++ outer c (Integers.Int.repr 0))
    ∗ (SW3 c fir ∗ HL b1 b2 hv pv)

theorem envO0_get {b1 b2 : Block} {id : Ident} (h1 : id ≠ _hostname) (h2 : id ≠ _port) :
    (envO0 b1 b2).get id = none :=
  (PTree.gso _port id _ _ (Ne.symm h2)).trans ((PTree.gso _hostname id _ _ (Ne.symm h1)).trans
    (PTree.gempty _))

set_option maxHeartbeats 4000000 in
theorem oauth_body_before (ge : CGenv) (c : Ctx) (fir : Bool) (xB bL : Block) (hv : Val)
    (pv : Integers.Int) (rd rp rl : Val) (r : Integers.Int)
    (hcenv : ge.genv_cenv = Deb2025_14524_u1.prog.prog_comp_env)
    (hpn : permOrder c.pm .Nonempty = true) (hpr : permOrder c.pm .Readable = true)
    (hpw : permOrder c.pm .Writable = true)
    (hbset : c.bset = true)
    (hO : Integers.Int.eq (Integers.Int.and (em c) (Integers.Int.repr 256)) Integers.Int.zero = false)
    (hsir : bitOf c.setw 1 = true) (hal : addr c.sO 28 % 4 = 0)
    (hcu : Case4debC.IsPtr c.cuV) (hhv : Case4debC.IsPtr hv)
    (X : ExtO ge c fir xB bL hv pv rd rp rl r) :
    Triple ge (FunctionEntry2 ge) Deb2025_14524_u0.f_sasl_choose_oauth (PbodyO0 c fir xB)
      Deb2025_14524_u0.f_sasl_choose_oauth.fn_body
      (RR (chooseSpec c xB (W1 c fir xB) (W2 c fir xB bL rd rp rl r) true).post Sep.Assn.no) := by
  refine Sep.triple_exists ge _ _ _ _ _ (fun bs => ?_)
  obtain ⟨b1, b2⟩ := bs
  refine Case1C.triple_pure ge _ _ _ _ _ _ (fun hne => ?_)
  have hbv : bearerV c = .Vptr c.bB c.bO := by unfold bearerV; rw [hbset]; rfl
  -- oauth_bearer = data->set.str[STRING_BEARER];
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _ (bearerV c)
      (fun le m hp hT hH hag => by
        have hl := ldW (X := Locs (LO b1 b2)) 18 (by simp) rfl hpr hH hag
        rw [hbv] at hl ⊢
        exact EvalExpr.Elvalue _ _ _ .Full _
          (EvalLvalue.Ederef _ _ _ _
            (EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Elvalue _ _ _ .Full _
                (Case4debC.lv_field (EvalExpr.Elvalue _ _ _ .Full _
                    (Case4debC.lv_field (Case4debC.eval_deref_temp (hT.get (by temps_get))) rfl
                      (hcenv ▸ co_easy) (hcenv ▸ off_set))
                    (DerefLoc.copy rfl))
                  rfl (hcenv ▸ co_ud) (hcenv ▸ off_str))
                (DerefLoc.reference rfl))
              (EvalExpr.Econst_int _ _)
              (semAdd_ptr_int _ _ _ _ _ rfl)))
          (DerefLoc.value Mptr _ rfl hl))) ?_
  -- return 1 で抜けるので、後続（return 0）は通らない
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _ (.Vptr c.uB c.uO)
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_ctx)
            (hcenv ▸ offx_user) rfl (ldW 2 (by simp) rfl freeable_r hH hag)))
        (triple_if_local ge _ _ (envO0 b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ true _ _ _
          (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.uB c.uO) (hT.get (by temps_get)),
            boolVal_ptr _ rfl (validW 23 (by simp) rfl hpn hH hag)⟩)
          (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _ (Val.ofBool true)
            (fun le m hp hT hH hag => EvalExpr.Ecast _ _ _ _
              (EvalExpr.Etempvar _ _ (bearerV c) (hT.get (by temps_get)))
              (by rw [hbv]; exact cast_bool_ptr (validW 24 (by simp) rfl hpn hH hag))))))
      (triple_if_local ge _ _ (envO0 b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩)
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _
            (.Vint (Integers.Int.zero_ext 16 (em c)))
            (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_ctx)
              (hcenv ▸ offx_em) rfl (ldW 3 (by simp) rfl freeable_r hH hag)))
          (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ _ (Val.ofBool true)
            (fun le m hp hT _ _ => EvalExpr.Ecast _ _
              (.Vint (Integers.Int.and (Integers.Int.zero_ext 16 (em c))
                (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 8)))) _
              (EvalExpr.Ebinop _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl)
                rfl)
              (cast_bool_nz (by rw [zext_em]; exact hO) m)))))) ?_
  refine triple_if_local ge _ _ (envO0 b1 b2) _ (W1 c fir xB ∗ Locs (LO b1 b2)) _ true _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩) ?_
  -- Curl_conn_get_current_host(data, FIRSTSOCKET, &hostname, &port);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ gchTy tvoid cc_default (W1 c fir xB ∗ Locs (LO b1 b2)) (W1 c fir xB ∗ HL b1 b2 hv pv)
      none _ _ (envO0 b1 b2) _ _ X.gch.b X.fdG (X.sG b1 b2) X.gch.fp X.tG rfl
      (fun _ _ _ => eval_callee_global (envO0_get (by decide) (by decide)) X.gch.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get))) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _
              ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)))) rfl
            (EvalExprlist.cons _ _ _ _ _ _ _
              (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (PTree.gss _ _ _))) rfl
              EvalExprlist.nil))))) ?_
  refine pre_conv ge _ _ (H2 := Cells (sctxS c xB ++ outer c (Integers.Int.repr 0))
      ∗ (SW2 c fir (Integers.Int.repr 0) ∗ HL b1 b2 hv pv))
    (fun hp h => by unfold W1 at h; rwa [sep_assoc_eq] at h) ?_
  -- sctx->mech = "OAUTHBEARER"; state1 = SASL_OAUTH2; state2 = SASL_OAUTH2_RESP;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell3 ge _ _ (envO0 b1 b2) _ _ _ 6 (by simp) Mptr .Freeable xB _ z64
      (.Vptr bL Integers.Ptrofs.zero) rfl _ _ rfl rfl
      (fun le m hT => Case4debC.lv_field (Case4debC.eval_deref_temp (hT.get (by temps_get))) rfl
        (hcenv ▸ co_ctx) (hcenv ▸ offx_mech))
      (fun _ _ _ _ _ _ => ⟨_, eval_callee_global (envO0_get (by decide) (by decide)) X.lit rfl, rfl⟩)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell3 ge _ _ (envO0 b1 b2) _ _ _ 7 (by simp) .Mint32 .Freeable xB _
      (.Vint (Integers.Int.repr 0)) (.Vint (Integers.Int.repr 13)) rfl _ _ rfl rfl
      (fun le m hT => Case4debC.lv_field (Case4debC.eval_deref_temp (hT.get (by temps_get))) rfl
        (hcenv ▸ co_ctx) (hcenv ▸ offx_s1))
      (fun _ _ _ _ _ _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell3 ge _ _ (envO0 b1 b2) _ _ _ 8 (by simp) .Mint32 .Freeable xB _
      (.Vint (Integers.Int.repr 17)) (.Vint (Integers.Int.repr 14)) rfl _ _ rfl rfl
      (fun le m hT => Case4debC.lv_field (Case4debC.eval_deref_temp (hT.get (by temps_get))) rfl
        (hcenv ▸ co_ctx) (hcenv ▸ offx_s2))
      (fun _ _ _ _ _ _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  -- sctx->sasl->authused = SASL_MECH_OAUTHBEARER;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ _ _ _ (.Vptr c.sB c.sO)
        (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_ctx)
          (hcenv ▸ offx_sasl) rfl (ldC hH hag 0 (by simp) rfl freeable_r)))
      (store_in_R ge _ _ (envO0 b1 b2) _ _ _ _ .Mint16unsigned c.pm c.sB
        (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 28)) (.Vint (Integers.Int.repr 0))
        (.Vint (Integers.Int.repr 256)) _ _ hpw rfl
        (fun le m hT => Case4debC.lv_field (Case4debC.eval_deref_temp (hT.get (by temps_get))) rfl
          (hcenv ▸ co_sasl) (hcenv ▸ off_au))
        (fun le m hT => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _)
          (EvalExpr.Econst_int _ _) rfl, rfl⟩))) ?_
  refine pre_conv ge _ _ (H2 := Cells (sctxO c xB bL z64 z64 z64 (Integers.Int.repr 0)
      ++ outer c (Integers.Int.repr 0)) ∗ (SW3 c fir ∗ HL b1 b2 hv pv)) (fun hp h => h) ?_
  -- if(sctx->sasl->force_ir || data->set.sasl_ir) …（どちらの枝でも t'2 は真）
  have hld : ∀ hp m, (Cells (sctxO c xB bL z64 z64 z64 (Integers.Int.repr 0) ++ outer c (Integers.Int.repr 0))
      ∗ (SW3 c fir ∗ HL b1 b2 hv pv)) hp → Heap.Agrees hp m →
      Mem.load .Mint32 m c.sB (addr c.sO 28) = some (.Vint (w16x (Integers.Int.repr 256) (swF c fir))) := by
    intro hp m hH hag
    obtain ⟨h1, c1, a1⟩ := sep_r hH hag
    obtain ⟨h2, c2, a2⟩ := sep_l c1 a1
    exact word16_load hpr hal c2 a2
  have hHL : ∀ hp m, (Cells (sctxO c xB bL z64 z64 z64 (Integers.Int.repr 0) ++ outer c (Integers.Int.repr 0))
      ∗ (SW3 c fir ∗ HL b1 b2 hv pv)) hp → Heap.Agrees hp m →
      Mem.load Mptr m b1 (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) = some hv
      ∧ Mem.load .Mint32 m b2 (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) = some (.Vint pv) := by
    intro hp m hH hag
    obtain ⟨h1, c1, a1⟩ := sep_r hH hag
    obtain ⟨h2, c2, a2⟩ := sep_r c1 a1
    obtain ⟨h3, c3, a3⟩ := sep_l c2 a2
    obtain ⟨h4, c4, a4⟩ := sep_r c2 a2
    obtain ⟨h5, c5, a5⟩ := sep_l c4 a4
    exact ⟨by rw [mapsto_load freeable_r c3 a3, Case4debC.loadResult_ptr hhv],
      mapsto_load freeable_r c5 a5⟩
  refine triple_seq_fwd ge _ _ _ (LocalSt (envO0 b1 b2) [(_sctx, .Vptr xB Integers.Ptrofs.zero)]
      (Cells (sctxO c xB bL rd rp rl r ++ outer c (Integers.Int.repr 0)) ∗ (SW3 c fir ∗ HL b1 b2 hv pv)))
    _ _ _ ?mid ?ret
  case ret =>
    refine pre_conv ge _ _ (H2 := W2 c fir xB bL rd rp rl r ∗ Locs (LO b1 b2)) (fun hp h => by
      unfold W2; rw [← sep_assoc_eq] at h
      exact sep_mono (fun _ x => x) (fun _ x => HL_locs x) hp h) ?_
    refine Case3C.ret_locs ge _ _ (envO0 b1 b2) _ (W2 c fir xB bL rd rp rl r) (LO b1 b2) _
      (.Vint (Integers.Int.repr 1)) (Val.ofBool true) _ (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
      (fun _ => rfl) ?_ ?_ (fun hp hH => ⟨rfl, hH⟩)
    · rw [blocks_envO0 ge hcenv]
      intro x hx'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
      rcases hx' with rfl | rfl
      · exact ⟨b2, 4, rfl, by simp⟩
      · exact ⟨b1, 8, rfl, by simp⟩
    · rw [blocks_envO0 ge hcenv]
      simp [Ne.symm hne]
  case mid =>
  refine triple_seq_fwd ge _ _ _ (LocalSt (envO0 b1 b2)
      [(_t'2, Val.ofBool true), (_oauth_bearer, bearerV c), (_sctx, .Vptr xB Integers.Ptrofs.zero),
       (_data, .Vptr c.dB c.dO)]
      (Cells (sctxO c xB bL z64 z64 z64 (Integers.Int.repr 0) ++ outer c (Integers.Int.repr 0))
        ∗ (SW3 c fir ∗ HL b1 b2 hv pv))) _ _ _ ?fi ?cr
  case fi =>
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (Wc c fir xB bL b1 b2 hv pv) _ _ (.Vptr c.sB c.sO)
        (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_ctx)
          (hcenv ▸ offx_sasl) rfl (ldC hH hag 0 (by simp) rfl freeable_r))) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (Wc c fir xB bL b1 b2 hv pv) _ _
        (.Vint (Cop.bitfieldExtract .I32 .Unsigned 18 1 (w16x (Integers.Int.repr 256) (swF c fir))))
        (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_sasl)
          (hcenv ▸ off_fir) (by decide) (by decide) (hld hp m hH hag))) ?_
    cases hx : Integers.Int.eq (Cop.bitfieldExtract .I32 .Unsigned 18 1
        (w16x (Integers.Int.repr 256) (swF c fir))) Integers.Int.zero
    · refine triple_if_local ge _ _ (envO0 b1 b2) _ (Wc c fir xB bL b1 b2 hv pv) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
          by show some (!Integers.Int.eq _ _) = some true; rw [hx]; rfl⟩) ?_
      exact weaken ge _ _ (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (Wc c fir xB bL b1 b2 hv pv) _ _ (Val.ofBool true)
        (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) (by subt)
    · refine triple_if_local ge _ _ (envO0 b1 b2) _ (Wc c fir xB bL b1 b2 hv pv) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
          by show some (!Integers.Int.eq _ _) = some false; rw [hx]; rfl⟩) ?_
      exact weaken ge _ _ (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (Wc c fir xB bL b1 b2 hv pv) _ _
          (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 c.setw))
          (fun le m hp hT hH hag => eval_bit2 (hT.get (by temps_get)) (hcenv ▸ co_easy)
            (hcenv ▸ off_set) (hcenv ▸ co_ud) (hcenv ▸ off_sasl_ir) (by decide) (by decide)
            (ldC hH hag 19 (by simp) rfl hpr)))
        (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (Wc c fir xB bL b1 b2 hv pv) _ _ (Val.ofBool true)
          (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (cast_bool_nz (bitOf_nz hsir) m))))
        (by subt)
  case cr =>
  refine triple_if_local ge _ _ (envO0 b1 b2) _ (Wc c fir xB bL b1 b2 hv pv) _ true _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩) ?_
  rw [if_pos rfl]
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envO0 b1 b2)
        [(_t'2, Val.ofBool true), (_oauth_bearer, bearerV c), (_sctx, .Vptr xB Integers.Ptrofs.zero),
         (_data, .Vptr c.dB c.dO)] (Wc c fir xB bL b1 b2 hv pv) _t'5 _ (.Vptr c.cB c.cO)
        (fun le m hp hT hH hag => eval_field
          (hT.get (id := _sctx) (v := .Vptr xB Integers.Ptrofs.zero) (by temps_get)) (hcenv ▸ co_ctx)
          (hcenv ▸ offx_conn) rfl (ldC hH hag 1 (by simp) rfl freeable_r)))
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (Wc c fir xB bL b1 b2 hv pv) _t'6 _ c.cuV
          (fun le m hp hT hH hag => eval_field
            (hT.get (id := _t'5) (v := .Vptr c.cB c.cO) (by temps_get)) (hcenv ▸ co_conn)
            (hcenv ▸ off_cuser) rfl (by
              rw [← Case4debC.loadResult_ptr hcu]
              exact ldC hH hag 22 (by simp) rfl hpr)))
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (Wc c fir xB bL b1 b2 hv pv) _t'7 _ hv
            (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _
              (EvalLvalue.Evar_local _ _ _ ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)))
              (DerefLoc.value Mptr _ rfl (hHL hp m hH hag).1)))
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ (envO0 b1 b2) _ (Wc c fir xB bL b1 b2 hv pv) _t'8 _ (.Vint pv)
              (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _
                (EvalLvalue.Evar_local _ _ _ (PTree.gss _ _ _))
                (DerefLoc.value .Mint32 _ rfl (hHL hp m hH hag).2)))
            (callS_some ge _ _ _ _ _ (.Vint r) _t'1 _ _ (envO0 b1 b2) _ _ X.cr.b X.fdC (X.sC b1 b2)
              X.cr.fp X.tC rfl
              (fun _ _ _ => eval_callee_global (envO0_get (by decide) (by decide)) X.cr.sym rfl)
              (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ (tptr tschar) c.cuV (hT.get (id := _t'6) (by temps_get))) (Case4debC.cast_ptr hcu _ _ m)
                (EvalExprlist.cons _ _ _ _ _ _ _
                  (EvalExpr.Etempvar _ (tptr tschar) hv (hT.get (id := _t'7) (by temps_get))) (Case4debC.cast_ptr hhv _ _ m)
                  (EvalExprlist.cons _ _ _ _ _ _ _
                    (EvalExpr.Etempvar _ tint (.Vint pv) (hT.get (id := _t'8) (by temps_get))) rfl
                    (EvalExprlist.cons _ _ _ _ _ _ _
                      (EvalExpr.Etempvar _ (tptr tschar) (bearerV c) (hT.get (id := _oauth_bearer) (by temps_get)))
                      (show Cop.semCast (bearerV c) (tptr tschar) (tptr tschar) m = some (bearerV c) by
                        rw [hbv]; rfl)
                      (EvalExprlist.cons _ _ _ _ _ _ _
                        (EvalExpr.Eaddrof _ (tptr (Ty.Tstruct _bufref noattr)) _ _
                          (Case4debC.lv_field (ty := Ty.Tstruct _bufref noattr) (Case4debC.eval_deref_temp (hT.get (id := _sctx) (v := .Vptr xB Integers.Ptrofs.zero) (by temps_get))) rfl
                            (hcenv ▸ co_ctx) (hcenv ▸ offx_resp))) rfl EvalExprlist.nil)))))
              (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h)))))) ?_
  exact weaken ge _ _ (assign_cell3 ge _ _ (envO0 b1 b2) _ _ _ 12 (by simp) .Mint32 .Freeable xB _
    (.Vint (Integers.Int.repr 0)) (.Vint r) rfl _ _ rfl rfl
    (fun le m hT => Case4debC.lv_field (Case4debC.eval_deref_temp (hT.get (id := _sctx) (v := .Vptr xB Integers.Ptrofs.zero) (by temps_get))) rfl
      (hcenv ▸ co_ctx) (hcenv ▸ offx_res))
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint r) (hT.get (id := _t'1) (by temps_get)), rfl⟩))
    (by subt)

theorem oauth_before (ge : CGenv) (c : Ctx) (fir : Bool) (xB bL : Block) (hv : Val)
    (pv : Integers.Int) (rd rp rl : Val) (r : Integers.Int)
    (hcenv : ge.genv_cenv = Deb2025_14524_u1.prog.prog_comp_env)
    (hpn : permOrder c.pm .Nonempty = true) (hpr : permOrder c.pm .Readable = true)
    (hpw : permOrder c.pm .Writable = true)
    (hbset : c.bset = true)
    (hO : Integers.Int.eq (Integers.Int.and (em c) (Integers.Int.repr 256)) Integers.Int.zero = false)
    (hsir : bitOf c.setw 1 = true) (hal : addr c.sO 28 % 4 = 0)
    (hcu : Case4debC.IsPtr c.cuV) (hhv : Case4debC.IsPtr hv)
    (X : ExtO ge c fir xB bL hv pv rd rp rl r) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sasl_choose_oauth)
      (chooseSpec c xB (W1 c fir xB) (W2 c fir xB bL rd rp rl r) true) vs := by
  by_cases hvs : vs = [.Vptr c.dB c.dO, .Vptr xB Integers.Ptrofs.zero]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hnv : listNorepet (varNames f_sasl_choose_oauth.fn_vars) := by decide
  have hnp : listNorepet (varNames f_sasl_choose_oauth.fn_params) := by decide
  have hdisj : listDisjoint (varNames f_sasl_choose_oauth.fn_params)
      (varNames f_sasl_choose_oauth.fn_temps) := by decide
  refine satisfies_internal ge (FunctionEntry2 ge) f_sasl_choose_oauth _ _ (PbodyO0 c fir xB)
    (fun m hp hf hpre hd hag => ?_) (oauth_body_before ge c fir xB bL hv pv rd rp rl r hcenv hpn hpr hpw hbset hO hsir hal hcu hhv X)
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (tptr tschar))
  let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv tint)
  have hav : AllocVariables ge.genv_cenv emptyEnv m f_sasl_choose_oauth.fn_vars (envO0 a1.2 a2.2) a2.1 :=
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
