/-
CVE-2025-14524: 上流の修正後（U1、curl 1a822275d3）の `Curl_sasl_start`。

証明すること（`start_after`、P1）: リダイレクトのあと（`this_is_a_follow` が 1）で `allow_auth_to_other_hosts` が 0、
利用者名があり、`enabledmechs` が EXTERNAL・PLAIN・LOGIN のビットを含まないなら、`force_ir` によらず CURLE_OK を返す。
`*progress` は SASL_IDLE（0）、`sasl->authused` は 0 になる。
`Curl_auth_create_oauth_bearer_message`・`Curl_auth_create_xoauth_bearer_message` には仕様を与えず、
`sasl->params` も所有させない（`sendauth` を読む経路は証明が通らない）。
`sasl_choose_*` の仕様は `Deb2025_14524UH1.lean` で本体から導いた。
-/
import Deb2025_14524UH1
open CC CC.Sep CC.HProp
open Deb2025_14524_u1
open Deb2025_14524
open Case5C (addr RR call_fwd eval_field bitOf triple_nop_loop)
open Case4debC (lv_field eval_deref_temp)
open Case3C (CellD cellH Cells cell_load3 assign_cell3 Locs)

set_option maxRecDepth 20000

namespace Deb2025_14524U

/-! ## 関数の入口と出口のメモリ -/

/-- 入口で所有するもの: `sasl` の 28 番地の単位と、関数の外のセル。 -/
def Hs (c : Ctx) : HProp :=
  mapsto .Mint32 c.pm c.sB (addr c.sO 28) (.Vint c.sw) ∗ Cells (outer c c.prv)

def argsS (c : Ctx) (fir : Bool) : List Val :=
  [.Vptr c.sB c.sO, .Vptr c.dB c.dO, Val.ofBool fir, .Vptr c.pB c.pO]

/-- P1 の仕様: 戻り値は CURLE_OK。`*progress` は 0、`authused` は 0。 -/
def startSpecA (c : Ctx) (fir : Bool) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _SASL noattr), tptr (Ty.Tstruct _Curl_easy noattr), tbool, tptr tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = argsS c fir ∧ Hs c hp
  post := fun v hp => v = .Vint (Integers.Int.repr 0) ∧
    (Cells (outer c (Integers.Int.repr 0)) ∗ SW2 c fir (Integers.Int.repr 0)) hp
  measure := fun _ => 0

/-- `memset` の前と後。 -/
def Kms (c : Ctx) (fir : Bool) (xB : Block) : HProp :=
  Cells (outer c (Integers.Int.repr 0)) ∗ (SW2 c fir (Integers.Int.repr 0) ∗ Locs [(xB, 80)])
def Kms' (c : Ctx) (fir : Bool) (xB : Block) : HProp :=
  Cells (sctxZ xB ++ outer c (Integers.Int.repr 0)) ∗ SW2 c fir (Integers.Int.repr 0)

/-- `Curl_bufref_init(&sctx.resp)` を呼ぶとき（`sasl`・`conn`・`user` を埋めたあと）。 -/
def Win (c : Ctx) (fir : Bool) (xB : Block) : HProp :=
  Cells (sctxL xB (.Vptr c.sB c.sO) (.Vptr c.cB c.cO) (.Vptr c.uB c.uO) (Integers.Int.repr 0) z64
      (Integers.Int.repr 0) (Integers.Int.repr 0) z64 z64 z64 (Integers.Int.repr 0)
    ++ outer c (Integers.Int.repr 0)) ∗ SW2 c fir (Integers.Int.repr 0)

def msTy : List Ty := [tptr tvoid, tint, tulong]
def brTy : List Ty := [tptr (Ty.Tstruct _bufref noattr)]

/-- 関数の置き場所。 -/
structure Callee (ge : CGenv) (id : Ident) (fd : FunDef) where
  b : Block
  sym : Genv.findSymbol ge.genv_genv id = some b
  fp : FuncPtr ge b fd

/-- 呼ばれる側の関数（外部3つと、同じ翻訳単位の `sasl_choose_*` 5つ）。外部の仕様は局所変数のブロック `xB` について全称。 -/
structure ExtU1 (ge : CGenv) (c : Ctx) (fir : Bool) where
  fdMs : FunDef
  ms : Callee ge _memset fdMs
  tMs : typeOfFundef fdMs = .Tfunction msTy (tptr tvoid) cc_default
  sMs : ∀ xB vs, SatisfiesAt ge (FunctionEntry2 ge) fdMs
    (specK msTy (tptr tvoid) cc_default (Kms c fir xB) (Kms' c fir xB) none) vs
  fdIn : FunDef
  bin : Callee ge _Curl_bufref_init fdIn
  tIn : typeOfFundef fdIn = .Tfunction brTy tvoid cc_default
  sIn : ∀ xB vs, SatisfiesAt ge (FunctionEntry2 ge) fdIn
    (specK brTy tvoid cc_default (Win c fir xB) (Win c fir xB) none) vs
  fdFr : FunDef
  bfr : Callee ge _Curl_bufref_free fdFr
  tFr : typeOfFundef fdFr = .Tfunction brTy tvoid cc_default
  sFr : ∀ xB vs, SatisfiesAt ge (FunctionEntry2 ge) fdFr
    (specK brTy tvoid cc_default (W1 c fir xB) (W1 c fir xB) none) vs
  ext : Callee ge _sasl_choose_external (.Internal f_sasl_choose_external)
  oa : Callee ge _sasl_choose_oauth (.Internal f_sasl_choose_oauth)
  oa2 : Callee ge _sasl_choose_oauth2 (.Internal f_sasl_choose_oauth2)
  pl : Callee ge _sasl_choose_plain (.Internal f_sasl_choose_plain)
  lg : Callee ge _sasl_choose_login (.Internal f_sasl_choose_login)

def envS (xB : Block) : Env := emptyEnv.set _sctx (xB, Ty.Tstruct _sasl_ctx noattr)

abbrev lS (c : Ctx) (fir : Bool) : List (Ident × Val) :=
  [(_progress, .Vptr c.pB c.pO), (_force_ir, Val.ofBool fir), (_data, .Vptr c.dB c.dO),
   (_sasl, .Vptr c.sB c.sO)]

def PbodyS (c : Ctx) (fir : Bool) : Sep.Assn := fun e le hp =>
  ∃ xB : Block, LocalSt (envS xB) (lS c fir) (Hs c ∗ Locs [(xB, 80)]) e le hp

theorem blocks_envS (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (xB : Block) :
    blocksOfEnv ge.genv_cenv (envS xB) = [(xB, 0, 80)] := by
  rw [hcenv]; rfl

/-- `sctx.fld` -/
theorem lvx {ge : CGenv} {le : TempEnv} {m : Mem} {xB : Block} {fld : Ident} {ty : Ty} {d : Z}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hfld : fieldOffset prog.prog_comp_env fld (coOf _sasl_ctx).co_members = .OK (d, .Full)) :
    EvalLvalue ge (envS xB) le m (.Efield (.Evar _sctx (Ty.Tstruct _sasl_ctx noattr)) fld ty) xB
      (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr d)) .Full :=
  lv_field (EvalExpr.Elvalue _ _ _ .Full _ (EvalLvalue.Evar_local _ _ _ (PTree.gss _ _ _))
    (DerefLoc.copy rfl)) rfl (hcenv ▸ co_ctx) (hcenv ▸ hfld)

theorem ldC {l : List CellD} {R : HProp} {hp : Heap} {m : Mem} (hH : (Cells l ∗ R) hp)
    (hag : Heap.Agrees hp m) (k : Nat) (hk : k < l.length) {ch : Chunk} {p : Permission} {b : Block}
    {o : Z} {v : Val} (hl : l[k]'hk = (ch, p, b, o, v)) (hpr : permOrder p .Readable = true) :
    Mem.load ch m b o = some (Val.loadResult ch v) :=
  cell_load3 hl hpr hH hag

theorem envS_get {xB : Block} {id : Ident} (h : id ≠ _sctx) : (envS xB).get id = none :=
  (PTree.gso _sctx id _ _ (Ne.symm h)).trans (PTree.gempty _)

/-- 局所変数を解放する前に、`sctx` のセルを 80 バイトに戻す。 -/
theorem w1_ret {c : Ctx} {fir : Bool} {xB : Block} {hp : Heap} (hH : W1 c fir xB hp) :
    ((Cells (outer c (Integers.Int.repr 0)) ∗ SW2 c fir (Integers.Int.repr 0)) ∗ Locs [(xB, 80)]) hp := by
  unfold W1 at hH
  rw [cells_append, sep_assoc_eq, sep_comm_eq, sep_assoc_eq] at hH
  rw [sep_assoc_eq]
  obtain ⟨h1, h2, d, rfl, ho, h2'⟩ := hH
  obtain ⟨h3, h4, d', rfl, hsw, hs⟩ := h2'
  refine ⟨h1, Heap.union h3 h4, d, rfl, ho, h3, h4, d', rfl, hsw, ?_⟩
  show (anyBytes .Freeable xB 0 80 ∗ emp) h4
  rw [sep_emp_eq]
  exact sctx_any hs

/-- `sasl_choose_*` を呼び、偽を受け取る。 -/
theorem call_choose (ge : CGenv) (c : Ctx) (fir : Bool) (xB : Block) (l : List (Ident × Val))
    (id fid : Ident) (fn : Function) (cal : Callee ge fid (.Internal fn))
    (hpar : typeOfFundef (.Internal fn) = .Tfunction
      [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _sasl_ctx noattr)] tbool cc_default)
    (hS : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal fn)
      (chooseSpec c xB (W1 c fir xB) (W1 c fir xB) false) vs)
    (hd : (_data, Val.Vptr c.dB c.dO) ∈ l) (hne : fid ≠ _sctx) :
    Triple ge (FunctionEntry2 ge) f_Curl_sasl_start (LocalSt (envS xB) l (W1 c fir xB))
      (.Scall (some id) (.Evar fid (Ty.Tfunction
          [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _sasl_ctx noattr)] tbool cc_default))
        [.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)),
         .Eaddrof (.Evar _sctx (Ty.Tstruct _sasl_ctx noattr)) (tptr (Ty.Tstruct _sasl_ctx noattr))])
      (.only (LocalSt (envS xB) (setLocal l id (Val.ofBool false)) (W1 c fir xB))) :=
  callS_some ge _ _ _ (W1 c fir xB) (W1 c fir xB) (Val.ofBool false) id _ _ (envS xB) l
    [.Vptr c.dB c.dO, .Vptr xB Integers.Ptrofs.zero] cal.b (.Internal fn) hS cal.fp hpar rfl
    (fun _ _ _ => eval_callee_global (envS_get hne) cal.sym rfl)
    (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get hd)) rfl
      (EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (PTree.gss _ _ _))) rfl
        EvalExprlist.nil))
    (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h)

/-! ## 本体 -/

set_option maxHeartbeats 4000000 in
theorem start_body_after (ge : CGenv) (c : Ctx) (fir : Bool)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hfollow : bitOf c.stw 0 = true) (hallow : bitOf c.setw 0 = false)
    (hE : Integers.Int.and (em c) (Integers.Int.repr 32) = Integers.Int.zero)
    (hP : Integers.Int.and (em c) (Integers.Int.repr 2) = Integers.Int.zero)
    (hL : Integers.Int.and (em c) (Integers.Int.repr 1) = Integers.Int.zero)
    (X : ExtU1 ge c fir) :
    Triple ge (FunctionEntry2 ge) f_Curl_sasl_start (PbodyS c fir) f_Curl_sasl_start.fn_body
      (RR (startSpecA c fir).post Sep.Assn.no) := by
  refine Sep.triple_exists ge _ _ _ _ _ (fun xB => ?_)
  refine pre_conv ge _ _ (H2 := mapsto .Mint32 c.pm c.sB (addr c.sO 28) (.Vint c.sw)
    ∗ (Cells (outer c c.prv) ∗ Locs [(xB, 80)])) (fun hp h => by unfold Hs at h; rwa [sep_assoc_eq] at h) ?_
  -- sasl->force_ir = force_ir;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (bitstore_front ge _ _ (envS xB) _ _ c.pm c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 28))
      18 c.sw (if fir then Integers.Int.one else Integers.Int.zero) _ _ hpw hpr rfl (by decide) (by decide)
      (fun le m hT => EvalLvalue.Efield_struct _ _ _ _ _ _ _ _ _ _
        (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_sasl) (hcenv ▸ off_fir))
      (fun le m hT => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool fir) (hT.get (by temps_get)),
        by cases fir <;> rfl⟩)) ?_
  -- sasl->authused = 0;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (store16_word ge _ _ (envS xB) _ _ c.pm c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 28))
      (swF c fir) (.Vint (Integers.Int.repr 0)) _ _ hpw rfl
      (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_sasl)
        (hcenv ▸ off_au))
      (fun le m hT => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  refine pre_conv ge _ _ (H2 := Cells (outer c c.prv) ∗ (SW2 c fir (Integers.Int.repr 0) ∗ Locs [(xB, 80)]))
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
    (callK_none ge _ _ msTy (tptr tvoid) cc_default (Kms c fir xB) (Kms' c fir xB) none _ _ (envS xB) _
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
    (callK_none ge _ _ brTy tvoid cc_default (Win c fir xB) (Win c fir xB) none _ _ (envS xB) _
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
  refine pre_conv ge _ _ (H2 := W1 c fir xB) (fun hp h => h) ?_
  -- sasl_choose_external(…) || sasl_choose_oauth(…) || … ：どれも偽
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_seq_fwd ge _ _ _ _ _ _ _
              (call_choose ge c fir xB (hne := by decide) _ _ _ _ X.ext rfl (ext_after ge c fir xB hcenv hE)
                (by temps_get))
              (triple_if_local ge _ _ (envS xB) _ (W1 c fir xB) _ false _ _ _
                (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false)
                  (hT.get (by temps_get)), rfl⟩)
                (triple_seq_fwd ge _ _ _ _ _ _ _
                  (call_choose ge c fir xB (hne := by decide) _ _ _ _ X.oa rfl
                    (oauth_after ge c fir xB hcenv hpn hpr hfollow hallow) (by temps_get))
                  (triple_set_local_fwd ge _ _ (envS xB) _ (W1 c fir xB) _ _ (Val.ofBool false)
                    (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                      (EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get))) rfl)))))
            (triple_if_local ge _ _ (envS xB) _ (W1 c fir xB) _ false _ _ _
              (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false)
                (hT.get (by temps_get)), rfl⟩)
              (triple_seq_fwd ge _ _ _ _ _ _ _
                (call_choose ge c fir xB (hne := by decide) _ _ _ _ X.oa2 rfl
                  (oauth2_after ge c fir xB hcenv hpn hpr hfollow hallow) (by temps_get))
                (triple_set_local_fwd ge _ _ (envS xB) _ (W1 c fir xB) _ _ (Val.ofBool false)
                  (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                    (EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get))) rfl)))))
          (triple_if_local ge _ _ (envS xB) _ (W1 c fir xB) _ false _ _ _
            (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false)
              (hT.get (by temps_get)), rfl⟩)
            (triple_seq_fwd ge _ _ _ _ _ _ _
              (call_choose ge c fir xB (hne := by decide) _ _ _ _ X.pl rfl (plain_after ge c fir xB hcenv hpn hP)
                (by temps_get))
              (triple_set_local_fwd ge _ _ (envS xB) _ (W1 c fir xB) _ _ (Val.ofBool false)
                (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                  (EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get))) rfl)))))
        (triple_if_local ge _ _ (envS xB) _ (W1 c fir xB) _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false)
            (hT.get (by temps_get)), rfl⟩)
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (call_choose ge c fir xB (hne := by decide) _ _ _ _ X.lg rfl (login_after ge c fir xB hcenv hpn hL)
              (by temps_get))
            (triple_set_local_fwd ge _ _ (envS xB) _ (W1 c fir xB) _ _ (Val.ofBool false)
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get))) rfl)))))
      (triple_if_local ge _ _ (envS xB) _ (W1 c fir xB) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false)
          (hT.get (by temps_get)), rfl⟩)
        (triple_skip ge _ _ _))) ?_
  -- if(!sctx.result && sctx.mech) …（mech は NULL なので通らない）
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envS xB) _ (W1 c fir xB) _ _ (.Vint (Integers.Int.repr 0))
          (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _ (lvx hcenv offx_res)
            (DerefLoc.value .Mint32 _ rfl
              (ldW (X := emp) 12 (by simp) rfl freeable_r (W1_emp hH) hag))))
        (triple_if_local ge _ _ (envS xB) _ (W1 c fir xB) _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0)) (hT.get (by temps_get))) rfl, rfl⟩)
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ (envS xB) _ (W1 c fir xB) _ _ z64
              (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _ (lvx hcenv offx_mech)
                (DerefLoc.value Mptr _ rfl
                  (ldW (X := emp) 6 (by simp) rfl freeable_r (W1_emp hH) hag))))
            (triple_set_local_fwd ge _ _ (envS xB) _ (W1 c fir xB) _ _ (Val.ofBool false)
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Etempvar _ _ z64 (hT.get (by temps_get))) rfl)))))
      (triple_if_local ge _ _ (envS xB) _ (W1 c fir xB) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false)
          (hT.get (by temps_get)), rfl⟩)
        (triple_skip ge _ _ _))) ?_
  -- Curl_bufref_free(&sctx.resp);  return sctx.result;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ brTy tvoid cc_default (W1 c fir xB) (W1 c fir xB) none _ _ (envS xB) _
      _ X.bfr.b X.fdFr (X.sFr xB) X.bfr.fp X.tFr rfl
      (fun _ _ _ => eval_callee_global (envS_get (by decide)) X.bfr.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (lvx hcenv offx_resp)) rfl EvalExprlist.nil)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envS xB) _ (W1 c fir xB) _ _ (.Vint (Integers.Int.repr 0))
      (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _ (lvx hcenv offx_res)
        (DerefLoc.value .Mint32 _ rfl
          (ldW (X := emp) 12 (by simp) rfl freeable_r (W1_emp hH) hag)))) ?_
  refine pre_conv ge _ _ (fun _ h => w1_ret h) ?_
  refine Case3C.ret_locs ge _ _ (envS xB) _ _ [(xB, 80)] _ (.Vint (Integers.Int.repr 0))
    (.Vint (Integers.Int.repr 0)) _
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (fun _ => rfl) ?_ ?_
    (fun hp hH => ⟨rfl, hH⟩)
  · rw [blocks_envS ge hcenv]
    intro x hx'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
    subst hx'
    exact ⟨xB, 80, rfl, by simp⟩
  · rw [blocks_envS ge hcenv]
    simp

/-! ## 関数全体 -/

theorem start_after (ge : CGenv) (c : Ctx) (fir : Bool)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hfollow : bitOf c.stw 0 = true) (hallow : bitOf c.setw 0 = false)
    (hE : Integers.Int.and (em c) (Integers.Int.repr 32) = Integers.Int.zero)
    (hP : Integers.Int.and (em c) (Integers.Int.repr 2) = Integers.Int.zero)
    (hL : Integers.Int.and (em c) (Integers.Int.repr 1) = Integers.Int.zero)
    (X : ExtU1 ge c fir) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_Curl_sasl_start) (startSpecA c fir) vs := by
  by_cases hvs : vs = argsS c fir
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hnv : listNorepet (varNames f_Curl_sasl_start.fn_vars) := by decide
  have hnp : listNorepet (varNames f_Curl_sasl_start.fn_params) := by decide
  have hdisj : listDisjoint (varNames f_Curl_sasl_start.fn_params)
      (varNames f_Curl_sasl_start.fn_temps) := by decide
  refine satisfies_internal ge (FunctionEntry2 ge) f_Curl_sasl_start _ _ (PbodyS c fir)
    (fun m hp hf hpre hd hag => ?_)
    (start_body_after ge c fir hcenv hpr hpn hpw hfollow hallow hE hP hL X)
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (Ty.Tstruct _sasl_ctx noattr))
  have hav : AllocVariables ge.genv_cenv emptyEnv m f_Curl_sasl_start.fn_vars (envS a1.2) a1.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [f_Curl_sasl_start, List.mem_cons, List.mem_nil_iff, or_false] at hv
      subst hv; rw [hcenv]; decide)
    (Heap.union hp hf) hag
  have hLs : Locs [(a1.2, 80)] hl := by
    have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv] at this
    exact this
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envS a1.2,
    PTree.set _progress (.Vptr c.pB c.pO) (PTree.set _force_ir (Val.ofBool fir)
      (PTree.set _data (.Vptr c.dB c.dO) (PTree.set _sasl (.Vptr c.sB c.sO)
        (createUndefTemps f_Curl_sasl_start.fn_temps)))),
    a1.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨a1.2, rfl, ?_, ⟨hp, hl, dph, rfl, hpre.2, hLs⟩⟩
    refine TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_cons ?_
      (TempsHold_nil _)))) <;> ptget

end Deb2025_14524U
