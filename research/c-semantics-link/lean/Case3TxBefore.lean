/-
Case 3（CURL-CVE-2026-92389）: 修正前の `tftp_tx`（curl 3a397f7a05。修正 63dd390fab の親）。

証明すること（`tx_before_reads`）: OACK のイベント（6）で呼ばれると、`data->state.upload` の値によらず
（ダウンロード中を含む）、`Curl_client_read` を呼び、その戻り値 `r`（0 でない）をそのまま返す。

修正後の `tftp_tx` は、ダウンロード中なら呼ばれる側の関数について何も仮定せずに 71 を返す（`tx_after_illegal`）。
修正前の関数の戻り値は、`Curl_client_read` の仕様が決める値 `r` になる。`r` は任意なので、
戻り値は `Curl_client_read` を呼んだ結果である。

仮定するのは、この経路で呼ばれる `setpacketevent`・`setpacketblock`・`Curl_client_read` の3つの仕様だけで、
どれも「この関数が所有するメモリの形を保つ」と述べる。`R` はそれ以外のメモリ（`data` の中身や送信バッファ）で、
形は問わない。
-/
import Case3RecvAfter
open CC CC.Sep CC.HProp
open Case3_after
open Case5C (addr eval_field)
open Case4C (lv_field eval_deref_temp)
open Case1C (triple_pure call_some call_none seq_ex)

set_option maxRecDepth 20000

namespace Case3C

/-! ## 読み書きするメモリ -/

structure CtxB where
  sB : Block                 -- state
  sO : Integers.Ptrofs
  dB : Block                 -- state->data
  dO : Integers.Ptrofs
  pB : Block                 -- state->spacket.data（送信バッファ）
  pO : Integers.Ptrofs
  bs : Integers.Int          -- state->blksize
  pm : Permission

/-- 書き込まれるセルの値。 -/
structure ValsB where
  blk : Val                  -- state->block（16 bit）
  rt : Val                   -- state->retries
  sb : Val                   -- state->sbytes

abbrev cellsB (c : CtxB) (v : ValsB) : List CellD :=
  [ (Mptr, c.pm, c.sB, addr c.sO 160, .Vptr c.dB c.dO),                                     -- 0
    (.Mint16unsigned, c.pm, c.sB, addr c.sO 216, v.blk),                                    -- 1
    (.Mint32, c.pm, c.sB, addr c.sO 172, v.rt),                                             -- 2
    (.Mint64, c.pm, c.sB, addr c.sO 200, v.sb),                                             -- 3
    (.Mint32, c.pm, c.sB, addr c.sO 208, .Vint c.bs),                                       -- 4
    (Mptr, c.pm, c.sB, addr (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 136)) 0,
      .Vptr c.pB c.pO) ]                                                                    -- 5

/-- 関数の中のメモリ全体: セル、それ以外のメモリ `R`、局所変数 cb・buffer・eos。 -/
abbrev WB (c : CtxB) (v : ValsB) (R : HProp) (b1 b2 b3 : Block) : HProp :=
  Cells (cellsB c v) ∗ (R ∗ Locs (LT b1 b2 b3))

/-- `state->block = 1;` のあとの値（`unsigned short` への変換）。 -/
def blk1 : Val := .Vint (Integers.Int.zero_ext 16 (Integers.Int.repr 1))
/-- `state->sbytes = 0;` のあとの値（`size_t` への変換）。 -/
def sb0 : Val := .Vlong (Cop.castIntLong .Signed (Integers.Int.repr 0))

/-- `bufptr` の値（`(char *)state->spacket.data + 4`）。 -/
def bufV (ge : CGenv) (c : CtxB) : Val :=
  .Vptr c.pB (Integers.Ptrofs.add c.pO (Integers.Ptrofs.mul
    (Integers.Ptrofs.repr (sizeof ge.genv_cenv tschar)) (Cop.ptrofsOfInt .Signed (Integers.Int.repr 4))))

abbrev vA (v0 : ValsB) : ValsB := ⟨blk1, v0.rt, v0.sb⟩
abbrev vB (v0 : ValsB) : ValsB := ⟨blk1, .Vint (Integers.Int.repr 0), v0.sb⟩
abbrev vC (v0 : ValsB) : ValsB := ⟨blk1, .Vint (Integers.Int.repr 0), sb0⟩

/-! ## 仕様 -/

def txSpecB (c : CtxB) (v0 : ValsB) (R : HProp) (r : Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _tftp_conn noattr), tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.sB c.sO, .Vint (Integers.Int.repr 6)]
    ∧ (Cells (cellsB c v0) ∗ R) hp
  post := fun v hp => v = .Vint r ∧ ∃ v', (Cells (cellsB c v') ∗ R) hp
  measure := fun _ => 0

def setTy : List Ty := [tptr (Ty.Tstruct _tftp_packet noattr), tushort]
def readTy : List Ty :=
  [tptr (Ty.Tstruct _Curl_easy noattr), tptr tschar, tulong, tptr tulong, tptr tbool]

/-- 仮定する3つの仕様。局所変数のブロックとセルの値は任意。 -/
structure ExtB (ge : CGenv) (c : CtxB) (R : HProp) (r : Integers.Int) where
  sev : Callee ge _setpacketevent setTy tvoid cc_default
  sSev : ∀ v b1 b2 b3 vs, SatisfiesAt ge (FunctionEntry2 ge) sev.fd
    (specK setTy tvoid cc_default (WB c v R b1 b2 b3) (WB c v R b1 b2 b3) none) vs
  sbl : Callee ge _setpacketblock setTy tvoid cc_default
  sSbl : ∀ v b1 b2 b3 vs, SatisfiesAt ge (FunctionEntry2 ge) sbl.fd
    (specK setTy tvoid cc_default (WB c v R b1 b2 b3) (WB c v R b1 b2 b3) none) vs
  rd : Callee ge _Curl_client_read readTy tint cc_default
  sRd : ∀ v b1 b2 b3 vs, SatisfiesAt ge (FunctionEntry2 ge) rd.fd
    (specK readTy tint cc_default (WB c v R b1 b2 b3) (WB c v R b1 b2 b3) (some (.Vint r))) vs

/-! ## 式の評価 -/

theorem off_spacket : fieldOffset prog.prog_comp_env _spacket (coOf _tftp_conn).co_members
    = .OK (136, .Full) := off_conn.2.2.1
theorem off_retries : fieldOffset prog.prog_comp_env _retries (coOf _tftp_conn).co_members
    = .OK (172, .Full) := off_conn.2.2.2.2.2.1
theorem off_sbytes : fieldOffset prog.prog_comp_env _sbytes (coOf _tftp_conn).co_members
    = .OK (200, .Full) := off_conn.2.2.2.2.2.2.2.2.1
theorem off_block : fieldOffset prog.prog_comp_env _block (coOf _tftp_conn).co_members
    = .OK (216, .Full) := off_conn.2.2.2.2.2.2.2.2.2.2.1

/-- `&state->spacket` -/
theorem eval_spacket {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {sB : Block}
    {sO : Integers.Ptrofs} (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hle : le.get _state = some (.Vptr sB sO)) :
    EvalExpr ge e le m
      (.Eaddrof (.Efield (.Ederef (.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
          (Ty.Tstruct _tftp_conn noattr)) _spacket (Ty.Tstruct _tftp_packet noattr))
        (tptr (Ty.Tstruct _tftp_packet noattr)))
      (.Vptr sB (Integers.Ptrofs.add sO (Integers.Ptrofs.repr 136))) :=
  EvalExpr.Eaddrof _ _ _ _ (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_conn) (hcenv ▸ off_spacket))

/-- `state->spacket.data` -/
theorem eval_spdata {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {c : CtxB}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hle : le.get _state = some (.Vptr c.sB c.sO))
    (hload : Mem.load Mptr m c.sB (addr (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 136)) 0)
      = some (.Vptr c.pB c.pO)) :
    EvalExpr ge e le m
      (.Efield (.Efield (.Ederef (.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
          (Ty.Tstruct _tftp_conn noattr)) _spacket (Ty.Tstruct _tftp_packet noattr)) _data
        (tptr tuchar))
      (.Vptr c.pB c.pO) :=
  EvalExpr.Elvalue _ c.sB _ .Full _
    (EvalLvalue.Efield_struct _ _data _ c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 136))
      _tftp_packet (coOf _tftp_packet) noattr 0 .Full
      (EvalExpr.Elvalue _ _ _ .Full _
        (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_conn) (hcenv ▸ off_spacket))
        (DerefLoc.copy rfl))
      rfl (hcenv ▸ co_pkt) (hcenv ▸ off_pdata))
    (DerefLoc.value Mptr _ rfl hload)

/-! ## `return result;`（局所変数を解放する） -/

abbrev lTB (c : CtxB) : List (Ident × Val) :=
  [(Case3_before._event, .Vint (Integers.Int.repr 6)), (Case3_before._state, .Vptr c.sB c.sO)]

theorem ret_B (ge : CGenv) (fe) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : CtxB) (v0 v : ValsB)
    (R : HProp) (r : Integers.Int) (b1 b2 b3 : Block) (hne : b1 ≠ b2 ∧ b1 ≠ b3 ∧ b2 ≠ b3)
    (l : List (Ident × Val)) (hmem : (Case3_before._result, Val.Vint r) ∈ l) (Rx : Sep.ExitConds)
    (hR : Rx.ret = (txSpecB c v0 R r).post) :
    Triple ge fe Case3_before.f_tftp_tx (LocalSt (envT b1 b2 b3) l (WB c v R b1 b2 b3))
      (.Sreturn (some (.Etempvar Case3_before._result tint))) Rx := by
  obtain ⟨n12, n13, n23⟩ := hne
  refine triple_conseq ge fe _
    (ret_locs ge fe _ (envT b1 b2 b3) l (Cells (cellsB c v) ∗ R) (LT b1 b2 b3) _ (.Vint r) (.Vint r)
      Rx.ret (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get hmem)) (fun _ => rfl) ?_ ?_ ?_)
    (fun e le hp hP => ?_) (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
    (fun _ _ _ x => False.elim x) (fun _ _ x => x)
  · rw [blocks_envT ge hcenv]
    intro x hx'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
    rcases hx' with rfl | rfl | rfl
    · exact ⟨b2, 256, rfl, by simp⟩
    · exact ⟨b3, 1, rfl, by simp⟩
    · exact ⟨b1, 8, rfl, by simp⟩
  · rw [blocks_envT ge hcenv]
    simp [n23, Ne.symm n12, Ne.symm n13]
  · intro hp hH
    rw [hR]
    exact ⟨rfl, v, hH⟩
  · obtain ⟨he, hT, hH⟩ := hP
    refine ⟨he, hT, ?_⟩
    show ((Cells (cellsB c v) ∗ R) ∗ Locs (LT b1 b2 b3)) hp
    rw [sep_assoc_eq]
    exact hH

/-! ## 本体 -/

def PbodyB (c : CtxB) (v0 : ValsB) (R : HProp) : Sep.Assn := fun e le hp =>
  ∃ bs : Block × Block × Block,
    (bs.1 ≠ bs.2.1 ∧ bs.1 ≠ bs.2.2 ∧ bs.2.1 ≠ bs.2.2) ∧
    LocalSt (envT bs.1 bs.2.1 bs.2.2) (lTB c) (WB c v0 R bs.1 bs.2.1 bs.2.2) e le hp

set_option maxHeartbeats 4000000 in
theorem tx_body_before (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : CtxB)
    (v0 : ValsB) (R : HProp) (r : Integers.Int) (X : ExtB ge c R r)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hr : Integers.Int.eq r Integers.Int.zero = false) :
    Triple ge (FunctionEntry2 ge) Case3_before.f_tftp_tx (PbodyB c v0 R) Case3_before.f_tftp_tx.fn_body
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := (txSpecB c v0 R r).post } := by
  refine Sep.triple_exists ge _ _ _ _ _ (fun bs => ?_)
  obtain ⟨b1, b2, b3⟩ := bs
  refine triple_pure ge _ _ _ _ _ _ (fun hne => ?_)
  -- data = state->data;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (WB c v0 R b1 b2 b3) _data _ (.Vptr c.dB c.dO)
      (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
        (hcenv ▸ off_data) rfl (cell_load3 (l := cellsB c v0) (k := 0) (hk := by simp) rfl hpr hH hag))) ?_
  -- result = CURLE_OK;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (WB c v0 R b1 b2 b3) _result _
      (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  -- k = &data->req;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (WB c v0 R b1 b2 b3) _k _
      (.Vptr c.dB (Integers.Ptrofs.add c.dO (Integers.Ptrofs.repr 0)))
      (fun le m hp hT _ _ => EvalExpr.Eaddrof _ _ _ _
        (lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_easy)
          (hcenv ▸ off_req)))) ?_
  -- switch(event) { case TFTP_EVENT_ACK: case TFTP_EVENT_OACK: ... }（event は OACK = 6）
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  refine Sep.triple_switch_const ge _ _ _ _ _ _ 6 ?_
    (fun e le hp m hP _ => ⟨.Vint (Integers.Int.repr 6),
      EvalExpr.Etempvar _ _ _ (hP.2.1.get (by temps_get)), rfl⟩)
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  -- if(event == TFTP_EVENT_ACK) { ... } else state->block = 1;
  refine triple_seq_fwd ge _ _ _
    (LocalSt (envT b1 b2 b3) _ (WB c (vA v0) R b1 b2 b3)) _ _ _
    (triple_if_local ge _ _ (envT b1 b2 b3) _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 6)) (hT.get (by temps_get))) (EvalExpr.Econst_int _ _) rfl, rfl⟩)
      (assign_cell3 ge _ _ (envT b1 b2 b3) _ (cellsB c v0) _ 1 (by simp) .Mint16unsigned c.pm c.sB
        (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 216)) v0.blk blk1 rfl _ _ hpw rfl
        (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_conn)
          (hcenv ▸ off_block))
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩))) ?_
  -- state->retries = 0;
  refine triple_seq_fwd ge _ _ _
    (LocalSt (envT b1 b2 b3) _ (WB c (vB v0) R b1 b2 b3)) _ _ _
    (assign_cell3 ge _ _ (envT b1 b2 b3) _ (cellsB c (vA v0)) _ 2 (by simp) .Mint32 c.pm c.sB
      (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 172)) v0.rt (.Vint (Integers.Int.repr 0)) rfl _ _
      hpw rfl
      (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_conn)
        (hcenv ▸ off_retries))
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  -- setpacketevent(&state->spacket, TFTP_EVENT_DATA);
  refine seq_ex ge _ _ _ _ _ _ _
    (call_none ge _ _ (specK setTy tvoid cc_default (WB c (vB v0) R b1 b2 b3)
        (WB c (vB v0) R b1 b2 b3) none) _ _ (envT b1 b2 b3) _ _ _ X.sev.b X.sev.fd
      (fun _ => True) (fun _ => WB c (vB v0) R b1 b2 b3) (X.sSev (vB v0) b1 b2 b3) X.sev.fp X.sev.ty rfl
      (fun le m _ => eval_callee_global rfl X.sev.sym rfl)
      (fun le m hT => .cons _ _ _ _ _ _ _ (eval_spacket (sB := c.sB) (sO := c.sO) hcenv (hT.get (by temps_get))) rfl
        (.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl .nil))
      (fun h hH => hH) (fun v h hs => ⟨trivial, hs.2⟩))
    (fun _ => triple_pure ge _ _ _ _ _ _ (fun _ => ?_))
  -- setpacketblock(&state->spacket, state->block);
  refine seq_ex ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (WB c (vB v0) R b1 b2 b3) _t'52 _
        (Val.loadResult .Mint16unsigned blk1)
        (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
          (hcenv ▸ off_block) rfl (cell_load3 (l := cellsB c (vB v0)) (k := 1) (hk := by simp) rfl hpr hH hag)))
      (call_none ge _ _ (specK setTy tvoid cc_default (WB c (vB v0) R b1 b2 b3)
          (WB c (vB v0) R b1 b2 b3) none) _ _ (envT b1 b2 b3) _ _ _ X.sbl.b X.sbl.fd
        (fun _ => True) (fun _ => WB c (vB v0) R b1 b2 b3) (X.sSbl (vB v0) b1 b2 b3) X.sbl.fp X.sbl.ty rfl
        (fun le m _ => eval_callee_global rfl X.sbl.sym rfl)
        (fun le m hT => .cons _ _ _ _ _ _ _ (eval_spacket (sB := c.sB) (sO := c.sO) hcenv (hT.get (by temps_get))) rfl
          (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ (Val.loadResult .Mint16unsigned blk1) (hT.get (by temps_get))) rfl .nil))
        (fun h hH => hH) (fun v h hs => ⟨trivial, hs.2⟩)))
    (fun _ => triple_pure ge _ _ _ _ _ _ (fun _ => ?_))
  -- if(state->block > 1 && state->sbytes < state->blksize) { ... }（block は 1 なので偽）
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (WB c (vB v0) R b1 b2 b3) _t'49 _
          (Val.loadResult .Mint16unsigned blk1)
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
            (hcenv ▸ off_block) rfl (cell_load3 (l := cellsB c (vB v0)) (k := 1) (hk := by simp) rfl hpr hH hag)))
        (triple_if_local ge _ _ (envT b1 b2 b3) _ _ _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ (Val.loadResult .Mint16unsigned blk1) (hT.get (by temps_get))) (EvalExpr.Econst_int _ _) rfl, rfl⟩)
          (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (WB c (vB v0) R b1 b2 b3) _t'8 _
            (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))))
      (triple_if_local ge _ _ (envT b1 b2 b3) _ _ _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0)) (hT.get (by temps_get)), rfl⟩)
        (triple_skip ge _ _ _))) ?_
  -- state->sbytes = 0;
  refine triple_seq_fwd ge _ _ _
    (LocalSt (envT b1 b2 b3) _ (WB c (vC v0) R b1 b2 b3)) _ _ _
    (assign_cell3 ge _ _ (envT b1 b2 b3) _ (cellsB c (vB v0)) _ 3 (by simp) .Mint64 c.pm c.sB
      (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 200)) v0.sb sb0 rfl _ _ hpw rfl
      (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_conn)
        (hcenv ▸ off_sbytes))
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  -- bufptr = (char *)state->spacket.data + 4;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (WB c (vC v0) R b1 b2 b3) _t'48 _
        (.Vptr c.pB c.pO)
        (fun le m hp hT hH hag => eval_spdata hcenv (hT.get (by temps_get))
          (cell_load3 (l := cellsB c (vC v0)) (k := 5) (hk := by simp) rfl hpr hH hag)))
      (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (WB c (vC v0) R b1 b2 b3) _bufptr _ (bufV ge c)
        (fun le m hp hT _ _ => EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ (.Vptr c.pB c.pO) (hT.get (by temps_get))) rfl)
          (EvalExpr.Econst_int _ _) rfl))) ?_
  -- do { result = Curl_client_read(...); if(result) return result; ... } while(...);
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  refine triple_loop ge _ _ _ (fun _ => LocalSt (envT b1 b2 b3) _ (WB c (vC v0) R b1 b2 b3))
    (fun _ => Sep.Assn.no) _ _ (fun _ => ?_) (fun _ => Sep.triple_vacuous ge _ _ _ _) 0
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (seq_ex ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (WB c (vC v0) R b1 b2 b3) _t'46 _ (.Vint c.bs)
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
            (hcenv ▸ off_blksize) rfl (cell_load3 (l := cellsB c (vC v0)) (k := 4) (hk := by simp) rfl hpr hH hag)))
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (WB c (vC v0) R b1 b2 b3) _t'47 _ sb0
            (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
              (hcenv ▸ off_sbytes) rfl (cell_load3 (l := cellsB c (vC v0)) (k := 3) (hk := by simp) rfl hpr hH hag)))
          (call_some ge _ _ (specK readTy tint cc_default (WB c (vC v0) R b1 b2 b3)
              (WB c (vC v0) R b1 b2 b3) (some (.Vint r))) _t'10 _ _ (envT b1 b2 b3) _
            (WB c (vC v0) R b1 b2 b3) _ X.rd.b X.rd.fd (fun v => v = .Vint r)
            (fun _ => WB c (vC v0) R b1 b2 b3) (X.sRd (vC v0) b1 b2 b3) X.rd.fp X.rd.ty rfl
            (fun le m _ => eval_callee_global rfl X.rd.sym rfl)
            (fun le m hT =>
              .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get))) rfl
              (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ (bufV ge c) (hT.get (by temps_get))) rfl
              (.cons _ _ _ _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
                  (EvalExpr.Etempvar _ _ (.Vint c.bs) (hT.get (by temps_get)))
                  (EvalExpr.Etempvar _ _ (sb0) (hT.get (by temps_get))) rfl) rfl
              (.cons _ _ _ _ _ _ _ (eval_laddr (E := envT b1 b2 b3) rfl _) rfl
              (.cons _ _ _ _ _ _ _ (eval_laddr (E := envT b1 b2 b3) rfl _) rfl .nil)))))
            (fun h hH => hH) (fun v h hs => ⟨hs.1 _ rfl, hs.2⟩))))
      (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => by
        subst hv
        exact triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ _ _result _ (.Vint r)
          (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ (.Vint r) (hT.get (by temps_get))))))
    ?_
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  refine triple_if_local ge _ _ (envT b1 b2 b3) _ _ _ true _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint r) (hT.get (by temps_get)),
      (boolVal_int' r m).trans (by rw [hr]; rfl)⟩) ?_
  rw [if_pos rfl]
  exact ret_B ge _ hcenv c v0 (vC v0) R r b1 b2 b3 hne _ (by temps_get) _ rfl

/-! ## 関数全体（入口で局所変数を確保するところから） -/

theorem txB_entry_wf :
    listNorepet (varNames Case3_before.f_tftp_tx.fn_vars)
    ∧ listNorepet (varNames Case3_before.f_tftp_tx.fn_params)
    ∧ listDisjoint (varNames Case3_before.f_tftp_tx.fn_params)
        (varNames Case3_before.f_tftp_tx.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **修正前の `tftp_tx` は、OACK のイベントで呼ばれると、ダウンロード中でも `Curl_client_read` を呼び、
    その戻り値（0 でない任意の `r`）をそのまま返す。** -/
theorem tx_before_reads (ge : CGenv) (hcenv : ge.genv_cenv = Case3_before.prog.prog_comp_env)
    (c : CtxB) (v0 : ValsB) (R : HProp) (r : Integers.Int) (X : ExtB ge c R r)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hr : Integers.Int.eq r Integers.Int.zero = false) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal Case3_before.f_tftp_tx) (txSpecB c v0 R r) vs := by
  have hcenv' : ge.genv_cenv = prog.prog_comp_env := hcenv.trans cenv_same
  by_cases hvs : vs = [.Vptr c.sB c.sO, .Vint (Integers.Int.repr 6)]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := txB_entry_wf
  refine satisfies_internal ge (FunctionEntry2 ge) Case3_before.f_tftp_tx _ _ (PbodyB c v0 R)
    (fun m hp hf hpre hd hag => ?_) (tx_body_before ge hcenv' c v0 R r X hpr hpw hr)
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv tulong)
  let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv (tarray tschar 256))
  let a3 := Mem.alloc a2.1 0 (sizeof ge.genv_cenv tbool)
  have hav : AllocVariables ge.genv_cenv emptyEnv m Case3_before.f_tftp_tx.fn_vars
      (envT a1.2 a2.2 a3.2) a3.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)))
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [Case3_before.f_tftp_tx, List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> rw [hcenv'] <;> decide)
    (Heap.union hp hf) hag
  have hL : Locs (LT a1.2 a2.2 a3.2) hl := by
    have := locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv'] at this
    exact this
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envT a1.2 a2.2 a3.2,
    PTree.set Case3_before._event (.Vint (Integers.Int.repr 6)) (PTree.set Case3_before._state (.Vptr c.sB c.sO)
      (createUndefTemps Case3_before.f_tftp_tx.fn_temps)),
    a3.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨(a1.2, a2.2, a3.2), locs3_ne hL (by decide) (by decide) (by decide), rfl, ?_, ?_⟩
    · exact TempsHold_cons (PTree.gss _ _ _)
        (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)) (TempsHold_nil _))
    · show (Cells (cellsB c v0) ∗ (R ∗ Locs (LT a1.2 a2.2 a3.2))) (Heap.union hp hl)
      rw [← sep_assoc_eq]
      exact ⟨hp, hl, dph, rfl, hpre.2, hL⟩

end Case3C

#print axioms Case3C.tx_before_reads
