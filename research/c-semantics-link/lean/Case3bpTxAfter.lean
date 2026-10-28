/-
Case 3 のバックポート: curl 8.14.1 に 63dd390fab をバックポートした `tftp_tx`
（research/backport-proof/PROTOCOL.md の B1 の前半）。`Case3TxAfter` と同じ形の定理を、
8.14.1 の構造体のレイアウト（`Case3bpCommon`）の上で示す。

証明すること（`tx_after_illegal`）: ダウンロード中（`data->state.upload` が 0）なら、
どのイベントでも CURLE_TFTP_ILLEGAL（71）を返す。

呼ばれる側の関数（`Curl_client_read` を含む）については、何も仮定しない。
大域環境 `ge` は composite の環境が生成物と同じことだけを仮定し、関数の中身は問わない。
-/
import Case3bpCommon
import Case4After
open CC CC.Sep CC.HProp
open Case3bp_after
open Case5C (addr bitOf boolVal_ofBool_tint)
open Case4C (lv_field eval_deref_temp)
open Case1C (triple_pure)
open Case3C (Locs locs_of_localsAt ret_locs locs3_ne)

set_option maxRecDepth 20000

namespace Case3bpC

/-! ## 読むメモリ -/

/-- `tftp_tx` が修正の検査までに読むもの。 -/
structure CtxT where
  sB : Block                 -- state
  sO : Integers.Ptrofs
  dB : Block                 -- state->data
  dO : Integers.Ptrofs
  word : Integers.Int        -- data->state の prefer_ascii・upload を入れた 32 bit の単位
  pm : Permission

/-- `data->state.upload` を入れた単位の番地（`Efield` が計算するのと同じ式）。 -/
def updAddr (dO : Integers.Ptrofs) : Z := addr (Integers.Ptrofs.add dO (Integers.Ptrofs.repr 24)) 16

def HT (c : CtxT) : HProp :=
  mapsto Mptr c.pm c.sB (addr c.sO 16) (.Vptr c.dB c.dO) ∗
  mapsto .Mint32 c.pm c.dB (updAddr c.dO) (.Vint c.word)

def txSpecA (c : CtxT) (ev : Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _tftp_conn noattr), tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.sB c.sO, .Vint ev] ∧ HT c hp
  post := fun v hp => v = .Vint (Integers.Int.repr 71) ∧ HT c hp
  measure := fun _ => 0

/-! ## 局所変数（cb・buffer・eos） -/

def envT (b1 b2 b3 : Block) : Env :=
  ((emptyEnv.set _cb (b1, tulong)).set _buffer (b2, tarray tschar 256)).set _eos (b3, tbool)

abbrev LT (b1 b2 b3 : Block) : List (Block × Nat) := [(b1, 8), (b2, 256), (b3, 1)]

abbrev lT (c : CtxT) (ev : Integers.Int) : List (Ident × Val) :=
  [(_event, .Vint ev), (_state, .Vptr c.sB c.sO)]

def PbodyT (c : CtxT) (ev : Integers.Int) : Sep.Assn := fun e le hp =>
  ∃ bs : Block × Block × Block,
    (bs.1 ≠ bs.2.1 ∧ bs.1 ≠ bs.2.2 ∧ bs.2.1 ≠ bs.2.2) ∧
    LocalSt (envT bs.1 bs.2.1 bs.2.2) (lT c ev) (HT c ∗ Locs (LT bs.1 bs.2.1 bs.2.2)) e le hp

theorem blocks_envT (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (b1 b2 b3 : Block) :
    blocksOfEnv ge.genv_cenv (envT b1 b2 b3) = [(b2, 0, 256), (b3, 0, 1), (b1, 0, 8)] := by
  rw [hcenv]
  rfl

theorem tx_entry_wf :
    listNorepet (varNames f_tftp_tx.fn_vars)
    ∧ listNorepet (varNames f_tftp_tx.fn_params)
    ∧ listDisjoint (varNames f_tftp_tx.fn_params) (varNames f_tftp_tx.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## 式の評価 -/

theorem off_req : fieldOffset prog.prog_comp_env _req (coOf _Curl_easy).co_members
    = .OK (8, .Full) := by decide

theorem notbool_zero {x : Integers.Int} (hx : Integers.Int.eq x Integers.Int.zero = true) (m : Mem) :
    Cop.semUnaryOperation .Onotbool (.Vint x) tint m = some (Val.ofBool true) := by
  show (Cop.boolVal (.Vint x) tint m).map (fun b => Val.ofBool (!b)) = _
  rw [show Cop.boolVal (.Vint x) tint m = some (!Integers.Int.eq x Integers.Int.zero) from rfl, hx]
  rfl

theorem HT_loads {c : CtxT} {L : List (Block × Nat)} {hp : Heap} {m : Mem}
    (hpr : permOrder c.pm .Readable = true) (hH : (HT c ∗ Locs L) hp) (hag : Heap.Agrees hp m) :
    Mem.load Mptr m c.sB (addr c.sO 16) = some (.Vptr c.dB c.dO)
    ∧ Mem.load .Mint32 m c.dB (updAddr c.dO) = some (.Vint c.word) := by
  obtain ⟨h0, hHT, a0⟩ := Case5C.sep_l hH hag
  obtain ⟨h1, c1, a1⟩ := Case5C.sep_l hHT a0
  obtain ⟨h2, c2, a2⟩ := Case5C.sep_r hHT a0
  exact ⟨by rw [mapsto_load hpr c1 a1]; rfl, by rw [mapsto_load hpr c2 a2]; rfl⟩

/-- `data->state.upload` -/
theorem eval_upload {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {c : CtxT}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hle : le.get _data = some (.Vptr c.dB c.dO))
    (hload : Mem.load .Mint32 m c.dB (updAddr c.dO) = some (.Vint c.word)) :
    EvalExpr ge e le m
      (.Efield (.Efield (.Ederef (.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
          (Ty.Tstruct _Curl_easy noattr)) _state (Ty.Tstruct _UrlState noattr)) _upload tint)
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 c.word)) :=
  EvalExpr.Elvalue _ c.dB
    (Integers.Ptrofs.add (Integers.Ptrofs.add c.dO (Integers.Ptrofs.repr 24)) (Integers.Ptrofs.repr 16))
    (.Bits .I32 .Unsigned 1 1) _
    (EvalLvalue.Efield_struct _ _upload tint c.dB (Integers.Ptrofs.add c.dO (Integers.Ptrofs.repr 24))
      _UrlState (coOf _UrlState) noattr 16 _
      (EvalExpr.Elvalue _ _ _ .Full _
        (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_easy) (hcenv ▸ off_state))
        (DerefLoc.copy rfl))
      rfl (hcenv ▸ co_us) (hcenv ▸ off_upload))
    (DerefLoc.bitfield .I32 .Unsigned 1 1 _
      (Cop.LoadBitfield.intro .I32 .Signed noattr .Unsigned 1 1 m _ c.word (by decide) (by decide)
        (by decide) (by decide) (by decide) hload))

/-! ## 本体 -/

theorem tx_body_after (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : CtxT)
    (ev : Integers.Int) (hpr : permOrder c.pm .Readable = true) (hup : bitOf c.word 1 = false) :
    Triple ge (FunctionEntry2 ge) f_tftp_tx (PbodyT c ev) f_tftp_tx.fn_body
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := (txSpecA c ev).post } := by
  have hx : Integers.Int.eq (Cop.bitfieldExtract .I32 .Unsigned 1 1 c.word) Integers.Int.zero = true := by
    unfold bitOf at hup
    revert hup
    cases Integers.Int.eq _ _ <;> simp
  refine Sep.triple_exists ge _ _ _ _ _ (fun bs => ?_)
  obtain ⟨b1, b2, b3⟩ := bs
  refine triple_pure ge _ _ _ _ _ _ (fun hne => ?_)
  -- data = state->data;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (HT c ∗ Locs (LT b1 b2 b3)) _data _
      (.Vptr c.dB c.dO)
      (fun le m hp hT hH hag => Case5C.eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
        (hcenv ▸ off_data) rfl (HT_loads hpr hH hag).1)) ?_
  -- result = CURLE_OK;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (HT c ∗ Locs (LT b1 b2 b3)) _result _
      (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  -- k = &data->req;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (HT c ∗ Locs (LT b1 b2 b3)) _k _
      (.Vptr c.dB (Integers.Ptrofs.add c.dO (Integers.Ptrofs.repr 8)))
      (fun le m hp hT _ _ => EvalExpr.Eaddrof _ _ _ _
        (lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_easy)
          (hcenv ▸ off_req)))) ?_
  -- if(!data->state.upload) return CURLE_TFTP_ILLEGAL;
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envT b1 b2 b3) _ (HT c ∗ Locs (LT b1 b2 b3)) _t'66 _
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 c.word))
      (fun le m hp hT hH hag => eval_upload hcenv (hT.get (by temps_get)) (HT_loads hpr hH hag).2)) ?_
  refine triple_if_local ge _ _ (envT b1 b2 b3) _ (HT c ∗ Locs (LT b1 b2 b3)) _ true _ _ _
    (fun le m hp hT _ _ =>
      ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
            (notbool_zero hx m),
       boolVal_ofBool_tint _ m⟩) ?_
  rw [if_pos rfl]
  obtain ⟨n12, n13, n23⟩ := hne
  refine ret_locs ge _ _ (envT b1 b2 b3) _ (HT c) (LT b1 b2 b3) _ (.Vint (Integers.Int.repr 71))
    (.Vint (Integers.Int.repr 71)) _ (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl)
    ?_ ?_ (fun hp hH => ⟨rfl, hH⟩)
  · rw [blocks_envT ge hcenv]
    intro x hx'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
    rcases hx' with rfl | rfl | rfl
    · exact ⟨b2, 256, rfl, by simp⟩
    · exact ⟨b3, 1, rfl, by simp⟩
    · exact ⟨b1, 8, rfl, by simp⟩
  · rw [blocks_envT ge hcenv]
    simp [n23, Ne.symm n12, Ne.symm n13]

/-! ## 関数全体（入口で局所変数を確保するところから） -/

/-- **修正後の `tftp_tx` は、ダウンロード中なら、どのイベントでも CURLE_TFTP_ILLEGAL を返す。**
    呼ばれる側の関数については何も仮定しない（`ge` の関数の中身は問わない）。 -/
theorem tx_after_illegal (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : CtxT)
    (ev : Integers.Int) (hpr : permOrder c.pm .Readable = true) (hup : bitOf c.word 1 = false)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_tftp_tx) (txSpecA c ev) vs := by
  by_cases hvs : vs = [.Vptr c.sB c.sO, .Vint ev]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := tx_entry_wf
  refine satisfies_internal ge (FunctionEntry2 ge) f_tftp_tx _ _ (PbodyT c ev)
    (fun m hp hf hpre hd hag => ?_) (tx_body_after ge hcenv c ev hpr hup)
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv tulong)
  let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv (tarray tschar 256))
  let a3 := Mem.alloc a2.1 0 (sizeof ge.genv_cenv tbool)
  have hav : AllocVariables ge.genv_cenv emptyEnv m f_tftp_tx.fn_vars (envT a1.2 a2.2 a3.2) a3.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)))
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [f_tftp_tx, List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> rw [hcenv] <;> decide)
    (Heap.union hp hf) hag
  have hL : Locs (LT a1.2 a2.2 a3.2) hl := by
    have := locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv] at this
    exact this
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envT a1.2 a2.2 a3.2,
    PTree.set _event (.Vint ev) (PTree.set _state (.Vptr c.sB c.sO)
      (createUndefTemps f_tftp_tx.fn_temps)),
    a3.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨(a1.2, a2.2, a3.2), locs3_ne hL (by decide) (by decide) (by decide), rfl, ?_,
      ⟨hp, hl, dph, rfl, hpre.2, hL⟩⟩
    exact TempsHold_cons (PTree.gss _ _ _)
      (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)) (TempsHold_nil _))

end Case3bpC

#print axioms Case3bpC.tx_after_illegal
