/-
Case 3 のバックポート: curl 8.14.1 に 63dd390fab をバックポートした `tftp_receive_packet`
（research/backport-proof/PROTOCOL.md の B1 の後半）。

証明すること: アップロード中（`data->state.upload` が 1）に受け取ったパケットが
DATA（`getrpacketevent` が 3 を返し、長さが 4 以上）なら、戻り値は CURLE_TFTP_ILLEGAL（71）である。

- `recv_bp_illegal`: 戻り値は 71（8.14.1 には送信元のアドレスを固定する分岐が無いので、56 を返す経路が無い）
- `recv_bp_illegal_form`: `Case3RecvAfter.recv_after_illegal` と同じ形（71 か 56）の事後条件

`Curl_client_write` については何も仮定しない。仮定するのは `recvfrom`・`getrpacketevent` の2つの仕様だけで、
どれも「この関数が所有するメモリの形を保つ」と述べる。上流の修正では、アドレスの固定のために
`memcmp`・`memcpy`・`Curl_failf` の仕様も要った（`Case3RecvAfter` の `ExtR`）。
上流で置いた前提 `hn0`（受信バイト数が 0 以上）も、8.14.1 の経路では使わないので置かない。
-/
import Case3bpTxAfter
import Case3RecvAfter
open CC CC.Sep CC.HProp
open Case3bp_after
open Case5C (addr bitOf boolVal_ofBool_tint eval_field)
open Case4C (lv_field eval_deref_temp)
open Case1C (triple_pure call_some seq_ex)
open Case3C (Locs ret_locs CellD Cells assign_cell3 cell_load3 mapsto_anyBytes
  Callee specK boolVal_int' cmp_lt4 ls_weak)

set_option maxRecDepth 20000

namespace Case3bpC

/-! ## 読み書きするメモリ -/

structure CtxR where
  sB : Block                 -- state
  sO : Integers.Ptrofs
  dB : Block                 -- data
  dO : Integers.Ptrofs
  pkB : Block                -- state->rpacket.data（受信バッファ）
  pkO : Integers.Ptrofs
  pkN : Nat                  -- 受信バッファの大きさ
  sock : Integers.Int        -- state->sockfd
  bs : Integers.Int          -- state->blksize
  word : Integers.Int        -- data->state の prefer_ascii・upload を入れた単位
  pm : Permission

/-- 書き込まれるセルの値。 -/
structure ValsR where
  rb : Val                   -- state->rbytes
  alen : Integers.Int        -- state->remote_addrlen
  ev : Val                   -- state->event

abbrev cellsK (c : CtxR) (v : ValsR) : List CellD :=
  [ (.Mint32, c.pm, c.sB, addr c.sO 24, .Vint c.sock),                                     -- 0
    (Mptr, c.pm, c.sB, addr (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 208)) 0,
      .Vptr c.pkB c.pkO),                                                                   -- 1
    (.Mint32, c.pm, c.sB, addr c.sO 192, .Vint c.bs),                                      -- 2
    (.Mint32, c.pm, c.sB, addr c.sO 180, v.rb),                                            -- 3
    (.Mint32, c.pm, c.sB, addr c.sO 176, .Vint v.alen),                                    -- 4
    (.Mint32, c.pm, c.sB, addr c.sO 8, v.ev),                                              -- 5
    (.Mint32, c.pm, c.dB, updAddr c.dO, .Vint c.word) ]                                    -- 6

/-- 中身を問わない領域: state->remote_addr（recvfrom が書き込む）と受信バッファ。 -/
def regK (c : CtxR) : HProp :=
  anyBytes c.pm c.sB (addr c.sO 48) 128 ∗ anyBytes c.pm c.pkB (Integers.Ptrofs.unsigned c.pkO) c.pkN

/-- 呼ばれる前のメモリ（局所変数を除く）。 -/
abbrev HK (c : CtxR) (v : ValsR) : HProp := Cells (cellsK c v) ∗ regK c

/-- 関数の中のメモリ全体: `HK` と、局所変数 fromlen。 -/
abbrev W (c : CtxR) (bfl : Block) (v : ValsR) (fl : Val) : HProp :=
  Cells (cellsK c v) ∗ (regK c ∗ (mapsto .Mint32 .Freeable bfl 0 fl ∗ emp))

theorem W_fl (c : CtxR) (bfl : Block) (v : ValsR) (fl : Val) :
    W c bfl v fl = mapsto .Mint32 .Freeable bfl 0 fl ∗ (Cells (cellsK c v) ∗ (regK c ∗ emp)) := by
  unfold W
  rw [sep_left_comm_eq (regK c), sep_left_comm_eq (Cells (cellsK c v))]

def envR (bfl : Block) : Env := emptyEnv.set _fromlen (bfl, tuint)

abbrev lR (c : CtxR) : List (Ident × Val) := [(_state, .Vptr c.sB c.sO), (_data, .Vptr c.dB c.dO)]

/-- `(int)` で切り詰めた `recvfrom` の戻り値。 -/
def rOf (n : Integers.Int64) : Integers.Int := Integers.Int.repr (Integers.Int64.unsigned n)

/-! ## 仕様 -/

/-- 戻り値についての述語 `Q` を引数にとる。`Q := (· = 71)` と `Q := (· = 71 ∨ · = 56)` で使う。 -/
def rpSpec (Q : Val → Prop) (c : CtxR) (v0 : ValsR) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _tftp_conn noattr)]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dB c.dO, .Vptr c.sB c.sO] ∧ HK c v0 hp
  post := fun r hp => Q r ∧ ∃ v, HK c v hp
  measure := fun _ => 0

def recvTy : List Ty :=
  [tint, tptr tvoid, tulong, tint, tptr (Ty.Tstruct _sockaddr noattr), tptr tuint]
def pktTy : List Ty := [tptr (Ty.Tstruct _tftp_packet noattr)]

/-- 仮定する2つの仕様。`bfl`（局所変数のブロック）と `v`・`f0`（その時点の値）は任意。 -/
structure ExtR (ge : CGenv) (c : CtxR) (n : Integers.Int64) (fl : Integers.Int) where
  recv : Callee ge _recvfrom recvTy tlong cc_default
  sRecv : ∀ bfl v f0 vs, SatisfiesAt ge (FunctionEntry2 ge) recv.fd
    (specK recvTy tlong cc_default (W c bfl v f0) (W c bfl v (.Vint fl)) (some (.Vlong n))) vs
  ev : Callee ge _getrpacketevent pktTy tushort cc_default
  sEv : ∀ bfl v f0 vs, SatisfiesAt ge (FunctionEntry2 ge) ev.fd
    (specK pktTy tushort cc_default (W c bfl v f0) (W c bfl v f0)
      (some (.Vint (Integers.Int.repr 3)))) vs

/-! ## フィールドのオフセット（`off_conn` から取り出したもの） -/

theorem off_event : fieldOffset prog.prog_comp_env _event (coOf _tftp_conn).co_members
    = .OK (8, .Full) := off_conn.1
theorem off_sockfd : fieldOffset prog.prog_comp_env _sockfd (coOf _tftp_conn).co_members
    = .OK (24, .Full) := off_conn.2.1
theorem off_raddr : fieldOffset prog.prog_comp_env _remote_addr (coOf _tftp_conn).co_members
    = .OK (48, .Full) := off_conn.2.2.2.1
theorem off_addrlen : fieldOffset prog.prog_comp_env _remote_addrlen (coOf _tftp_conn).co_members
    = .OK (176, .Full) := off_conn.2.2.2.2.1
theorem off_rbytes : fieldOffset prog.prog_comp_env _rbytes (coOf _tftp_conn).co_members
    = .OK (180, .Full) := off_conn.2.2.2.2.2.1
theorem off_blksize' : fieldOffset prog.prog_comp_env _blksize (coOf _tftp_conn).co_members
    = .OK (192, .Full) := off_conn.2.2.2.2.2.2.2.1
theorem off_rpacket : fieldOffset prog.prog_comp_env _rpacket (coOf _tftp_conn).co_members
    = .OK (208, .Full) := off_conn.2.2.2.2.2.2.2.2.2.1

/-! ## 式の評価 -/

theorem eval_upload2 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {dB : Block}
    {dO : Integers.Ptrofs} {word : Integers.Int}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hle : le.get _data = some (.Vptr dB dO))
    (hload : Mem.load .Mint32 m dB (updAddr dO) = some (.Vint word)) :
    EvalExpr ge e le m
      (.Efield (.Efield (.Ederef (.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
          (Ty.Tstruct _Curl_easy noattr)) _state (Ty.Tstruct _UrlState noattr)) _upload tint)
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 word)) :=
  eval_upload (c := ⟨Mem.empty.nextblock, Integers.Ptrofs.zero, dB, dO, word, .Freeable⟩)
    hcenv hle hload

/-- `state->rpacket.data` -/
theorem eval_rpdata {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {c : CtxR}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hle : le.get _state = some (.Vptr c.sB c.sO))
    (hload : Mem.load Mptr m c.sB (addr (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 208)) 0)
      = some (.Vptr c.pkB c.pkO)) :
    EvalExpr ge e le m
      (.Efield (.Efield (.Ederef (.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
          (Ty.Tstruct _tftp_conn noattr)) _rpacket (Ty.Tstruct _tftp_packet noattr)) _data
        (tptr tuchar))
      (.Vptr c.pkB c.pkO) :=
  EvalExpr.Elvalue _ c.sB _ .Full _
    (EvalLvalue.Efield_struct _ _data _ c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 208))
      _tftp_packet (coOf _tftp_packet) noattr 0 .Full
      (EvalExpr.Elvalue _ _ _ .Full _
        (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_conn) (hcenv ▸ off_rpacket))
        (DerefLoc.copy rfl))
      rfl (hcenv ▸ co_pkt) (hcenv ▸ off_pdata))
    (DerefLoc.value Mptr _ rfl hload)

/-- `&state->fld`（`fld` は構造体の中の、オフセット `d` の構造体） -/
theorem eval_saddr {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {c : CtxR} {fld sid : Ident}
    {d : Z} (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hle : le.get _state = some (.Vptr c.sB c.sO))
    (hoff : fieldOffset prog.prog_comp_env fld (coOf _tftp_conn).co_members = .OK (d, .Full)) :
    EvalExpr ge e le m
      (.Eaddrof (.Efield (.Ederef (.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
          (Ty.Tstruct _tftp_conn noattr)) fld (Ty.Tstruct sid noattr)) (tptr (Ty.Tstruct sid noattr)))
      (.Vptr c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr d))) :=
  EvalExpr.Eaddrof _ _ _ _ (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_conn) (hcenv ▸ hoff))

theorem envR_fl (bfl : Block) : (envR bfl).get _fromlen = some (bfl, tuint) := rfl

/-- 局所変数 fromlen の読み出し。 -/
theorem eval_fromlen {ge : CGenv} {le : TempEnv} {m : Mem} {c : CtxR} {bfl : Block}
    {v : ValsR} {fl : Integers.Int} {hp : Heap}
    (hH : W c bfl v (.Vint fl) hp) (hag : Heap.Agrees hp m) :
    EvalExpr ge (envR bfl) le m (.Evar _fromlen tuint) (.Vint fl) := by
  rw [W_fl] at hH
  obtain ⟨h1, h2, _, rfl, hm, _⟩ := hH
  have hl := mapsto_load (rfl : permOrder .Freeable .Readable = true) hm (Heap.Agrees_union_left hag)
  refine EvalExpr.Elvalue _ bfl Integers.Ptrofs.zero .Full _
    (EvalLvalue.Evar_local _ _ _ (envR_fl bfl)) (DerefLoc.value .Mint32 _ rfl ?_)
  show Mem.load .Mint32 m bfl (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) = _
  rw [ptrofs_unsigned_zero]
  exact hl

theorem eval_laddr_fl {ge : CGenv} {le : TempEnv} {m : Mem} (bfl : Block) (t : Ty) :
    EvalExpr ge (envR bfl) le m (.Eaddrof (.Evar _fromlen tuint) t) (.Vptr bfl Integers.Ptrofs.zero) :=
  EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (envR_fl bfl))

/-! ## 文の規則（この関数のメモリの形に合わせたもの） -/

/-- `fromlen = a2;`（局所変数への書き込み）。 -/
theorem assign_fromlen (ge fe f) (c : CtxR) (bfl : Block) (v : ValsR) (x : Val)
    (l : List (Ident × Val)) (a2 : Expr)
    (hrhs : ∀ le m, TempsHold l le →
      ∃ v2 vnew, EvalExpr ge (envR bfl) le m a2 v2 ∧ Cop.semCast v2 (typeof a2) tuint m = some vnew) :
    Triple ge fe f (LocalSt (envR bfl) l (W c bfl v x)) (.Sassign (.Evar _fromlen tuint) a2)
      (.only (fun e le hp => ∃ f0, LocalSt (envR bfl) l (W c bfl v f0) e le hp)) := by
  refine triple_assign ge fe f _ _ _ a2 .Mint32 .Freeable bfl Integers.Ptrofs.zero rfl rfl
    (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  obtain ⟨v2, vnew, hev, hcast⟩ := hrhs le m hT
  rw [W_fl] at hH
  obtain ⟨h1, h2, hd, rfl, hm, hR⟩ := hH
  refine ⟨x, vnew, h1, h2, hd, rfl, by rw [ptrofs_unsigned_zero]; exact hm,
    EvalLvalue.Evar_local _ _ _ (envR_fl bfl), ⟨v2, hev, hcast⟩, fun h1' hm' hd' => ?_⟩
  refine ⟨vnew, rfl, hT, ?_⟩
  rw [W_fl]
  rw [ptrofs_unsigned_zero] at hm'
  exact ⟨h1', h2, hd', rfl, hm', hR⟩

/-- 局所変数を解放して `return k;`（k は定数）。戻ったあとのメモリは `HK c v`。 -/
theorem ret_W (Q : Val → Prop) (ge : CGenv) (fe f) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (c : CtxR) (bfl : Block) (v : ValsR) (x : Val) (l : List (Ident × Val))
    (k : Integers.Int) (hk : Q (.Vint k))
    (hret : f.fn_return = tint) (R : Sep.ExitConds) (hR : R.ret = fun r hp => Q r ∧ ∃ v, HK c v hp) :
    Triple ge fe f (LocalSt (envR bfl) l (W c bfl v x)) (.Sreturn (some (.Econst_int k tint))) R := by
  have hblk : blocksOfEnv ge.genv_cenv (envR bfl) = [(bfl, 0, 4)] := by
    rw [hcenv]; rfl
  refine triple_conseq ge fe f
    (ret_locs ge fe f (envR bfl) l (HK c v) [(bfl, 4)] _ (.Vint k) (.Vint k)
      R.ret (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) (fun _ => by rw [hret]; rfl) ?_ ?_ ?_)
    (fun e le hp hP => ?_) (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
    (fun _ _ _ x => False.elim x) (fun _ _ x => x)
  · rw [hblk]
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    subst hy
    exact ⟨bfl, 4, rfl, by simp⟩
  · rw [hblk]; simp
  · intro hp hH
    rw [hR]
    exact ⟨hk, v, hH⟩
  · obtain ⟨he, hT, hH⟩ := hP
    refine ⟨he, hT, ?_⟩
    obtain ⟨h1, h2, hd, rfl, hC, hr⟩ := hH
    obtain ⟨h3, h4, hd', rfl, hrg, hl⟩ := hr
    obtain ⟨h7, h8, hd3, rfl, hm, he8⟩ := hl
    rw [← Heap.union_assoc]
    refine ⟨_, _, Heap.disjoint_union_left.mpr ⟨?_, ?_⟩, rfl, ⟨h1, h3, ?_, rfl, hC, hrg⟩,
      ⟨h7, h8, hd3, rfl, mapsto_anyBytes hm, he8⟩⟩
    · exact Heap.disjoint_union_right.mp hd |>.2
    · exact hd'
    · exact Heap.disjoint_union_right.mp hd |>.1

/-! ## 本体 -/

theorem rp_body_bp (Q : Val → Prop) (hQ : Q (.Vint (Integers.Int.repr 71)))
    (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : CtxR)
    (v0 : ValsR) (n : Integers.Int64) (fl : Integers.Int) (X : ExtR ge c n fl)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hup : bitOf c.word 1 = true)
    (hn4 : Integers.Int.lt (rOf n) (Integers.Int.repr 4) = false)
    (bfl : Block) :
    Triple ge (FunctionEntry2 ge) f_tftp_receive_packet
      (LocalSt (envR bfl) (lR c) (W c bfl v0 .Vundef)) f_tftp_receive_packet.fn_body
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := (rpSpec Q c v0).post } := by
  -- result = CURLE_OK;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envR bfl) _ (W c bfl v0 .Vundef) _result _
      (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  -- fromlen = sizeof(state->remote_addr);
  refine seq_ex ge _ _ _ _ _ _ _
    (assign_fromlen ge _ _ c bfl v0 .Vundef _ _
      (fun le m _ => ⟨_, _, EvalExpr.Esizeof _ _, rfl⟩)) (fun f0 => ?_)
  -- t'22 = state->sockfd; t'23 = state->rpacket.data; t'24 = state->blksize; t'1 = recvfrom(...);
  -- state->rbytes = (int)t'1;
  refine triple_seq_fwd ge _ _ _
    (LocalSt (envR bfl) _ (W c bfl ⟨.Vint (rOf n), v0.alen, v0.ev⟩ (.Vint fl))) _ _ _
    (seq_ex ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envR bfl) _ (W c bfl v0 f0) _t'22 _ (.Vint c.sock)
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
            (hcenv ▸ off_sockfd) rfl (cell_load3 (l := cellsK c _) (k := 0) (hk := by simp) rfl hpr hH hag)))
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ (envR bfl) _ (W c bfl v0 f0) _t'23 _
            (.Vptr c.pkB c.pkO)
            (fun le m hp hT hH hag => eval_rpdata hcenv (hT.get (by temps_get))
              (cell_load3 (l := cellsK c _) (k := 1) (hk := by simp) rfl hpr hH hag)))
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ (envR bfl) _ (W c bfl v0 f0) _t'24 _ (.Vint c.bs)
              (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
                (hcenv ▸ off_blksize') rfl (cell_load3 (l := cellsK c _) (k := 2) (hk := by simp) rfl hpr hH hag)))
            (call_some ge _ _ (specK recvTy tlong cc_default (W c bfl v0 f0)
                (W c bfl v0 (.Vint fl)) (some (.Vlong n))) _t'1 _ _ (envR bfl) _
              (W c bfl v0 f0) _ X.recv.b X.recv.fd (fun v => v = .Vlong n)
              (fun _ => W c bfl v0 (.Vint fl)) (X.sRecv bfl v0 f0) X.recv.fp X.recv.ty rfl
              (fun le m _ => eval_callee_global rfl X.recv.sym rfl)
              (fun le m hT =>
                .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl
                (.cons _ _ _ _ _ _ _ (EvalExpr.Ecast _ _ _ _
                    (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl) rfl
                (.cons _ _ _ _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
                    (EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl)
                    (EvalExpr.Econst_int _ _) rfl) rfl
                (.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl
                (.cons _ _ _ _ _ _ _ (EvalExpr.Ecast _ _ _ _
                    (eval_saddr (c := c) hcenv (hT.get (by temps_get)) off_raddr) rfl) rfl
                (.cons _ _ _ _ _ _ _ (eval_laddr_fl bfl _) rfl .nil))))))
              (fun h hH => hH) (fun v h hs => ⟨hs.1 _ rfl, hs.2⟩)))))
      (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => by
        subst hv
        exact assign_cell3 ge _ _ (envR bfl) _ (cellsK c v0) _ 3 (by simp) .Mint32 c.pm c.sB
          (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 180)) v0.rb (.Vint (rOf n)) rfl _ _ hpw rfl
          (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_conn)
            (hcenv ▸ off_rbytes))
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Ecast _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl, rfl⟩))))
    ?_
  -- t'21 = fromlen; state->remote_addrlen = t'21;
  refine triple_seq_fwd ge _ _ _
    (LocalSt (envR bfl) _ (W c bfl ⟨.Vint (rOf n), fl, v0.ev⟩ (.Vint fl))) _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envR bfl) _ _ _t'21 _ (.Vint fl)
        (fun le m hp hT hH hag => eval_fromlen hH hag))
      (assign_cell3 ge _ _ (envR bfl) _ (cellsK c ⟨.Vint (rOf n), v0.alen, v0.ev⟩) _ 4 (by simp)
        .Mint32 c.pm c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 176)) (.Vint v0.alen) (.Vint fl)
        rfl _ _ hpw rfl
        (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_conn)
          (hcenv ▸ off_addrlen))
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩))) ?_
  -- if(state->rbytes < 4) { ... } else { ... }
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envR bfl) _ _ _t'10 _ (.Vint (rOf n))
      (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
        (hcenv ▸ off_rbytes) rfl (cell_load3 (l := cellsK c _) (k := 3) (hk := by simp) rfl hpr hH hag)))
    ?_
  refine triple_if_local ge _ _ (envR bfl) _ _ _ false _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
      (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _)
      (cmp_lt4 _ _ _), (boolVal_ofBool_tint _ m).trans (by rw [hn4])⟩) ?_
  rw [if_neg Bool.false_ne_true]
  -- t'2 = getrpacketevent(&state->rpacket); event = (unsigned short)t'2;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (seq_ex ge _ _ _ _ _ _ _
      (call_some ge _ _ (specK pktTy tushort cc_default
          (W c bfl ⟨.Vint (rOf n), fl, v0.ev⟩ (.Vint fl))
          (W c bfl ⟨.Vint (rOf n), fl, v0.ev⟩ (.Vint fl)) (some (.Vint (Integers.Int.repr 3))))
        _t'2 _ _ (envR bfl) _ _ _ X.ev.b X.ev.fd (fun v => v = .Vint (Integers.Int.repr 3))
        (fun _ => W c bfl ⟨.Vint (rOf n), fl, v0.ev⟩ (.Vint fl)) (X.sEv bfl _ _)
        X.ev.fp X.ev.ty rfl
        (fun le m _ => eval_callee_global rfl X.ev.sym rfl)
        (fun le m hT => .cons _ _ _ _ _ _ _ (eval_saddr (c := c) hcenv (hT.get (by temps_get)) off_rpacket) rfl .nil)
        (fun h hH => hH) (fun v h hs => ⟨hs.1 _ rfl, hs.2⟩))
      (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => by
        subst hv
        exact triple_set_local_fwd ge _ _ (envR bfl) _ _ _event _ (.Vint (Integers.Int.repr 3))
          (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl))))
    ?_
  -- state->event = (int)event;
  refine triple_seq_fwd ge _ _ _
    (LocalSt (envR bfl) _
      (W c bfl ⟨.Vint (rOf n), fl, .Vint (Integers.Int.repr 3)⟩ (.Vint fl))) _ _ _
    (assign_cell3 ge _ _ (envR bfl) _ (cellsK c ⟨.Vint (rOf n), fl, v0.ev⟩) _ 5 (by simp)
      .Mint32 c.pm c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 8)) v0.ev
      (.Vint (Integers.Int.repr 3)) rfl _ _ hpw rfl
      (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_conn)
        (hcenv ▸ off_event))
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Ecast _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl, rfl⟩)) ?_
  -- switch(state->event) { case TFTP_EVENT_DATA: if(data->state.upload) return CURLE_TFTP_ILLEGAL; ...
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envR bfl) _ _ _t'11 _ (.Vint (Integers.Int.repr 3))
      (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
        (hcenv ▸ off_event) rfl (cell_load3 (l := cellsK c _) (k := 5) (hk := by simp) rfl hpr hH hag)))
    ?_
  refine Sep.triple_switch_const ge _ _ _ _ _ _ 3 ?_
    (fun e le hp m hP _ => ⟨_, EvalExpr.Etempvar _ _ _ (hP.2.1.get (by temps_get)), rfl⟩)
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envR bfl) _ _ _t'20 _
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 c.word))
      (fun le m hp hT hH hag => eval_upload2 hcenv (hT.get (by temps_get))
        (cell_load3 (l := cellsK c _) (k := 6) (hk := by simp) rfl hpr hH hag)))
    ?_
  refine triple_if_local ge _ _ (envR bfl) _ _ _ true _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
      (boolVal_int' _ m).trans (by
        rw [show (!Integers.Int.eq (Cop.bitfieldExtract .I32 .Unsigned 1 1 c.word) Integers.Int.zero)
          = bitOf c.word 1 from rfl, hup])⟩) ?_
  rw [if_pos rfl]
  exact ret_W Q ge _ _ hcenv c bfl _ _ _ _ hQ rfl _ rfl

/-! ## 関数全体（入口で局所変数を確保するところから） -/

theorem rp_entry_wf :
    listNorepet (varNames f_tftp_receive_packet.fn_vars)
    ∧ listNorepet (varNames f_tftp_receive_packet.fn_params)
    ∧ listDisjoint (varNames f_tftp_receive_packet.fn_params)
        (varNames f_tftp_receive_packet.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

def PbodyR (c : CtxR) (v0 : ValsR) : Sep.Assn := fun e le hp =>
  ∃ bfl : Block, LocalSt (envR bfl) (lR c) (W c bfl v0 .Vundef) e le hp

theorem recv_bp_general (Q : Val → Prop) (hQ : Q (.Vint (Integers.Int.repr 71)))
    (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : CtxR)
    (v0 : ValsR) (n : Integers.Int64) (fl : Integers.Int) (X : ExtR ge c n fl)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hup : bitOf c.word 1 = true)
    (hn4 : Integers.Int.lt (rOf n) (Integers.Int.repr 4) = false) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_tftp_receive_packet) (rpSpec Q c v0) vs := by
  by_cases hvs : vs = [.Vptr c.dB c.dO, .Vptr c.sB c.sO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := rp_entry_wf
  refine satisfies_internal ge (FunctionEntry2 ge) f_tftp_receive_packet _ _ (PbodyR c v0)
    (fun m hp hf hpre hd hag => ?_)
    (Sep.triple_exists ge _ _ _ _ _ (fun bfl =>
      rp_body_bp Q hQ ge hcenv c v0 n fl X hpr hpw hup hn4 bfl))
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv tuint)
  have hav : AllocVariables ge.genv_cenv emptyEnv m f_tftp_receive_packet.fn_vars (envR a1.2) a1.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [f_tftp_receive_packet, List.mem_cons, List.mem_nil_iff, or_false] at hv
      subst hv
      rw [hcenv]
      decide)
    (Heap.union hp hf) hag
  have hLP : (mapsto .Mint32 .Freeable a1.2 0 .Vundef ∗ emp) hl := by
    obtain ⟨h3, h4, hd34, rfl, ⟨b', hb'⟩, he⟩ := hloc
    obtain ⟨hget', hu'⟩ := pure_sep_elim hb'
    rw [envR_fl] at hget'
    cases hget'
    rw [hcenv] at hu'
    have hm : mapsto .Mint32 .Freeable a1.2 0 .Vundef h3 := by
      rw [← undefBytes_mapsto .Freeable a1.2 0 undefEncoded_Mint32 (by decide)]
      exact hu'
    exact ⟨h3, h4, hd34, rfl, hm, he⟩
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envR a1.2,
    PTree.set _state (.Vptr c.sB c.sO) (PTree.set _data (.Vptr c.dB c.dO)
      (createUndefTemps f_tftp_receive_packet.fn_temps)),
    a1.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨a1.2, rfl, ?_, ?_⟩
    · exact TempsHold_cons (PTree.gss _ _ _)
        (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)) (TempsHold_nil _))
    · show (Cells (cellsK c v0) ∗ (regK c ∗ _)) _
      rw [← sep_assoc_eq]
      exact ⟨hp, hl, dph, rfl, hpre.2, hLP⟩

/-- **バックポートした 8.14.1 の `tftp_receive_packet` は、アップロード中に DATA を受け取ると、
    CURLE_TFTP_ILLEGAL を返す。** `Curl_client_write` については何も仮定しない。 -/
theorem recv_bp_illegal (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : CtxR)
    (v0 : ValsR) (n : Integers.Int64) (fl : Integers.Int) (X : ExtR ge c n fl)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hup : bitOf c.word 1 = true)
    (hn4 : Integers.Int.lt (rOf n) (Integers.Int.repr 4) = false) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_tftp_receive_packet)
      (rpSpec (fun r => r = .Vint (Integers.Int.repr 71)) c v0) vs :=
  recv_bp_general (fun r => r = .Vint (Integers.Int.repr 71)) rfl ge hcenv c v0 n fl X hpr hpw hup hn4 vs

/-- `Case3RecvAfter.recv_after_illegal` と同じ形（71 か 56）の事後条件で述べたもの。 -/
theorem recv_bp_illegal_form (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : CtxR)
    (v0 : ValsR) (n : Integers.Int64) (fl : Integers.Int) (X : ExtR ge c n fl)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hup : bitOf c.word 1 = true)
    (hn4 : Integers.Int.lt (rOf n) (Integers.Int.repr 4) = false) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_tftp_receive_packet)
      (rpSpec (fun r => r = .Vint (Integers.Int.repr 71) ∨ r = .Vint (Integers.Int.repr 56)) c v0) vs :=
  recv_bp_general _ (Or.inl rfl) ge hcenv c v0 n fl X hpr hpw hup hn4 vs

end Case3bpC

#print axioms Case3bpC.recv_bp_illegal
#print axioms Case3bpC.recv_bp_illegal_form
