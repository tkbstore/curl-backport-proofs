/-
Case 3（CURL-CVE-2026-92389）: 修正後の `tftp_receive_packet`（curl 63dd390fab）。

証明すること（`recv_after_illegal`）: アップロード中（`data->state.upload` が 1）に受け取ったパケットが
DATA（`getrpacketevent` が 3 を返し、長さが 4 以上）なら、戻り値は CURLE_TFTP_ILLEGAL（71）か、
送信元のアドレスが固定したものと違うときの CURLE_RECV_ERROR（56）のどちらかである。

`Curl_client_write` については何も仮定しない。仮定するのは、DATA の経路の手前で呼ばれる
`recvfrom`・`memcmp`・`memcpy`・`Curl_failf`・`getrpacketevent` の5つの仕様だけで、
どれも「この関数が所有するメモリの形を保つ」と述べる（中身を問わない領域には何を書いてもよい）。
`recvfrom` の戻り値 `n`・書き込む送信元アドレスの長さ `fl`、`memcmp` の戻り値 `rc` は任意。
-/
import Case3Cells
import Case3TxAfter
open CC CC.Sep CC.HProp
open Case3_after
open Case5C (addr bitOf boolVal_ofBool_tint eval_field eval_bitfield)
open Case4C (lv_field eval_deref_temp)
open Case1C (triple_pure call_some call_none seq_ex Sub sub_left disjoint_sub)

set_option maxRecDepth 20000

namespace Case3C

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
  pin : Integers.Int         -- state の block・remote_pinned を入れた単位
  alen : Integers.Int        -- state->remote_addrlen
  ev : Val                   -- state->event

abbrev cellsK (c : CtxR) (v : ValsR) : List CellD :=
  [ (.Mint32, c.pm, c.sB, addr c.sO 168, .Vint c.sock),                                    -- 0
    (Mptr, c.pm, c.sB, addr (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 128)) 0,
      .Vptr c.pkB c.pkO),                                                                   -- 1
    (.Mint32, c.pm, c.sB, addr c.sO 208, .Vint c.bs),                                      -- 2
    (.Mint32, c.pm, c.sB, addr c.sO 196, v.rb),                                            -- 3
    (.Mint32, c.pm, c.sB, addr c.sO 216, .Vint v.pin),                                     -- 4
    (.Mint32, c.pm, c.sB, addr c.sO 192, .Vint v.alen),                                    -- 5
    (.Mint32, c.pm, c.sB, addr c.sO 152, v.ev),                                            -- 6
    (.Mint32, c.pm, c.dB, updAddr c.dO, .Vint c.word) ]                                    -- 7

/-- 中身を問わない領域: state->remote_addr と受信バッファ。 -/
def regK (c : CtxR) : HProp :=
  anyBytes c.pm c.sB (addr c.sO 0) 128 ∗ anyBytes c.pm c.pkB (Integers.Ptrofs.unsigned c.pkO) c.pkN

/-- 呼ばれる前のメモリ（局所変数を除く）。 -/
abbrev HK (c : CtxR) (v : ValsR) : HProp := Cells (cellsK c v) ∗ regK c

/-- 関数の中のメモリ全体: `HK` と、局所変数 remote_addr（128 バイト）・fromlen。 -/
abbrev W (c : CtxR) (bra bfl : Block) (v : ValsR) (fl : Val) : HProp :=
  Cells (cellsK c v) ∗ (regK c ∗ (anyBytes .Freeable bra 0 128 ∗ (mapsto .Mint32 .Freeable bfl 0 fl ∗ emp)))

theorem W_fl (c : CtxR) (bra bfl : Block) (v : ValsR) (fl : Val) :
    W c bra bfl v fl = mapsto .Mint32 .Freeable bfl 0 fl ∗
      (Cells (cellsK c v) ∗ (regK c ∗ (anyBytes .Freeable bra 0 128 ∗ emp))) := by
  unfold W
  rw [sep_left_comm_eq (anyBytes .Freeable bra 0 128), sep_left_comm_eq (regK c),
    sep_left_comm_eq (Cells (cellsK c v))]

def envR (bra bfl : Block) : Env :=
  (emptyEnv.set _remote_addr (bra, Ty.Tstruct _Curl_sockaddr_storage noattr)).set _fromlen (bfl, tuint)

abbrev lR (c : CtxR) : List (Ident × Val) := [(_state, .Vptr c.sB c.sO), (_data, .Vptr c.dB c.dO)]

/-- `(int)` で切り詰めた `recvfrom` の戻り値。 -/
def rOf (n : Integers.Int64) : Integers.Int := Integers.Int.repr (Integers.Int64.unsigned n)

/-! ## 仕様 -/

def rpSpec (c : CtxR) (v0 : ValsR) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _tftp_conn noattr)]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dB c.dO, .Vptr c.sB c.sO] ∧ HK c v0 hp
  post := fun r hp => (r = .Vint (Integers.Int.repr 71) ∨ r = .Vint (Integers.Int.repr 56))
    ∧ ∃ v, HK c v hp
  measure := fun _ => 0

/-- 呼ばれる側の仕様の形: メモリの形 `K` を受け取り、`K'` にして返す。戻り値は `r`（`none` なら問わない）。 -/
def specK (tyargs : List Ty) (tyres : Ty) (cc : CallConv) (K K' : HProp) (r : Option Val) :
    FunSpec where
  tyargs := tyargs
  tyres := tyres
  cc := cc
  pre := fun _ hp => K hp
  post := fun v hp => (∀ x, r = some x → v = x) ∧ K' hp
  measure := fun _ => 0

def recvTy : List Ty :=
  [tint, tptr tvoid, tulong, tint, tptr (Ty.Tstruct _sockaddr noattr), tptr tuint]
def memcmpTy : List Ty := [tptr tvoid, tptr tvoid, tulong]
def failfTy : List Ty := [tptr (Ty.Tstruct _Curl_easy noattr), tptr tschar]
def failfCC : CallConv := { cc_vararg := some 2, cc_unproto := false, cc_structret := false }
def pktTy : List Ty := [tptr (Ty.Tstruct _tftp_packet noattr)]

/-- 呼ばれる側の関数の置き場所。 -/
structure Callee (ge : CGenv) (id : Ident) (tyargs : List Ty) (tyres : Ty) (cc : CallConv) where
  b : Block
  fd : FunDef
  sym : Genv.findSymbol ge.genv_genv id = some b
  fp : FuncPtr ge b fd
  ty : typeOfFundef fd = .Tfunction tyargs tyres cc

/-- 仮定する5つの仕様。`bra`・`bfl`（局所変数のブロック）と `v`・`f0`（その時点の値）は任意。 -/
structure ExtR (ge : CGenv) (c : CtxR) (n : Integers.Int64) (fl rc : Integers.Int) where
  recv : Callee ge _recvfrom recvTy tlong cc_default
  sRecv : ∀ bra bfl v f0 vs, SatisfiesAt ge (FunctionEntry2 ge) recv.fd
    (specK recvTy tlong cc_default (W c bra bfl v f0) (W c bra bfl v (.Vint fl)) (some (.Vlong n))) vs
  cmp : Callee ge _memcmp memcmpTy tint cc_default
  sCmp : ∀ bra bfl v f0 vs, SatisfiesAt ge (FunctionEntry2 ge) cmp.fd
    (specK memcmpTy tint cc_default (W c bra bfl v f0) (W c bra bfl v f0) (some (.Vint rc))) vs
  cpy : Callee ge _memcpy memcmpTy (tptr tvoid) cc_default
  sCpy : ∀ bra bfl v f0 vs, SatisfiesAt ge (FunctionEntry2 ge) cpy.fd
    (specK memcmpTy (tptr tvoid) cc_default (W c bra bfl v f0) (W c bra bfl v f0) none) vs
  fail : Callee ge _Curl_failf failfTy tvoid failfCC
  sFail : ∀ bra bfl v f0 vs, SatisfiesAt ge (FunctionEntry2 ge) fail.fd
    (specK failfTy tvoid failfCC (W c bra bfl v f0) (W c bra bfl v f0) none) vs
  lit19 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_19 = some b
  ev : Callee ge _getrpacketevent pktTy tushort cc_default
  sEv : ∀ bra bfl v f0 vs, SatisfiesAt ge (FunctionEntry2 ge) ev.fd
    (specK pktTy tushort cc_default (W c bra bfl v f0) (W c bra bfl v f0)
      (some (.Vint (Integers.Int.repr 3)))) vs

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
    (hload : Mem.load Mptr m c.sB (addr (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 128)) 0)
      = some (.Vptr c.pkB c.pkO)) :
    EvalExpr ge e le m
      (.Efield (.Efield (.Ederef (.Etempvar _state (tptr (Ty.Tstruct _tftp_conn noattr)))
          (Ty.Tstruct _tftp_conn noattr)) _rpacket (Ty.Tstruct _tftp_packet noattr)) _data
        (tptr tuchar))
      (.Vptr c.pkB c.pkO) :=
  EvalExpr.Elvalue _ c.sB _ .Full _
    (EvalLvalue.Efield_struct _ _data _ c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 128))
      _tftp_packet (coOf _tftp_packet) noattr 0 .Full
      (EvalExpr.Elvalue _ _ _ .Full _
        (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_conn) (hcenv ▸ off_conn.2.1))
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

theorem envR_ra (bra bfl : Block) :
    (envR bra bfl).get _remote_addr = some (bra, Ty.Tstruct _Curl_sockaddr_storage noattr) := rfl
theorem envR_fl (bra bfl : Block) : (envR bra bfl).get _fromlen = some (bfl, tuint) := rfl

/-- 局所変数 fromlen の読み出し。 -/
theorem eval_fromlen {ge : CGenv} {le : TempEnv} {m : Mem} {c : CtxR} {bra bfl : Block}
    {v : ValsR} {fl : Integers.Int} {hp : Heap}
    (hH : W c bra bfl v (.Vint fl) hp) (hag : Heap.Agrees hp m) :
    EvalExpr ge (envR bra bfl) le m (.Evar _fromlen tuint) (.Vint fl) := by
  rw [W_fl] at hH
  obtain ⟨h1, h2, _, rfl, hm, _⟩ := hH
  have hl := mapsto_load (rfl : permOrder .Freeable .Readable = true) hm (Heap.Agrees_union_left hag)
  refine EvalExpr.Elvalue _ bfl Integers.Ptrofs.zero .Full _
    (EvalLvalue.Evar_local _ _ _ (envR_fl bra bfl)) (DerefLoc.value .Mint32 _ rfl ?_)
  show Mem.load .Mint32 m bfl (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) = _
  rw [ptrofs_unsigned_zero]
  exact hl

theorem eval_laddr {ge : CGenv} {le : TempEnv} {m : Mem} {E : Env} {id : Ident} {b : Block}
    {ty : Ty} (hE : E.get id = some (b, ty)) (t : Ty) :
    EvalExpr ge E le m (.Eaddrof (.Evar id ty) t) (.Vptr b Integers.Ptrofs.zero) :=
  EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ hE)

/-! ## 値の計算 -/

theorem boolVal_int' (r : Integers.Int) (m : Mem) :
    Cop.boolVal (.Vint r) tint m = some (!Integers.Int.eq r Integers.Int.zero) := rfl

theorem cast_bool_uint (x : Integers.Int) (m : Mem) :
    Cop.semCast (.Vint x) tuint tbool m = some (Val.ofBool (!Integers.Int.eq x Integers.Int.zero)) := by
  cases h : Integers.Int.eq x Integers.Int.zero <;> simp [Cop.semCast, Cop.classifyCast, h] <;> rfl

theorem cmp_ge0 (ce : CompositeEnv) (r : Integers.Int) (m : Mem) :
    Cop.semBinaryOperation ce .Oge (.Vint r) tint (.Vint (Integers.Int.repr 0)) tint m
      = some (Val.ofBool (!Integers.Int.lt r (Integers.Int.repr 0))) := rfl

theorem cmp_lt4 (ce : CompositeEnv) (r : Integers.Int) (m : Mem) :
    Cop.semBinaryOperation ce .Olt (.Vint r) tint (.Vint (Integers.Int.repr 4)) tint m
      = some (Val.ofBool (Integers.Int.lt r (Integers.Int.repr 4))) := rfl

theorem cmp_ne_u (ce : CompositeEnv) (a b : Integers.Int) (m : Mem) :
    Cop.semBinaryOperation ce .One (.Vint a) tuint (.Vint b) tuint m
      = some (Val.ofBool (!Integers.Int.eq a b)) := rfl

theorem cast_bool_int (x : Integers.Int) (m : Mem) :
    Cop.semCast (.Vint x) tint tbool m = some (Val.ofBool (!Integers.Int.eq x Integers.Int.zero)) := by
  cases h : Integers.Int.eq x Integers.Int.zero <;> simp [Cop.semCast, Cop.classifyCast, h] <;> rfl

/-! ## フィールドのオフセット（`off_conn` から取り出したもの） -/

theorem off_rpacket : fieldOffset prog.prog_comp_env _rpacket (coOf _tftp_conn).co_members
    = .OK (128, .Full) := off_conn.2.1
theorem off_event : fieldOffset prog.prog_comp_env _event (coOf _tftp_conn).co_members
    = .OK (152, .Full) := off_conn.2.2.2.1
theorem off_sockfd : fieldOffset prog.prog_comp_env _sockfd (coOf _tftp_conn).co_members
    = .OK (168, .Full) := off_conn.2.2.2.2.1
theorem off_addrlen : fieldOffset prog.prog_comp_env _remote_addrlen (coOf _tftp_conn).co_members
    = .OK (192, .Full) := off_conn.2.2.2.2.2.2.1
theorem off_rbytes : fieldOffset prog.prog_comp_env _rbytes (coOf _tftp_conn).co_members
    = .OK (196, .Full) := off_conn.2.2.2.2.2.2.2.1
theorem off_blksize : fieldOffset prog.prog_comp_env _blksize (coOf _tftp_conn).co_members
    = .OK (208, .Full) := off_conn.2.2.2.2.2.2.2.2.2.1
theorem off_pinned : fieldOffset prog.prog_comp_env _remote_pinned (coOf _tftp_conn).co_members
    = .OK (216, .Bits .I32 .Unsigned 16 1) := off_conn.2.2.2.2.2.2.2.2.2.2.2

/-! ## 文の規則（この関数のメモリの形に合わせたもの） -/

/-- `fromlen = a2;`（局所変数への書き込み）。 -/
theorem assign_fromlen (ge fe f) (c : CtxR) (bra bfl : Block) (v : ValsR) (x : Val)
    (l : List (Ident × Val)) (a2 : Expr)
    (hrhs : ∀ le m, TempsHold l le →
      ∃ v2 vnew, EvalExpr ge (envR bra bfl) le m a2 v2 ∧ Cop.semCast v2 (typeof a2) tuint m = some vnew) :
    Triple ge fe f (LocalSt (envR bra bfl) l (W c bra bfl v x)) (.Sassign (.Evar _fromlen tuint) a2)
      (.only (fun e le hp => ∃ f0, LocalSt (envR bra bfl) l (W c bra bfl v f0) e le hp)) := by
  refine triple_assign ge fe f _ _ _ a2 .Mint32 .Freeable bfl Integers.Ptrofs.zero rfl rfl
    (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  obtain ⟨v2, vnew, hev, hcast⟩ := hrhs le m hT
  rw [W_fl] at hH
  obtain ⟨h1, h2, hd, rfl, hm, hR⟩ := hH
  refine ⟨x, vnew, h1, h2, hd, rfl, by rw [ptrofs_unsigned_zero]; exact hm,
    EvalLvalue.Evar_local _ _ _ (envR_fl bra bfl), ⟨v2, hev, hcast⟩, fun h1' hm' hd' => ?_⟩
  refine ⟨vnew, rfl, hT, ?_⟩
  rw [W_fl]
  rw [ptrofs_unsigned_zero] at hm'
  exact ⟨h1', h2, hd', rfl, hm', hR⟩

/-- 一時変数の並びを、後で使うものだけに減らす。 -/
theorem ls_weak {E : Env} {l l' : List (Ident × Val)} {H : HProp}
    (hsub : ∀ p ∈ l', p ∈ l) : ∀ e le hp, LocalSt E l H e le hp → LocalSt E l' H e le hp :=
  fun _ _ _ ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono hsub hT, hH⟩

/-- 局所変数を解放して `return n;`（n は定数）。戻ったあとのメモリは `HK c v`。 -/
theorem ret_W (ge : CGenv) (fe f) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : CtxR)
    (bra bfl : Block) (hne : bra ≠ bfl) (v : ValsR) (x : Val) (l : List (Ident × Val))
    (k : Integers.Int) (hk : k = Integers.Int.repr 71 ∨ k = Integers.Int.repr 56)
    (hret : f.fn_return = tint) (R : Sep.ExitConds) (hR : R.ret = fun r hp =>
      (r = .Vint (Integers.Int.repr 71) ∨ r = .Vint (Integers.Int.repr 56)) ∧ ∃ v, HK c v hp) :
    Triple ge fe f (LocalSt (envR bra bfl) l (W c bra bfl v x)) (.Sreturn (some (.Econst_int k tint)))
      R := by
  have hblk : blocksOfEnv ge.genv_cenv (envR bra bfl) = [(bra, 0, 128), (bfl, 0, 4)] := by
    rw [hcenv]; rfl
  refine triple_conseq ge fe f
    (ret_locs ge fe f (envR bra bfl) l (HK c v) [(bra, 128), (bfl, 4)] _ (.Vint k) (.Vint k)
      R.ret (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) (fun _ => by rw [hret]; rfl) ?_ ?_ ?_)
    (fun e le hp hP => ?_) (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
    (fun _ _ _ x => False.elim x) (fun _ _ x => x)
  · rw [hblk]
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨bra, 128, rfl, by simp⟩
    · exact ⟨bfl, 4, rfl, by simp⟩
  · rw [hblk]; simp [hne]
  · intro hp hH
    rw [hR]
    exact ⟨by rcases hk with rfl | rfl <;> simp, v, hH⟩
  · obtain ⟨he, hT, hH⟩ := hP
    refine ⟨he, hT, ?_⟩
    obtain ⟨h1, h2, hd, rfl, hC, hr⟩ := hH
    obtain ⟨h3, h4, hd', rfl, hrg, hl⟩ := hr
    obtain ⟨h5, h6, hd'', rfl, hra, hfl⟩ := hl
    obtain ⟨h7, h8, hd3, rfl, hm, he8⟩ := hfl
    rw [← Heap.union_assoc]
    refine ⟨_, _, Heap.disjoint_union_left.mpr ⟨?_, ?_⟩, rfl, ⟨h1, h3, ?_, rfl, hC, hrg⟩,
      ⟨h5, Heap.union h7 h8, hd'', rfl, hra, ⟨h7, h8, hd3, rfl, mapsto_anyBytes hm, he8⟩⟩⟩
    · exact Heap.disjoint_union_right.mp hd |>.2
    · exact hd'
    · exact Heap.disjoint_union_right.mp hd |>.1

/-! ## 本体 -/

theorem rp_body_after (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : CtxR)
    (v0 : ValsR) (n : Integers.Int64) (fl rc : Integers.Int) (X : ExtR ge c n fl rc)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hup : bitOf c.word 1 = true)
    (hn0 : Integers.Int.lt (rOf n) (Integers.Int.repr 0) = false)
    (hn4 : Integers.Int.lt (rOf n) (Integers.Int.repr 4) = false)
    (bra bfl : Block) (hne : bra ≠ bfl) :
    Triple ge (FunctionEntry2 ge) f_tftp_receive_packet
      (LocalSt (envR bra bfl) (lR c) (W c bra bfl v0 .Vundef)) f_tftp_receive_packet.fn_body
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := (rpSpec c v0).post } := by
  -- result = CURLE_OK;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envR bra bfl) _ (W c bra bfl v0 .Vundef) _result _
      (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  -- fromlen = sizeof(remote_addr);
  refine seq_ex ge _ _ _ _ _ _ _
    (assign_fromlen ge _ _ c bra bfl v0 .Vundef _ _
      (fun le m _ => ⟨_, _, EvalExpr.Esizeof _ _, rfl⟩)) (fun f0 => ?_)
  -- t'32 = state->sockfd; t'33 = state->rpacket.data; t'34 = state->blksize; t'1 = recvfrom(...);
  -- state->rbytes = (int)t'1;
  refine triple_seq_fwd ge _ _ _
    (LocalSt (envR bra bfl) _ (W c bra bfl ⟨.Vint (rOf n), v0.pin, v0.alen, v0.ev⟩ (.Vint fl))) _ _ _
    (seq_ex ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envR bra bfl) _ (W c bra bfl v0 f0) _t'32 _ (.Vint c.sock)
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
            (hcenv ▸ off_sockfd) rfl (cell_load3 (l := cellsK c _) (k := 0) (hk := by simp) rfl hpr hH hag)))
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ (envR bra bfl) _ (W c bra bfl v0 f0) _t'33 _
            (.Vptr c.pkB c.pkO)
            (fun le m hp hT hH hag => eval_rpdata hcenv (hT.get (by temps_get))
              (cell_load3 (l := cellsK c _) (k := 1) (hk := by simp) rfl hpr hH hag)))
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ (envR bra bfl) _ (W c bra bfl v0 f0) _t'34 _ (.Vint c.bs)
              (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
                (hcenv ▸ off_blksize) rfl (cell_load3 (l := cellsK c _) (k := 2) (hk := by simp) rfl hpr hH hag)))
            (call_some ge _ _ (specK recvTy tlong cc_default (W c bra bfl v0 f0)
                (W c bra bfl v0 (.Vint fl)) (some (.Vlong n))) _t'1 _ _ (envR bra bfl) _
              (W c bra bfl v0 f0) _ X.recv.b X.recv.fd (fun v => v = .Vlong n)
              (fun _ => W c bra bfl v0 (.Vint fl)) (X.sRecv bra bfl v0 f0) X.recv.fp X.recv.ty rfl
              (fun le m _ => eval_callee_global rfl X.recv.sym rfl)
              (fun le m hT =>
                .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl
                (.cons _ _ _ _ _ _ _ (EvalExpr.Ecast _ _ _ _
                    (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl) rfl
                (.cons _ _ _ _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
                    (EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl)
                    (EvalExpr.Econst_int _ _) rfl) rfl
                (.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl
                (.cons _ _ _ _ _ _ _ (EvalExpr.Ecast _ _ _ _ (eval_laddr (envR_ra bra bfl) _) rfl) rfl
                (.cons _ _ _ _ _ _ _ (eval_laddr (envR_fl bra bfl) _) rfl .nil))))))
              (fun h hH => hH) (fun v h hs => ⟨hs.1 _ rfl, hs.2⟩)))))
      (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => by
        subst hv
        exact assign_cell3 ge _ _ (envR bra bfl) _ (cellsK c v0) _ 3 (by simp) .Mint32 c.pm c.sB
          (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 196)) v0.rb (.Vint (rOf n)) rfl _ _ hpw rfl
          (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_conn)
            (hcenv ▸ off_rbytes))
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Ecast _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl, rfl⟩))))
    ?_
  -- if((state->rbytes >= 0) && fromlen) { 送信元のアドレスを確かめるか固定する }
  refine triple_seq ge _ _ _
    (fun e le hp => ∃ pa : Integers.Int × Integers.Int,
      LocalSt (envR bra bfl) (lR c) (W c bra bfl ⟨.Vint (rOf n), pa.1, pa.2, v0.ev⟩ (.Vint fl)) e le hp)
    _ _ _ ?pin ?tail
  case pin =>
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'30 _ (.Vint (rOf n))
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
            (hcenv ▸ off_rbytes) rfl (cell_load3 (l := cellsK c _) (k := 3) (hk := by simp) rfl hpr hH hag)))
        (triple_if_local ge _ _ (envR bra bfl) _ _ _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _)
            (cmp_ge0 _ _ _), (boolVal_ofBool_tint _ m).trans (by rw [hn0]; rfl)⟩)
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'31 _ (.Vint fl)
              (fun le m hp hT hH hag => eval_fromlen hH hag))
            (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'4 _
              (Val.ofBool (!Integers.Int.eq fl Integers.Int.zero))
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (cast_bool_uint _ _))))))
      ?_
    refine triple_if_local ge _ _ (envR bra bfl) _ _ _ (!Integers.Int.eq fl Integers.Int.zero) _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
        boolVal_ofBool_tint _ m⟩) ?_
    cases hfl : Integers.Int.eq fl Integers.Int.zero
    case true =>
      -- fromlen が 0: 何もしない
      exact Sep.triple_fallthrough ge _ _ _ _ _ _ (triple_skip ge _ _ _)
        (fun e le hp h => ⟨(v0.pin, v0.alen),
          ls_weak (fun p hp' => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
            rcases hp' with rfl | rfl <;> temps_get) e le hp h⟩)
    case false =>
    rw [if_pos (by decide : (!false) = true)]
    obtain ⟨b19, hb19⟩ := X.lit19
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'24 _
        (.Vint (Cop.bitfieldExtract .I32 .Unsigned 16 1 v0.pin))
        (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_conn)
          (hcenv ▸ off_pinned) (by decide) (by decide)
          (cell_load3 (l := cellsK c ⟨.Vint (rOf n), v0.pin, v0.alen, v0.ev⟩) (k := 4) (hk := by simp) rfl hpr hH hag))) ?_
    refine triple_if_local ge _ _ (envR bra bfl) _ _ _ (bitOf v0.pin 16) _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_int' _ m⟩) ?_
    have hw : ∀ (l : List (Ident × Val)), (_state, Val.Vptr c.sB c.sO) ∈ l → (_data, Val.Vptr c.dB c.dO) ∈ l →
        ∀ p ∈ lR c, p ∈ l := by
      intro l h1 h2 p hp'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
      rcases hp' with rfl | rfl
      · exact h1
      · exact h2
    -- `if(failed) { failf(...); return CURLE_RECV_ERROR; }` を、failed が真の場合に示す
    have hfail : ∀ (v : ValsR) (l : List (Ident × Val)) (R : Sep.ExitConds),
        (_data, Val.Vptr c.dB c.dO) ∈ l →
        R.ret = (rpSpec c v0).post →
        Triple ge (FunctionEntry2 ge) f_tftp_receive_packet
          (LocalSt (envR bra bfl) l (W c bra bfl v (.Vint fl)))
          (.Ssequence
            (.Scall none
              (.Evar _Curl_failf (Ty.Tfunction [tptr (Ty.Tstruct _Curl_easy noattr), tptr tschar] tvoid
                { cc_vararg := some 2, cc_unproto := false, cc_structret := false }))
              [.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)),
               .Evar ___stringlit_19 (tarray tschar 35)])
            (.Sreturn (some (.Econst_int (Integers.Int.repr 56) tint)))) R := by
      intro v l R hd hR
      exact seq_ex ge _ _ _ _ _ _ _
        (call_none ge _ _ (specK failfTy tvoid failfCC (W c bra bfl v (.Vint fl))
            (W c bra bfl v (.Vint fl)) none) _ _ (envR bra bfl) _ _ _ X.fail.b X.fail.fd
          (fun _ => True) (fun _ => W c bra bfl v (.Vint fl)) (X.sFail bra bfl v _) X.fail.fp X.fail.ty rfl
          (fun le m _ => eval_callee_global rfl X.fail.sym rfl)
          (fun le m hT => .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get hd)) rfl
            (.cons _ _ _ _ _ _ _ (eval_callee_global rfl hb19 rfl) rfl .nil))
          (fun h hH => hH) (fun v h hs => ⟨trivial, hs.2⟩))
        (fun _ => triple_pure ge _ _ _ _ _ _ (fun _ =>
          ret_W ge _ _ hcenv c bra bfl hne v _ l _ (Or.inr rfl) rfl R hR))
    cases hpin : bitOf v0.pin 16
    case true =>
      -- 固定済み: 長さかアドレスが違えば CURLE_RECV_ERROR
      rw [if_pos rfl]
      cases hal : Integers.Int.eq v0.alen fl
      case false =>
        refine triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'27 _ (.Vint v0.alen)
              (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
                (hcenv ▸ off_addrlen) rfl (cell_load3 (l := cellsK c ⟨.Vint (rOf n), v0.pin, v0.alen, v0.ev⟩) (k := 5) (hk := by simp) rfl hpr hH hag)))
            (triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'28 _ (.Vint fl)
                (fun le m hp hT hH hag => eval_fromlen hH hag))
              (triple_if_local ge _ _ (envR bra bfl) _ _ _ true _ _ _
                (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
                  (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                  (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (cmp_ne_u _ _ _ _),
                  (boolVal_ofBool_tint _ m).trans (by rw [hal]; rfl)⟩)
                (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'2 _ (.Vint (Integers.Int.repr 1))
                  (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))))) ?_
        refine triple_if_local ge _ _ (envR bra bfl) _ _ _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
        rw [if_pos rfl]
        exact hfail _ _ _ (by temps_get) rfl
      case true =>
        refine triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'27 _ (.Vint v0.alen)
              (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
                (hcenv ▸ off_addrlen) rfl (cell_load3 (l := cellsK c ⟨.Vint (rOf n), v0.pin, v0.alen, v0.ev⟩) (k := 5) (hk := by simp) rfl hpr hH hag)))
            (triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'28 _ (.Vint fl)
                (fun le m hp hT hH hag => eval_fromlen hH hag))
              (triple_if_local ge _ _ (envR bra bfl) _ _ _ false _ _ _
                (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
                  (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                  (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (cmp_ne_u _ _ _ _),
                  (boolVal_ofBool_tint _ m).trans (by rw [hal]; rfl)⟩)
                (seq_ex ge _ _ _ _ _ _ _
                  (triple_seq_fwd ge _ _ _ _ _ _ _
                    (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'29 _ (.Vint fl)
                      (fun le m hp hT hH hag => eval_fromlen hH hag))
                    (call_some ge _ _ (specK memcmpTy tint cc_default
                        (W c bra bfl ⟨.Vint (rOf n), v0.pin, v0.alen, v0.ev⟩ (.Vint fl))
                        (W c bra bfl ⟨.Vint (rOf n), v0.pin, v0.alen, v0.ev⟩ (.Vint fl)) (some (.Vint rc)))
                      _t'3 _ _ (envR bra bfl) _ _ _ X.cmp.b X.cmp.fd (fun v => v = .Vint rc)
                      (fun _ => W c bra bfl ⟨.Vint (rOf n), v0.pin, v0.alen, v0.ev⟩ (.Vint fl))
                      (X.sCmp bra bfl _ _) X.cmp.fp X.cmp.ty rfl
                      (fun le m _ => eval_callee_global rfl X.cmp.sym rfl)
                      (fun le m hT => .cons _ _ _ _ _ _ _ (eval_laddr (envR_ra bra bfl) _) rfl
                        (.cons _ _ _ _ _ _ _ (eval_saddr (c := c) hcenv (hT.get (by temps_get)) off_conn.1) rfl
                        (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl .nil)))
                      (fun h hH => hH) (fun v h hs => ⟨hs.1 _ rfl, hs.2⟩)))
                  (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => by
                    subst hv
                    exact triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'2 _
                      (Val.ofBool (!Integers.Int.eq rc Integers.Int.zero))
                      (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (cast_bool_int _ _)))))))) ?_
        refine triple_if_local ge _ _ (envR bra bfl) _ _ _ (!Integers.Int.eq rc Integers.Int.zero) _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
            boolVal_ofBool_tint _ m⟩) ?_
        cases hrc : Integers.Int.eq rc Integers.Int.zero
        case false =>
          rw [if_pos (by decide : (!false) = true)]
          exact hfail _ _ _ (by temps_get) rfl
        case true =>
          exact Sep.triple_fallthrough ge _ _ _ _ _ _ (triple_skip ge _ _ _)
            (fun e le hp h => ⟨(v0.pin, v0.alen),
              ls_weak (hw _ (by temps_get) (by temps_get)) e le hp h⟩)
    case false =>
      -- 未固定: 固定する
      rw [if_neg Bool.false_ne_true]
      refine triple_seq_fwd ge _ _ _
        (LocalSt (envR bra bfl) _ (W c bra bfl ⟨.Vint (rOf n),
          Integers.Int.bitfield_insert (Cop.firstBit .I32 16 1).toNat 1 v0.pin (Integers.Int.repr 1),
          v0.alen, v0.ev⟩ (.Vint fl))) _ _ _
        (assign_bit3 ge _ _ (envR bra bfl) _ (cellsK c ⟨.Vint (rOf n), v0.pin, v0.alen, v0.ev⟩) _ 4
          (by simp) c.pm c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 216)) 16 v0.pin
          (Integers.Int.repr 1) rfl _ _ hpw hpr rfl (by decide) (by decide)
          (fun le m hT => EvalLvalue.Efield_struct _ _ _ c.sB c.sO _tftp_conn (coOf _tftp_conn) noattr
            216 _ (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_conn) (hcenv ▸ off_pinned))
          (fun le m hT => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
      refine triple_seq_fwd ge _ _ _
        (LocalSt (envR bra bfl) _ (W c bra bfl ⟨.Vint (rOf n),
          Integers.Int.bitfield_insert (Cop.firstBit .I32 16 1).toNat 1 v0.pin (Integers.Int.repr 1),
          fl, v0.ev⟩ (.Vint fl))) _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'26 _ (.Vint fl)
            (fun le m hp hT hH hag => eval_fromlen hH hag))
          (assign_cell3 ge _ _ (envR bra bfl) _ (cellsK c ⟨.Vint (rOf n),
              Integers.Int.bitfield_insert (Cop.firstBit .I32 16 1).toNat 1 v0.pin (Integers.Int.repr 1),
              v0.alen, v0.ev⟩) _ 5 (by simp) .Mint32 c.pm c.sB
            (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 192)) (.Vint v0.alen) (.Vint fl) rfl _ _ hpw rfl
            (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_conn)
              (hcenv ▸ off_addrlen))
            (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩))) ?_
      exact Sep.triple_fallthrough ge _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'25 _ (.Vint fl)
            (fun le m hp hT hH hag => eval_fromlen hH hag))
          (call_none ge _ _ (specK memcmpTy (tptr tvoid) cc_default
              (W c bra bfl ⟨.Vint (rOf n),
                Integers.Int.bitfield_insert (Cop.firstBit .I32 16 1).toNat 1 v0.pin (Integers.Int.repr 1),
                fl, v0.ev⟩ (.Vint fl))
              (W c bra bfl ⟨.Vint (rOf n),
                Integers.Int.bitfield_insert (Cop.firstBit .I32 16 1).toNat 1 v0.pin (Integers.Int.repr 1),
                fl, v0.ev⟩ (.Vint fl)) none)
            _ _ (envR bra bfl) _ _ _ X.cpy.b X.cpy.fd (fun _ => True)
            (fun _ => W c bra bfl ⟨.Vint (rOf n),
                Integers.Int.bitfield_insert (Cop.firstBit .I32 16 1).toNat 1 v0.pin (Integers.Int.repr 1),
                fl, v0.ev⟩ (.Vint fl))
            (X.sCpy bra bfl _ _) X.cpy.fp X.cpy.ty rfl
            (fun le m _ => eval_callee_global rfl X.cpy.sym rfl)
            (fun le m hT => .cons _ _ _ _ _ _ _ (eval_saddr (c := c) hcenv (hT.get (by temps_get)) off_conn.1) rfl
              (.cons _ _ _ _ _ _ _ (eval_laddr (envR_ra bra bfl) _) rfl
              (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl .nil)))
            (fun h hH => hH) (fun v h hs => ⟨trivial, hs.2⟩)))
        (fun e le hp ⟨_, _, h⟩ => ⟨(_, fl), ls_weak (hw _ (by temps_get) (by temps_get)) e le hp h⟩)
  case tail =>
    refine Sep.triple_exists ge _ _ _ _ _ (fun pa => ?_)
    obtain ⟨p1, p2⟩ := pa
    refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'13 _ (.Vint (rOf n))
        (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
          (hcenv ▸ off_rbytes) rfl (cell_load3 (l := cellsK c _) (k := 3) (hk := by simp) rfl hpr hH hag)))
      ?_
    refine triple_if_local ge _ _ (envR bra bfl) _ _ _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _)
        (cmp_lt4 _ _ _), (boolVal_ofBool_tint _ m).trans (by rw [hn4])⟩) ?_
    rw [if_neg Bool.false_ne_true]
    -- t'5 = getrpacketevent(&state->rpacket); event = (unsigned short)t'5;
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (seq_ex ge _ _ _ _ _ _ _
        (call_some ge _ _ (specK pktTy tushort cc_default
            (W c bra bfl ⟨.Vint (rOf n), p1, p2, v0.ev⟩ (.Vint fl))
            (W c bra bfl ⟨.Vint (rOf n), p1, p2, v0.ev⟩ (.Vint fl)) (some (.Vint (Integers.Int.repr 3))))
          _t'5 _ _ (envR bra bfl) _ _ _ X.ev.b X.ev.fd (fun v => v = .Vint (Integers.Int.repr 3))
          (fun _ => W c bra bfl ⟨.Vint (rOf n), p1, p2, v0.ev⟩ (.Vint fl)) (X.sEv bra bfl _ _)
          X.ev.fp X.ev.ty rfl
          (fun le m _ => eval_callee_global rfl X.ev.sym rfl)
          (fun le m hT => .cons _ _ _ _ _ _ _ (eval_saddr (c := c) hcenv (hT.get (by temps_get)) off_rpacket) rfl .nil)
          (fun h hH => hH) (fun v h hs => ⟨hs.1 _ rfl, hs.2⟩))
        (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => by
          subst hv
          exact triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _event _ (.Vint (Integers.Int.repr 3))
            (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
              (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl))))
      ?_
    -- state->event = (int)event;
    refine triple_seq_fwd ge _ _ _
      (LocalSt (envR bra bfl) _
        (W c bra bfl ⟨.Vint (rOf n), p1, p2, .Vint (Integers.Int.repr 3)⟩ (.Vint fl))) _ _ _
      (assign_cell3 ge _ _ (envR bra bfl) _ (cellsK c ⟨.Vint (rOf n), p1, p2, v0.ev⟩) _ 6 (by simp)
        .Mint32 c.pm c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 152)) v0.ev
        (.Vint (Integers.Int.repr 3)) rfl _ _ hpw rfl
        (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_conn)
          (hcenv ▸ off_event))
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Ecast _ _ _ _
          (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl, rfl⟩)) ?_
    -- switch(state->event) { case TFTP_EVENT_DATA: if(data->state.upload) return CURLE_TFTP_ILLEGAL; ...
    refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'14 _ (.Vint (Integers.Int.repr 3))
        (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn)
          (hcenv ▸ off_event) rfl (cell_load3 (l := cellsK c _) (k := 6) (hk := by simp) rfl hpr hH hag)))
      ?_
    refine Sep.triple_switch_const ge _ _ _ _ _ _ 3 ?_
      (fun e le hp m hP _ => ⟨_, EvalExpr.Etempvar _ _ _ (hP.2.1.get (by temps_get)), rfl⟩)
    refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
    refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envR bra bfl) _ _ _t'23 _
        (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 c.word))
        (fun le m hp hT hH hag => eval_upload2 hcenv (hT.get (by temps_get))
          (cell_load3 (l := cellsK c _) (k := 7) (hk := by simp) rfl hpr hH hag)))
      ?_
    refine triple_if_local ge _ _ (envR bra bfl) _ _ _ true _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
        (boolVal_int' _ m).trans (by
          rw [show (!Integers.Int.eq (Cop.bitfieldExtract .I32 .Unsigned 1 1 c.word) Integers.Int.zero)
            = bitOf c.word 1 from rfl, hup])⟩) ?_
    rw [if_pos rfl]
    exact ret_W ge _ _ hcenv c bra bfl hne _ _ _ _ (Or.inl rfl) rfl _ rfl

/-! ## 関数全体（入口で局所変数を確保するところから） -/

theorem rp_entry_wf :
    listNorepet (varNames f_tftp_receive_packet.fn_vars)
    ∧ listNorepet (varNames f_tftp_receive_packet.fn_params)
    ∧ listDisjoint (varNames f_tftp_receive_packet.fn_params)
        (varNames f_tftp_receive_packet.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

def PbodyR (c : CtxR) (v0 : ValsR) : Sep.Assn := fun e le hp =>
  ∃ bs : Block × Block, bs.1 ≠ bs.2 ∧
    LocalSt (envR bs.1 bs.2) (lR c) (W c bs.1 bs.2 v0 .Vundef) e le hp

/-- **修正後の `tftp_receive_packet` は、アップロード中に DATA を受け取ると、
    CURLE_TFTP_ILLEGAL（または送信元が違うときの CURLE_RECV_ERROR）を返す。**
    `Curl_client_write` については何も仮定しない。 -/
theorem recv_after_illegal (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : CtxR)
    (v0 : ValsR) (n : Integers.Int64) (fl rc : Integers.Int) (X : ExtR ge c n fl rc)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hup : bitOf c.word 1 = true)
    (hn0 : Integers.Int.lt (rOf n) (Integers.Int.repr 0) = false)
    (hn4 : Integers.Int.lt (rOf n) (Integers.Int.repr 4) = false) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_tftp_receive_packet) (rpSpec c v0) vs := by
  by_cases hvs : vs = [.Vptr c.dB c.dO, .Vptr c.sB c.sO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := rp_entry_wf
  refine satisfies_internal ge (FunctionEntry2 ge) f_tftp_receive_packet _ _ (PbodyR c v0)
    (fun m hp hf hpre hd hag => ?_)
    (Sep.triple_exists ge _ _ _ _ _ (fun bs => triple_pure ge _ _ _ _ _ _ (fun hne =>
      rp_body_after ge hcenv c v0 n fl rc X hpr hpw hup hn0 hn4 bs.1 bs.2 hne)))
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (Ty.Tstruct _Curl_sockaddr_storage noattr))
  let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv tuint)
  have hav : AllocVariables ge.genv_cenv emptyEnv m f_tftp_receive_packet.fn_vars
      (envR a1.2 a2.2) a2.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _))
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [f_tftp_receive_packet, List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl <;> rw [hcenv] <;> decide)
    (Heap.union hp hf) hag
  have hLP : (anyBytes .Freeable a1.2 0 128 ∗ (mapsto .Mint32 .Freeable a2.2 0 .Vundef ∗ emp)) hl := by
    obtain ⟨h1, h2, hd12, rfl, ⟨b, hb⟩, hr⟩ := hloc
    obtain ⟨hget, hu⟩ := pure_sep_elim hb
    obtain ⟨h3, h4, hd34, rfl, ⟨b', hb'⟩, he⟩ := hr
    obtain ⟨hget', hu'⟩ := pure_sep_elim hb'
    rw [envR_ra] at hget
    rw [envR_fl] at hget'
    cases hget
    cases hget'
    rw [hcenv] at hu hu'
    have hm : mapsto .Mint32 .Freeable a2.2 0 .Vundef h3 := by
      rw [← undefBytes_mapsto .Freeable a2.2 0 undefEncoded_Mint32 (by decide)]
      exact hu'
    exact ⟨h1, Heap.union h3 h4, hd12, rfl, undefBytes_anyBytes hu, ⟨h3, h4, hd34, rfl, hm, he⟩⟩
  have hne : a1.2 ≠ a2.2 := by
    obtain ⟨h1, h2, hd12, rfl, ha, hr⟩ := hLP
    obtain ⟨h3, h4, hd34, rfl, hm, _⟩ := hr
    exact anyBytes_ne ha (mapsto_anyBytes hm)
      (Heap.disjoint_comm (disjoint_sub (sub_left h3 h4) (Heap.disjoint_comm hd12))) (by decide) (by decide)
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envR a1.2 a2.2,
    PTree.set _state (.Vptr c.sB c.sO) (PTree.set _data (.Vptr c.dB c.dO)
      (createUndefTemps f_tftp_receive_packet.fn_temps)),
    a2.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨(a1.2, a2.2), hne, rfl, ?_, ?_⟩
    · exact TempsHold_cons (PTree.gss _ _ _)
        (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)) (TempsHold_nil _))
    · show (Cells (cellsK c v0) ∗ (regK c ∗ _)) _
      rw [← sep_assoc_eq]
      exact ⟨hp, hl, dph, rfl, hpre.2, hLP⟩

end Case3C

#print axioms Case3C.recv_after_illegal
