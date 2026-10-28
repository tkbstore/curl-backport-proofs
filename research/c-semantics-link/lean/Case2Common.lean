/-
Case 2（CURL-CVE-2026-86413）: 共通に使う部分。

構造体のレイアウト（生成された composite 環境から取り出す）、ビットフィールドへの書き込みの規則、
`url_match_auth_nego` が読み書きするメモリ（`Ctx2`・`H2`）、外部関数の仕様。
-/
import GenCase2After
import H5Case2
import Case4Common
import Case5After
open CC CC.Sep CC.HProp
open Case2_after
open Case5C (addr call_fwd RR return_const skip_end skip_fall boolVal_ofBool_tint boolVal_ofBool_tbool
  notbool_ofBool eval_bitfield bitOf sep_l sep_r)
open Case4C (IsPtr loadResult_ptr cast_ptr eval_deref_temp lv_field mapsto_weakValid)

set_option maxRecDepth 20000

namespace Case2C

/-! ## 構造体のレイアウト -/

def coOf (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_conn : prog.prog_comp_env.get _connectdata = some (coOf _connectdata) := rfl
theorem co_match : prog.prog_comp_env.get _url_conn_match = some (coOf _url_conn_match) := rfl
theorem co_easy : prog.prog_comp_env.get _Curl_easy = some (coOf _Curl_easy) := rfl
theorem co_state : prog.prog_comp_env.get _UrlState = some (coOf _UrlState) := rfl

theorem off_creds :
    fieldOffset prog.prog_comp_env _creds (coOf _connectdata).co_members = .OK (0, .Full) := by
  decide
theorem off_creds_origin :
    fieldOffset prog.prog_comp_env _creds_origin (coOf _connectdata).co_members
      = .OK (8, .Full) := by decide
theorem off_nego :
    fieldOffset prog.prog_comp_env _http_negotiate_state (coOf _connectdata).co_members
      = .OK (32, .Full) := by decide
theorem off_found :
    fieldOffset prog.prog_comp_env _found (coOf _url_conn_match).co_members = .OK (0, .Full) := by
  decide
theorem off_data :
    fieldOffset prog.prog_comp_env _data (coOf _url_conn_match).co_members = .OK (8, .Full) := by
  decide
theorem off_want :
    fieldOffset prog.prog_comp_env _want_nego_http (coOf _url_conn_match).co_members
      = .OK (40, .Bits .I32 .Unsigned 1 1) := by decide
theorem off_proxy :
    fieldOffset prog.prog_comp_env _want_proxy_nego_http (coOf _url_conn_match).co_members
      = .OK (40, .Bits .I32 .Unsigned 2 1) := by decide
theorem off_force :
    fieldOffset prog.prog_comp_env _force_reuse (coOf _url_conn_match).co_members
      = .OK (40, .Bits .I32 .Unsigned 6 1) := by decide
theorem off_state :
    fieldOffset prog.prog_comp_env _state (coOf _Curl_easy).co_members = .OK (8, .Full) := by
  decide
theorem off_origin :
    fieldOffset prog.prog_comp_env _origin (coOf _UrlState).co_members = .OK (0, .Full) := by
  decide
theorem off_screds :
    fieldOffset prog.prog_comp_env _creds (coOf _UrlState).co_members = .OK (16, .Full) := by
  decide

/-! ## ビットフィールドへの書き込み（`triple_assign` はビットフィールドを扱わない） -/

theorem triple_assign_bitfield (ge fe f) (P Q : Sep.Assn) (a1 a2 : Expr) (p : Permission)
    (b : Block) (ofs : Integers.Ptrofs) (pos : Z)
    (hpw : permOrder p .Writable = true) (hpr : permOrder p .Readable = true)
    (hty : typeof a1 = tint) (hpos0 : 0 ≤ pos) (hpos : pos + 1 ≤ 32)
    (hsplit : ∀ e le hp m, P e le hp → Heap.Agrees hp m →
        ∃ c n h1 h2,
          Heap.disjoint h1 h2 ∧ hp = Heap.union h1 h2
          ∧ mapsto .Mint32 p b (Integers.Ptrofs.unsigned ofs) (.Vint c) h1
          ∧ EvalLvalue ge e le m a1 b ofs (.Bits .I32 .Unsigned pos 1)
          ∧ (∃ v2, EvalExpr ge e le m a2 v2
                   ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some (.Vint n))
          ∧ (∀ h1', mapsto .Mint32 p b (Integers.Ptrofs.unsigned ofs)
                      (.Vint (Integers.Int.bitfield_insert (Cop.firstBit .I32 pos 1).toNat 1 c n))
                      h1' →
                Heap.disjoint h1' h2 → Q e le (Heap.union h1' h2))) :
    Triple ge fe f P (.Sassign a1 a2) (.only Q) := by
  intro k e le hp hf m hd hag hP
  obtain ⟨c, n, h1, h2, hd12, heq, hm1, hlv, ⟨v2, hev2, hcast⟩, hQ⟩ :=
    hsplit e le hp m hP (Heap.Agrees_union_left hag)
  subst heq
  rw [Heap.disjoint_union_left] at hd
  have hd1 : Heap.disjoint h1 (Heap.union h2 hf) := by
    rw [Heap.disjoint_union_right]; exact ⟨hd12, hd.1⟩
  have hag1 : Heap.Agrees (Heap.union h1 (Heap.union h2 hf)) m := by
    rw [← Heap.union_assoc]; exact hag
  have hload : Mem.load .Mint32 m b (Integers.Ptrofs.unsigned ofs) = some (.Vint c) :=
    mapsto_load hpr hm1 (Heap.Agrees_union_left hag1)
  obtain ⟨m', h1', hstore, hm1', hd1', hag1'⟩ :=
    mapsto_store (v' := .Vint (Integers.Int.bitfield_insert (Cop.firstBit .I32 pos 1).toNat 1 c n))
      hpw hm1 hd1 hag1
  rw [Heap.disjoint_union_right] at hd1'
  refine ⟨.Normal e le m', Heap.union h1' h2, ?_, ?_, ?_, ?_⟩
  · refine Steps.one (Step.assign f a1 a2 k e le m b ofs _ v2 (.Vint n) m' hlv hev2 hcast ?_)
    rw [hty]
    exact AssignLoc.bitfield .I32 .Unsigned pos 1 (.Vint n) m' _
      (Cop.StoreBitfield.intro .I32 .Signed noattr .Unsigned pos 1 m _ c n m' hpos0 (by decide)
        (by decide) hpos (by decide) hload hstore)
  · rw [Heap.disjoint_union_left]; exact ⟨hd1'.2, hd.2⟩
  · show Heap.Agrees (Heap.union (Heap.union h1' h2) hf) m'
    rw [Heap.union_assoc]; exact hag1'
  · exact hQ h1' hm1' hd1'.1

/-! ## `url_match_auth_nego` が読み書きするメモリ -/

structure Ctx2 where
  connB : Block
  connO : Integers.Ptrofs
  mB : Block
  mO : Integers.Ptrofs
  dataB : Block
  dataO : Integers.Ptrofs
  credsV : Val              -- conn->creds（NULL か、credB・credO を指す）
  credB : Block
  credO : Integers.Ptrofs
  corigV : Val              -- conn->creds_origin
  ns : Integers.Int         -- conn->http_negotiate_state
  originV : Val             -- data->state.origin
  scredsV : Val             -- data->state.creds
  pm : Permission

/-- `data->state.<fld>` の番地（`Efield` を2段たどるのと同じ式）。 -/
def addr2 (o : Integers.Ptrofs) (d1 d2 : Z) : Z :=
  Integers.Ptrofs.unsigned
    (Integers.Ptrofs.add (Integers.Ptrofs.add o (Integers.Ptrofs.repr d1)) (Integers.Ptrofs.repr d2))

/-- 書き込む2つのセル（`m->found`・ビットの単位）と、読むだけのセル。 -/
def H2 (c : Ctx2) (foundV : Val) (word : Integers.Int) : HProp :=
  mapsto Mptr c.pm c.mB (addr c.mO 0) foundV ∗
  (mapsto .Mint32 c.pm c.mB (addr c.mO 40) (.Vint word) ∗
  (mapsto Mptr c.pm c.mB (addr c.mO 8) (.Vptr c.dataB c.dataO) ∗
  (mapsto Mptr c.pm c.connB (addr c.connO 0) c.credsV ∗
  (mapsto Mptr c.pm c.connB (addr c.connO 8) c.corigV ∗
  (mapsto .Mint32 c.pm c.connB (addr c.connO 32) (.Vint c.ns) ∗
  (mapsto Mptr c.pm c.dataB (addr2 c.dataO 8 0) c.originV ∗
  (mapsto Mptr c.pm c.dataB (addr2 c.dataO 8 16) c.scredsV ∗
   mapsto .Mint8unsigned c.pm c.credB (Integers.Ptrofs.unsigned c.credO) (.Vint (Integers.Int.repr 0)))))))))

structure Ptrs2 (c : Ctx2) : Prop where
  creds : c.credsV = .Vlong Integers.Int64.zero ∨ c.credsV = .Vptr c.credB c.credO
  corig : IsPtr c.corigV
  origin : IsPtr c.originV
  screds : IsPtr c.scredsV

theorem creds_isPtr {c : Ctx2} (h : Ptrs2 c) : IsPtr c.credsV := by
  rcases h.creds with h | h <;> rw [h]
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩

structure Loads2 (c : Ctx2) (foundV : Val) (word : Integers.Int) (m : Mem) : Prop where
  word : Mem.load .Mint32 m c.mB (addr c.mO 40) = some (.Vint word)
  data : Mem.load Mptr m c.mB (addr c.mO 8) = some (.Vptr c.dataB c.dataO)
  creds : Mem.load Mptr m c.connB (addr c.connO 0) = some c.credsV
  corig : Mem.load Mptr m c.connB (addr c.connO 8) = some c.corigV
  ns : Mem.load .Mint32 m c.connB (addr c.connO 32) = some (.Vint c.ns)
  origin : Mem.load Mptr m c.dataB (addr2 c.dataO 8 0) = some c.originV
  screds : Mem.load Mptr m c.dataB (addr2 c.dataO 8 16) = some c.scredsV
  valid : Mem.weakValidPointer m c.credB (Integers.Ptrofs.unsigned c.credO) = true

theorem H2_loads {c : Ctx2} {foundV : Val} {word : Integers.Int} {hp : Heap} {m : Mem}
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hptr : Ptrs2 c) (hH : H2 c foundV word hp) (hag : Heap.Agrees hp m) :
    Loads2 c foundV word m := by
  obtain ⟨r1, d1, b1⟩ := sep_r hH hag
  obtain ⟨h2, c2, a2⟩ := sep_l d1 b1
  obtain ⟨r2, d2, b2⟩ := sep_r d1 b1
  obtain ⟨h3, c3, a3⟩ := sep_l d2 b2
  obtain ⟨r3, d3, b3⟩ := sep_r d2 b2
  obtain ⟨h4, c4, a4⟩ := sep_l d3 b3
  obtain ⟨r4, d4, b4⟩ := sep_r d3 b3
  obtain ⟨h5, c5, a5⟩ := sep_l d4 b4
  obtain ⟨r5, d5, b5⟩ := sep_r d4 b4
  obtain ⟨h6, c6, a6⟩ := sep_l d5 b5
  obtain ⟨r6, d6, b6⟩ := sep_r d5 b5
  obtain ⟨h7, c7, a7⟩ := sep_l d6 b6
  obtain ⟨r7, d7, b7⟩ := sep_r d6 b6
  obtain ⟨h8, c8, a8⟩ := sep_l d7 b7
  obtain ⟨h9, c9, a9⟩ := sep_r d7 b7
  refine ⟨mapsto_load hpr c2 a2, mapsto_load hpr c3 a3, ?_, ?_, mapsto_load hpr c6 a6, ?_, ?_,
    mapsto_weakValid hpn c9 a9 (by decide)⟩
  · rw [mapsto_load hpr c4 a4, loadResult_ptr (creds_isPtr hptr)]
  · rw [mapsto_load hpr c5 a5, loadResult_ptr hptr.corig]
  · rw [mapsto_load hpr c7 a7, loadResult_ptr hptr.origin]
  · rw [mapsto_load hpr c8 a8, loadResult_ptr hptr.screds]

/-! ## 式の評価 -/

/-- `p->state.<fld>`（`p` は `struct Curl_easy *` の一時変数） -/
theorem eval_state_field {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {p fld : Ident}
    {ty : Ty} {b : Block} {o : Integers.Ptrofs} {d : Z} {chunk : Chunk} {v : Val}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hle : le.get p = some (.Vptr b o))
    (hfld : fieldOffset prog.prog_comp_env fld (coOf _UrlState).co_members = .OK (d, .Full))
    (hacc : accessMode ty = .By_value chunk)
    (hload : Mem.load chunk m b (addr2 o 8 d) = some v) :
    EvalExpr ge e le m
      (.Efield (.Efield (.Ederef (.Etempvar p (tptr (Ty.Tstruct _Curl_easy noattr)))
          (Ty.Tstruct _Curl_easy noattr)) _state (Ty.Tstruct _UrlState noattr)) fld ty)
      v :=
  EvalExpr.Elvalue _ _ _ .Full _
    (lv_field (EvalExpr.Elvalue _ _ _ .Full _
        (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_easy) (hcenv ▸ off_state))
        (DerefLoc.copy rfl))
      rfl (hcenv ▸ co_state) (hcenv ▸ hfld))
    (DerefLoc.value chunk _ hacc hload)

theorem boolVal_ptr_creds {c : Ctx2} {m : Mem} (hptr : Ptrs2 c)
    (hv : Mem.weakValidPointer m c.credB (Integers.Ptrofs.unsigned c.credO) = true) :
    Cop.boolVal c.credsV (tptr (Ty.Tstruct _Curl_creds noattr)) m
      = some (c.credsV != .Vlong Integers.Int64.zero) := by
  rcases hptr.creds with h | h <;> rw [h]
  · rfl
  · simp only [Cop.boolVal, hv]
    rfl

/-! ## 呼ばれる側の仕様（引数を問わず、決まった真偽値を返し、メモリを変えない） -/

def boolSpec (tyargs : List Ty) (r : Bool) : FunSpec where
  tyargs := tyargs
  tyres := tbool
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun v hp => v = Val.ofBool r ∧ emp hp
  measure := fun _ => 0

/-- `Curl_creds_same(c1, c2)` -/
def credsSpec (r : Bool) : FunSpec :=
  boolSpec [tptr (Ty.Tstruct _Curl_creds noattr), tptr (Ty.Tstruct _Curl_creds noattr)] r

/-- `Curl_peer_equal(p1, p2)` -/
def peerSpec (r : Bool) : FunSpec :=
  boolSpec [tptr (Ty.Tstruct _Curl_peer noattr), tptr (Ty.Tstruct _Curl_peer noattr)] r

end Case2C
