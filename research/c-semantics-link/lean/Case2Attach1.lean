/-
Case 2: `url_attach_existing` の証明の部品（その2）。読むメモリ `H3`、外部関数の仕様、規則と評価の補題。
-/
import Case2AttachBase
import Case2NegoMain
open CC CC.Sep CC.HProp
open Case2_after
open Case5C (addr bitOf call_fwd RR return_const skip_fall boolVal_ofBool_tint sep_l sep_r cast_ofBool_bool)
open Case4C (IsPtr loadResult_ptr cast_ptr eval_deref_temp lv_field)

set_option maxRecDepth 20000

namespace Case2C

/-! ## 読むメモリ -/

structure Ctx3 where
  dataB : Block
  dataO : Integers.Ptrofs
  needleB : Block
  needleO : Integers.Ptrofs
  wpB : Block                -- waitpipe
  wpO : Integers.Ptrofs
  schemeB : Block            -- needle->scheme
  schemeO : Integers.Ptrofs
  destV : Val                -- needle->destination
  want32 : Integers.Int      -- data->state.authhost.want
  ussl : Integers.Int        -- data->set.use_ssl（1 バイト）
  proto : Integers.Int64     -- needle->scheme->protocol
  nowB : Block               -- Curl_pgrs_now(data) が返す struct curltime
  nowO : Integers.Ptrofs
  nowBytes : List MemVal
  cpV : Val                  -- Curl_cpool_get_instance(data) の戻り値
  pm : Permission

/-- `data->state.authhost.want` の番地。 -/
def addr3 (o : Integers.Ptrofs) : Z :=
  Integers.Ptrofs.unsigned (Integers.Ptrofs.add
    (Integers.Ptrofs.add (Integers.Ptrofs.add o (Integers.Ptrofs.repr 8)) (Integers.Ptrofs.repr 8))
    (Integers.Ptrofs.repr 0))

/-- 読むセルと、書く `*waitpipe`。先頭は構造体のコピー元（`*Curl_pgrs_now(data)`）。 -/
def H3 (c : Ctx3) (wp : Val) : HProp :=
  bytesPtsTo c.nowB c.pm (Integers.Ptrofs.unsigned c.nowO) c.nowBytes ∗
  (mapsto .Mint32 c.pm c.dataB (addr3 c.dataO) (.Vint c.want32) ∗
  (mapsto .Mint8unsigned c.pm c.dataB (addr2 c.dataO 0 0) (.Vint c.ussl) ∗
  (mapsto Mptr c.pm c.needleB (addr c.needleO 16) (.Vptr c.schemeB c.schemeO) ∗
  (mapsto .Mint64 c.pm c.schemeB (addr c.schemeO 0) (.Vlong c.proto) ∗
  (mapsto Mptr c.pm c.needleB (addr c.needleO 24) c.destV ∗
   mapsto .Mbool c.pm c.wpB (Integers.Ptrofs.unsigned c.wpO) wp)))))

structure Loads3 (c : Ctx3) (m : Mem) : Prop where
  want : Mem.load .Mint32 m c.dataB (addr3 c.dataO) = some (.Vint c.want32)
  ussl : Mem.load .Mint8unsigned m c.dataB (addr2 c.dataO 0 0)
    = some (.Vint (Integers.Int.zero_ext 8 c.ussl))
  scheme : Mem.load Mptr m c.needleB (addr c.needleO 16) = some (.Vptr c.schemeB c.schemeO)
  proto : Mem.load .Mint64 m c.schemeB (addr c.schemeO 0) = some (.Vlong c.proto)
  dest : Mem.load Mptr m c.needleB (addr c.needleO 24) = some c.destV

theorem H3_loads {c : Ctx3} {wp : Val} {X : HProp} {hp : Heap} {m : Mem}
    (hpr : permOrder c.pm .Readable = true) (hdest : IsPtr c.destV)
    (hH : (H3 c wp ∗ X) hp) (hag : Heap.Agrees hp m) : Loads3 c m := by
  obtain ⟨h0, c0, a0⟩ := sep_l hH hag
  obtain ⟨r1, d1, b1⟩ := sep_r c0 a0
  obtain ⟨h2, c2, a2⟩ := sep_l d1 b1
  obtain ⟨r2, d2, b2⟩ := sep_r d1 b1
  obtain ⟨h3, c3, a3⟩ := sep_l d2 b2
  obtain ⟨r3, d3, b3⟩ := sep_r d2 b2
  obtain ⟨h4, c4, a4⟩ := sep_l d3 b3
  obtain ⟨r4, d4, b4⟩ := sep_r d3 b3
  obtain ⟨h5, c5, a5⟩ := sep_l d4 b4
  obtain ⟨r5, d5, b5⟩ := sep_r d4 b4
  obtain ⟨h6, c6, a6⟩ := sep_l d5 b5
  refine ⟨mapsto_load hpr c2 a2, mapsto_load hpr c3 a3, mapsto_load hpr c4 a4,
    mapsto_load hpr c5 a5, ?_⟩
  rw [mapsto_load hpr c6 a6, loadResult_ptr hdest]

/-! ## 外部関数の仕様 -/

def tyMatchP : Ty := tptr (Ty.Tstruct _url_conn_match noattr)

/-- `match` を呼ばれる側に渡すときの所有: 中身は問わず、ビットの単位だけ値を持つ。 -/
def MlocAny (b : Block) (w : Integers.Int) : HProp :=
  anyBytes .Freeable b 0 40 ∗ (mapsto .Mint32 .Freeable b 40 (.Vint w) ∗ anyBytes .Freeable b 44 4)

/-- `memset(s, 0, n)`: C の標準どおり、`n` バイトを 0 にする。 -/
def memsetSpec (b : Block) : FunSpec where
  tyargs := [tptr tvoid, tint, tulong]
  tyres := tptr tvoid
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr b Integers.Ptrofs.zero, .Vint (Integers.Int.repr 0),
             Val.Vptrofs (Integers.Ptrofs.repr 48)]
    ∧ undefBytes .Freeable b 0 48 hp
  post := fun _ hp => bytesPtsTo b .Freeable 0 (List.replicate 48 zeroByte) hp
  measure := fun _ => 0

/-- 値だけを返し、メモリを変えない関数。 -/
def valSpec (tyargs : List Ty) (tyres : Ty) (r : Val) : FunSpec where
  tyargs := tyargs
  tyres := tyres
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun v hp => v = r ∧ emp hp
  measure := fun _ => 0

def instSpec (cp : Val) : FunSpec :=
  valSpec [tptr (Ty.Tstruct _Curl_easy noattr)] (tptr (Ty.Tstruct _cpool noattr)) cp
def nowSpec (c : Ctx3) : FunSpec :=
  valSpec [tptr (Ty.Tstruct _Curl_easy noattr)] (tptr (Ty.Tstruct _curltime noattr))
    (.Vptr c.nowB c.nowO)
def mmSpec (mm : Bool) : FunSpec :=
  valSpec [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _connectdata noattr)] tbool
    (Val.ofBool mm)
def allowSpec (al : Bool) : FunSpec :=
  valSpec [tptr (Ty.Tstruct _Curl_easy noattr)] tbool (Val.ofBool al)

/-- `Curl_cpool_prune_dead(cpool, data)`: 何も返さず、ここで見るメモリを変えない。 -/
def pruneSpec : FunSpec where
  tyargs := [tptr (Ty.Tstruct _cpool noattr), tptr (Ty.Tstruct _Curl_easy noattr)]
  tyres := tvoid
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun _ hp => emp hp
  measure := fun _ => 0

/-- **`Curl_cpool_find(data, dest, url_match_conn, url_match_result, &match)`**。
    前提に「`match.want_nego_http` が `expected`、`match.want_proxy_nego_http` が 0」を要求する。
    `url_attach_existing` がこの仕様のもとで証明できることが、呼び出しの時点でビットがそうなっていることの証拠になる。
    戻り値は `fb`（任意）。`match` の所有は返す（中身は変わってよい）。 -/
def findSpec (expected : Bool) (b : Block) (fb : Bool) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr tschar,
             tptr (Ty.Tfunction [tptr (Ty.Tstruct _connectdata noattr), tptr tvoid] tbool cc_default),
             tptr (Ty.Tfunction [tptr tvoid] tbool cc_default), tptr tvoid]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp =>
    (∃ v1 v2 v3 v4, vargs = [v1, v2, v3, v4, .Vptr b Integers.Ptrofs.zero])
    ∧ ∃ w, bitOf w 1 = expected ∧ bitOf w 2 = false ∧ MlocAny b w hp
  post := fun v hp => v = Val.ofBool fb ∧ ∃ w, MlocAny b w hp
  measure := fun _ => 0

/-! ## 規則 -/

/-- 戻り値を捨てる呼び出し。呼ばれる側に `Hpre` を渡し、`Hpost` を受け取る。 -/
theorem call_void (ge fe f) (S : FunSpec) (callee : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (Hpre Hpost Hk : HProp) (vargs : List Val)
    (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs)
    (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof callee) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le →
                 EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, Hpre h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → Hpost h) :
    Triple ge fe f (LocalSt E l (Hpre ∗ Hk)) (.Scall none callee al)
      (.only (LocalSt E l (Hpost ∗ Hk))) := by
  refine triple_call ge fe f S none callee al _ _ fb fd hspec hfind hty hclass
    (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, h1, h2, hd, heq, hH1, hH2⟩ := hP
  subst he
  refine ⟨vargs, h1, h2, hd, heq, hcallee le m hT, hargs le m hT, hpre h1 hH1, ?_⟩
  intro v h1' hS hd'
  exact ⟨rfl, hT, h1', h2, hd', rfl, hpost v h1' hS, hH2⟩

/-- 先頭のセルへの代入（`triple_assign` を `LocalSt` の形にしたもの）。 -/
theorem assign_head (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp)
    (a1 a2 : Expr) (chunk : Chunk) (p : Permission) (b : Block) (ofs : Integers.Ptrofs) (o : Z)
    (vold vnew : Val)
    (hpw : permOrder p .Writable = true)
    (hacc : accessMode (typeof a1) = .By_value chunk)
    (ho : Integers.Ptrofs.unsigned ofs = o)
    (hlv : ∀ le m, TempsHold l le → EvalLvalue ge E le m a1 b ofs .Full)
    (hev : ∀ le m, TempsHold l le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew) :
    Triple ge fe f (LocalSt E l (mapsto chunk p b o vold ∗ R)) (.Sassign a1 a2)
      (.only (LocalSt E l (mapsto chunk p b o vnew ∗ R))) := by
  subst ho
  refine triple_assign ge fe f _ _ a1 a2 chunk p b ofs hpw hacc (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, heq, hm, hr⟩ := hP
  subst he
  refine ⟨vold, vnew, h1, h2, hd, heq, hm, hlv le m hT, hev le m hT, fun h1' hm' hd' => ?_⟩
  exact ⟨rfl, hT, h1', h2, hd', rfl, hm', hr⟩

/-- 先頭のビットの単位への代入。 -/
theorem assign_bits_head (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp)
    (a1 a2 : Expr) (b : Block) (ofs : Integers.Ptrofs) (o pos : Z) (w n : Integers.Int)
    (hty : typeof a1 = tint) (hpos0 : 0 ≤ pos) (hpos : pos + 1 ≤ 32)
    (ho : Integers.Ptrofs.unsigned ofs = o)
    (hlv : ∀ le m, TempsHold l le → EvalLvalue ge E le m a1 b ofs (.Bits .I32 .Unsigned pos 1))
    (hev : ∀ le m, TempsHold l le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some (.Vint n)) :
    Triple ge fe f (LocalSt E l (mapsto .Mint32 .Freeable b o (.Vint w) ∗ R)) (.Sassign a1 a2)
      (.only (LocalSt E l (mapsto .Mint32 .Freeable b o
        (.Vint (Integers.Int.bitfield_insert (Cop.firstBit .I32 pos 1).toNat 1 w n)) ∗ R))) := by
  subst ho
  refine Case2C.triple_assign_bitfield ge fe f _ _ a1 a2 .Freeable b ofs pos rfl rfl hty hpos0 hpos
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, heq, hm, hr⟩ := hP
  subst he
  refine ⟨w, n, h1, h2, hd, heq, hm, hlv le m hT, hev le m hT, fun h1' hm' hd' => ?_⟩
  exact ⟨rfl, hT, h1', h2, hd', rfl, hm', hr⟩

/-- 前提と事後の所有を、同じ等式で書き換える。 -/
theorem triple_rw (ge fe f) (E : Env) (l l' : List (Ident × Val)) (A A' B B' : HProp) (s : Stmt)
    (hA : A = A') (hB : B = B')
    (h : Triple ge fe f (LocalSt E l A') s (.only (LocalSt E l' B'))) :
    Triple ge fe f (LocalSt E l A) s (.only (LocalSt E l' B)) := by
  subst hA hB; exact h

/-! ## 値の形 -/

def boolInt (b : Bool) : Integers.Int := if b then Integers.Int.one else Integers.Int.zero

theorem ofBool_eq (b : Bool) : Val.ofBool b = .Vint (boolInt b) := by cases b <;> rfl

theorem cast_ofBool_int (b : Bool) (m : Mem) :
    Cop.semCast (Val.ofBool b) tint tint m = some (.Vint (boolInt b)) := by cases b <;> rfl
theorem cast_ofBool_bool_int (b : Bool) (m : Mem) :
    Cop.semCast (Val.ofBool b) tbool tint m = some (.Vint (boolInt b)) := by cases b <;> rfl
theorem cast_ofBool_bb (b : Bool) (m : Mem) :
    Cop.semCast (Val.ofBool b) tbool tbool m = some (Val.ofBool b) := by cases b <;> rfl
theorem cast_long_bool (x : Integers.Int64) (m : Mem) :
    Cop.semCast (.Vlong x) tlong tbool m
      = some (Val.ofBool (!Integers.Int64.eq x Integers.Int64.zero)) := by
  cases h : Integers.Int64.eq x Integers.Int64.zero <;> simp [Cop.semCast, Cop.classifyCast, h] <;> rfl

/-- `ins pos w n`: 32 bit の単位 `w` の bit `pos` に `n` を書く（ビットフィールドへの書き込み）。 -/
def ins (pos : Z) (w n : Integers.Int) : Integers.Int :=
  Integers.Int.bitfield_insert (Cop.firstBit .I32 pos 1).toNat 1 w n

/-- **ビットの計算**: 0 から始めて bit 0・1・4・3 に書いたあと、bit 1 は書いた値、bit 2 は 0 のまま。 -/
theorem bits_after (mm wn rq mt : Bool) :
    bitOf (ins 3 (ins 4 (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt wn))
      (boolInt rq)) (boolInt mt)) 1 = wn
    ∧ bitOf (ins 3 (ins 4 (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt wn))
      (boolInt rq)) (boolInt mt)) 2 = false := by
  cases mm <;> cases wn <;> cases rq <;> cases mt <;> decide

/-- `(authhost.want & CURLAUTH_NEGOTIATE)` が 0 でない。 -/
def rw1 (c : Ctx3) : Bool :=
  !Integers.Int64.eq (Integers.Int64.and (Integers.Int64.repr (Integers.Int.unsigned c.want32))
    (Integers.Int64.shl (Integers.Int64.repr 1) (Integers.Int64.repr 2))) Integers.Int64.zero

/-- `PROTO_FAMILY_HTTP` -/
def famC : Integers.Int64 :=
  Integers.Int64.or (Integers.Int64.or (Integers.Int64.or
    (Integers.Int64.shl (Integers.Int64.repr 1) (Integers.Int64.repr 0))
    (Integers.Int64.shl (Integers.Int64.repr 1) (Integers.Int64.repr 1)))
    (Integers.Int64.shl (Integers.Int64.repr 1) (Integers.Int64.repr 30)))
    (Integers.Int64.shl (Integers.Int64.repr 1) (Integers.Int64.repr 31))

/-- `(needle->scheme->protocol & PROTO_FAMILY_HTTP)` が 0 でない。 -/
def rw2 (c : Ctx3) : Bool :=
  !Integers.Int64.eq (Integers.Int64.and c.proto famC) Integers.Int64.zero

/-- H5 のモデルの `rawWant`。 -/
def rawWant (c : Ctx3) : Bool := rw1 c && rw2 c

end Case2C
