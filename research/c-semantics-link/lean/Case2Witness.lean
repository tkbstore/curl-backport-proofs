/-
Case 2: 前提 `H3`（`url_attach_existing`）・`H2`（`url_match_auth_nego`）を満たすヒープが、具体的なメモリの上にあること。
値は H5 の P0 の反例（Negotiate を要求する HTTP の転送、送り先の許可は無い、Negotiate 済みの接続）。
-/
import Case2AttachMain
import Case5Witness
open CC CC.Sep CC.HProp
open Case2_after
open Case5C (addr bitOf cell mapsto_disj agrees_union bytes_agrees)

set_option maxRecDepth 20000

namespace Case2C

/-! ## `H3`: 1 ブロック 88 バイト

   0  struct curltime（16 バイト、未定義のまま）       32  data->state.authhost.want = CURLAUTH_NEGOTIATE（4）
  16  data->set.use_ssl = 0                             56  needle->scheme = &scheme（72）
  64  needle->destination = NULL                        72  scheme->protocol = CURLPROTO_HTTP（1）
  80  *waitpipe = 0 -/

def bw3 : Block := Mem.empty.nextblock
def m0_3 : Mem := (Mem.alloc Mem.empty 0 88).1

def storesW3 : Option Mem := do
  let m ← Mem.store .Mint8unsigned m0_3 bw3 16 (.Vint (Integers.Int.repr 0))
  let m ← Mem.store .Mint32 m bw3 32 (.Vint (Integers.Int.repr 4))
  let m ← Mem.store Mptr m bw3 56 (.Vptr bw3 (Integers.Ptrofs.repr 72))
  let m ← Mem.store Mptr m bw3 64 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store .Mint64 m bw3 72 (.Vlong (Integers.Int64.repr 1))
  Mem.store .Mbool m bw3 80 (.Vint (Integers.Int.repr 0))

theorem storesW3_isSome : storesW3.isSome = true := by decide
def mW3 : Mem := storesW3.get storesW3_isSome

def cW3 : Ctx3 where
  dataB := bw3
  dataO := Integers.Ptrofs.repr 16
  needleB := bw3
  needleO := Integers.Ptrofs.repr 40
  wpB := bw3
  wpO := Integers.Ptrofs.repr 80
  schemeB := bw3
  schemeO := Integers.Ptrofs.repr 72
  destV := .Vlong (Integers.Int64.repr 0)
  want32 := Integers.Int.repr 4
  ussl := Integers.Int.repr 0
  proto := Integers.Int64.repr 1
  nowB := bw3
  nowO := Integers.Ptrofs.repr 0
  nowBytes := List.replicate 16 .Undef
  cpV := .Vlong (Integers.Int64.repr 0)
  pm := .Freeable

theorem rawWant_cW3 : rawWant cW3 = true := by decide

theorem cW3_cells :
    Integers.Ptrofs.unsigned cW3.nowO = 0 ∧ addr3 cW3.dataO = 32 ∧ addr2 cW3.dataO 0 0 = 16
    ∧ addr cW3.needleO 16 = 56 ∧ addr cW3.schemeO 0 = 72 ∧ addr cW3.needleO 24 = 64
    ∧ Integers.Ptrofs.unsigned cW3.wpO = 80 := by
  decide

theorem bytes_disj {b : Block} {p : Permission} {o1 o2 : _root_.Int} {l1 l2 : List MemVal}
    {h1 h2 : Heap} (hb1 : bytesPtsTo b p o1 l1 h1) (hb2 : bytesPtsTo b p o2 l2 h2)
    (hr : o1 + (l1.length : _root_.Int) ≤ o2 ∨ o2 + (l2.length : _root_.Int) ≤ o1) :
    Heap.disjoint h1 h2 := by
  intro b' o
  rcases hr with hr | hr
  · rcases Int.lt_or_le o (o1 + (l1.length : _root_.Int)) with h | h
    · exact Or.inr (bytesPtsTo_none b p l2 o2 h2 hb2 b' o (Or.inr (Or.inl (by omega))))
    · exact Or.inl (bytesPtsTo_none b p l1 o1 h1 hb1 b' o (Or.inr (Or.inr h)))
  · rcases Int.lt_or_le o o1 with h | h
    · exact Or.inl (bytesPtsTo_none b p l1 o1 h1 hb1 b' o (Or.inr (Or.inl h)))
    · exact Or.inr (bytesPtsTo_none b p l2 o2 h2 hb2 b' o (Or.inr (Or.inr (by omega))))

theorem H3_cW3_satisfiable :
    ∃ hp, H3 cW3 (.Vint (Integers.Int.repr 0)) hp ∧ Heap.Agrees hp mW3 := by
  obtain ⟨a0, a32, a16, a56, a72, a64, a80⟩ := cW3_cells
  obtain ⟨h0, b0⟩ := bytesPtsTo_exists bw3 .Freeable (List.replicate 16 .Undef) 0
  have g0 : Heap.Agrees h0 mW3 := bytes_agrees b0 (by decide)
  obtain ⟨h1, m1, g1⟩ := cell (chunk := .Mint32) (b := bw3) (ofs := 32)
    (v := .Vint (Integers.Int.repr 4)) (m := mW3) (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := cell (chunk := .Mint8unsigned) (b := bw3) (ofs := 16)
    (v := .Vint (Integers.Int.repr 0)) (m := mW3) (by decide) (by decide)
  obtain ⟨h3, m3, g3⟩ := cell (chunk := Mptr) (b := bw3) (ofs := 56)
    (v := .Vptr bw3 (Integers.Ptrofs.repr 72)) (m := mW3) (by decide) (by decide)
  obtain ⟨h4, m4, g4⟩ := cell (chunk := .Mint64) (b := bw3) (ofs := 72)
    (v := .Vlong (Integers.Int64.repr 1)) (m := mW3) (by decide) (by decide)
  obtain ⟨h5, m5, g5⟩ := cell (chunk := Mptr) (b := bw3) (ofs := 64)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW3) (by decide) (by decide)
  obtain ⟨h6, m6, g6⟩ := cell (chunk := .Mbool) (b := bw3) (ofs := 80)
    (v := .Vint (Integers.Int.repr 0)) (m := mW3) (by decide) (by decide)
  -- 0 番の区画（バイト列）と、各セルとの交わり
  have bm := fun {c2 o2 v2 h2} (y : mapsto c2 .Freeable bw3 o2 v2 h2)
      (r : (0 : _root_.Int) + ((List.replicate 16 MemVal.Undef).length : _root_.Int) ≤ o2) =>
    bytes_disj b0 (pure_sep_elim y).2 (Or.inl r)
  have d56 := mapsto_disj m5 m6 (by decide)
  have d4 := Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m5 (by decide), mapsto_disj m4 m6 (by decide)⟩
  have d3 := Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m4 (by decide),
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m5 (by decide), mapsto_disj m3 m6 (by decide)⟩⟩
  have d2 := Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m3 (by decide),
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m4 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m5 (by decide), mapsto_disj m2 m6 (by decide)⟩⟩⟩
  have d1 := Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m2 (by decide),
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m3 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m4 (by decide),
        Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m5 (by decide), mapsto_disj m1 m6 (by decide)⟩⟩⟩⟩
  have d0 := Heap.disjoint_union_right.mpr ⟨bm m1 (by decide),
    Heap.disjoint_union_right.mpr ⟨bm m2 (by decide),
      Heap.disjoint_union_right.mpr ⟨bm m3 (by decide),
        Heap.disjoint_union_right.mpr ⟨bm m4 (by decide),
          Heap.disjoint_union_right.mpr ⟨bm m5 (by decide), bm m6 (by decide)⟩⟩⟩⟩⟩
  refine ⟨_, ?_, agrees_union g0 (agrees_union g1 (agrees_union g2 (agrees_union g3
    (agrees_union g4 (agrees_union g5 g6)))))⟩
  unfold H3
  rw [a0, a32, a16, a56, a72, a64, a80]
  exact ⟨_, _, d0, rfl, b0, _, _, d1, rfl, m1, _, _, d2, rfl, m2, _, _, d3, rfl, m3,
    _, _, d4, rfl, m4, _, _, d56, rfl, m5, m6⟩

/-! ## `H2`: 1 ブロック 128 バイト

   0  m->found = NULL      8  m->data = &data（88）            40  m のビットの単位 = 2（want_nego_http）
  48  conn->creds = &creds（120）   56  conn->creds_origin = NULL   80  conn->http_negotiate_state = 2
  96  data->state.origin = NULL    112  data->state.creds = NULL    120  creds の 1 バイト -/

def bw2 : Block := Mem.empty.nextblock
def m0_2 : Mem := (Mem.alloc Mem.empty 0 128).1

def storesW2 : Option Mem := do
  let m ← Mem.store Mptr m0_2 bw2 0 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store Mptr m bw2 8 (.Vptr bw2 (Integers.Ptrofs.repr 88))
  let m ← Mem.store .Mint32 m bw2 40 (.Vint (Integers.Int.repr 2))
  let m ← Mem.store Mptr m bw2 48 (.Vptr bw2 (Integers.Ptrofs.repr 120))
  let m ← Mem.store Mptr m bw2 56 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store .Mint32 m bw2 80 (.Vint (Integers.Int.repr 2))
  let m ← Mem.store Mptr m bw2 96 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store Mptr m bw2 112 (.Vlong (Integers.Int64.repr 0))
  Mem.store .Mint8unsigned m bw2 120 (.Vint (Integers.Int.repr 0))

theorem storesW2_isSome : storesW2.isSome = true := by decide
def mW2 : Mem := storesW2.get storesW2_isSome

def cW2 : Ctx2 where
  connB := bw2
  connO := Integers.Ptrofs.repr 48
  mB := bw2
  mO := Integers.Ptrofs.repr 0
  dataB := bw2
  dataO := Integers.Ptrofs.repr 88
  credsV := .Vptr bw2 (Integers.Ptrofs.repr 120)
  credB := bw2
  credO := Integers.Ptrofs.repr 120
  corigV := .Vlong (Integers.Int64.repr 0)
  ns := Integers.Int.repr 2
  originV := .Vlong (Integers.Int64.repr 0)
  scredsV := .Vlong (Integers.Int64.repr 0)
  pm := .Freeable

def wordW2 : Integers.Int := Integers.Int.repr 2

theorem wordW2_bits : bitOf wordW2 1 = true ∧ bitOf wordW2 2 = false := by decide

theorem cW2_cells :
    addr cW2.mO 0 = 0 ∧ addr cW2.mO 40 = 40 ∧ addr cW2.mO 8 = 8 ∧ addr cW2.connO 0 = 48
    ∧ addr cW2.connO 8 = 56 ∧ addr cW2.connO 32 = 80 ∧ addr2 cW2.dataO 8 0 = 96
    ∧ addr2 cW2.dataO 8 16 = 112 ∧ Integers.Ptrofs.unsigned cW2.credO = 120 := by
  decide

theorem cW2_ptrs : Ptrs2 cW2 :=
  ⟨Or.inr rfl, Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩⟩

theorem H2_cW2_satisfiable :
    ∃ hp, H2 cW2 (.Vlong (Integers.Int64.repr 0)) wordW2 hp ∧ Heap.Agrees hp mW2 := by
  obtain ⟨a0, a40, a8, a48, a56, a80, a96, a112, a120⟩ := cW2_cells
  obtain ⟨h1, m1, g1⟩ := cell (chunk := Mptr) (b := bw2) (ofs := 0)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW2) (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := cell (chunk := .Mint32) (b := bw2) (ofs := 40)
    (v := .Vint (Integers.Int.repr 2)) (m := mW2) (by decide) (by decide)
  obtain ⟨h3, m3, g3⟩ := cell (chunk := Mptr) (b := bw2) (ofs := 8)
    (v := .Vptr bw2 (Integers.Ptrofs.repr 88)) (m := mW2) (by decide) (by decide)
  obtain ⟨h4, m4, g4⟩ := cell (chunk := Mptr) (b := bw2) (ofs := 48)
    (v := .Vptr bw2 (Integers.Ptrofs.repr 120)) (m := mW2) (by decide) (by decide)
  obtain ⟨h5, m5, g5⟩ := cell (chunk := Mptr) (b := bw2) (ofs := 56)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW2) (by decide) (by decide)
  obtain ⟨h6, m6, g6⟩ := cell (chunk := .Mint32) (b := bw2) (ofs := 80)
    (v := .Vint (Integers.Int.repr 2)) (m := mW2) (by decide) (by decide)
  obtain ⟨h7, m7, g7⟩ := cell (chunk := Mptr) (b := bw2) (ofs := 96)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW2) (by decide) (by decide)
  obtain ⟨h8, m8, g8⟩ := cell (chunk := Mptr) (b := bw2) (ofs := 112)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW2) (by decide) (by decide)
  obtain ⟨h9, m9, g9⟩ := cell (chunk := .Mint8unsigned) (b := bw2) (ofs := 120)
    (v := .Vint (Integers.Int.repr 0)) (m := mW2) (by decide) (by decide)
  have d89 := mapsto_disj m8 m9 (by decide)
  have d7 := Heap.disjoint_union_right.mpr ⟨mapsto_disj m7 m8 (by decide), mapsto_disj m7 m9 (by decide)⟩
  have d6 := Heap.disjoint_union_right.mpr ⟨mapsto_disj m6 m7 (by decide),
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m6 m8 (by decide), mapsto_disj m6 m9 (by decide)⟩⟩
  have d5 := Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m6 (by decide),
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m7 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m8 (by decide), mapsto_disj m5 m9 (by decide)⟩⟩⟩
  have d4 := Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m5 (by decide),
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m6 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m7 (by decide),
        Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m8 (by decide), mapsto_disj m4 m9 (by decide)⟩⟩⟩⟩
  have d3 := Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m4 (by decide),
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m5 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m6 (by decide),
        Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m7 (by decide),
          Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m8 (by decide), mapsto_disj m3 m9 (by decide)⟩⟩⟩⟩⟩
  have d2 := Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m3 (by decide),
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m4 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m5 (by decide),
        Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m6 (by decide),
          Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m7 (by decide),
            Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m8 (by decide), mapsto_disj m2 m9 (by decide)⟩⟩⟩⟩⟩⟩
  have d1 := Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m2 (by decide),
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m3 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m4 (by decide),
        Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m5 (by decide),
          Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m6 (by decide),
            Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m7 (by decide),
              Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m8 (by decide), mapsto_disj m1 m9 (by decide)⟩⟩⟩⟩⟩⟩⟩
  refine ⟨_, ?_, agrees_union g1 (agrees_union g2 (agrees_union g3 (agrees_union g4
    (agrees_union g5 (agrees_union g6 (agrees_union g7 (agrees_union g8 g9)))))))⟩
  unfold H2
  rw [a0, a40, a8, a48, a56, a80, a96, a112, a120]
  exact ⟨_, _, d1, rfl, m1, _, _, d2, rfl, m2, _, _, d3, rfl, m3, _, _, d4, rfl, m4,
    _, _, d5, rfl, m5, _, _, d6, rfl, m6, _, _, d7, rfl, m7, _, _, d89, rfl, m8, m9⟩

end Case2C
