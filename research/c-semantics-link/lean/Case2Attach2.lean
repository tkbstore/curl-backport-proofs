/-
Case 2: `url_attach_existing` の証明の部品（その3）。所有の並べ替え、`Mloc` → `MlocAny`、
ローカル変数の読み出し、解放。
-/
import Case2Attach1
open CC CC.Sep CC.HProp
open Case2_after
open Case5C (addr bitOf sep_l sep_r)


set_option maxRecDepth 20000

namespace Case2C

/-! ## 並べ替え（`sep_cancel` で示す等式） -/

def c0 (b : Block) (v : Val) : HProp := mapsto Mptr .Freeable b 0 v
def c8 (b : Block) (v : Val) : HProp := mapsto Mptr .Freeable b 8 v
def c16 (b : Block) (v : Val) : HProp := mapsto Mptr .Freeable b 16 v
def cnow (b : Block) (nb : List MemVal) : HProp := bytesPtsTo b .Freeable 24 nb
def cw (b : Block) (w : Integers.Int) : HProp := mapsto .Mint32 .Freeable b 40 (.Vint w)
def cpad (b : Block) (pad : List MemVal) : HProp := bytesPtsTo b .Freeable 44 pad

theorem Mloc_eq (b : Block) (vf vd vn : Val) (nb : List MemVal) (w : Integers.Int)
    (pad : List MemVal) :
    Mloc b vf vd vn nb w pad = c0 b vf ∗ (c8 b vd ∗ (c16 b vn ∗ (cnow b nb ∗ (cw b w ∗ cpad b pad)))) :=
  rfl

theorem pick8 (H : HProp) (b : Block) (vf vd vn : Val) (nb : List MemVal) (w : Integers.Int)
    (pad : List MemVal) :
    (H ∗ Mloc b vf vd vn nb w pad)
      = (c8 b vd ∗ (H ∗ (c0 b vf ∗ (c16 b vn ∗ (cnow b nb ∗ (cw b w ∗ cpad b pad)))))) := by
  rw [Mloc_eq]; sep_cancel

theorem pick16 (H : HProp) (b : Block) (vf vd vn : Val) (nb : List MemVal) (w : Integers.Int)
    (pad : List MemVal) :
    (H ∗ Mloc b vf vd vn nb w pad)
      = (c16 b vn ∗ (H ∗ (c0 b vf ∗ (c8 b vd ∗ (cnow b nb ∗ (cw b w ∗ cpad b pad)))))) := by
  rw [Mloc_eq]; sep_cancel

theorem pickw (H : HProp) (b : Block) (vf vd vn : Val) (nb : List MemVal) (w : Integers.Int)
    (pad : List MemVal) :
    (H ∗ Mloc b vf vd vn nb w pad)
      = (cw b w ∗ (H ∗ (c0 b vf ∗ (c8 b vd ∗ (c16 b vn ∗ (cnow b nb ∗ cpad b pad)))))) := by
  rw [Mloc_eq]; sep_cancel

def srcNow (c : Ctx3) : HProp := bytesPtsTo c.nowB c.pm (Integers.Ptrofs.unsigned c.nowO) c.nowBytes

def H3r (c : Ctx3) (wp : Val) : HProp :=
  mapsto .Mint32 c.pm c.dataB (addr3 c.dataO) (.Vint c.want32) ∗
  (mapsto .Mint8unsigned c.pm c.dataB (addr2 c.dataO 0 0) (.Vint c.ussl) ∗
  (mapsto Mptr c.pm c.needleB (addr c.needleO 16) (.Vptr c.schemeB c.schemeO) ∗
  (mapsto .Mint64 c.pm c.schemeB (addr c.schemeO 0) (.Vlong c.proto) ∗
  (mapsto Mptr c.pm c.needleB (addr c.needleO 24) c.destV ∗
   mapsto .Mbool c.pm c.wpB (Integers.Ptrofs.unsigned c.wpO) wp))))

theorem H3_eq (c : Ctx3) (wp : Val) : H3 c wp = srcNow c ∗ H3r c wp := rfl

theorem picknow (c : Ctx3) (wp : Val) (b : Block) (vf vd vn : Val) (nb : List MemVal)
    (w : Integers.Int) (pad : List MemVal) :
    (H3 c wp ∗ Mloc b vf vd vn nb w pad)
      = (cnow b nb ∗ (srcNow c ∗ (H3r c wp ∗ (c0 b vf ∗ (c8 b vd ∗ (c16 b vn ∗ (cw b w ∗ cpad b pad))))))) := by
  rw [H3_eq, Mloc_eq]; sep_cancel

def wpCell (c : Ctx3) (wp : Val) : HProp :=
  mapsto .Mbool c.pm c.wpB (Integers.Ptrofs.unsigned c.wpO) wp

def H3w (c : Ctx3) : HProp :=
  srcNow c ∗
  (mapsto .Mint32 c.pm c.dataB (addr3 c.dataO) (.Vint c.want32) ∗
  (mapsto .Mint8unsigned c.pm c.dataB (addr2 c.dataO 0 0) (.Vint c.ussl) ∗
  (mapsto Mptr c.pm c.needleB (addr c.needleO 16) (.Vptr c.schemeB c.schemeO) ∗
  (mapsto .Mint64 c.pm c.schemeB (addr c.schemeO 0) (.Vlong c.proto) ∗
   mapsto Mptr c.pm c.needleB (addr c.needleO 24) c.destV))))

theorem pickwp (c : Ctx3) (wp : Val) (X : HProp) :
    (X ∗ H3 c wp) = (wpCell c wp ∗ (X ∗ H3w c)) := by
  unfold H3 wpCell H3w srcNow; sep_cancel

/-! ## `Mloc` → `MlocAny`（`Curl_cpool_find` に渡すとき） -/

theorem len_ptr (v : Val) : (encodeVal Mptr v).length = 8 := by
  rw [length_encodeVal]; rfl

theorem Mloc_bytes (b : Block) (vf vd vn : Val) (nb : List MemVal) (w : Integers.Int)
    (pad : List MemVal) :
    Mloc b vf vd vn nb w pad
      = bytesPtsTo b .Freeable 0 (encodeVal Mptr vf ++ (encodeVal Mptr vd ++ (encodeVal Mptr vn ++ nb)))
        ∗ (cw b w ∗ cpad b pad) := by
  rw [Mloc_eq]
  unfold c0 c8 c16 cnow
  rw [mapsto_eq_bytes (by decide), mapsto_eq_bytes (by decide), mapsto_eq_bytes (by decide),
    bytesPtsTo_append, bytesPtsTo_append, bytesPtsTo_append, len_ptr, len_ptr, len_ptr]
  rw [show (0 : _root_.Int) + ((8 : Nat) : _root_.Int) = 8 from rfl,
    show (8 : _root_.Int) + ((8 : Nat) : _root_.Int) = 16 from rfl,
    show (16 : _root_.Int) + ((8 : Nat) : _root_.Int) = 24 from rfl]
  sep_cancel

theorem Mloc_any {b : Block} {vf vd vn : Val} {nb : List MemVal} {w : Integers.Int}
    {pad : List MemVal} (hnb : nb.length = 16) (hpad : pad.length = 4) {h : Heap}
    (hm : Mloc b vf vd vn nb w pad h) : MlocAny b w h := by
  rw [Mloc_bytes] at hm
  obtain ⟨h1, h2, hd, rfl, hb1, h3, h4, hd34, rfl, hw, hp⟩ := hm
  refine ⟨h1, Heap.union h3 h4, hd, rfl, ⟨_, pure_sep_intro ?_ hb1⟩, h3, h4, hd34, rfl, hw,
    ⟨_, pure_sep_intro hpad hp⟩⟩
  simp [len_ptr, hnb]

/-! ## ローカル変数の読み出し・番地 -/

theorem uz8 : Integers.Ptrofs.unsigned
    (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 8)) = 8 := by decide
theorem uz16 : Integers.Ptrofs.unsigned
    (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 16)) = 16 := by decide
theorem uz24 : Integers.Ptrofs.unsigned
    (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 24)) = 24 := by decide
theorem uz40 : Integers.Ptrofs.unsigned
    (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 40)) = 40 := by decide

end Case2C
