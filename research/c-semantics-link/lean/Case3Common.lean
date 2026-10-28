/-
Case 3（CURL-CVE-2026-92389）: 修正前・修正後の証明で共通に使う部分。

- 局所変数（`fn_vars`）の所有 `Locs` と、入口・return での扱い
  - `locs_of_localsAt`: 入口で確保された局所変数（`localsAt`、中身は undef）を `Locs` に移す
  - `ret_locs`: 局所変数を解放して return する規則（中身は問わない）
- 構造体のレイアウト（生成された composite の環境から `decide` で確かめる）
-/
import GenCase3After
import GenCase3Before
import Case1Rules
open CC CC.Sep CC.HProp
open Case5C (addr RR)
open Case1C (Sub sub_left sub_right sub_trans sub_union agrees_sub disjoint_sub none_of_disjoint owns_at)

set_option maxRecDepth 20000

namespace Case3C

/-! ## 局所変数の所有 -/

/-- 局所変数のブロック（ブロックと大きさ）をすべて所有している。中身は問わない。 -/
def Locs : List (Block × Nat) → HProp
  | [] => emp
  | (b, n) :: r => anyBytes .Freeable b 0 n ∗ Locs r

/-- 環境 `e` で、変数の並び `vars` が束縛されているブロックと大きさ。 -/
def locsOf (ce : CompositeEnv) (e : Env) : List (Ident × Ty) → List (Block × Nat)
  | [] => []
  | (id, ty) :: r =>
    match e.get id with
    | some (b, _) => (b, (sizeof ce ty).toNat) :: locsOf ce e r
    | none => locsOf ce e r

theorem locs_of_localsAt (ce : CompositeEnv) (e : Env) :
    ∀ (vars : List (Ident × Ty)) (h : Heap), localsAt ce e vars h → Locs (locsOf ce e vars) h
  | [], h, hl => hl
  | (id, ty) :: r, h, hl => by
    obtain ⟨h1, h2, hd, rfl, ⟨b, hb⟩, hr⟩ := hl
    obtain ⟨hget, hu⟩ := pure_sep_elim hb
    simp only [locsOf, hget]
    exact ⟨h1, h2, hd, rfl, undefBytes_anyBytes hu, locs_of_localsAt ce e r h2 hr⟩

/-- `Locs L` の中の1つのブロックは、`hl` の部分として所有されている。 -/
theorem locs_piece : ∀ {L : List (Block × Nat)} {hl : Heap} {b : Block} {n : Nat},
    Locs L hl → (b, n) ∈ L → ∃ hb, Sub hb hl ∧ anyBytes .Freeable b 0 n hb
  | [], _, _, _, _, hm => by cases hm
  | (b', n') :: r, hl, b, n, hL, hm => by
    obtain ⟨h1, h2, hd, rfl, ha, hr⟩ := hL
    rcases List.mem_cons.mp hm with he | hm'
    · cases he
      exact ⟨h1, sub_left _ _, ha⟩
    · obtain ⟨hb, hs, hab⟩ := locs_piece hr hm'
      exact ⟨hb, sub_trans hs (sub_right hd), hab⟩

theorem anyBytes_owns {b : Block} {n : Nat} {h : Heap} (ha : anyBytes .Freeable b 0 n h)
    (o : _root_.Int) (h0 : 0 ≤ o) (hlt : o < (n : _root_.Int)) : ∃ c, h b o = some c := by
  obtain ⟨bytes, hb⟩ := ha
  obtain ⟨hlen, hbp⟩ := pure_sep_elim hb
  exact owns_at hbp o h0 (by rw [hlen]; exact hlt)

theorem anyBytes_rangePerm {b : Block} {n : Nat} {h : Heap} {m : Mem}
    (ha : anyBytes .Freeable b 0 n h) (hag : Heap.Agrees h m) :
    Mem.rangePerm m b 0 (n : _root_.Int) .Cur .Freeable = true := by
  obtain ⟨bytes, hb⟩ := ha
  obtain ⟨hlen, hbp⟩ := pure_sep_elim hb
  have := bytesPtsTo_rangePerm hbp hag
  rwa [hlen, show (0 : _root_.Int) + (n : _root_.Int) = n from by omega] at this

/-- 局所変数を解放する。解放の前後で、局所変数以外の所有 `hk` と外側 `hf` は変わらない。 -/
theorem locs_free (L : List (Block × Nat)) (l : List (Block × Z × Z)) (hk hl : Heap) (m : Mem)
    (hL : Locs L hl) (hag : Heap.Agrees (Heap.union hk hl) m)
    (hd : Heap.disjoint hk hl)
    (hsub : ∀ x ∈ l, ∃ (b : Block) (n : Nat), x = (b, 0, (n : _root_.Int)) ∧ (b, n) ∈ L)
    (hpw : l.Pairwise (fun a b => a.1 ≠ b.1)) :
    ∃ m', Mem.freeList m l = some m' ∧
      ∀ hf, Heap.disjoint (Heap.union hk hl) hf → Heap.Agrees (Heap.union (Heap.union hk hl) hf) m →
        Heap.disjoint hk hf ∧ Heap.Agrees (Heap.union hk hf) m' := by
  have sL : Sub hl (Heap.union hk hl) := sub_right hd
  obtain ⟨m', hm'⟩ := freeList_isSome_of_rangePerm l m
    (fun blk hb => by
      obtain ⟨b, n, rfl, hbn⟩ := hsub blk hb
      obtain ⟨hb', hs, ha⟩ := locs_piece hL hbn
      exact anyBytes_rangePerm ha (agrees_sub (sub_trans hs sL) hag))
    hpw
  refine ⟨m', hm', fun hf hdf hagf => ⟨disjoint_sub (sub_left _ _) hdf, ?_⟩⟩
  have hdkf : Heap.disjoint hk hf := disjoint_sub (sub_left _ _) hdf
  refine Sep.Agrees_freeList l m m' hm' ?_
    (agrees_sub (sub_union (sub_trans (sub_left hk hl) (sub_left _ _)) (sub_right hdf)) hagf)
  intro blk hb ofs h0 hlt
  obtain ⟨b, n, rfl, hbn⟩ := hsub blk hb
  obtain ⟨hb', hs, ha⟩ := locs_piece hL hbn
  obtain ⟨c, hc⟩ := anyBytes_owns ha ofs (by simpa using h0) (by simpa using hlt)
  have hcl : hl b ofs = some c := hs b ofs c hc
  have e1 : hk b ofs = none := none_of_disjoint (Heap.disjoint_comm hd) hcl
  have e2 : hf b ofs = none :=
    none_of_disjoint (disjoint_sub sL hdf) hcl
  simp only [Heap.union, e1, e2]

/-- 局所変数を解放する `return a;`。`a` の値は局所変数を読まずに決まる。 -/
theorem ret_locs (ge fe f) (E : Env) (l : List (Ident × Val)) (Hk : HProp)
    (L : List (Block × Nat)) (a : Expr) (v v' : Val) (Ret : Val → HProp)
    (hev : ∀ le m hp, TempsHold l le → (Hk ∗ Locs L) hp → Heap.Agrees hp m →
      EvalExpr ge E le m a v)
    (hcast : ∀ m, Cop.semCast v (typeof a) f.fn_return m = some v')
    (hsub : ∀ x ∈ blocksOfEnv ge.genv_cenv E,
      ∃ (b : Block) (n : Nat), x = (b, 0, (n : _root_.Int)) ∧ (b, n) ∈ L)
    (hpw : (blocksOfEnv ge.genv_cenv E).Pairwise (fun a b => a.1 ≠ b.1))
    (hret : ∀ hp, Hk hp → Ret v' hp) :
    Triple ge fe f (LocalSt E l (Hk ∗ Locs L)) (.Sreturn (some a))
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := Ret } := by
  refine Sep.triple_return ge fe f _ _ a (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  obtain ⟨hk, hl, hd, rfl, hK, hL⟩ := hH
  obtain ⟨m', hm', hfr⟩ := locs_free L _ hk hl m hL hag hd hsub hpw
  exact ⟨v, v', m', hk, hev le m _ hT ⟨hk, hl, hd, rfl, hK, hL⟩ hag, hcast m, hm', hret hk hK,
    fun hf hdf hagf => hfr hf hdf hagf⟩

/-- 2つの局所変数のブロックは異なる（どちらも 1 バイト以上を所有していて、所有が重ならない）。 -/
theorem anyBytes_ne {b1 b2 : Block} {n1 n2 : Nat} {h1 h2 : Heap}
    (a1 : anyBytes .Freeable b1 0 n1 h1) (a2 : anyBytes .Freeable b2 0 n2 h2)
    (hd : Heap.disjoint h1 h2) (p1 : 0 < n1) (p2 : 0 < n2) : b1 ≠ b2 := by
  intro heq
  subst heq
  obtain ⟨c1, hc1⟩ := anyBytes_owns a1 0 (by omega) (by omega)
  obtain ⟨c2, hc2⟩ := anyBytes_owns a2 0 (by omega) (by omega)
  rw [none_of_disjoint hd hc1] at hc2
  cases hc2

/-- 3つの局所変数のブロックは互いに異なる。 -/
theorem locs3_ne {b1 b2 b3 : Block} {n1 n2 n3 : Nat} {h : Heap}
    (hL : Locs [(b1, n1), (b2, n2), (b3, n3)] h) (p1 : 0 < n1) (p2 : 0 < n2) (p3 : 0 < n3) :
    b1 ≠ b2 ∧ b1 ≠ b3 ∧ b2 ≠ b3 := by
  obtain ⟨h1, r1, d1, rfl, a1, hr1⟩ := hL
  obtain ⟨h2, r2, d2, rfl, a2, hr2⟩ := hr1
  obtain ⟨h3, r3, d3, rfl, a3, _⟩ := hr2
  have s3 : Sub h3 (Heap.union h2 (Heap.union h3 r3)) := sub_trans (sub_left h3 r3) (sub_right d2)
  refine ⟨anyBytes_ne a1 a2
      (Heap.disjoint_comm (disjoint_sub (sub_left h2 _) (Heap.disjoint_comm d1))) p1 p2,
    anyBytes_ne a1 a3 (Heap.disjoint_comm (disjoint_sub s3 (Heap.disjoint_comm d1))) p1 p3,
    anyBytes_ne a2 a3
      (Heap.disjoint_comm (disjoint_sub (sub_left h3 r3) (Heap.disjoint_comm d2))) p2 p3⟩

/-! ## 構造体のレイアウト（修正後の翻訳単位。修正前も前置きは同じ） -/

def coOf (id : Ident) : Composite :=
  match Case3_after.prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_conn : Case3_after.prog.prog_comp_env.get Case3_after._tftp_conn
    = some (coOf Case3_after._tftp_conn) := rfl
theorem co_easy : Case3_after.prog.prog_comp_env.get Case3_after._Curl_easy
    = some (coOf Case3_after._Curl_easy) := rfl
theorem co_us : Case3_after.prog.prog_comp_env.get Case3_after._UrlState
    = some (coOf Case3_after._UrlState) := rfl

theorem off_data : fieldOffset Case3_after.prog.prog_comp_env Case3_after._data
    (coOf Case3_after._tftp_conn).co_members = .OK (160, .Full) := by decide
theorem off_state : fieldOffset Case3_after.prog.prog_comp_env Case3_after._state
    (coOf Case3_after._Curl_easy).co_members = .OK (16, .Full) := by decide
theorem off_upload : fieldOffset Case3_after.prog.prog_comp_env Case3_after._upload
    (coOf Case3_after._UrlState).co_members = .OK (16, .Bits .I32 .Unsigned 1 1) := by decide

/-- 修正前と修正後で、composite の環境は同じ（前置きが同じため）。 -/
theorem cenv_same : Case3_before.prog.prog_comp_env = Case3_after.prog.prog_comp_env := rfl

theorem co_pkt : Case3_after.prog.prog_comp_env.get Case3_after._tftp_packet
    = some (coOf Case3_after._tftp_packet) := rfl

/-- `struct tftp_conn` のフィールド（名前・オフセット）。`block`（16 bit）と `remote_pinned` は同じ 4 バイトの単位にある。 -/
theorem off_conn :
    fieldOffset Case3_after.prog.prog_comp_env Case3_after._remote_addr (coOf Case3_after._tftp_conn).co_members = .OK (0, .Full)
    ∧ fieldOffset Case3_after.prog.prog_comp_env Case3_after._rpacket (coOf Case3_after._tftp_conn).co_members = .OK (128, .Full)
    ∧ fieldOffset Case3_after.prog.prog_comp_env Case3_after._spacket (coOf Case3_after._tftp_conn).co_members = .OK (136, .Full)
    ∧ fieldOffset Case3_after.prog.prog_comp_env Case3_after._event (coOf Case3_after._tftp_conn).co_members = .OK (152, .Full)
    ∧ fieldOffset Case3_after.prog.prog_comp_env Case3_after._sockfd (coOf Case3_after._tftp_conn).co_members = .OK (168, .Full)
    ∧ fieldOffset Case3_after.prog.prog_comp_env Case3_after._retries (coOf Case3_after._tftp_conn).co_members = .OK (172, .Full)
    ∧ fieldOffset Case3_after.prog.prog_comp_env Case3_after._remote_addrlen (coOf Case3_after._tftp_conn).co_members = .OK (192, .Full)
    ∧ fieldOffset Case3_after.prog.prog_comp_env Case3_after._rbytes (coOf Case3_after._tftp_conn).co_members = .OK (196, .Full)
    ∧ fieldOffset Case3_after.prog.prog_comp_env Case3_after._sbytes (coOf Case3_after._tftp_conn).co_members = .OK (200, .Full)
    ∧ fieldOffset Case3_after.prog.prog_comp_env Case3_after._blksize (coOf Case3_after._tftp_conn).co_members = .OK (208, .Full)
    ∧ fieldOffset Case3_after.prog.prog_comp_env Case3_after._block (coOf Case3_after._tftp_conn).co_members = .OK (216, .Full)
    ∧ fieldOffset Case3_after.prog.prog_comp_env Case3_after._remote_pinned (coOf Case3_after._tftp_conn).co_members
        = .OK (216, .Bits .I32 .Unsigned 16 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem off_pdata : fieldOffset Case3_after.prog.prog_comp_env Case3_after._data
    (coOf Case3_after._tftp_packet).co_members = .OK (0, .Full) := by decide

end Case3C
