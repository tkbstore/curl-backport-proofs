/-
CVE-2026-5545: `url_match_auth_ntlm` の4つの翻訳単位に共通の部分（CVE-2026-1965 の `Deb2026_1965Common.lean` を写して、
フィールドと判定をこの関数に合わせた）。性質は `research/backport-proof-debian/cases/CVE-2026-5545.md`（証明の前にコミットした）。
U と D は関数の本体が文字として同じ。構造体の宣言も同じ。
-/
import GenDeb2026_5545U1
import GenDeb2026_5545U0
import GenDeb2026_5545D1
import GenDeb2026_5545D0
import Deb2026_1965Tac
open CC CC.Sep CC.HProp
open Case5C (addr call_fwd RR return_const boolVal_ofBool_tint eval_field eval_bitfield bitOf
  cast_int_bool cast_ofBool_bool sep_l sep_r)
open Case4C (IsPtr loadResult_ptr cast_ptr)

set_option maxRecDepth 20000

namespace Deb2026_5545C

/-! ## 構造体のレイアウト（4つの翻訳単位で同じ。翻訳単位ごとに `decide` で確かめる） -/

def connMembers : List Member :=
  [Member.Member_plain (identOfString "user") (tptr tschar),
   Member.Member_plain (identOfString "passwd") (tptr tschar),
   Member.Member_plain (identOfString "http_ntlm_state") tint,
   Member.Member_plain (identOfString "proxy_ntlm_state") tint,
   Member.Member_plain (identOfString "http_negotiate_state") tint]

def matchMembers : List Member :=
  [Member.Member_plain (identOfString "found") (tptr (Ty.Tstruct (identOfString "connectdata") noattr)),
   Member.Member_plain (identOfString "needle") (tptr (Ty.Tstruct (identOfString "connectdata") noattr)),
   Member.Member_bitfield (identOfString "want_ntlm_http") IntSize.I32 Signedness.Unsigned noattr 1 false,
   Member.Member_bitfield (identOfString "want_proxy_ntlm_http") IntSize.I32 Signedness.Unsigned noattr 1 false,
   Member.Member_bitfield (identOfString "force_reuse") IntSize.I32 Signedness.Unsigned noattr 1 false]

def coConn : Composite :=
  { co_su := SU.Struct, co_members := connMembers, co_attr := noattr,
    co_sizeof := 32, co_alignof := 8, co_rank := 0 }
def coMatch : Composite :=
  { co_su := SU.Struct, co_members := matchMembers, co_attr := noattr,
    co_sizeof := 24, co_alignof := 8, co_rank := 0 }

/-- 証明が使うレイアウトの事実。 -/
structure Layout (env : CompositeEnv) : Prop where
  co_conn : env.get (identOfString "connectdata") = some coConn
  co_match : env.get (identOfString "url_conn_match") = some coMatch
  off_user : fieldOffset env (identOfString "user") connMembers = .OK (0, .Full)
  off_passwd : fieldOffset env (identOfString "passwd") connMembers = .OK (8, .Full)
  off_hnt : fieldOffset env (identOfString "http_ntlm_state") connMembers = .OK (16, .Full)
  off_pnt : fieldOffset env (identOfString "proxy_ntlm_state") connMembers = .OK (20, .Full)
  off_hns : fieldOffset env (identOfString "http_negotiate_state") connMembers = .OK (24, .Full)
  off_found : fieldOffset env (identOfString "found") matchMembers = .OK (0, .Full)
  off_needle : fieldOffset env (identOfString "needle") matchMembers = .OK (8, .Full)
  off_wt : fieldOffset env (identOfString "want_ntlm_http") matchMembers
    = .OK (16, .Bits .I32 .Unsigned 0 1)
  off_wpt : fieldOffset env (identOfString "want_proxy_ntlm_http") matchMembers
    = .OK (16, .Bits .I32 .Unsigned 1 1)
  off_force : fieldOffset env (identOfString "force_reuse") matchMembers
    = .OK (16, .Bits .I32 .Unsigned 2 1)

theorem layout_u1 : Layout Deb2026_5545_u1.prog.prog_comp_env := by
  constructor <;> decide
theorem layout_u0 : Layout Deb2026_5545_u0.prog.prog_comp_env := by
  constructor <;> decide
theorem layout_d1 : Layout Deb2026_5545_d1.prog.prog_comp_env := by
  constructor <;> decide
theorem layout_d0 : Layout Deb2026_5545_d0.prog.prog_comp_env := by
  constructor <;> decide

/-! ## 読み書きするメモリ -/

structure Ctx where
  connB : Block
  connO : Integers.Ptrofs
  mB : Block
  mO : Integers.Ptrofs
  ndlB : Block               -- m->needle
  ndlO : Integers.Ptrofs
  nu : Val                   -- m->needle->user
  np : Val                   -- m->needle->passwd
  cu : Val                   -- conn->user
  cp : Val                   -- conn->passwd
  hnt : Integers.Int         -- conn->http_ntlm_state
  pnt : Integers.Int         -- conn->proxy_ntlm_state
  hns : Integers.Int         -- conn->http_negotiate_state
  pm : Permission

/-- 書き込む2つのセル（`m->found`・ビットの単位）と、読むだけの8つのセル。 -/
def H (c : Ctx) (fv : Val) (w : Integers.Int) : HProp :=
  mapsto Mptr c.pm c.mB (addr c.mO 0) fv ∗
  (mapsto .Mint32 c.pm c.mB (addr c.mO 16) (.Vint w) ∗
  (mapsto Mptr c.pm c.mB (addr c.mO 8) (.Vptr c.ndlB c.ndlO) ∗
  (mapsto Mptr c.pm c.ndlB (addr c.ndlO 0) c.nu ∗
  (mapsto Mptr c.pm c.ndlB (addr c.ndlO 8) c.np ∗
  (mapsto Mptr c.pm c.connB (addr c.connO 0) c.cu ∗
  (mapsto Mptr c.pm c.connB (addr c.connO 8) c.cp ∗
  (mapsto .Mint32 c.pm c.connB (addr c.connO 16) (.Vint c.hnt) ∗
  (mapsto .Mint32 c.pm c.connB (addr c.connO 20) (.Vint c.pnt) ∗
   mapsto .Mint32 c.pm c.connB (addr c.connO 24) (.Vint c.hns)))))))))

structure Ptrs (c : Ctx) : Prop where
  nu : IsPtr c.nu
  np : IsPtr c.np
  cu : IsPtr c.cu
  cp : IsPtr c.cp

structure Loads (c : Ctx) (w : Integers.Int) (m : Mem) : Prop where
  word : Mem.load .Mint32 m c.mB (addr c.mO 16) = some (.Vint w)
  needle : Mem.load Mptr m c.mB (addr c.mO 8) = some (.Vptr c.ndlB c.ndlO)
  nu : Mem.load Mptr m c.ndlB (addr c.ndlO 0) = some c.nu
  np : Mem.load Mptr m c.ndlB (addr c.ndlO 8) = some c.np
  cu : Mem.load Mptr m c.connB (addr c.connO 0) = some c.cu
  cp : Mem.load Mptr m c.connB (addr c.connO 8) = some c.cp
  hnt : Mem.load .Mint32 m c.connB (addr c.connO 16) = some (.Vint c.hnt)
  pnt : Mem.load .Mint32 m c.connB (addr c.connO 20) = some (.Vint c.pnt)
  hns : Mem.load .Mint32 m c.connB (addr c.connO 24) = some (.Vint c.hns)

theorem H_loads {c : Ctx} {fv : Val} {w : Integers.Int} {hp : Heap} {m : Mem}
    (hpr : permOrder c.pm .Readable = true) (hptr : Ptrs c)
    (hH : H c fv w hp) (hag : Heap.Agrees hp m) : Loads c w m := by
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
  obtain ⟨r8, d8, b8⟩ := sep_r d7 b7
  obtain ⟨h9, c9, a9⟩ := sep_l d8 b8
  obtain ⟨h10, c10, a10⟩ := sep_r d8 b8
  refine ⟨mapsto_load hpr c2 a2, mapsto_load hpr c3 a3, ?_, ?_, ?_, ?_,
    mapsto_load hpr c8 a8, mapsto_load hpr c9 a9, mapsto_load hpr c10 a10⟩
  · rw [mapsto_load hpr c4 a4, loadResult_ptr hptr.nu]
  · rw [mapsto_load hpr c5 a5, loadResult_ptr hptr.np]
  · rw [mapsto_load hpr c6 a6, loadResult_ptr hptr.cu]
  · rw [mapsto_load hpr c7 a7, loadResult_ptr hptr.cp]

/-! ## 判定（関数が読む値から決まる） -/

inductive Verdict where
  | reject     -- FALSE。何も書かない
  | candidate  -- FALSE。`m->found = conn`
  | forceReuse -- TRUE。`m->found = conn`、`m->force_reuse = TRUE`
  | accept     -- TRUE。何も書かない
  deriving DecidableEq, Repr

/-- `fix`: 修正の `&& (conn->http_negotiate_state == GSS_AUTHNONE)` があるか（U1・D1 は真、U0・D0 は偽）。
    `diff` は認証情報の照合（`Curl_timestrcmp` のどちらかが 0 でない）。 -/
def verdict (fix wt wpt ntlm pntlm nego diff : Bool) : Verdict :=
  if wt && diff then (if !ntlm && (!fix || !nego) then .candidate else .reject)
  else if !wt && ntlm then .reject
  else if wt || wpt then (if (wt && ntlm) || (wpt && pntlm) then .forceReuse else .candidate)
  else .accept

/-- ビットの位置: want_ntlm_http 0、want_proxy_ntlm_http 1、force_reuse 2 -/
def vdOf (fix : Bool) (c : Ctx) (w : Integers.Int) (cmp : Val → Val → Integers.Int) : Verdict :=
  verdict fix (bitOf w 0) (bitOf w 1)
    (!Integers.Int.eq c.hnt Integers.Int.zero) (!Integers.Int.eq c.pnt Integers.Int.zero)
    (!Integers.Int.eq c.hns Integers.Int.zero)
    ((!Integers.Int.eq (cmp c.nu c.cu) Integers.Int.zero)
      || (!Integers.Int.eq (cmp c.np c.cp) Integers.Int.zero))

def retOf : Verdict → Bool
  | .forceReuse => true
  | .accept => true
  | _ => false

def foundOf (c : Ctx) (fv : Val) : Verdict → Val
  | .candidate => .Vptr c.connB c.connO
  | .forceReuse => .Vptr c.connB c.connO
  | _ => fv

def forceWord (w : Integers.Int) : Integers.Int :=
  Integers.Int.bitfield_insert (Cop.firstBit .I32 2 1).toNat 1 w (Integers.Int.repr 1)

def wordOf (w : Integers.Int) : Verdict → Integers.Int
  | .forceReuse => forceWord w
  | _ => w

def ntlmSpec (fix : Bool) (c : Ctx) (fv : Val) (w : Integers.Int)
    (cmp : Val → Val → Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct (identOfString "connectdata") noattr),
             tptr (Ty.Tstruct (identOfString "url_conn_match") noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.connB c.connO, .Vptr c.mB c.mO] ∧ H c fv w hp
  post := fun v hp =>
    v = Val.ofBool (retOf (vdOf fix c w cmp))
    ∧ H c (foundOf c fv (vdOf fix c w cmp)) (wordOf w (vdOf fix c w cmp)) hp
  measure := fun _ => 0

theorem post_of {fix : Bool} {c : Ctx} {fv : Val} {w : Integers.Int}
    {cmp : Val → Val → Integers.Int} {v : Val} {hp : Heap}
    (vd : Verdict) (hvd : vdOf fix c w cmp = vd) (hv : v = Val.ofBool (retOf vd))
    (hH : H c (foundOf c fv vd) (wordOf w vd) hp) :
    (ntlmSpec fix c fv w cmp).post v hp := by
  subst hvd
  exact ⟨hv, hH⟩

/- 外部関数 `Curl_timestrcmp` の仕様は CVE-2026-1965 と同じもの（`Deb2026_1965C.TsExt`）を使う。 -/

end Deb2026_5545C
