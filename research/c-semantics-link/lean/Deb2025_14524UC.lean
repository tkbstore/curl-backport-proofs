/-
CVE-2025-14524: 上流（U1・U0）の翻訳単位で共通に使う部分。構造体の配置、`sasl_ctx` のセル、`sasl_choose_*` の仕様の形。

`sasl_ctx sctx` は `Curl_sasl_start` の局所変数（80 バイト）。`memset` のあと、隙間なく並んだ 14 個のセルとして持つ
（パディングと `resp` の中身もセルにする。`memset` が 0 で埋めるので、どれも 0 の値を持つ）。
-/
import GenDeb2025_14524U1
import GenDeb2025_14524U0
import Deb2025_14524Lib
open CC CC.Sep CC.HProp
open Deb2025_14524_u1
open Deb2025_14524
open Case5C (addr)
open Case3C (CellD cellH Cells)

set_option maxRecDepth 20000

namespace Deb2025_14524U

theorem cenv_same : Deb2025_14524_u0.prog.prog_comp_env = Deb2025_14524_u1.prog.prog_comp_env := rfl

/-! ## 構造体の配置 -/

def coOf (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_easy : prog.prog_comp_env.get _Curl_easy = some (coOf _Curl_easy) := rfl
theorem co_ud : prog.prog_comp_env.get _UserDefined = some (coOf _UserDefined) := rfl
theorem co_us : prog.prog_comp_env.get _UrlState = some (coOf _UrlState) := rfl
theorem co_aptr : prog.prog_comp_env.get _dynamically_allocated_data
    = some (coOf _dynamically_allocated_data) := rfl
theorem co_sasl : prog.prog_comp_env.get _SASL = some (coOf _SASL) := rfl
theorem co_ctx : prog.prog_comp_env.get _sasl_ctx = some (coOf _sasl_ctx) := rfl
theorem co_conn : prog.prog_comp_env.get _connectdata = some (coOf _connectdata) := rfl

theorem off_conn : fieldOffset prog.prog_comp_env _conn (coOf _Curl_easy).co_members
    = .OK (0, .Full) := by decide
theorem off_set : fieldOffset prog.prog_comp_env _set (coOf _Curl_easy).co_members
    = .OK (8, .Full) := by decide
theorem off_state : fieldOffset prog.prog_comp_env _state (coOf _Curl_easy).co_members
    = .OK (576, .Full) := by decide
theorem off_str : fieldOffset prog.prog_comp_env _str (coOf _UserDefined).co_members
    = .OK (0, .Full) := by decide
theorem off_allow : fieldOffset prog.prog_comp_env _allow_auth_to_other_hosts
    (coOf _UserDefined).co_members = .OK (560, .Bits .I32 .Unsigned 0 1) := by decide
theorem off_sasl_ir : fieldOffset prog.prog_comp_env _sasl_ir
    (coOf _UserDefined).co_members = .OK (560, .Bits .I32 .Unsigned 1 1) := by decide
theorem off_aptr : fieldOffset prog.prog_comp_env _aptr (coOf _UrlState).co_members
    = .OK (0, .Full) := by decide
theorem off_follow : fieldOffset prog.prog_comp_env _this_is_a_follow (coOf _UrlState).co_members
    = .OK (8, .Bits .I32 .Unsigned 0 1) := by decide
theorem off_auser : fieldOffset prog.prog_comp_env _user
    (coOf _dynamically_allocated_data).co_members = .OK (0, .Full) := by decide
theorem off_cuser : fieldOffset prog.prog_comp_env _user (coOf _connectdata).co_members
    = .OK (0, .Full) := by decide
theorem off_am : fieldOffset prog.prog_comp_env _authmechs (coOf _SASL).co_members
    = .OK (24, .Full) := by decide
theorem off_pf : fieldOffset prog.prog_comp_env _prefmech (coOf _SASL).co_members
    = .OK (26, .Full) := by decide
theorem off_au : fieldOffset prog.prog_comp_env _authused (coOf _SASL).co_members
    = .OK (28, .Full) := by decide
theorem off_fir : fieldOffset prog.prog_comp_env _force_ir (coOf _SASL).co_members
    = .OK (28, .Bits .I32 .Unsigned 18 1) := by decide

theorem offx_sasl : fieldOffset prog.prog_comp_env _sasl (coOf _sasl_ctx).co_members
    = .OK (0, .Full) := by decide
theorem offx_conn : fieldOffset prog.prog_comp_env _conn (coOf _sasl_ctx).co_members
    = .OK (8, .Full) := by decide
theorem offx_user : fieldOffset prog.prog_comp_env _user (coOf _sasl_ctx).co_members
    = .OK (16, .Full) := by decide
theorem offx_em : fieldOffset prog.prog_comp_env _enabledmechs (coOf _sasl_ctx).co_members
    = .OK (24, .Full) := by decide
theorem offx_mech : fieldOffset prog.prog_comp_env _mech (coOf _sasl_ctx).co_members
    = .OK (32, .Full) := by decide
theorem offx_s1 : fieldOffset prog.prog_comp_env _state1 (coOf _sasl_ctx).co_members
    = .OK (40, .Full) := by decide
theorem offx_s2 : fieldOffset prog.prog_comp_env _state2 (coOf _sasl_ctx).co_members
    = .OK (44, .Full) := by decide
theorem offx_resp : fieldOffset prog.prog_comp_env _resp (coOf _sasl_ctx).co_members
    = .OK (48, .Full) := by decide
theorem offx_res : fieldOffset prog.prog_comp_env _result (coOf _sasl_ctx).co_members
    = .OK (72, .Full) := by decide

/-! ## `sctx` のセル -/

abbrev z64 : Val := .Vlong (Integers.Int64.repr 0)
abbrev addr0 (d : Z) : Z := addr Integers.Ptrofs.zero d

/-- `sctx` の 80 バイトを隙間なく覆う 14 個のセル。 -/
abbrev sctxL (xB : Block) (vs vc vu : Val) (emv : Integers.Int) (mech : Val) (s1 s2 : Integers.Int)
    (rd rp rl : Val) (res : Integers.Int) : List CellD :=
  [(Mptr, .Freeable, xB, addr0 0, vs),
   (Mptr, .Freeable, xB, addr0 8, vc),
   (Mptr, .Freeable, xB, addr0 16, vu),
   (.Mint16unsigned, .Freeable, xB, addr0 24, .Vint emv),
   (.Mint16unsigned, .Freeable, xB, addr0 26, .Vint (Integers.Int.repr 0)),
   (.Mint32, .Freeable, xB, addr0 28, .Vint (Integers.Int.repr 0)),
   (Mptr, .Freeable, xB, addr0 32, mech),
   (.Mint32, .Freeable, xB, addr0 40, .Vint s1),
   (.Mint32, .Freeable, xB, addr0 44, .Vint s2),
   (Mptr, .Freeable, xB, addr0 48, rd),
   (Mptr, .Freeable, xB, addr0 56, rp),
   (.Mint64, .Freeable, xB, addr0 64, rl),
   (.Mint32, .Freeable, xB, addr0 72, .Vint res),
   (.Mint32, .Freeable, xB, addr0 76, .Vint (Integers.Int.repr 0))]

/-- `memset(&sctx, 0, sizeof(sctx))` のあと。 -/
abbrev sctxZ (xB : Block) : List CellD :=
  sctxL xB z64 z64 z64 (Integers.Int.repr 0) z64 (Integers.Int.repr 0) (Integers.Int.repr 0)
    z64 z64 z64 (Integers.Int.repr 0)

/-- フィールドを埋めたあと（`sasl_choose_*` を呼ぶ直前）。 -/
abbrev sctxS (c : Ctx) (xB : Block) : List CellD :=
  sctxL xB (.Vptr c.sB c.sO) (.Vptr c.cB c.cO) (.Vptr c.uB c.uO) (em c) z64 (Integers.Int.repr 0)
    (Integers.Int.repr 17) z64 z64 z64 (Integers.Int.repr 0)

theorem sctx_contig (xB : Block) (vs vc vu : Val) (emv : Integers.Int) (mech : Val)
    (s1 s2 : Integers.Int) (rd rp rl : Val) (res : Integers.Int) :
    contig xB .Freeable 0 (sctxL xB vs vc vu emv mech s1 s2 rd rp rl res) := by
  simp only [contig]
  decide

theorem sctx_any {xB : Block} {vs vc vu : Val} {emv : Integers.Int} {mech : Val}
    {s1 s2 : Integers.Int} {rd rp rl : Val} {res : Integers.Int} {h : Heap}
    (hc : Cells (sctxL xB vs vc vu emv mech s1 s2 rd rp rl res) h) :
    anyBytes .Freeable xB 0 80 h :=
  cells_anyBytes xB .Freeable _ 0 h (sctx_contig xB vs vc vu emv mech s1 s2 rd rp rl res) hc

/-- `sasl_choose_*` を呼ぶときのメモリ: `sctx` のセル、関数の外のセル、`authused` の単位。 -/
def W1 (c : Ctx) (fir : Bool) (xB : Block) : HProp :=
  Cells (sctxS c xB ++ outer c (Integers.Int.repr 0)) ∗ SW2 c fir (Integers.Int.repr 0)

/-- `sasl_choose_*(data, &sctx)` の仕様の形。 -/
def chooseSpec (c : Ctx) (xB : Block) (Wpre Wpost : HProp) (ret : Bool) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _sasl_ctx noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dB c.dO, .Vptr xB Integers.Ptrofs.zero] ∧ Wpre hp
  post := fun v hp => v = Val.ofBool ret ∧ Wpost hp
  measure := fun _ => 0

/-! ## 式の評価 -/

theorem zext_em (c : Ctx) : Integers.Int.zero_ext 16 (em c) = em c := zext16_idem _

/-- `x & k` が 0 なら、条件は偽。 -/
theorem cond_and_false (x k : Integers.Int) (hx : Integers.Int.and x k = Integers.Int.zero) (m : Mem) :
    Cop.boolVal (.Vint (Integers.Int.and x k)) tint m = some false := by
  show some (!Integers.Int.eq (Integers.Int.and x k) Integers.Int.zero) = some false
  rw [hx]
  rfl

/-- `data->state.this_is_a_follow`・`data->set.allow_auth_to_other_hosts`・`data->set.sasl_ir` のような
    `p->s.fld`（`s` は構造体のフィールド、`fld` は 1 ビットのビットフィールド）。 -/
theorem eval_bit2 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {p sid sid2 fld fld2 : Ident} {co co2 : Composite}
    {b : Block} {o : Integers.Ptrofs} {d1 d2 pos : Z} {w : Integers.Int}
    (hle : le.get p = some (.Vptr b o))
    (hco : ge.genv_cenv.get sid = some co)
    (hf1 : fieldOffset ge.genv_cenv fld co.co_members = .OK (d1, .Full))
    (hco2 : ge.genv_cenv.get sid2 = some co2)
    (hf2 : fieldOffset ge.genv_cenv fld2 co2.co_members = .OK (d2, .Bits .I32 .Unsigned pos 1))
    (hpos0 : 0 ≤ pos) (hpos : pos + 1 ≤ 32)
    (hload : Mem.load .Mint32 m b (addr (Integers.Ptrofs.add o (Integers.Ptrofs.repr d1)) d2)
      = some (.Vint w)) :
    EvalExpr ge e le m
      (.Efield (.Efield (.Ederef (.Etempvar p (tptr (.Tstruct sid noattr))) (.Tstruct sid noattr))
          fld (.Tstruct sid2 noattr)) fld2 tint)
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned pos 1 w)) :=
  EvalExpr.Elvalue _ b _ (.Bits .I32 .Unsigned pos 1) _
    (EvalLvalue.Efield_struct _ fld2 tint b _ sid2 co2 noattr d2 _
      (EvalExpr.Elvalue _ _ _ .Full _
        (Case4debC.lv_field (Case4debC.eval_deref_temp hle) rfl hco hf1) (DerefLoc.copy rfl))
      rfl hco2 hf2)
    (DerefLoc.bitfield .I32 .Unsigned pos 1 _
      (Cop.LoadBitfield.intro .I32 .Signed noattr .Unsigned pos 1 m _ w hpos0 (by decide)
        (by decide) hpos (by decide) hload))

end Deb2025_14524U
