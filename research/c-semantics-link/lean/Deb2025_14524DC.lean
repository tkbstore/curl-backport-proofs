/-
CVE-2025-14524: 8.14.1（D1・D0）の翻訳単位で共通に使う部分。構造体の配置（前置きが U と同じなので、値も U と同じ）と、局所変数。

8.14.1 の `Curl_sasl_start` の局所変数は `resp`・`hostname`・`disp_hostname`・`port`・`nullmsg` の5つ。
P1 の経路ではどれも中身を問わないバイト列のまま持つ。
-/
import GenDeb2025_14524D1
import GenDeb2025_14524D0
import Deb2025_14524U0
open CC CC.Sep CC.HProp
open Deb2025_14524_d1
open Deb2025_14524
open Case5C (addr)
open Case3C (CellD cellH Cells Locs)

set_option maxRecDepth 20000

namespace Deb2025_14524D

theorem cenv_same : Deb2025_14524_d0.prog.prog_comp_env = Deb2025_14524_d1.prog.prog_comp_env := rfl

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


/-! ## 局所変数 -/

def envD (b1 b2 b3 b4 b5 : Block) : Env :=
  ((((emptyEnv.set _resp (b1, Ty.Tstruct _bufref noattr)).set _hostname (b2, tptr tschar)).set
    _disp_hostname (b3, tptr tschar)).set _port (b4, tint)).set _nullmsg (b5, Ty.Tstruct _bufref noattr)

abbrev LD (b1 b2 b3 b4 b5 : Block) : List (Block × Nat) := [(b1, 24), (b2, 8), (b3, 8), (b4, 4), (b5, 24)]

/-- 局所変数のブロックは互いに異なる。 -/
theorem locs_nodup : ∀ {L : List (Block × Nat)} {h : Heap}, Locs L h → (∀ x ∈ L, 0 < x.2) →
    (L.map Prod.fst).Pairwise (· ≠ ·)
  | [], _, _, _ => List.Pairwise.nil
  | (b, n) :: r, h, hL, hpos => by
      obtain ⟨h1, h2, hd, rfl, ha, hr⟩ := hL
      refine List.Pairwise.cons ?_ (locs_nodup hr (fun x hx => hpos x (List.mem_cons_of_mem _ hx)))
      intro b' hb' heq
      subst heq
      obtain ⟨⟨b'', n'⟩, hm, rfl⟩ := List.mem_map.mp hb'
      obtain ⟨hb, hs, hab⟩ := Case3C.locs_piece hr hm
      exact Case3C.anyBytes_ne ha hab (Case1C.disjoint_sub hs (Heap.disjoint_comm hd) |> Heap.disjoint_comm)
        (hpos _ (List.mem_cons_self)) (hpos _ (List.mem_cons_of_mem _ hm)) rfl

theorem pw_reorder {b1 b2 b3 b4 b5 : Block} (h : [b1, b2, b3, b4, b5].Pairwise (· ≠ ·)) :
    [(b4, (0 : Z), (4 : Z)), (b2, 0, 8), (b3, 0, 8), (b1, 0, 24), (b5, 0, 24)].Pairwise
      (fun a b => a.1 ≠ b.1) := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true] at h ⊢
  obtain ⟨⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45, _⟩ := h
  exact ⟨⟨Ne.symm h24, Ne.symm h34, Ne.symm h14, h45⟩, ⟨h23, Ne.symm h12, h25⟩, ⟨Ne.symm h13, h35⟩,
    h15, fun _ h => h.elim⟩

end Deb2025_14524D
