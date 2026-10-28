/-
CVE-2025-14524: P0 の関数全体（入口で局所変数を確保するところから）。U0 は `start_same` で U1 と同じ関数に書き換えて使う。
-/
import Deb2025_14524D0
open CC CC.Sep CC.HProp
open Deb2025_14524
open Case5C (addr bitOf)
open Case3C (Locs)

set_option maxRecDepth 20000

namespace Deb2025_14524U
open Deb2025_14524_u1

/-- **P0（U0）**: 修正前の `Curl_sasl_start` は、Bearer を渡して `Curl_auth_create_oauth_bearer_message` を呼び、その戻り値 `r` を返す。 -/
theorem start_before (ge : CGenv) (c : Ctx) (bL : Block) (hv : Val) (pv : Integers.Int)
    (rd rp rl : Val) (r : Integers.Int)
    (hcenv : ge.genv_cenv = Deb2025_14524_u0.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hE : Integers.Int.and (em c) (Integers.Int.repr 32) = Integers.Int.zero)
    (hr : Integers.Int.eq r Integers.Int.zero = false)
    (hbset : c.bset = true)
    (hO : Integers.Int.eq (Integers.Int.and (em c) (Integers.Int.repr 256)) Integers.Int.zero = false)
    (hsir : bitOf c.setw 1 = true) (hal : addr c.sO 28 % 4 = 0)
    (hcu : Case4debC.IsPtr c.cuV) (hhv : Case4debC.IsPtr hv)
    (X : ExtU0 ge c bL hv pv rd rp rl r) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2025_14524_u0.f_Curl_sasl_start) (startSpecB c r) vs := by
  rw [start_same]
  have hcenv1 : ge.genv_cenv = prog.prog_comp_env := hcenv.trans cenv_same
  by_cases hvs : vs = argsS c true
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hnv : listNorepet (varNames f_Curl_sasl_start.fn_vars) := by decide
  have hnp : listNorepet (varNames f_Curl_sasl_start.fn_params) := by decide
  have hdisj : listDisjoint (varNames f_Curl_sasl_start.fn_params)
      (varNames f_Curl_sasl_start.fn_temps) := by decide
  refine satisfies_internal ge (FunctionEntry2 ge) f_Curl_sasl_start _ _ (PbodyS c true)
    (fun m hp hf hpre hd hag => ?_)
    (start_body_before ge c bL hv pv rd rp rl r hcenv1 hpr hpn hpw hE hr hbset hO hsir hal hcu hhv X)
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (Ty.Tstruct _sasl_ctx noattr))
  have hav : AllocVariables ge.genv_cenv emptyEnv m f_Curl_sasl_start.fn_vars (envS a1.2) a1.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [f_Curl_sasl_start, List.mem_cons, List.mem_nil_iff, or_false] at hv
      subst hv; rw [hcenv1]; decide)
    (Heap.union hp hf) hag
  have hLs : Locs [(a1.2, 80)] hl := by
    have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv1] at this
    exact this
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envS a1.2,
    PTree.set _progress (.Vptr c.pB c.pO) (PTree.set _force_ir (Val.ofBool true)
      (PTree.set _data (.Vptr c.dB c.dO) (PTree.set _sasl (.Vptr c.sB c.sO)
        (createUndefTemps f_Curl_sasl_start.fn_temps)))),
    a1.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨a1.2, rfl, ?_, ⟨hp, hl, dph, rfl, hpre.2, hLs⟩⟩
    refine TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_cons ?_
      (TempsHold_nil _)))) <;> ptget


end Deb2025_14524U

namespace Deb2025_14524D
open Deb2025_14524_d1
open Deb2025_14524U (Hs argsS startSpecB)

/-- **P0（D0）**: U0 の `Deb2025_14524U.start_before` と同じ形（仕様 `startSpecB` も同じ）。 -/
theorem start_before (ge : CGenv) (c : Ctx) (bL : Block) (hv : Val) (pv r : Integers.Int)
    (hcenv : ge.genv_cenv = Deb2025_14524_d0.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hE : Integers.Int.and (em c) (Integers.Int.repr 32) = Integers.Int.zero)
    (hr : Integers.Int.eq r Integers.Int.zero = false)
    (hbset : c.bset = true)
    (hO : Integers.Int.eq (Integers.Int.and (em c) (Integers.Int.repr 256)) Integers.Int.zero = false)
    (hcu : Case4debC.IsPtr c.cuV) (hhv : Case4debC.IsPtr hv)
    (X : ExtD0 ge c bL hv pv r) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2025_14524_d0.f_Curl_sasl_start) (startSpecB c r) vs := by
  by_cases hvs : vs = argsS c true
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hnv : listNorepet (varNames Deb2025_14524_d0.f_Curl_sasl_start.fn_vars) := by decide
  have hnp : listNorepet (varNames Deb2025_14524_d0.f_Curl_sasl_start.fn_params) := by decide
  have hdisj : listDisjoint (varNames Deb2025_14524_d0.f_Curl_sasl_start.fn_params)
      (varNames Deb2025_14524_d0.f_Curl_sasl_start.fn_temps) := by decide
  refine satisfies_internal ge (FunctionEntry2 ge) Deb2025_14524_d0.f_Curl_sasl_start _ _ (PbodyD0 c true)
    (fun m hp hf hpre hd hag => ?_)
    (start_body_before ge c bL hv pv r hcenv hpr hpn hpw hE hr hbset hO hcu hhv X)
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (Ty.Tstruct Deb2025_14524_d0._bufref noattr))
  let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv (tptr tschar))
  let a3 := Mem.alloc a2.1 0 (sizeof ge.genv_cenv (tptr tschar))
  let a4 := Mem.alloc a3.1 0 (sizeof ge.genv_cenv tint)
  let a5 := Mem.alloc a4.1 0 (sizeof ge.genv_cenv (Ty.Tstruct Deb2025_14524_d0._bufref noattr))
  have hav : AllocVariables ge.genv_cenv emptyEnv m Deb2025_14524_d0.f_Curl_sasl_start.fn_vars
      (envD0 a1.2 a2.2 a3.2 a4.2 a5.2) a5.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl
      (.cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)))))
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [Deb2025_14524_d0.f_Curl_sasl_start, List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> rw [hcenv] <;> decide)
    (Heap.union hp hf) hag
  have hL5 : Locs (LD a1.2 a2.2 a3.2 a4.2 a5.2) hl := by
    have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv] at this
    exact this
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envD0 a1.2 a2.2 a3.2 a4.2 a5.2,
    PTree.set Deb2025_14524_d0._progress (.Vptr c.pB c.pO) (PTree.set Deb2025_14524_d0._force_ir (Val.ofBool true)
      (PTree.set Deb2025_14524_d0._data (.Vptr c.dB c.dO) (PTree.set Deb2025_14524_d0._sasl (.Vptr c.sB c.sO)
        (createUndefTemps Deb2025_14524_d0.f_Curl_sasl_start.fn_temps)))),
    a5.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨(a1.2, a2.2, a3.2, a4.2, a5.2), locs_nodup hL5 (by intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> (show 0 < _; simp)), rfl, ?_,
      ⟨hp, hl, dph, rfl, hpre.2, hL5⟩⟩
    refine TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_cons ?_
      (TempsHold_nil _)))) <;> ptget


end Deb2025_14524D
