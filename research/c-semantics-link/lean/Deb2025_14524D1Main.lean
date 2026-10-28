/-
CVE-2025-14524: D1 の `Curl_sasl_start` 全体（入口で局所変数5つを確保するところから）。本体は `Deb2025_14524D1.lean`。
-/
import Deb2025_14524D1
open CC CC.Sep CC.HProp
open Deb2025_14524_d1
open Deb2025_14524
open Case5C (bitOf)
open Case3C (Locs)
open Deb2025_14524U (Hs argsS startSpecA)

set_option maxRecDepth 20000

namespace Deb2025_14524D

/-- **P1（D1）**: U1 の `Deb2025_14524U.start_after` と同じ形。 -/
theorem start_after (ge : CGenv) (c : Ctx) (fir : Bool)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hfollow : bitOf c.stw 0 = true) (hallow : bitOf c.setw 0 = false)
    (hE : Integers.Int.and (em c) (Integers.Int.repr 32) = Integers.Int.zero)
    (hP : Integers.Int.and (em c) (Integers.Int.repr 2) = Integers.Int.zero)
    (hL : Integers.Int.and (em c) (Integers.Int.repr 1) = Integers.Int.zero)
    (X : ExtD1 ge c fir) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_Curl_sasl_start) (startSpecA c fir) vs := by
  by_cases hvs : vs = argsS c fir
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hnv : listNorepet (varNames f_Curl_sasl_start.fn_vars) := by decide
  have hnp : listNorepet (varNames f_Curl_sasl_start.fn_params) := by decide
  have hdisj : listDisjoint (varNames f_Curl_sasl_start.fn_params)
      (varNames f_Curl_sasl_start.fn_temps) := by decide
  refine satisfies_internal ge (FunctionEntry2 ge) f_Curl_sasl_start _ _ (PbodyD c fir)
    (fun m hp hf hpre hd hag => ?_)
    (start_body_after ge c fir hcenv hpr hpn hpw hfollow hallow hE hP hL X)
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (Ty.Tstruct _bufref noattr))
  let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv (tptr tschar))
  let a3 := Mem.alloc a2.1 0 (sizeof ge.genv_cenv (tptr tschar))
  let a4 := Mem.alloc a3.1 0 (sizeof ge.genv_cenv tint)
  let a5 := Mem.alloc a4.1 0 (sizeof ge.genv_cenv (Ty.Tstruct _bufref noattr))
  have hav : AllocVariables ge.genv_cenv emptyEnv m f_Curl_sasl_start.fn_vars
      (envD a1.2 a2.2 a3.2 a4.2 a5.2) a5.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl
      (.cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)))))
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [f_Curl_sasl_start, List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> rw [hcenv] <;> decide)
    (Heap.union hp hf) hag
  have hL5 : Locs (LD a1.2 a2.2 a3.2 a4.2 a5.2) hl := by
    have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv] at this
    exact this
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envD a1.2 a2.2 a3.2 a4.2 a5.2,
    PTree.set _progress (.Vptr c.pB c.pO) (PTree.set _force_ir (Val.ofBool fir)
      (PTree.set _data (.Vptr c.dB c.dO) (PTree.set _sasl (.Vptr c.sB c.sO)
        (createUndefTemps f_Curl_sasl_start.fn_temps)))),
    a5.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨(a1.2, a2.2, a3.2, a4.2, a5.2), locs_nodup hL5 (by intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> (show 0 < _; simp)), rfl, ?_,
      ⟨hp, hl, dph, rfl, hpre.2, hL5⟩⟩
    refine TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_cons ?_
      (TempsHold_nil _)))) <;> ptget

end Deb2025_14524D
