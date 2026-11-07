/-
CVE-2023-27533 bookworm: 7.88.1（D0: series でこのパッチの直前まで）の `check_telnet_options` の上の P0。
-/
import DebBookworm2023_27533D1
open CC CC.Sep CC.HProp
open DebBookworm2023_27533_d0
open Case5C (RR)
open Case3C (Locs)
open Case4C (IsPtr)
open Deb2026_8924 (Arr3)

set_option maxRecDepth 100000

namespace DebBookworm2023_27533C

/-- 関数の入口（局所変数を割り当てる）。 -/
theorem entryD0 (ge : CGenv) (c : Ctx) (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env) (Pre : HProp)
    (Post : Val → HProp)
    (body : ∀ b1 b2, b1 ≠ b2 → Triple ge (FunctionEntry2 ge) f_check_telnet_options
      (LocalSt (envD1 b1 b2) [(_data, .Vptr c.dB c.dO)] (Pre ∗ Locs (LD b1 b2)))
      f_check_telnet_options.fn_body (RR Post Sep.Assn.no)) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_check_telnet_options) (ctoSpec c Pre Post) vs := by
  by_cases hvs : vs = [.Vptr c.dB c.dO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hnv : listNorepet (varNames f_check_telnet_options.fn_vars) := by decide
  have hnp : listNorepet (varNames f_check_telnet_options.fn_params) := by decide
  have hdisj : listDisjoint (varNames f_check_telnet_options.fn_params)
      (varNames f_check_telnet_options.fn_temps) := by decide
  let Pb : Sep.Assn := fun e le hp => ∃ bs : Block × Block, bs.1 ≠ bs.2 ∧
    LocalSt (envD1 bs.1 bs.2) [(_data, .Vptr c.dB c.dO)] (Pre ∗ Locs (LD bs.1 bs.2)) e le hp
  refine satisfies_internal ge (FunctionEntry2 ge) f_check_telnet_options _ _ Pb
    (fun m hp hf hpre hd hag => ?_) ?_
  · let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (tarray tschar 128))
    let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv (tarray tschar 256))
    have hav : AllocVariables ge.genv_cenv emptyEnv m f_check_telnet_options.fn_vars (envD1 a1.2 a2.2) a2.1 :=
      .cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _))
    obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
      (by
        intro v hv
        simp only [f_check_telnet_options, List.mem_cons, List.mem_nil_iff, or_false] at hv
        rcases hv with rfl | rfl <;> rw [hcenv] <;> decide)
      (Heap.union hp hf) hag
    have hL : Locs (LD a1.2 a2.2) hl := by
      have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
      rw [hcenv] at this
      exact this
    obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
    refine ⟨envD1 a1.2 a2.2,
      PTree.set _data (.Vptr c.dB c.dO) (createUndefTemps f_check_telnet_options.fn_temps),
      a2.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
      Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
    · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
      exact hagl
    · have hne : a1.2 ≠ a2.2 := by
        obtain ⟨h1, _, d1, rfl, x1, h2, _, d2, rfl, x2, _⟩ := hL
        exact Case3C.anyBytes_ne x1 x2 (by
          rw [Heap.disjoint_union_right] at d1; exact d1.1) (by decide) (by decide)
      refine ⟨(a1.2, a2.2), hne, rfl, ?_, ⟨hp, hl, dph, rfl, hpre.2, hL⟩⟩
      exact TempsHold_cons (PTree.gss _ _ _) (TempsHold_nil _)
  · refine Sep.triple_exists ge _ _ _ _ _ (fun bs => ?_)
    refine Case1C.triple_pure ge _ _ _ _ _ _ (fun hne => ?_)
    exact body bs.1 bs.2 hne

theorem body_d0 : f_check_telnet_options.fn_body =
    initSeq _option_keyword 128 0 128 (initSeq _option_arg 256 0 256 (dropS 384 f_check_telnet_options.fn_body)) := rfl

abbrev LQ1 (c : Ctx) : List (Ident × Val) :=
  [(_result, .Vint (Integers.Int.repr 0)), (_tn, .Vptr c.tnB c.tnO), (_data, .Vptr c.dB c.dO)]
abbrev LL1 (c : Ctx) (h : Val) : List (Ident × Val) := (_head, h) :: LQ1 c

abbrev slTyD : Ty := tptr (Ty.Tstruct _curl_slist noattr)
abbrev msnTyD : List Ty := [tptr tschar, tulong, tptr tschar, tptr tschar]

/-! ## P0u（ユーザー名） -/

/-- `curl_msnprintf` が書いたあと: `option_arg` の `5 + j` 番目がユーザー名の `j` 番目。 -/
abbrev W1D0 (c : Ctx) (u : SU) (b1 b2 : Block) : HProp :=
  Hs c c.vars c.pref (XU c u) ∗ (anyBytes .Freeable b1 0 128 ∗ (Arr3 b2 (5 + u.j) (.Vint (u.byte u.j)) ∗ emp))
abbrev W2D0 (c : Ctx) (u : SU) (nbB : Block) (nbO : P) (w : Integers.Int) (b1 b2 : Block) : HProp :=
  Hs c c.vars c.pref (XU c u ∗ NB c nbB nbO w) ∗ Locs (LD b1 b2)
abbrev W3D0 (c : Ctx) (u : SU) (nbB : Block) (nbO : P) (w : Integers.Int) (b1 b2 : Block) : HProp :=
  Hs c (.Vptr nbB nbO) (Integers.Int.repr 1) (XU c u ∗ NB c nbB nbO w) ∗ Locs (LD b1 b2)

set_option maxHeartbeats 4000000 in
theorem p0u_body_d0 (ge : CGenv) (c : Ctx) (u : SU) (nbB : Block) (nbO : P) (w : Integers.Int)
    (b1 b2 : Block) (hne : b1 ≠ b2)
    (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hP : Ptrs c) (hv : IsPtr c.vars) (hu : SUok c u) (hopt : c.optV = Deb2026_3805C.nullV)
    (fdM : FunDef) (sm : Callee ge _curl_msnprintf fdM)
    (tM : typeOfFundef fdM = .Tfunction msnTyD tint cc_default)
    (litB : Block) (hlit : Genv.findSymbol ge.genv_genv ___stringlit_1 = some litB)
    (hM : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdM
      (specA msnTyD tint [.Vptr b2 Integers.Ptrofs.zero, .Vlong (r64 256), .Vptr litB Integers.Ptrofs.zero,
          .Vptr u.sB u.sO]
        (WUD c u b1 b2) (W1D0 c u b1 b2) none) vs)
    (fdA : FunDef) (sa : Callee ge _curl_slist_append fdA)
    (tA : typeOfFundef fdA = .Tfunction [slTyD, tptr tschar] slTyD cc_default)
    (hA : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdA
      (specA [slTyD, tptr tschar] slTyD [c.vars, .Vptr b2 Integers.Ptrofs.zero]
        (W1D0 c u b1 b2) (W2D0 c u nbB nbO w b1 b2) (some (.Vptr nbB nbO))) vs) :
    Triple ge (FunctionEntry2 ge) f_check_telnet_options
      (LocalSt (envD1 b1 b2) [(_data, .Vptr c.dB c.dO)] (WUD c u b1 b2))
      f_check_telnet_options.fn_body
      (RR (post0 c (.Vptr nbB nbO) (XU c u ∗ NB c nbB nbO w)) Sep.Assn.no) := by
  have hNB : IsPtr (.Vptr nbB nbO) := Or.inl ⟨_, _, rfl⟩
  rw [body_d0]
  refine initD _ _ _ b1 b2 _ _ _ _ ?_
  sq
  · sset (.Vptr c.tnB c.tnO)
    exact ev_tn hcenv (Hs_loads hpr hP hv hH hag) (hT.get (by temps_get))
  sq
  · sset (.Vptr c.cnB c.cnO)
    exact ev_conn hcenv (Hs_loads hpr hP hv hH hag) (hT.get (by temps_get))
  sq
  · sset (.Vint (Integers.Int.repr 0))
    exact EvalExpr.Econst_int _ _
  sq
  · sq
    · sset (.Vptr u.auB u.auO)
      rw [← hu.au]
      exact ev_au hcenv (Hs_loads hpr hP hv hH hag) (hT.get (by temps_get))
    refine triple_if_local ge _ _ _ _ _ _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, tv (.Vptr u.auB u.auO), boolVal_ptrc (XU_valid hpn hH hag)⟩) ?_
    rw [if_pos rfl]
    sq
    · sq
      · sset (.Vptr u.sB u.sO)
        rw [← hu.user]
        exact ev_user hcenv (Hs_loads hpr hP hv hH hag) (hT.get (id := _conn) (by temps_get))
      · exact callA_none ge _ _ _ _ _ _ _ _ _ _ _ sm.b fdM hM sm.fp tM rfl
          (fun _ _ _ => eval_callee_global (by envgetD) sm.sym rfl)
          (fun le m hT => .cons _ _ _ _ _ _ _ (ev_arr (envD1_arg b1 b2)) rfl
            (.cons _ _ _ _ _ _ _ (EvalExpr.Esizeof _ _) rfl
              (.cons _ _ _ _ _ _ _ (eval_callee_global (by envgetD) hlit rfl) rfl
                (.cons _ _ _ _ _ _ _ (tv (.Vptr u.sB u.sO)) rfl .nil))))
    sq
    · sq
      · sq
        · sset c.vars
          exact ev_vars hcenv (Hs_loads hpr hP hv hH hag) (hT.get (id := _tn) (by temps_get))
        · exact callA_some ge _ _ _ _ _ _ _ _ _ _ _ _ _ sa.b fdA hA sa.fp tA rfl
            (fun _ _ _ => eval_callee_global (by envgetD) sa.sym rfl)
            (fun le m hT => .cons _ _ _ _ _ _ _ (tv c.vars) (Case4C.cast_ptr hv _ _ _)
              (.cons _ _ _ _ _ _ _ (ev_arr (envD1_arg b1 b2)) rfl .nil))
      · sset (.Vptr nbB nbO)
        exact tv (.Vptr nbB nbO)
    sq
    · exact if_f_skip ge _ _ _ _ _ _ _
        (fun le m hp hT hH hag => ⟨_, EvalExpr.Eunop _ _ _ _ _ (tv (.Vptr nbB nbO))
          (notbool_p _ (NB_valid hpn hH hag)), rfl⟩)
    sq
    · exact store_vars ge _ _ _ _ c _ (.Vptr nbB nbO) _ _ _ _ _ hpw rfl
        (fun le m hT => lv_vars hcenv (hT.get (id := _tn) (by temps_get)))
        (fun le m hT => ⟨_, tv (.Vptr nbB nbO), rfl⟩)
    · exact store_pref ge _ _ _ _ c _ _ (Integers.Int.repr 1) _ _ _ _ hpw rfl
        (fun le m hT => lv_pref hcenv (hT.get (id := _tn) (by temps_get)))
        (fun le m hT => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)
  refine triple_seq_fwd _ _ _ _ (LocalSt (envD1 b1 b2) (LQ1 c) (W3D0 c u nbB nbO w b1 b2)) _ _ _ ?_ ?_
  · sq
    · sset Deb2026_3805C.nullV
      rw [← hopt]
      exact ev_opts hcenv (Hs_loads hpr hP hNB hH hag) (hT.get (by temps_get))
    refine tmono ge _ _ (l' := LL1 c Deb2026_3805C.nullV) (by subt) ?_
    refine loop_zero _ _ _ _ _ _ _ ?_
    refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
    refine triple_if_local ge _ _ _ _ _ _ false _ _ _
      (fun le m hp hT hH hag => ⟨_, tv Deb2026_3805C.nullV, rfl⟩) ?_
    rw [if_neg Bool.false_ne_true]
    exact triple_conseq ge _ _ (Sep.triple_break ge _ _ _) (fun _ _ _ x => x)
      (fun _ _ _ x => x) (fun _ _ _ x => lmono (by subt) x) (fun _ _ _ x => x) (fun _ _ x => x)
  sq
  · exact if_f_skip ge _ _ _ _ _ _ _
      (fun le m hp hT hH hag => ⟨_, tv (.Vint (Integers.Int.repr 0)), rfl⟩)
  exact retD1t ge _ _ hcenv b1 b2 hne _ _ _ _ (by temps_get) rfl (fun hp hH => ⟨rfl, hH⟩)

/-- **D0（P0u）**: 7.88.1 は、8 ビット目の立ったバイトを持つユーザー名でも、`option_arg` の `5 + j` 番目がそのバイトのまま
`curl_slist_append` を呼び、返ったリストを `tn->telnet_vars` に入れ、`tn->us_preferred[39]` を 1 にして 0 を返す。 -/
theorem P0u_D0 (ge : CGenv) (c : Ctx) (u : SU) (nbB : Block) (nbO : P) (w : Integers.Int)
    (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hP : Ptrs c) (hv : IsPtr c.vars) (hu : SUok c u) (_hj : u.j < 250)
    (hopt : c.optV = Deb2026_3805C.nullV)
    (fdM : FunDef) (sm : Callee ge _curl_msnprintf fdM)
    (tM : typeOfFundef fdM = .Tfunction msnTyD tint cc_default)
    (litB : Block) (hlit : Genv.findSymbol ge.genv_genv ___stringlit_1 = some litB)
    (hM : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdM
      (specA msnTyD tint [.Vptr b2 Integers.Ptrofs.zero, .Vlong (r64 256), .Vptr litB Integers.Ptrofs.zero,
          .Vptr u.sB u.sO]
        (WUD c u b1 b2) (W1D0 c u b1 b2) none) vs)
    (fdA : FunDef) (sa : Callee ge _curl_slist_append fdA)
    (tA : typeOfFundef fdA = .Tfunction [slTyD, tptr tschar] slTyD cc_default)
    (hA : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdA
      (specA [slTyD, tptr tschar] slTyD [c.vars, .Vptr b2 Integers.Ptrofs.zero]
        (W1D0 c u b1 b2) (W2D0 c u nbB nbO w b1 b2) (some (.Vptr nbB nbO))) vs) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_check_telnet_options)
      (ctoSpec c (Hs c c.vars c.pref (XU c u)) (post0 c (.Vptr nbB nbO) (XU c u ∗ NB c nbB nbO w))) vs :=
  entryD0 ge c hcenv _ _ (fun b1 b2 hne =>
    p0u_body_d0 ge c u nbB nbO w b1 b2 hne hcenv hpr hpn hpw hP hv hu hopt fdM sm tM litB hlit (hM b1 b2)
      fdA sa tA (hA b1 b2)) vs

/-! ## P0o（オプション） -/

abbrev W2OD (c : Ctx) (s : SOD) (nbB : Block) (nbO : P) (w : Integers.Int) (b1 b2 : Block) : HProp :=
  Hs c c.vars c.pref (XD c s ∗ NB c nbB nbO w) ∗ Locs (LD b1 b2)
abbrev W3OD (c : Ctx) (s : SOD) (nbB : Block) (nbO : P) (w : Integers.Int) (b1 b2 : Block) : HProp :=
  Hs c (.Vptr nbB nbO) (Integers.Int.repr 1) (XD c s ∗ NB c nbB nbO w) ∗ Locs (LD b1 b2)

abbrev scTy : List Ty := [tptr tschar, tptr tschar]

set_option maxHeartbeats 8000000 in
theorem p0o_body_d0 (ge : CGenv) (c : Ctx) (s : SOD) (nbB : Block) (nbO : P) (w : Integers.Int)
    (b1 b2 : Block) (hne : b1 ≠ b2)
    (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hP : Ptrs c) (hv : IsPtr c.vars) (hs : SODok c s)
    (fdF : FunDef) (sf : Callee ge _sscanf fdF)
    (tF : typeOfFundef fdF = .Tfunction sscanfTy tint cc_default)
    (litF : Block) (hlitF : Genv.findSymbol ge.genv_genv ___stringlit_2 = some litF)
    (hF : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdF
      (specA sscanfTy tint (sscanfArgs s litF b1 b2) (WOD c s b1 b2) (WOA c s b1 b2)
        (some (.Vint (Integers.Int.repr 2)))) vs)
    (fdK : FunDef) (sk : Callee ge _Curl_strcasecompare fdK)
    (tK : typeOfFundef fdK = .Tfunction scTy tint cc_default)
    (lit3 lit4 lit5 : Block)
    (hl3 : Genv.findSymbol ge.genv_genv ___stringlit_3 = some lit3)
    (hl4 : Genv.findSymbol ge.genv_genv ___stringlit_4 = some lit4)
    (hl5 : Genv.findSymbol ge.genv_genv ___stringlit_5 = some lit5)
    (hK3 : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdK
      (specA scTy tint [.Vptr b1 Integers.Ptrofs.zero, .Vptr lit3 Integers.Ptrofs.zero]
        (WOA c s b1 b2) (WOA c s b1 b2) (some (.Vint (Integers.Int.repr 0)))) vs)
    (hK4 : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdK
      (specA scTy tint [.Vptr b1 Integers.Ptrofs.zero, .Vptr lit4 Integers.Ptrofs.zero]
        (WOA c s b1 b2) (WOA c s b1 b2) (some (.Vint (Integers.Int.repr 0)))) vs)
    (hK5 : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdK
      (specA scTy tint [.Vptr b1 Integers.Ptrofs.zero, .Vptr lit5 Integers.Ptrofs.zero]
        (WOA c s b1 b2) (WOA c s b1 b2) (some (.Vint (Integers.Int.repr 1)))) vs)
    (fdA : FunDef) (sa : Callee ge _curl_slist_append fdA)
    (tA : typeOfFundef fdA = .Tfunction [slTyD, tptr tschar] slTyD cc_default)
    (hA : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdA
      (specA [slTyD, tptr tschar] slTyD [c.vars, .Vptr b2 Integers.Ptrofs.zero]
        (WOA c s b1 b2) (W2OD c s nbB nbO w b1 b2) (some (.Vptr nbB nbO))) vs) :
    Triple ge (FunctionEntry2 ge) f_check_telnet_options
      (LocalSt (envD1 b1 b2) [(_data, .Vptr c.dB c.dO)] (WOD c s b1 b2))
      f_check_telnet_options.fn_body
      (RR (post0 c (.Vptr nbB nbO) (XD c s ∗ NB c nbB nbO w)) Sep.Assn.no) := by
  have hNB : IsPtr (.Vptr nbB nbO) := Or.inl ⟨_, _, rfl⟩
  have hN := hs.oV
  rw [body_d0]
  refine initD _ _ _ b1 b2 _ _ _ _ ?_
  sq
  · sset (.Vptr c.tnB c.tnO)
    exact ev_tn hcenv (Hs_loads hpr hP hv hH hag) (hT.get (by temps_get))
  sq
  · sset (.Vptr c.cnB c.cnO)
    exact ev_conn hcenv (Hs_loads hpr hP hv hH hag) (hT.get (by temps_get))
  sq
  · sset (.Vint (Integers.Int.repr 0))
    exact EvalExpr.Econst_int _ _
  sq
  · sq
    · sset Deb2026_3805C.nullV
      rw [← hs.au]
      exact ev_au hcenv (Hs_loads hpr hP hv hH hag) (hT.get (by temps_get))
    · exact if_f_skip ge _ _ _ _ _ _ _
        (fun le m hp hT hH hag => ⟨_, tv Deb2026_3805C.nullV, rfl⟩)
  refine triple_seq_fwd _ _ _ _ (LocalSt (envD1 b1 b2) (LQ1 c) (W3OD c s nbB nbO w b1 b2)) _ _ _ ?_ ?_
  · sq
    · sset (.Vptr s.nd.nB s.nd.nO)
      rw [← hs.opt]
      exact ev_opts hcenv (Hs_loads hpr hP hv hH hag) (hT.get (by temps_get))
    refine tmono ge _ _ (l' := LL1 c (.Vptr s.nd.nB s.nd.nO)) (by subt) ?_
    refine loop_one _ _ _ _ (LocalSt (envD1 b1 b2) (LL1 c Deb2026_3805C.nullV) (W3OD c s nbB nbO w b1 b2))
      (LocalSt (envD1 b1 b2) (LL1 c (.Vptr s.nd.nB s.nd.nO)) (W3OD c s nbB nbO w b1 b2)) _ _ _ ?h1 ?h2 ?h0
    case h1 =>
      sq
      · exact if_t_skip ge _ _ _ _ _ _ _
          (fun le m hp hT hH hag => ⟨_, tv (.Vptr s.nd.nB s.nd.nO), boolVal_p _ (XN_valid hpn hH hag)⟩)
      refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
      sq
      · sq
        · sset s.nd.oV
          exact ev_sdata (b := s.nd.nB) (o := s.nd.nO) hcenv (hT.get (by temps_get)) (XN_load hpr hN hH hag).1
        · exact callA_some ge _ _ _ _ _ _ _ _ _ _ _ _ _ sf.b fdF hF sf.fp tF rfl
            (fun _ _ _ => eval_callee_global (by envgetD) sf.sym rfl)
            (fun le m hT => .cons _ _ _ _ _ _ _ (tv s.nd.oV) (Case4C.cast_ptr hN _ _ _)
              (.cons _ _ _ _ _ _ _ (eval_callee_global (by envgetD) hlitF rfl) rfl
                (.cons _ _ _ _ _ _ _ (ev_arr (envD1_kw b1 b2)) rfl
                  (.cons _ _ _ _ _ _ _ (ev_arr (envD1_arg b1 b2)) rfl .nil))))
      refine triple_if_local ge _ _ _ _ _ _ true _ _ _
        (fun le m hp hT hH hag => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (tv (.Vint (Integers.Int.repr 2)))
          (EvalExpr.Econst_int _ _) rfl, rfl⟩) ?_
      rw [if_pos rfl]
      -- TTYPE
      sq
      · sq
        · exact callA_some ge _ _ _ _ _ _ _ _ _ _ _ _ _ sk.b fdK hK3 sk.fp tK rfl
            (fun _ _ _ => eval_callee_global (by envgetD) sk.sym rfl)
            (fun le m hT => .cons _ _ _ _ _ _ _ (ev_arr (envD1_kw b1 b2)) rfl
              (.cons _ _ _ _ _ _ _ (eval_callee_global (by envgetD) hl3 rfl) rfl .nil))
        · exact if_f_skip ge _ _ _ _ _ _ _
            (fun le m hp hT hH hag => ⟨_, tv (.Vint (Integers.Int.repr 0)), rfl⟩)
      -- XDISPLOC
      sq
      · sq
        · exact callA_some ge _ _ _ _ _ _ _ _ _ _ _ _ _ sk.b fdK hK4 sk.fp tK rfl
            (fun _ _ _ => eval_callee_global (by envgetD) sk.sym rfl)
            (fun le m hT => .cons _ _ _ _ _ _ _ (ev_arr (envD1_kw b1 b2)) rfl
              (.cons _ _ _ _ _ _ _ (eval_callee_global (by envgetD) hl4 rfl) rfl .nil))
        · exact if_f_skip ge _ _ _ _ _ _ _
            (fun le m hp hT hH hag => ⟨_, tv (.Vint (Integers.Int.repr 0)), rfl⟩)
      -- NEW_ENV
      refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
      sq
      · exact callA_some ge _ _ _ _ _ _ _ _ _ _ _ _ _ sk.b fdK hK5 sk.fp tK rfl
          (fun _ _ _ => eval_callee_global (by envgetD) sk.sym rfl)
          (fun le m hT => .cons _ _ _ _ _ _ _ (ev_arr (envD1_kw b1 b2)) rfl
            (.cons _ _ _ _ _ _ _ (eval_callee_global (by envgetD) hl5 rfl) rfl .nil))
      refine triple_if_local ge _ _ _ _ _ _ true _ _ _
        (fun le m hp hT hH hag => ⟨_, tv (.Vint (Integers.Int.repr 1)), rfl⟩) ?_
      rw [if_pos rfl]
      sq
      · sq
        · sq
          · sset c.vars
            exact ev_vars hcenv (Hs_loads hpr hP hv hH hag) (hT.get (id := _tn) (by temps_get))
          · exact callA_some ge _ _ _ _ _ _ _ _ _ _ _ _ _ sa.b fdA hA sa.fp tA rfl
              (fun _ _ _ => eval_callee_global (by envgetD) sa.sym rfl)
              (fun le m hT => .cons _ _ _ _ _ _ _ (tv c.vars) (Case4C.cast_ptr hv _ _ _)
                (.cons _ _ _ _ _ _ _ (ev_arr (envD1_arg b1 b2)) rfl .nil))
        · sset (.Vptr nbB nbO)
          exact tv (.Vptr nbB nbO)
      sq
      · exact if_f_skip ge _ _ _ _ _ _ _
          (fun le m hp hT hH hag => ⟨_, EvalExpr.Eunop _ _ _ _ _ (tv (.Vptr nbB nbO))
            (notbool_p _ (NB_valid hpn hH hag)), rfl⟩)
      sq
      · exact store_vars ge _ _ _ _ c _ (.Vptr nbB nbO) _ _ _ _ _ hpw rfl
          (fun le m hT => lv_vars hcenv (hT.get (id := _tn) (by temps_get)))
          (fun le m hT => ⟨_, tv (.Vptr nbB nbO), rfl⟩)
      sq
      · exact store_pref ge _ _ _ _ c _ _ (Integers.Int.repr 1) _ _ _ _ hpw rfl
          (fun le m hT => lv_pref hcenv (hT.get (id := _tn) (by temps_get)))
          (fun le m hT => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)
      exact triple_conseq ge _ _ (Sep.triple_continue ge _ _ _) (fun _ _ _ x => x)
        (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => lmono (by subt) x) (fun _ _ x => x)
    case h2 =>
      refine triple_fallthrough ge _ _ _
        (LocalSt (envD1 b1 b2) (setLocal (LL1 c (.Vptr s.nd.nB s.nd.nO)) _head Deb2026_3805C.nullV)
          (W3OD c s nbB nbO w b1 b2))
        _ _ ?_ (fun _ _ _ x => lmono (by subt) x)
      sset Deb2026_3805C.nullV
      exact ev_snext (b := s.nd.nB) (o := s.nd.nO) hcenv (hT.get (by temps_get)) (XN_next2 hpr hH hag)
    case h0 =>
      refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
      refine triple_if_local ge _ _ _ _ _ _ false _ _ _
        (fun le m hp hT hH hag => ⟨_, tv Deb2026_3805C.nullV, rfl⟩) ?_
      rw [if_neg Bool.false_ne_true]
      exact triple_conseq ge _ _ (Sep.triple_break ge _ _ _) (fun _ _ _ x => x)
        (fun _ _ _ x => x) (fun _ _ _ x => lmono (by subt) x) (fun _ _ _ x => x) (fun _ _ x => x)
  sq
  · exact if_f_skip ge _ _ _ _ _ _ _
      (fun le m hp hT hH hag => ⟨_, tv (.Vint (Integers.Int.repr 0)), rfl⟩)
  exact retD1t ge _ _ hcenv b1 b2 hne _ _ _ _ (by temps_get) rfl (fun hp hH => ⟨rfl, hH⟩)

/-- **D0（P0o）**: 7.88.1 は、`NEW_ENV` のオプションの引数の `j` 番目が 8 ビット目の立ったバイトでも、`option_arg` がその文字列のまま
`curl_slist_append` を呼び、返ったリストを `tn->telnet_vars` に入れ、`tn->us_preferred[39]` を 1 にして 0 を返す。 -/
theorem P0o_D0 (ge : CGenv) (c : Ctx) (s : SOD) (nbB : Block) (nbO : P) (w : Integers.Int)
    (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hP : Ptrs c) (hv : IsPtr c.vars) (hs : SODok c s)
    (fdF : FunDef) (sf : Callee ge _sscanf fdF)
    (tF : typeOfFundef fdF = .Tfunction sscanfTy tint cc_default)
    (litF : Block) (hlitF : Genv.findSymbol ge.genv_genv ___stringlit_2 = some litF)
    (hF : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdF
      (specA sscanfTy tint (sscanfArgs s litF b1 b2) (WOD c s b1 b2) (WOA c s b1 b2)
        (some (.Vint (Integers.Int.repr 2)))) vs)
    (fdK : FunDef) (sk : Callee ge _Curl_strcasecompare fdK)
    (tK : typeOfFundef fdK = .Tfunction scTy tint cc_default)
    (lit3 lit4 lit5 : Block)
    (hl3 : Genv.findSymbol ge.genv_genv ___stringlit_3 = some lit3)
    (hl4 : Genv.findSymbol ge.genv_genv ___stringlit_4 = some lit4)
    (hl5 : Genv.findSymbol ge.genv_genv ___stringlit_5 = some lit5)
    (hK3 : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdK
      (specA scTy tint [.Vptr b1 Integers.Ptrofs.zero, .Vptr lit3 Integers.Ptrofs.zero]
        (WOA c s b1 b2) (WOA c s b1 b2) (some (.Vint (Integers.Int.repr 0)))) vs)
    (hK4 : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdK
      (specA scTy tint [.Vptr b1 Integers.Ptrofs.zero, .Vptr lit4 Integers.Ptrofs.zero]
        (WOA c s b1 b2) (WOA c s b1 b2) (some (.Vint (Integers.Int.repr 0)))) vs)
    (hK5 : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdK
      (specA scTy tint [.Vptr b1 Integers.Ptrofs.zero, .Vptr lit5 Integers.Ptrofs.zero]
        (WOA c s b1 b2) (WOA c s b1 b2) (some (.Vint (Integers.Int.repr 1)))) vs)
    (fdA : FunDef) (sa : Callee ge _curl_slist_append fdA)
    (tA : typeOfFundef fdA = .Tfunction [slTyD, tptr tschar] slTyD cc_default)
    (hA : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdA
      (specA [slTyD, tptr tschar] slTyD [c.vars, .Vptr b2 Integers.Ptrofs.zero]
        (WOA c s b1 b2) (W2OD c s nbB nbO w b1 b2) (some (.Vptr nbB nbO))) vs) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_check_telnet_options)
      (ctoSpec c (Hs c c.vars c.pref (XD c s)) (post0 c (.Vptr nbB nbO) (XD c s ∗ NB c nbB nbO w))) vs :=
  entryD0 ge c hcenv _ _ (fun b1 b2 hne =>
    p0o_body_d0 ge c s nbB nbO w b1 b2 hne hcenv hpr hpn hpw hP hv hs fdF sf tF litF hlitF (hF b1 b2)
      fdK sk tK lit3 lit4 lit5 hl3 hl4 hl5 (hK3 b1 b2) (hK4 b1 b2) (hK5 b1 b2) fdA sa tA (hA b1 b2)) vs

end DebBookworm2023_27533C
