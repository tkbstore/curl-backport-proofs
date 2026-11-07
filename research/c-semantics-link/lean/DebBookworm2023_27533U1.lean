/-
CVE-2023-27533 bookworm: 上流の修正後（U1、curl 538b1e79a6）の `check_telnet_options` の上の P1。
-/
import DebBookworm2023_27533Common
open CC CC.Sep CC.HProp
open DebBookworm2023_27533_u1
open Case5C (RR)
open Case3C (Locs)
open Case4C (IsPtr)

set_option maxRecDepth 20000

namespace DebBookworm2023_27533C

/-- 局所変数 `buffer`・`p` の環境。 -/
def envU1 (b1 b2 : Block) : Env :=
  (emptyEnv.set _buffer (b1, tarray tschar 256)).set _p (b2, tptr tschar)

macro "envget" : tactic =>
  `(tactic| (unfold envU1; repeat (first
      | exact PTree.gss _ _ _
      | exact PTree.gempty _
      | refine (PTree.gso _ _ _ _ (by decide)).trans ?_)))

abbrev LU (b1 b2 : Block) : List (Block × Nat) := [(b1, 256), (b2, 8)]

theorem blocks_envU1 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (b1 b2 : Block) :
    blocksOfEnv ge.genv_cenv (envU1 b1 b2) = [(b2, 0, 8), (b1, 0, 256)] := by
  rw [hcenv]; rfl

/-- 局所変数を解放する定数の `return`。 -/
theorem retU1 (ge fe f) (hcenv : ge.genv_cenv = prog.prog_comp_env) (b1 b2 : Block) (hne : b1 ≠ b2)
    (l : List (Ident × Val)) (Hk : HProp) (n : Integers.Int) (v' : Val) (Ret : Val → HProp)
    (hcast : ∀ m, Cop.semCast (.Vint n) tint f.fn_return m = some v')
    (hret : ∀ hp, Hk hp → Ret v' hp) :
    Triple ge fe f (LocalSt (envU1 b1 b2) l (Hk ∗ Locs (LU b1 b2)))
      (.Sreturn (some (.Econst_int n tint)))
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := Ret } := by
  refine Case3C.ret_locs ge _ _ (envU1 b1 b2) _ Hk (LU b1 b2) _ (.Vint n) v' _
    (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) hcast ?_ ?_ hret
  · rw [blocks_envU1 ge hcenv]
    intro x hx'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
    rcases hx' with rfl | rfl
    · exact ⟨b2, 8, rfl, by simp⟩
    · exact ⟨b1, 256, rfl, by simp⟩
  · rw [blocks_envU1 ge hcenv]
    simp [Ne.symm hne]

/-- 関数の入口（局所変数を割り当てる）。 -/
theorem entryU1 (ge : CGenv) (c : Ctx) (hcenv : ge.genv_cenv = prog.prog_comp_env) (Pre : HProp)
    (Post : Val → HProp)
    (body : ∀ b1 b2, b1 ≠ b2 → Triple ge (FunctionEntry2 ge) f_check_telnet_options
      (LocalSt (envU1 b1 b2) [(_data, .Vptr c.dB c.dO)] (Pre ∗ Locs (LU b1 b2)))
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
    LocalSt (envU1 bs.1 bs.2) [(_data, .Vptr c.dB c.dO)] (Pre ∗ Locs (LU bs.1 bs.2)) e le hp
  refine satisfies_internal ge (FunctionEntry2 ge) f_check_telnet_options _ _ Pb
    (fun m hp hf hpre hd hag => ?_) ?_
  · let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (tarray tschar 256))
    let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv (tptr tschar))
    have hav : AllocVariables ge.genv_cenv emptyEnv m f_check_telnet_options.fn_vars (envU1 a1.2 a2.2) a2.1 :=
      .cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _))
    obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
      (by
        intro v hv
        simp only [f_check_telnet_options, List.mem_cons, List.mem_nil_iff, or_false] at hv
        rcases hv with rfl | rfl <;> rw [hcenv] <;> decide)
      (Heap.union hp hf) hag
    have hL : Locs (LU a1.2 a2.2) hl := by
      have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
      rw [hcenv] at this
      exact this
    obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
    refine ⟨envU1 a1.2 a2.2,
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

/-! ## P1u（ユーザー名） -/

abbrev WU (c : Ctx) (u : SU) (b1 b2 : Block) : HProp :=
  Hs c c.vars c.pref (XU c u) ∗ Locs (LU b1 b2)

abbrev tyEasy : Ty := tptr (Ty.Tstruct _Curl_easy noattr)

theorem boolVal_ptrc {b : Block} {o : P} {m : Mem}
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.boolVal (.Vptr b o) (tptr tschar) m = some true :=
  Deb2025_14524.boolVal_ptr _ rfl hv

set_option maxHeartbeats 4000000 in
theorem p1u_body (ge : CGenv) (c : Ctx) (u : SU) (b1 b2 : Block) (hne : b1 ≠ b2)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hP : Ptrs c) (hv : IsPtr c.vars) (hu : SUok c u)
    (sin : Callee ge _str_is_nonascii (.Internal f_str_is_nonascii))
    (fdS : FunDef) (sl : Callee ge _strlen fdS)
    (tS : typeOfFundef fdS = .Tfunction [tptr tschar] tulong cc_default)
    (hS : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdS
      (strlenSpec (.Vptr u.sB u.sO) u.n (WU c u b1 b2)) vs) :
    Triple ge (FunctionEntry2 ge) f_check_telnet_options
      (LocalSt (envU1 b1 b2) [(_data, .Vptr c.dB c.dO)] (WU c u b1 b2))
      f_check_telnet_options.fn_body (RR (post1 43 (Hs c c.vars c.pref (XU c u))) Sep.Assn.no) := by
  have hL : ∀ hp m, WU c u b1 b2 hp → Heap.Agrees hp m → Loads c c.vars m :=
    fun hp m hH hag => Hs_loads hpr hP hv hH hag
  sq
  · refine triple_set_local_fwd ge _ _ _ _ _ _ _ (.Vptr c.tnB c.tnO) ?_
    intro le m hp hT hH hag
    exact ev_tn hcenv (hL hp m hH hag) (hT.get (by temps_get))
  sq
  · refine triple_set_local_fwd ge _ _ _ _ _ _ _ (.Vint (Integers.Int.repr 0)) ?_
    intro le m hp hT hH hag
    exact EvalExpr.Econst_int _ _
  refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  sq
  · refine triple_set_local_fwd ge _ _ _ _ _ _ _ (.Vptr u.auB u.auO) ?_
    intro le m hp hT hH hag
    rw [← hu.au]
    exact ev_au hcenv (hL hp m hH hag) (hT.get (by temps_get))
  refine triple_if_local ge _ _ _ _ _ _ true _ _ _
    (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr u.auB u.auO) (hT.get (by temps_get)),
      boolVal_ptrc (XU_valid hpn hH hag)⟩) ?_
  rw [if_pos rfl]
  refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  sq
  · sq
    · refine triple_set_local_fwd ge _ _ _ _ _ _ _ (.Vptr c.cnB c.cnO) ?_
      intro le m hp hT hH hag
      exact ev_conn hcenv (hL hp m hH hag) (hT.get (by temps_get))
    sq
    · refine triple_set_local_fwd ge _ _ _ _ _ _ _ (.Vptr u.sB u.sO) ?_
      intro le m hp hT hH hag
      rw [← hu.user]
      exact ev_user hcenv (hL hp m hH hag) (hT.get (by temps_get))
    · refine Deb2025_14524.callS_some ge _ _ (sinSpec (.Vptr u.sB u.sO) (WU c u b1 b2)) _ _
        (.Vint (Integers.Int.repr 1)) _ _ _ _ _ [.Vptr u.sB u.sO] sin.b _
        (sin_sat ge u.sB u.sO u.byte u.j u.n _ hu.hj hu.hn hu.hhi (XU_load hpr) fdS sl tS hS)
        sin.fp rfl rfl
        (fun _ _ _ => eval_callee_global (by envget) sin.sym rfl)
        (fun le m hT => .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ (.Vptr u.sB u.sO) (hT.get (by temps_get)))
          rfl .nil)
        (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h)
  refine triple_if_local ge _ _ _ _ _ _ true _ _ _
    (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 1)) (hT.get (by temps_get)), rfl⟩) ?_
  rw [if_pos rfl]
  exact retU1 ge _ _ hcenv b1 b2 hne _ _ _ _ _ (fun _ => rfl) (fun hp hH => ⟨rfl, hH⟩)

/-! ## P1o（オプション） -/

/-- 局所変数を解放する `return result;`。 -/
theorem retU1t (ge fe f) (hcenv : ge.genv_cenv = prog.prog_comp_env) (b1 b2 : Block) (hne : b1 ≠ b2)
    (l : List (Ident × Val)) (Hk : HProp) (n : Integers.Int) (Ret : Val → HProp)
    (hl : (_result, .Vint n) ∈ l) (hf : f.fn_return = tint)
    (hret : ∀ hp, Hk hp → Ret (.Vint n) hp) :
    Triple ge fe f (LocalSt (envU1 b1 b2) l (Hk ∗ Locs (LU b1 b2)))
      (.Sreturn (some (.Etempvar _result tint)))
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := Ret } := by
  refine Case3C.ret_locs ge _ _ (envU1 b1 b2) _ Hk (LU b1 b2) _ (.Vint n) (.Vint n) _
    (fun le _ _ hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get hl)) (fun m => ?_) ?_ ?_ hret
  · rw [hf]; rfl
  · rw [blocks_envU1 ge hcenv]
    intro x hx'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
    rcases hx' with rfl | rfl
    · exact ⟨b2, 8, rfl, by simp⟩
    · exact ⟨b1, 256, rfl, by simp⟩
  · rw [blocks_envU1 ge hcenv]
    simp [Ne.symm hne]

abbrev WO (c : Ctx) (s : SOU) (b1 b2 : Block) : HProp :=
  Hs c c.vars c.pref (XOU c s) ∗ Locs (LU b1 b2)

abbrev LQ (c : Ctx) : List (Ident × Val) :=
  [(_result, .Vint (Integers.Int.repr 0)), (_tn, .Vptr c.tnB c.tnO), (_data, .Vptr c.dB c.dO)]
abbrev LL (c : Ctx) (h : Val) : List (Ident × Val) := (_head, h) :: LQ c

def olenV (a b : P) : Val :=
  Val.Vptrofs (Integers.MI.divs (Integers.Ptrofs.sub a b) (Integers.Ptrofs.repr 1))

theorem sub_ptr (ce : CompositeEnv) (B : Block) (a b : P) (m : Mem) :
    Cop.semBinaryOperation ce .Osub (.Vptr B a) (tptr tschar) (.Vptr B b) (tptr tschar) m
      = some (olenV a b) := by
  have h : Cop.semSub ce (.Vptr B a) (tptr tschar) (.Vptr B b) (tptr tschar) m = some (olenV a b) := by
    unfold Cop.semSub
    show (if B = B then _ else none) = _
    rw [if_pos rfl]
    rfl
  simpa [Cop.semBinaryOperation] using h

set_option maxHeartbeats 4000000 in
theorem p1o_body (ge : CGenv) (c : Ctx) (s : SOU) (b1 b2 : Block) (hne : b1 ≠ b2)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hP : Ptrs c) (hv : IsPtr c.vars) (hs : SOUok c s)
    (sin : Callee ge _str_is_nonascii (.Internal f_str_is_nonascii))
    (fdS : FunDef) (sl : Callee ge _strlen fdS)
    (tS : typeOfFundef fdS = .Tfunction [tptr tschar] tulong cc_default)
    (hS : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdS
      (strlenSpec (.Vptr s.oB (nextO s.sepO)) s.n (WO c s b1 b2)) vs)
    (fdC : FunDef) (sc : Callee ge _strchr fdC)
    (tC : typeOfFundef fdC = .Tfunction [tptr tschar, tint] (tptr tschar) cc_default)
    (hC : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdC
      (specA [tptr tschar, tint] (tptr tschar) [.Vptr s.oB s.oO, .Vint (Integers.Int.repr 61)]
        (WO c s b1 b2) (WO c s b1 b2) (some (.Vptr s.oB s.sepO))) vs) :
    Triple ge (FunctionEntry2 ge) f_check_telnet_options
      (LocalSt (envU1 b1 b2) [(_data, .Vptr c.dB c.dO)] (WO c s b1 b2))
      f_check_telnet_options.fn_body (RR (post1 0 (Hs c c.vars c.pref (XOU c s))) Sep.Assn.no) := by
  have hL : ∀ hp m, WO c s b1 b2 hp → Heap.Agrees hp m → Loads c c.vars m :=
    fun hp m hH hag => Hs_loads hpr hP hv hH hag
  have hN : IsPtr s.nd.oV := Or.inl ⟨_, _, rfl⟩
  sq
  · sset (.Vptr c.tnB c.tnO)
    exact ev_tn hcenv (hL hp m hH hag) (hT.get (by temps_get))
  sq
  · sset (.Vint (Integers.Int.repr 0))
    exact EvalExpr.Econst_int _ _
  sq
  · sq
    · sset Deb2026_3805C.nullV
      rw [← hs.au]
      exact ev_au hcenv (hL hp m hH hag) (hT.get (by temps_get))
    · exact if_f_skip ge _ _ _ _ _ _ _
        (fun le m hp hT hH hag => ⟨_, tv Deb2026_3805C.nullV, rfl⟩)
  refine triple_seq_fwd _ _ _ _ (LocalSt (envU1 b1 b2) (LQ c) (WO c s b1 b2)) _ _ _ ?_ ?_
  · sq
    · sset (.Vptr s.nB s.nO)
      rw [← hs.opt]
      exact ev_opts hcenv (hL hp m hH hag) (hT.get (by temps_get))
    refine tmono ge _ _ (l' := LL c (.Vptr s.nB s.nO)) (by subt) ?_
    refine loop_one _ _ _ _ (LocalSt (envU1 b1 b2) (LL c Deb2026_3805C.nullV) (WO c s b1 b2))
      (LocalSt (envU1 b1 b2) (LL c (.Vptr s.nB s.nO)) (WO c s b1 b2)) _ _ _ ?h1 ?h2 ?h0
    case h1 =>
      sq
      · sq
        · refine triple_if_local ge _ _ _ _ _ _ true _ _ _
            (fun le m hp hT hH hag => ⟨_, tv (.Vptr s.nB s.nO), boolVal_p _ (XN_valid hpn hH hag)⟩) ?_
          rw [if_pos rfl]
          sset (.Vint (Integers.Int.repr 1))
          exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _ (tv (.Vint (Integers.Int.repr 0))) rfl) rfl
        · exact if_t_skip ge _ _ _ _ _ _ _
            (fun le m hp hT hH hag => ⟨_, tv (.Vint (Integers.Int.repr 1)), rfl⟩)
      sq
      · sset (.Vptr s.oB s.oO)
        exact ev_sdata (b := s.nB) (o := s.nO) hcenv (hT.get (by temps_get)) (XN_load hpr hN hH hag).1
      sq
      · sq
        · exact callA_some ge _ _ _ _ _ _ _ _ _ _ _ _ _ sc.b fdC hC sc.fp tC rfl
            (fun _ _ _ => eval_callee_global (by envget) sc.sym rfl)
            (fun le m hT => .cons _ _ _ _ _ _ _ (tv (.Vptr s.oB s.oO)) rfl
              (.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl .nil))
        · sset (.Vptr s.oB s.sepO)
          exact tv (.Vptr s.oB s.sepO)
      refine triple_if_local ge _ _ _ _ _ _ true _ _ _
        (fun le m hp hT hH hag => ⟨_, tv (.Vptr s.oB s.sepO), boolVal_ptrc (XOU_valid hpn hH hag)⟩) ?_
      rw [if_pos rfl]
      sq
      · sset (olenV s.sepO s.oO)
        exact EvalExpr.Ebinop _ _ _ _ _ _ _ (tv (.Vptr s.oB s.sepO)) (tv (.Vptr s.oB s.oO)) (sub_ptr _ _ _ _ _)
      sq
      · sq
        · sq
          · sset (.Vptr s.oB (nextO s.sepO))
            exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (tv (.Vptr s.oB s.sepO))
              (EvalExpr.Econst_int _ _) rfl) rfl
          · sset (.Vptr s.oB (nextO s.sepO))
            exact tv (.Vptr s.oB (nextO s.sepO))
        · sset (.Vptr s.oB (nextO s.sepO))
          exact tv (.Vptr s.oB (nextO s.sepO))
      refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
      sq
      · refine Deb2025_14524.callS_some ge _ _ (sinSpec (.Vptr s.oB (nextO s.sepO)) (WO c s b1 b2)) _ _
          (.Vint (Integers.Int.repr 1)) _ _ _ _ _ [.Vptr s.oB (nextO s.sepO)] sin.b _
          (sin_sat ge s.oB (nextO s.sepO) s.byte s.j s.n _ hs.hj hs.hn hs.hhi (XOU_load hpr) fdS sl tS hS)
          sin.fp rfl rfl
          (fun _ _ _ => eval_callee_global (by envget) sin.sym rfl)
          (fun le m hT => .cons _ _ _ _ _ _ _ (tv (.Vptr s.oB (nextO s.sepO))) rfl .nil)
          (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h)
      refine triple_if_local ge _ _ _ _ _ _ true _ _ _
        (fun le m hp hT hH hag => ⟨_, tv (.Vint (Integers.Int.repr 1)), rfl⟩) ?_
      rw [if_pos rfl]
      exact triple_conseq ge _ _ (Sep.triple_continue ge _ _ _) (fun _ _ _ x => x)
        (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => lmono (by subt) x) (fun _ _ x => x)
    case h2 =>
      refine triple_fallthrough ge _ _ _
        (LocalSt (envU1 b1 b2) (setLocal (LL c (.Vptr s.nB s.nO)) _head Deb2026_3805C.nullV) (WO c s b1 b2))
        _ _ ?_ (fun _ _ _ x => lmono (by subt) x)
      sset Deb2026_3805C.nullV
      exact ev_snext (b := s.nB) (o := s.nO) hcenv (hT.get (by temps_get)) (XN_load hpr hN hH hag).2
    case h0 =>
      refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
      sq
      · refine triple_if_local ge _ _ _ _ _ _ false _ _ _
          (fun le m hp hT hH hag => ⟨_, tv Deb2026_3805C.nullV, rfl⟩) ?_
        rw [if_neg Bool.false_ne_true]
        sset (.Vint (Integers.Int.repr 0))
        exact EvalExpr.Econst_int _ _
      refine triple_if_local ge _ _ _ _ _ _ false _ _ _
        (fun le m hp hT hH hag => ⟨_, tv (.Vint (Integers.Int.repr 0)), rfl⟩) ?_
      rw [if_neg Bool.false_ne_true]
      exact triple_conseq ge _ _ (Sep.triple_break ge _ _ _) (fun _ _ _ x => x)
        (fun _ _ _ x => x) (fun _ _ _ x => lmono (by subt) x) (fun _ _ _ x => x) (fun _ _ x => x)
  sq
  · exact if_f_skip ge _ _ _ _ _ _ _
      (fun le m hp hT hH hag => ⟨_, tv (.Vint (Integers.Int.repr 0)), rfl⟩)
  exact retU1t ge _ _ hcenv b1 b2 hne _ _ _ _ (by temps_get) rfl (fun hp hH => ⟨rfl, hH⟩)

/-- **U1（P1u）**: 修正後は、ユーザー名に 8 ビット目の立ったバイトがあれば 43 を返し、メモリは呼ぶ前のまま。 -/
theorem P1u_U1 (ge : CGenv) (c : Ctx) (u : SU)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hP : Ptrs c) (hv : IsPtr c.vars) (hu : SUok c u)
    (sin : Callee ge _str_is_nonascii (.Internal f_str_is_nonascii))
    (fdS : FunDef) (sl : Callee ge _strlen fdS)
    (tS : typeOfFundef fdS = .Tfunction [tptr tschar] tulong cc_default)
    (hS : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdS
      (strlenSpec (.Vptr u.sB u.sO) u.n (WU c u b1 b2)) vs) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_check_telnet_options)
      (ctoSpec c (Hs c c.vars c.pref (XU c u)) (post1 43 (Hs c c.vars c.pref (XU c u)))) vs :=
  entryU1 ge c hcenv _ _ (fun b1 b2 hne =>
    p1u_body ge c u b1 b2 hne hcenv hpr hpn hP hv hu sin fdS sl tS (hS b1 b2)) vs

/-- **U1（P1o）**: 修正後は、オプションの引数に 8 ビット目の立ったバイトがあれば、キーワードによらずそのオプションを飛ばす。
0 を返し、メモリは呼ぶ前のまま。 -/
theorem P1o_U1 (ge : CGenv) (c : Ctx) (s : SOU)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hP : Ptrs c) (hv : IsPtr c.vars) (hs : SOUok c s)
    (sin : Callee ge _str_is_nonascii (.Internal f_str_is_nonascii))
    (fdS : FunDef) (sl : Callee ge _strlen fdS)
    (tS : typeOfFundef fdS = .Tfunction [tptr tschar] tulong cc_default)
    (hS : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdS
      (strlenSpec (.Vptr s.oB (nextO s.sepO)) s.n (WO c s b1 b2)) vs)
    (fdC : FunDef) (sc : Callee ge _strchr fdC)
    (tC : typeOfFundef fdC = .Tfunction [tptr tschar, tint] (tptr tschar) cc_default)
    (hC : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdC
      (specA [tptr tschar, tint] (tptr tschar) [.Vptr s.oB s.oO, .Vint (Integers.Int.repr 61)]
        (WO c s b1 b2) (WO c s b1 b2) (some (.Vptr s.oB s.sepO))) vs) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_check_telnet_options)
      (ctoSpec c (Hs c c.vars c.pref (XOU c s)) (post1 0 (Hs c c.vars c.pref (XOU c s)))) vs :=
  entryU1 ge c hcenv _ _ (fun b1 b2 hne =>
    p1o_body ge c s b1 b2 hne hcenv hpr hpn hP hv hs sin fdS sl tS (hS b1 b2) fdC sc tC (hC b1 b2)) vs

end DebBookworm2023_27533C
