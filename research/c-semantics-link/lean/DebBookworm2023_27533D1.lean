/-
CVE-2023-27533 bookworm: Debian のバックポート（D1: curl 7.88.1 に CVE-2023-27533.patch を当てたもの）の `check_telnet_options` の上の P1。

7.88.1 の関数は `char option_keyword[128] = ""` と `char option_arg[256] = ""` を持つ。この初期化は 384 個の 1 バイトの代入になるので、
`body_d1` で並びの形にして `init_chain` で越える。オプションの分解は `strchr` でなく `sscanf`。
-/
import DebBookworm2023_27533U1
open CC CC.Sep CC.HProp
open DebBookworm2023_27533_d1
open Case5C (RR)
open Case3C (Locs)
open Case4C (IsPtr)

set_option maxRecDepth 100000

namespace DebBookworm2023_27533C

/-- 局所変数 `option_keyword`・`option_arg` の環境。 -/
def envD1 (b1 b2 : Block) : Env :=
  (emptyEnv.set _option_keyword (b1, tarray tschar 128)).set _option_arg (b2, tarray tschar 256)

macro "envgetD" : tactic =>
  `(tactic| (unfold envD1; repeat (first
      | exact PTree.gss _ _ _
      | exact PTree.gempty _
      | refine (PTree.gso _ _ _ _ (by decide)).trans ?_)))

abbrev LD (b1 b2 : Block) : List (Block × Nat) := [(b1, 128), (b2, 256)]

theorem blocks_envD1 (ge : CGenv) (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env) (b1 b2 : Block) :
    blocksOfEnv ge.genv_cenv (envD1 b1 b2) = [(b2, 0, 256), (b1, 0, 128)] := by
  rw [hcenv]; rfl

/-- 局所変数を解放する定数の `return`。 -/
theorem retD1 (ge fe f) (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env) (b1 b2 : Block) (hne : b1 ≠ b2)
    (l : List (Ident × Val)) (Hk : HProp) (n : Integers.Int) (v' : Val) (Ret : Val → HProp)
    (hcast : ∀ m, Cop.semCast (.Vint n) tint f.fn_return m = some v')
    (hret : ∀ hp, Hk hp → Ret v' hp) :
    Triple ge fe f (LocalSt (envD1 b1 b2) l (Hk ∗ Locs (LD b1 b2)))
      (.Sreturn (some (.Econst_int n tint)))
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := Ret } := by
  refine Case3C.ret_locs ge _ _ (envD1 b1 b2) _ Hk (LD b1 b2) _ (.Vint n) v' _
    (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) hcast ?_ ?_ hret
  · rw [blocks_envD1 ge hcenv]
    intro x hx'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
    rcases hx' with rfl | rfl
    · exact ⟨b2, 256, rfl, by simp⟩
    · exact ⟨b1, 128, rfl, by simp⟩
  · rw [blocks_envD1 ge hcenv]
    simp [Ne.symm hne]

/-- 関数の入口（局所変数を割り当てる）。 -/
theorem entryD1 (ge : CGenv) (c : Ctx) (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env) (Pre : HProp)
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

theorem body_d1 : f_check_telnet_options.fn_body =
    initSeq _option_keyword 128 0 128 (initSeq _option_arg 256 0 256 (dropS 384 f_check_telnet_options.fn_body)) := rfl

theorem envD1_kw (b1 b2 : Block) : (envD1 b1 b2).get _option_keyword = some (b1, tarray tschar 128) := by envgetD
theorem envD1_arg (b1 b2 : Block) : (envD1 b1 b2).get _option_arg = some (b2, tarray tschar 256) := by envgetD

/-- 2つの配列の初期化を越える。 -/
theorem initD (ge fe f) (b1 b2 : Block) (l : List (Ident × Val)) (Hk : HProp) (rest : Stmt) (Rx : Sep.ExitConds)
    (h : Triple ge fe f (LocalSt (envD1 b1 b2) l (Hk ∗ Locs (LD b1 b2))) rest Rx) :
    Triple ge fe f (LocalSt (envD1 b1 b2) l (Hk ∗ Locs (LD b1 b2)))
      (initSeq _option_keyword 128 0 128 (initSeq _option_arg 256 0 256 rest)) Rx := by
  have e1 : (Hk ∗ Locs (LD b1 b2))
      = anyBytes .Freeable b1 0 128 ∗ (Hk ∗ (anyBytes .Freeable b2 0 256 ∗ emp)) := by
    show (Hk ∗ (anyBytes .Freeable b1 0 128 ∗ (anyBytes .Freeable b2 0 256 ∗ emp))) = _
    rw [sep_left_comm_eq]
  have e2 : (Hk ∗ Locs (LD b1 b2))
      = anyBytes .Freeable b2 0 256 ∗ (anyBytes .Freeable b1 0 128 ∗ (Hk ∗ emp)) := by
    rw [e1, sep_left_comm_eq Hk, sep_left_comm_eq (anyBytes .Freeable b1 0 128)]
  have h1 : Triple ge fe f (LocalSt (envD1 b1 b2) l (Hk ∗ Locs (LD b1 b2)))
      (initSeq _option_arg 256 0 256 rest) Rx := by
    rw [e2] at h ⊢
    exact init_chain ge fe f _ l _ b2 _ 256 (envD1_arg b1 b2) (by decide) 256 0 rest Rx (by omega) h
  rw [e1] at h1 ⊢
  exact init_chain ge fe f _ l _ b1 _ 128 (envD1_kw b1 b2) (by decide) 128 0 _ Rx (by omega) h1

/-! ## P1u（ユーザー名） -/

abbrev WUD (c : Ctx) (u : SU) (b1 b2 : Block) : HProp :=
  Hs c c.vars c.pref (XU c u) ∗ Locs (LD b1 b2)

set_option maxHeartbeats 4000000 in
theorem p1u_body_d1 (ge : CGenv) (c : Ctx) (u : SU) (b1 b2 : Block) (hne : b1 ≠ b2)
    (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hP : Ptrs c) (hv : IsPtr c.vars) (hu : SUok c u)
    (sin : Callee ge _str_is_nonascii (.Internal f_str_is_nonascii))
    (fdS : FunDef) (sl : Callee ge _strlen fdS)
    (tS : typeOfFundef fdS = .Tfunction [tptr tschar] tulong cc_default)
    (hS : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdS
      (strlenSpec (.Vptr u.sB u.sO) u.n (WUD c u b1 b2)) vs) :
    Triple ge (FunctionEntry2 ge) f_check_telnet_options
      (LocalSt (envD1 b1 b2) [(_data, .Vptr c.dB c.dO)] (WUD c u b1 b2))
      f_check_telnet_options.fn_body (RR (post1 43 (Hs c c.vars c.pref (XU c u))) Sep.Assn.no) := by
  have hL : ∀ hp m, WUD c u b1 b2 hp → Heap.Agrees hp m → Loads c c.vars m :=
    fun hp m hH hag => Hs_loads hpr hP hv hH hag
  rw [body_d1]
  refine initD _ _ _ b1 b2 _ _ _ _ ?_
  sq
  · sset (.Vptr c.tnB c.tnO)
    exact ev_tn hcenv (hL hp m hH hag) (hT.get (by temps_get))
  sq
  · sset (.Vptr c.cnB c.cnO)
    exact ev_conn hcenv (hL hp m hH hag) (hT.get (by temps_get))
  sq
  · sset (.Vint (Integers.Int.repr 0))
    exact EvalExpr.Econst_int _ _
  refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  sq
  · sset (.Vptr u.auB u.auO)
    rw [← hu.au]
    exact ev_au hcenv (hL hp m hH hag) (hT.get (by temps_get))
  refine triple_if_local ge _ _ _ _ _ _ true _ _ _
    (fun le m hp hT hH hag => ⟨_, tv (.Vptr u.auB u.auO), boolVal_ptrc (XU_valid hpn hH hag)⟩) ?_
  rw [if_pos rfl]
  refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
  sq
  · sq
    · sset (.Vptr c.cnB c.cnO)
      exact ev_conn hcenv (hL hp m hH hag) (hT.get (by temps_get))
    sq
    · sset (.Vptr u.sB u.sO)
      rw [← hu.user]
      exact ev_user hcenv (hL hp m hH hag) (hT.get (by temps_get))
    · refine Deb2025_14524.callS_some ge _ _ (sinSpec (.Vptr u.sB u.sO) (WUD c u b1 b2)) _ _
        (.Vint (Integers.Int.repr 1)) _ _ _ _ _ [.Vptr u.sB u.sO] sin.b _
        (sin_sat ge u.sB u.sO u.byte u.j u.n _ hu.hj hu.hn hu.hhi (XU_load hpr) fdS sl tS hS)
        sin.fp rfl rfl
        (fun _ _ _ => eval_callee_global (by envgetD) sin.sym rfl)
        (fun le m hT => .cons _ _ _ _ _ _ _ (tv (.Vptr u.sB u.sO)) rfl .nil)
        (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h)
  refine triple_if_local ge _ _ _ _ _ _ true _ _ _
    (fun le m hp hT hH hag => ⟨_, tv (.Vint (Integers.Int.repr 1)), rfl⟩) ?_
  rw [if_pos rfl]
  exact retD1 ge _ _ hcenv b1 b2 hne _ _ _ _ _ (fun _ => rfl) (fun hp hH => ⟨rfl, hH⟩)

/-- **D1（P1u）**: バックポートは、ユーザー名に 8 ビット目の立ったバイトがあれば 43 を返し、メモリは呼ぶ前のまま。 -/
theorem P1u_D1 (ge : CGenv) (c : Ctx) (u : SU)
    (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hP : Ptrs c) (hv : IsPtr c.vars) (hu : SUok c u)
    (sin : Callee ge _str_is_nonascii (.Internal f_str_is_nonascii))
    (fdS : FunDef) (sl : Callee ge _strlen fdS)
    (tS : typeOfFundef fdS = .Tfunction [tptr tschar] tulong cc_default)
    (hS : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdS
      (strlenSpec (.Vptr u.sB u.sO) u.n (WUD c u b1 b2)) vs) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_check_telnet_options)
      (ctoSpec c (Hs c c.vars c.pref (XU c u)) (post1 43 (Hs c c.vars c.pref (XU c u)))) vs :=
  entryD1 ge c hcenv _ _ (fun b1 b2 hne =>
    p1u_body_d1 ge c u b1 b2 hne hcenv hpr hpn hP hv hu sin fdS sl tS (hS b1 b2)) vs

/-! ## P1o（オプション） -/

/-- 局所変数を解放する `return result;`。 -/
theorem retD1t (ge fe f) (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env) (b1 b2 : Block) (hne : b1 ≠ b2)
    (l : List (Ident × Val)) (Hk : HProp) (n : Integers.Int) (Ret : Val → HProp)
    (hl : (_result, .Vint n) ∈ l) (hf : f.fn_return = tint)
    (hret : ∀ hp, Hk hp → Ret (.Vint n) hp) :
    Triple ge fe f (LocalSt (envD1 b1 b2) l (Hk ∗ Locs (LD b1 b2)))
      (.Sreturn (some (.Etempvar _result tint)))
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := Ret } := by
  refine Case3C.ret_locs ge _ _ (envD1 b1 b2) _ Hk (LD b1 b2) _ (.Vint n) (.Vint n) _
    (fun le _ _ hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get hl)) (fun m => ?_) ?_ ?_ hret
  · rw [hf]; rfl
  · rw [blocks_envD1 ge hcenv]
    intro x hx'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
    rcases hx' with rfl | rfl
    · exact ⟨b2, 256, rfl, by simp⟩
    · exact ⟨b1, 128, rfl, by simp⟩
  · rw [blocks_envD1 ge hcenv]
    simp [Ne.symm hne]

abbrev WOD (c : Ctx) (s : SOD) (b1 b2 : Block) : HProp :=
  Hs c c.vars c.pref (XD c s) ∗ Locs (LD b1 b2)
abbrev WOA (c : Ctx) (s : SOD) (b1 b2 : Block) : HProp :=
  Hs c c.vars c.pref (XD c s) ∗ YA s b1 b2

abbrev LQD (c : Ctx) : List (Ident × Val) :=
  [(_result, .Vint (Integers.Int.repr 0)), (_tn, .Vptr c.tnB c.tnO), (_data, .Vptr c.dB c.dO)]
abbrev LLD (c : Ctx) (h : Val) : List (Ident × Val) := (_head, h) :: LQD c

abbrev sscanfTy : List Ty := [tptr tschar, tptr tschar, tptr tvoid, tptr tvoid]

/-- `sscanf(option, fmt, option_keyword, option_arg)` の引数。 -/
abbrev sscanfArgs (s : SOD) (litB b1 b2 : Block) : List Val :=
  [s.nd.oV, .Vptr litB Integers.Ptrofs.zero, .Vptr b1 Integers.Ptrofs.zero, .Vptr b2 Integers.Ptrofs.zero]

set_option maxHeartbeats 4000000 in
theorem p1o_body_d1 (ge : CGenv) (c : Ctx) (s : SOD) (b1 b2 : Block) (hne : b1 ≠ b2)
    (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hP : Ptrs c) (hv : IsPtr c.vars) (hs : SODok c s)
    (sin : Callee ge _str_is_nonascii (.Internal f_str_is_nonascii))
    (fdS : FunDef) (sl : Callee ge _strlen fdS)
    (tS : typeOfFundef fdS = .Tfunction [tptr tschar] tulong cc_default)
    (hS : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdS
      (strlenSpec (.Vptr b2 Integers.Ptrofs.zero) s.n (WOA c s b1 b2)) vs)
    (fdF : FunDef) (sf : Callee ge _sscanf fdF)
    (tF : typeOfFundef fdF = .Tfunction sscanfTy tint cc_default)
    (litB : Block) (hlit : Genv.findSymbol ge.genv_genv ___stringlit_2 = some litB)
    (hF : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdF
      (specA sscanfTy tint (sscanfArgs s litB b1 b2) (WOD c s b1 b2) (WOA c s b1 b2)
        (some (.Vint (Integers.Int.repr 2)))) vs) :
    Triple ge (FunctionEntry2 ge) f_check_telnet_options
      (LocalSt (envD1 b1 b2) [(_data, .Vptr c.dB c.dO)] (WOD c s b1 b2))
      f_check_telnet_options.fn_body (RR (post1 0 (Hs c c.vars c.pref (XD c s))) Sep.Assn.no) := by
  have hL : ∀ hp m, WOD c s b1 b2 hp → Heap.Agrees hp m → Loads c c.vars m :=
    fun hp m hH hag => Hs_loads hpr hP hv hH hag
  have hN := hs.oV
  rw [body_d1]
  refine initD _ _ _ b1 b2 _ _ _ _ ?_
  sq
  · sset (.Vptr c.tnB c.tnO)
    exact ev_tn hcenv (hL hp m hH hag) (hT.get (by temps_get))
  sq
  · sset (.Vptr c.cnB c.cnO)
    exact ev_conn hcenv (hL hp m hH hag) (hT.get (by temps_get))
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
  refine triple_seq_fwd _ _ _ _ (LocalSt (envD1 b1 b2) (LQD c) (WOD c s b1 b2)) _ _ _ ?_ ?_
  · sq
    · sset (.Vptr s.nd.nB s.nd.nO)
      rw [← hs.opt]
      exact ev_opts hcenv (hL hp m hH hag) (hT.get (by temps_get))
    refine tmono ge _ _ (l' := LLD c (.Vptr s.nd.nB s.nd.nO)) (by subt) ?_
    refine loop_one _ _ _ _ (LocalSt (envD1 b1 b2) (LLD c Deb2026_3805C.nullV) (WOD c s b1 b2))
      (LocalSt (envD1 b1 b2) (LLD c (.Vptr s.nd.nB s.nd.nO)) (WOD c s b1 b2)) _ _ _ ?h1 ?h2 ?h0
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
              (.cons _ _ _ _ _ _ _ (eval_callee_global (by envgetD) hlit rfl) rfl
                (.cons _ _ _ _ _ _ _ (ev_arr (envD1_kw b1 b2)) rfl
                  (.cons _ _ _ _ _ _ _ (ev_arr (envD1_arg b1 b2)) rfl .nil))))
      refine triple_if_local ge _ _ _ _ _ _ true _ _ _
        (fun le m hp hT hH hag => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (tv (.Vint (Integers.Int.repr 2)))
          (EvalExpr.Econst_int _ _) rfl, rfl⟩) ?_
      rw [if_pos rfl]
      refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
      sq
      · refine Deb2025_14524.callS_some ge _ _ (sinSpec (.Vptr b2 Integers.Ptrofs.zero) (WOA c s b1 b2)) _ _
          (.Vint (Integers.Int.repr 1)) _ _ _ _ _ [.Vptr b2 Integers.Ptrofs.zero] sin.b _
          (sin_sat ge b2 Integers.Ptrofs.zero s.byte s.j s.n _ hs.hj hs.hn hs.hhi YA_load fdS sl tS hS)
          sin.fp rfl rfl
          (fun _ _ _ => eval_callee_global (by envgetD) sin.sym rfl)
          (fun le m hT => .cons _ _ _ _ _ _ _ (ev_arr (envD1_arg b1 b2)) rfl .nil)
          (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h)
      refine triple_if_local ge _ _ _ _ _ _ true _ _ _
        (fun le m hp hT hH hag => ⟨_, tv (.Vint (Integers.Int.repr 1)), rfl⟩) ?_
      rw [if_pos rfl]
      refine triple_conseq ge _ _ (Sep.triple_continue ge _ _ _) (fun _ _ _ x => x)
        (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun e le hp x => ?_) (fun _ _ x => x)
      obtain ⟨he, hT, h1, h2, hd, hu, a1, a2⟩ := x
      exact ⟨he, TempsHold_mono (by subt) hT, h1, h2, hd, hu, a1, YA_locs hs.hj2 a2⟩
    case h2 =>
      refine triple_fallthrough ge _ _ _
        (LocalSt (envD1 b1 b2) (setLocal (LLD c (.Vptr s.nd.nB s.nd.nO)) _head Deb2026_3805C.nullV) (WOD c s b1 b2))
        _ _ ?_ (fun _ _ _ x => lmono (by subt) x)
      sset Deb2026_3805C.nullV
      exact ev_snext (b := s.nd.nB) (o := s.nd.nO) hcenv (hT.get (by temps_get)) (XN_load hpr hN hH hag).2
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

/-- **D1（P1o）**: バックポートは、`sscanf` が分けた引数に 8 ビット目の立ったバイトがあれば、キーワードによらずそのオプションを飛ばす。
0 を返し、メモリは呼ぶ前のまま。 -/
theorem P1o_D1 (ge : CGenv) (c : Ctx) (s : SOD)
    (hcenv : ge.genv_cenv = DebBookworm2023_27533_u1.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hP : Ptrs c) (hv : IsPtr c.vars) (hs : SODok c s)
    (sin : Callee ge _str_is_nonascii (.Internal f_str_is_nonascii))
    (fdS : FunDef) (sl : Callee ge _strlen fdS)
    (tS : typeOfFundef fdS = .Tfunction [tptr tschar] tulong cc_default)
    (hS : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdS
      (strlenSpec (.Vptr b2 Integers.Ptrofs.zero) s.n (WOA c s b1 b2)) vs)
    (fdF : FunDef) (sf : Callee ge _sscanf fdF)
    (tF : typeOfFundef fdF = .Tfunction sscanfTy tint cc_default)
    (litB : Block) (hlit : Genv.findSymbol ge.genv_genv ___stringlit_2 = some litB)
    (hF : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdF
      (specA sscanfTy tint (sscanfArgs s litB b1 b2) (WOD c s b1 b2) (WOA c s b1 b2)
        (some (.Vint (Integers.Int.repr 2)))) vs) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_check_telnet_options)
      (ctoSpec c (Hs c c.vars c.pref (XD c s)) (post1 0 (Hs c c.vars c.pref (XD c s)))) vs :=
  entryD1 ge c hcenv _ _ (fun b1 b2 hne =>
    p1o_body_d1 ge c s b1 b2 hne hcenv hpr hpn hP hv hs sin fdS sl tS (hS b1 b2) fdF sf tF litB hlit (hF b1 b2)) vs

end DebBookworm2023_27533C
