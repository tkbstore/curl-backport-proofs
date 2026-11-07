/-
CVE-2023-27533 bookworm: 4つの翻訳単位に共通の部分。
性質は `research/backport-proof-debian/cases/bookworm/CVE-2023-27533.md`（証明の前にコミットした）。

- 文字列のバイトの所有 `strH`、`*str & 0x80` を C の式のまま書いた `hiBit`
- `str_is_nonascii` の本体からの証明 `sin_sat`（U1・D1 で関数は同じ。読むメモリの形によらない）
-/
import GenDebBookworm2023_27533U1
import GenDebBookworm2023_27533U0
import GenDebBookworm2023_27533D1
import GenDebBookworm2023_27533D0
import Deb2026_8924Lib
import Deb2026_3805Common
open CC CC.Sep CC.HProp
open Case5C (addr sep_l sep_r RR return_const)
open Case4C (IsPtr cast_ptr mapsto_weakValid)

set_option maxRecDepth 20000

namespace DebBookworm2023_27533C

abbrev P := Integers.Ptrofs

/-- `str++`（`char *` に 1 を足す）の番地。 -/
def nextO (o : P) : P :=
  Integers.Ptrofs.add o
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr 1) (Integers.Ptrofs.of_ints (Integers.Int.repr 1)))

/-- 文字列の先頭から `i` 文字目の番地。 -/
def offs (o : P) : Nat → P
  | 0 => o
  | i + 1 => nextO (offs o i)

/-- `*str & 0x80` が 0 でない（C の式のまま。`*str` は `char` を読んで符号拡張した値）。 -/
def hiBit (x : Integers.Int) : Bool :=
  !Integers.Int.eq (Integers.Int.and (Integers.Int.sign_ext 8 x) (Integers.Int.repr 128)) Integers.Int.zero

def r64 (n : Nat) : Integers.Int64 := Integers.Int64.repr (n : _root_.Int)

theorem r64_pred (k : Nat) :
    Integers.Int64.sub (r64 (k + 1)) (Integers.Int64.repr (Integers.Int.signed (Integers.Int.repr 1))) = r64 k := by
  have h1 : Integers.Int.signed (Integers.Int.repr 1) = 1 := by decide
  rw [h1]
  show (BitVec.ofInt 64 ((k + 1 : Nat) : _root_.Int)) - BitVec.ofInt 64 1 = BitVec.ofInt 64 (k : _root_.Int)
  rw [show ((k + 1 : Nat) : _root_.Int) = (k : _root_.Int) + 1 by omega, BitVec.ofInt_add]
  exact BitVec.add_sub_cancel ..

theorem r64_ne {k : Nat} (h0 : 0 < k) (h1 : k < 18446744073709551616) :
    Integers.Int64.eq (r64 k) Integers.Int64.zero = false := by
  have h : (r64 k).toNat = k := by
    have := u64_toNat_repr k
    rw [Nat.mod_eq_of_lt (by simpa using h1)] at this
    exact this
  show ((r64 k) == (Integers.Int64.zero)) = false
  rw [beq_eq_false_iff_ne]
  intro he
  rw [he] at h
  have hz : BitVec.toNat (Integers.Int64.zero) = 0 := rfl
  omega

/-- `strlen(p)` は `n` を返す。メモリの形 `K` は変えない。 -/
def strlenSpec (p : Val) (n : Nat) (K : HProp) : FunSpec where
  tyargs := [tptr tschar]
  tyres := tulong
  cc := cc_default
  pre := fun vargs hp => vargs = [p] ∧ K hp
  post := fun v hp => v = .Vlong (r64 n) ∧ K hp
  measure := fun _ => 0

/-- `str_is_nonascii(p)` の仕様: 真（1）を返し、メモリを変えない。本体から示す。 -/
def sinSpec (p : Val) (K : HProp) : FunSpec where
  tyargs := [tptr tschar]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [p] ∧ K hp
  post := fun v hp => v = .Vint (Integers.Int.repr 1) ∧ K hp
  measure := fun _ => 0

structure Callee (ge : CGenv) (id : Ident) (fd : FunDef) where
  b : Block
  sym : Genv.findSymbol ge.genv_genv id = some b
  fp : FuncPtr ge b fd

/-! ## `str_is_nonascii`（U1 の本体。D1 の本体は `rfl` で同じ） -/

section sin
open DebBookworm2023_27533_u1

theorem sin_same : DebBookworm2023_27533_d1.f_str_is_nonascii = f_str_is_nonascii := rfl

abbrev sinL (sB : Block) (sO : P) (N i : Nat) : List (Ident × Val) :=
  [(_len, .Vlong (r64 (N - i))), (_str, .Vptr sB (offs sO i))]

/-- `s1; s2`: 前の文を先に証明して、その事後条件を後ろの文の事前条件にする（ゴールは前・後の順）。 -/
macro "sq" : tactic => `(tactic| apply triple_seq_fwd)

/-- 真の `if (a) ; else s2`（事後条件は事前条件のまま）。 -/
theorem if_t_skip (ge fe f) (E : Env) (l : List (Ident × Val)) (H : HProp) (a : Expr) (s2 : Stmt)
    (hev : ∀ le m hp, TempsHold l le → H hp → Heap.Agrees hp m →
      ∃ v, EvalExpr ge E le m a v ∧ Cop.boolVal v (typeof a) m = some true) :
    Triple ge fe f (LocalSt E l H) (.Sifthenelse a .Sskip s2) (.only (LocalSt E l H)) :=
  triple_if_local ge fe f E l H a true _ _ _ hev (triple_skip ge fe f _)

/-- 偽の `if (a) s1;`（事後条件は事前条件のまま）。 -/
theorem if_f_skip (ge fe f) (E : Env) (l : List (Ident × Val)) (H : HProp) (a : Expr) (s1 : Stmt)
    (hev : ∀ le m hp, TempsHold l le → H hp → Heap.Agrees hp m →
      ∃ v, EvalExpr ge E le m a v ∧ Cop.boolVal v (typeof a) m = some false) :
    Triple ge fe f (LocalSt E l H) (.Sifthenelse a s1 .Sskip) (.only (LocalSt E l H)) :=
  triple_if_local ge fe f E l H a false _ _ _ hev (triple_skip ge fe f _)

/-- 戻り値が定数の `return`（局所変数の無い関数）。 -/
theorem ret_const_any (ge fe f) (l : List (Ident × Val)) (Hh : HProp) (n : Integers.Int)
    (R : Sep.ExitConds) (v' : Val)
    (hcast : ∀ m : Mem, Cop.semCast (.Vint n) tint f.fn_return m = some v')
    (hret : ∀ hp, Hh hp → R.ret v' hp) :
    Triple ge fe f (LocalSt emptyEnv l Hh) (.Sreturn (some (.Econst_int n tint))) R :=
  triple_conseq ge fe f
    (triple_return_local ge fe f l Hh _ R.ret (.Vint n) v'
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) hcast hret)
    (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
    (fun _ _ _ x => False.elim x) (fun _ _ x => x)

theorem sin_iter (ge : CGenv) (sB : Block) (sO : P) (byte : Nat → Integers.Int) (j N n : Nat) (K : HProp)
    (R : Sep.ExitConds) (hn : n ≤ j) (hj : j < N) (hN : N < 18446744073709551616)
    (hhi : hiBit (byte j) = true)
    (hload : ∀ k, k ≤ j → ∀ hp m, K hp → Heap.Agrees hp m →
      Mem.load .Mint8signed m sB (Integers.Ptrofs.unsigned (offs sO k))
        = some (Val.loadResult .Mint8signed (.Vint (byte k))))
    (hret : ∀ hp, K hp → R.ret (.Vint (Integers.Int.repr 1)) hp)
    (hnext : ∀ e le hp, 0 < n → LocalSt emptyEnv (sinL sB sO N (j - n + 1)) K e le hp → R.normal e le hp) :
    Triple ge (FunctionEntry2 ge) f_str_is_nonascii
      (LocalSt emptyEnv (sinL sB sO N (j - n)) K)
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (.Sset _t'2 (.Etempvar _len tulong))
            (.Sset _len (.Ebinop .Osub (.Etempvar _t'2 tulong) (.Econst_int (Integers.Int.repr 1) tint) tulong)))
          (.Sifthenelse (.Etempvar _t'2 tulong) .Sskip .Sbreak))
        (.Ssequence
          (.Ssequence
            (.Sset _t'3 (.Ederef (.Etempvar _str (tptr tschar)) tschar))
            (.Sifthenelse (.Ebinop .Oand (.Etempvar _t'3 tschar) (.Econst_int (Integers.Int.repr 128) tint) tint)
              (.Sreturn (some (.Econst_int (Integers.Int.repr 1) tint))) .Sskip))
          (.Sset _str (.Ebinop .Oadd (.Etempvar _str (tptr tschar)) (.Econst_int (Integers.Int.repr 1) tint) (tptr tschar)))))
      R := by
  obtain ⟨k, hk⟩ : ∃ k, N - (j - n) = k + 1 := ⟨N - (j - n) - 1, by omega⟩
  have hk2 : N - (j - n + 1) = k := by omega
  sq
  · sq
    · sq
      · refine triple_set_local_fwd ge _ _ _ _ K _ _ (.Vlong (r64 (k + 1))) ?_
        intro le m hp hT _ _
        rw [← hk]
        exact EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))
      · refine triple_set_local_fwd ge _ _ _ _ K _ _ (.Vlong (r64 k)) ?_
        intro le m hp hT _ _
        refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
          (EvalExpr.Econst_int _ _) ?_
        rw [← r64_pred k]
        rfl
    · refine if_t_skip ge _ _ _ _ K _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), ?_⟩)
      show some (!(Integers.Int64.eq (r64 (k + 1)) Integers.Int64.zero)) = some true
      rw [r64_ne (by omega) (by omega)]
      rfl
  · obtain ⟨w, hw⟩ : ∃ w, w = Integers.Int.sign_ext 8 (byte (j - n)) := ⟨_, rfl⟩
    have hdj : j - n ≤ j := by omega
    have hg : ∀ m, Cop.boolVal (.Vint (Integers.Int.and w (Integers.Int.repr 128))) tint m
        = some (hiBit (byte (j - n))) := by
      intro m
      rw [hw]
      rfl
    cases hb : hiBit (byte (j - n))
    · have hnz : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | h
        · rw [Nat.sub_zero] at hb; rw [hb] at hhi; cases hhi
        · exact h
      sq
      · sq
        · refine triple_set_local_fwd ge _ _ _ _ K _ _ (.Vint w) ?_
          intro le m hp hT hK hag
          refine EvalExpr.Elvalue _ sB (offs sO (j - n)) .Full _
            (EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))
            (DerefLoc.value .Mint8signed _ rfl ?_)
          show Mem.load .Mint8signed m sB (Integers.Ptrofs.unsigned (offs sO (j - n))) = _
          rw [hload _ hdj hp m hK hag, hw]
          rfl
        · refine if_f_skip ge _ _ _ _ K _ _
            (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _) rfl,
              (hg m).trans (by rw [hb])⟩)
      · refine triple_fallthrough ge _ _ _ (LocalSt emptyEnv (setLocal _ _ _) K) _ _
          (triple_set_local_fwd ge _ _ _ _ K _ _ (.Vptr sB (offs sO (j - n + 1))) ?_) ?_
        · intro le m hp hT _ _
          exact EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ (.Vptr sB (offs sO (j - n))) (hT.get (by temps_get)))
            (EvalExpr.Econst_int _ _) rfl
        · intro e le hp ⟨he, hT, hK⟩
          refine hnext e le hp hnz ⟨he, TempsHold_mono ?_ hT, hK⟩
          intro p hp'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · rw [hk2]; temps_get
          · temps_get
    · refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
      sq
      · refine triple_set_local_fwd ge _ _ _ _ K _ _ (.Vint w) ?_
        intro le m hp hT hK hag
        refine EvalExpr.Elvalue _ sB (offs sO (j - n)) .Full _
          (EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))
          (DerefLoc.value .Mint8signed _ rfl ?_)
        show Mem.load .Mint8signed m sB (Integers.Ptrofs.unsigned (offs sO (j - n))) = _
        rw [hload _ hdj hp m hK hag, hw]
        rfl
      · refine triple_if_local ge _ _ _ _ K _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _) rfl,
            (hg m).trans (by rw [hb])⟩) ?_
        rw [if_pos rfl]
        exact ret_const_any ge _ _ _ K _ _ _ (fun _ => rfl) hret

theorem sin_body (ge : CGenv) (sB : Block) (sO : P) (byte : Nat → Integers.Int) (j N : Nat) (K : HProp)
    (hj : j < N) (hN : N < 18446744073709551616) (hhi : hiBit (byte j) = true)
    (hload : ∀ k, k ≤ j → ∀ hp m, K hp → Heap.Agrees hp m →
      Mem.load .Mint8signed m sB (Integers.Ptrofs.unsigned (offs sO k))
        = some (Val.loadResult .Mint8signed (.Vint (byte k))))
    (fd : FunDef) (X : Callee ge _strlen fd)
    (hty : typeOfFundef fd = .Tfunction [tptr tschar] tulong cc_default)
    (hsat : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd (strlenSpec (.Vptr sB sO) N K) vs) :
    Triple ge (FunctionEntry2 ge) f_str_is_nonascii
      (LocalSt emptyEnv [(_str, .Vptr sB sO)] K) f_str_is_nonascii.fn_body
      (RR (sinSpec (.Vptr sB sO) K).post Sep.Assn.no) := by
  sq
  · sq
    · refine Deb2025_14524.callS_some ge _ _ (strlenSpec (.Vptr sB sO) N K) K K (.Vlong (r64 N)) _ _ _ _ _
        [.Vptr sB sO] X.b fd hsat X.fp hty rfl
        (fun _ _ _ => eval_callee_global (PTree.gempty _) X.sym rfl)
        (fun le m hT => .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ (.Vptr sB sO) (hT.get (by temps_get))) rfl .nil)
        (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h)
    · refine triple_set_local_fwd ge _ _ _ _ K _ _ (.Vlong (r64 N)) ?_
      intro le m hp hT _ _
      exact EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))
  · refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ _ _ _)
    let R : Sep.ExitConds := { RR (sinSpec (.Vptr sB sO) K).post Sep.Assn.no with normal := Sep.Assn.no }
    let I : Nat → Sep.Assn := fun n e le hp => n ≤ j ∧ LocalSt emptyEnv (sinL sB sO N (j - n)) K e le hp
    let J : Nat → Sep.Assn := fun n e le hp => 0 < n ∧ n ≤ j ∧ LocalSt emptyEnv (sinL sB sO N (j - n + 1)) K e le hp
    refine triple_conseq ge _ _
      (Sep.triple_loop ge (FunctionEntry2 ge) f_str_is_nonascii R I J _ .Sskip (fun n => ?body) (fun n => ?incr) j)
      (fun e le hp ⟨he, hT, hK⟩ => ⟨Nat.le_refl _, he, ?pre, hK⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    case pre =>
      refine TempsHold_mono ?_ hT
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl
      · rw [show j - j = 0 by omega, Nat.sub_zero]; temps_get
      · rw [show j - j = 0 by omega]; show (_str, Val.Vptr sB sO) ∈ _; temps_get
    case body =>
      refine Case1C.triple_pure ge _ _ _ _ _ _ (fun hn => ?_)
      exact sin_iter ge sB sO byte j N n K _ hn hj hN hhi hload (fun hp hK => ⟨rfl, hK⟩)
        (fun e le hp h0 h1 => ⟨h0, hn, h1⟩)
    case incr =>
      refine triple_fallthrough ge _ _ _ _ _ _ (triple_skip ge _ _ _) ?_
      intro e le hp ⟨h0, hn, hL⟩
      refine ⟨n - 1, by omega, by omega, ?_⟩
      rw [show j - (n - 1) = j - n + 1 by omega]
      exact hL

/-- `str_is_nonascii` は、位置 `j` に高位のバイトがあり `strlen` が `j` より大きい値を返す文字列について真を返す。 -/
theorem sin_sat (ge : CGenv) (sB : Block) (sO : P) (byte : Nat → Integers.Int) (j N : Nat) (K : HProp)
    (hj : j < N) (hN : N < 18446744073709551616) (hhi : hiBit (byte j) = true)
    (hload : ∀ k, k ≤ j → ∀ hp m, K hp → Heap.Agrees hp m →
      Mem.load .Mint8signed m sB (Integers.Ptrofs.unsigned (offs sO k))
        = some (Val.loadResult .Mint8signed (.Vint (byte k))))
    (fd : FunDef) (X : Callee ge _strlen fd)
    (hty : typeOfFundef fd = .Tfunction [tptr tschar] tulong cc_default)
    (hsat : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd (strlenSpec (.Vptr sB sO) N K) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_str_is_nonascii) (sinSpec (.Vptr sB sO) K) vs := by
  by_cases hvs : vs = [.Vptr sB sO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hnv : listNorepet (varNames f_str_is_nonascii.fn_vars) := by decide
  have hnp : listNorepet (varNames f_str_is_nonascii.fn_params) := by decide
  have hdisj : listDisjoint (varNames f_str_is_nonascii.fn_params)
      (varNames f_str_is_nonascii.fn_temps) := by decide
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_str_is_nonascii _ _
    (LocalSt emptyEnv [(_str, .Vptr sB sO)] K) (fun m => ?_) ?_
  · refine ⟨PTree.set _str (.Vptr sB sO) (createUndefTemps f_str_is_nonascii.fn_temps),
      FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl, fun hp hpre => ?_⟩
    exact ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_nil _), hpre.2⟩
  · exact triple_conseq ge _ _ (sin_body ge sB sO byte j N K hj hN hhi hload fd X hty hsat)
      (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

end sin

/-! ## 読む・書くメモリ -/

def fld (o : P) (d : Z) : P := Integers.Ptrofs.add o (Integers.Ptrofs.repr d)

/-- `data->conn` -/
def oConn (o : P) : P := fld o 0
/-- `data->req.p.telnet` -/
def oTel (o : P) : P := fld (fld (fld o 8) 0) 0
/-- `data->state.aptr.user` -/
def oAu (o : P) : P := fld (fld (fld o 16) 0) 0
/-- `data->set.telnet_options` -/
def oOpt (o : P) : P := fld (fld o 24) 0
/-- `tn->telnet_vars` -/
def oVars (o : P) : P := fld o 2216
/-- `tn->us_preferred[CURL_TELOPT_NEW_ENVIRON]`（39） -/
def oPref (o : P) : P :=
  Integers.Ptrofs.add (fld o 0)
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr 4) (Integers.Ptrofs.of_ints (Integers.Int.repr 39)))

/-- `byte` の `i` 文字目から `cnt` 文字を所有する。 -/
def strH (p : Permission) (b : Block) (o : P) (byte : Nat → Integers.Int) : Nat → Nat → HProp
  | _, 0 => emp
  | i, cnt + 1 => mapsto .Mint8signed p b (Integers.Ptrofs.unsigned (offs o i)) (.Vint (byte i))
      ∗ strH p b o byte (i + 1) cnt

theorem strH_load {p : Permission} {b : Block} {o : P} {byte : Nat → Integers.Int}
    (hpr : permOrder p .Readable = true) :
    ∀ (cnt i k : Nat) (h : Heap) (m : Mem), k < cnt → strH p b o byte i cnt h → Heap.Agrees h m →
      Mem.load .Mint8signed m b (Integers.Ptrofs.unsigned (offs o (i + k)))
        = some (Val.loadResult .Mint8signed (.Vint (byte (i + k))))
  | 0, _, _, _, _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | cnt + 1, i, 0, h, m, _, hs, hag => by
      obtain ⟨h1, c1, a1⟩ := sep_l hs hag
      exact mapsto_load hpr c1 a1
  | cnt + 1, i, k + 1, h, m, hk, hs, hag => by
      obtain ⟨h2, c2, a2⟩ := sep_r hs hag
      have := strH_load hpr cnt (i + 1) k h2 m (by omega) c2 a2
      rw [show i + (k + 1) = i + 1 + k by omega]
      exact this

structure Ctx where
  dB : Block              -- data
  dO : P
  tnB : Block             -- data->req.p.telnet
  tnO : P
  cnB : Block             -- data->conn
  cnO : P
  auV : Val               -- data->state.aptr.user
  uV : Val                -- conn->user
  optV : Val              -- data->set.telnet_options
  vars : Val              -- tn->telnet_vars（呼ぶ前）
  pref : Integers.Int     -- tn->us_preferred[39]（呼ぶ前）
  pm : Permission

/-- 呼び出しの前後で変わらないセル。 -/
def K (c : Ctx) : HProp :=
  mapsto Mptr c.pm c.dB (Integers.Ptrofs.unsigned (oConn c.dO)) (.Vptr c.cnB c.cnO) ∗
  (mapsto Mptr c.pm c.dB (Integers.Ptrofs.unsigned (oTel c.dO)) (.Vptr c.tnB c.tnO) ∗
  (mapsto Mptr c.pm c.dB (Integers.Ptrofs.unsigned (oAu c.dO)) c.auV ∗
  (mapsto Mptr c.pm c.dB (Integers.Ptrofs.unsigned (oOpt c.dO)) c.optV ∗
   mapsto Mptr c.pm c.cnB (Integers.Ptrofs.unsigned (fld c.cnO 0)) c.uV)))

/-- `tn` の2つのセル。ほかの `tn` のフィールドは所有しない。 -/
def T (c : Ctx) (vars : Val) (pref : Integers.Int) : HProp :=
  mapsto Mptr c.pm c.tnB (Integers.Ptrofs.unsigned (oVars c.tnO)) vars ∗
  mapsto .Mint32 c.pm c.tnB (Integers.Ptrofs.unsigned (oPref c.tnO)) (.Vint pref)

/-- 場面のメモリ `X` を足した全体。 -/
def Hs (c : Ctx) (vars : Val) (pref : Integers.Int) (X : HProp) : HProp := T c vars pref ∗ (K c ∗ X)

structure Loads (c : Ctx) (vars : Val) (m : Mem) : Prop where
  conn : Mem.load Mptr m c.dB (Integers.Ptrofs.unsigned (oConn c.dO)) = some (.Vptr c.cnB c.cnO)
  tel : Mem.load Mptr m c.dB (Integers.Ptrofs.unsigned (oTel c.dO)) = some (.Vptr c.tnB c.tnO)
  au : Mem.load Mptr m c.dB (Integers.Ptrofs.unsigned (oAu c.dO)) = some c.auV
  opt : Mem.load Mptr m c.dB (Integers.Ptrofs.unsigned (oOpt c.dO)) = some c.optV
  user : Mem.load Mptr m c.cnB (Integers.Ptrofs.unsigned (fld c.cnO 0)) = some c.uV
  vr : Mem.load Mptr m c.tnB (Integers.Ptrofs.unsigned (oVars c.tnO)) = some vars

/-- 読むポインタの値はポインタか NULL。 -/
structure Ptrs (c : Ctx) : Prop where
  au : IsPtr c.auV
  u : IsPtr c.uV
  opt : IsPtr c.optV

theorem Hs_loads {c : Ctx} {vars : Val} {pref : Integers.Int} {X Y : HProp} {hp : Heap} {m : Mem}
    (hpr : permOrder c.pm .Readable = true) (hP : Ptrs c) (hv : IsPtr vars)
    (hH : (Hs c vars pref X ∗ Y) hp) (hag : Heap.Agrees hp m) : Loads c vars m := by
  obtain ⟨h0, c0, a0⟩ := sep_l hH hag
  obtain ⟨t0, ct, at0⟩ := sep_l c0 a0
  obtain ⟨r0, cr, ar⟩ := sep_r c0 a0
  obtain ⟨tv, cv, av⟩ := sep_l ct at0
  obtain ⟨hK, cK, aK⟩ := sep_l cr ar
  obtain ⟨h1, c1, a1⟩ := sep_l cK aK
  obtain ⟨r1, d1, b1⟩ := sep_r cK aK
  obtain ⟨h2, c2, a2⟩ := sep_l d1 b1
  obtain ⟨r2, d2, b2⟩ := sep_r d1 b1
  obtain ⟨h3, c3, a3⟩ := sep_l d2 b2
  obtain ⟨r3, d3, b3⟩ := sep_r d2 b2
  obtain ⟨h4, c4, a4⟩ := sep_l d3 b3
  obtain ⟨h5, c5, a5⟩ := sep_r d3 b3
  have l3 := mapsto_load hpr c3 a3
  have l4 := mapsto_load hpr c4 a4
  have l5 := mapsto_load hpr c5 a5
  have l6 := mapsto_load hpr cv av
  rw [Case4C.loadResult_ptr hP.au] at l3
  rw [Case4C.loadResult_ptr hP.opt] at l4
  rw [Case4C.loadResult_ptr hP.u] at l5
  rw [Case4C.loadResult_ptr hv] at l6
  exact ⟨mapsto_load hpr c1 a1, mapsto_load hpr c2 a2, l3, l4, l5, l6⟩

/-! ## 構造体の配置（前置きが同じなので4つの翻訳単位で同じ） -/

section lay
open DebBookworm2023_27533_u1

theorem cenv_u0 : DebBookworm2023_27533_u0.prog.prog_comp_env = prog.prog_comp_env := rfl
theorem comp_d1 : DebBookworm2023_27533_d1.composites = composites := rfl
theorem comp_d0 : DebBookworm2023_27533_d0.composites = composites := rfl
theorem cenv_mk (t : List CompositeDef) (d d' p p' q q') :
    (mkprogram t d p q).prog_comp_env = (mkprogram t d' p' q').prog_comp_env := rfl
theorem cenv_d1 : DebBookworm2023_27533_d1.prog.prog_comp_env = prog.prog_comp_env := by
  unfold DebBookworm2023_27533_d1.prog prog
  rw [comp_d1]
  exact cenv_mk _ _ _ _ _ _ _
theorem cenv_d0 : DebBookworm2023_27533_d0.prog.prog_comp_env = prog.prog_comp_env := by
  unfold DebBookworm2023_27533_d0.prog prog
  rw [comp_d0]
  exact cenv_mk _ _ _ _ _ _ _

def coOf (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_easy : prog.prog_comp_env.get _Curl_easy = some (coOf _Curl_easy) := rfl
theorem co_req : prog.prog_comp_env.get _SingleRequest = some (coOf _SingleRequest) := rfl
theorem co_p : prog.prog_comp_env.get __105 = some (coOf __105) := rfl
theorem co_state : prog.prog_comp_env.get _UrlState = some (coOf _UrlState) := rfl
theorem co_aptr : prog.prog_comp_env.get _dynamically_allocated_data = some (coOf _dynamically_allocated_data) := rfl
theorem co_set : prog.prog_comp_env.get _UserDefined = some (coOf _UserDefined) := rfl
theorem co_conn : prog.prog_comp_env.get _connectdata = some (coOf _connectdata) := rfl
theorem co_tn : prog.prog_comp_env.get _TELNET = some (coOf _TELNET) := rfl
theorem co_sl : prog.prog_comp_env.get _curl_slist = some (coOf _curl_slist) := rfl

theorem off_conn : fieldOffset prog.prog_comp_env _conn (coOf _Curl_easy).co_members = .OK (0, .Full) := by decide
theorem off_req : fieldOffset prog.prog_comp_env _req (coOf _Curl_easy).co_members = .OK (8, .Full) := by decide
theorem off_p : fieldOffset prog.prog_comp_env _p (coOf _SingleRequest).co_members = .OK (0, .Full) := by decide
theorem off_telnet : fieldOffset prog.prog_comp_env _telnet (coOf __105).co_members = .OK (0, .Full) := by decide
theorem off_state : fieldOffset prog.prog_comp_env _state (coOf _Curl_easy).co_members = .OK (16, .Full) := by decide
theorem off_aptr : fieldOffset prog.prog_comp_env _aptr (coOf _UrlState).co_members = .OK (0, .Full) := by decide
theorem off_auser : fieldOffset prog.prog_comp_env _user (coOf _dynamically_allocated_data).co_members = .OK (0, .Full) := by decide
theorem off_set : fieldOffset prog.prog_comp_env _set (coOf _Curl_easy).co_members = .OK (24, .Full) := by decide
theorem off_opts : fieldOffset prog.prog_comp_env _telnet_options (coOf _UserDefined).co_members = .OK (0, .Full) := by decide
theorem off_cuser : fieldOffset prog.prog_comp_env _user (coOf _connectdata).co_members = .OK (0, .Full) := by decide
theorem off_vars : fieldOffset prog.prog_comp_env _telnet_vars (coOf _TELNET).co_members = .OK (2216, .Full) := by decide
theorem off_pref : fieldOffset prog.prog_comp_env _us_preferred (coOf _TELNET).co_members = .OK (0, .Full) := by decide
theorem off_sdata : fieldOffset prog.prog_comp_env _data (coOf _curl_slist).co_members = .OK (0, .Full) := by decide
theorem off_snext : fieldOffset prog.prog_comp_env _next (coOf _curl_slist).co_members = .OK (8, .Full) := by decide

/-! ## 式の値 -/

section ev
variable {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}

/-- 構造体の値を持つ `Efield`（内側の構造体。値はその番地）。 -/
theorem ev_sfld {a : Expr} {f sid sid' : Ident} {co : Composite} {b : Block} {o : P} {delta : Z}
    (hptr : EvalExpr ge e le m a (.Vptr b o)) (hty : typeof a = .Tstruct sid noattr)
    (hco : ge.genv_cenv.get sid = some co)
    (hfld : fieldOffset ge.genv_cenv f co.co_members = .OK (delta, .Full)) :
    EvalExpr ge e le m (.Efield a f (.Tstruct sid' noattr)) (.Vptr b (fld o delta)) :=
  EvalExpr.Elvalue _ _ _ .Full _
    (EvalLvalue.Efield_struct a f _ b o sid co noattr delta .Full hptr hty hco hfld)
    (DerefLoc.copy rfl)

/-- スカラーの `Efield`。 -/
theorem ev_vfld {a : Expr} {f sid : Ident} {ty : Ty} {co : Composite} {chunk : Chunk}
    {b : Block} {o : P} {delta : Z} {v : Val}
    (hptr : EvalExpr ge e le m a (.Vptr b o)) (hty : typeof a = .Tstruct sid noattr)
    (hco : ge.genv_cenv.get sid = some co)
    (hfld : fieldOffset ge.genv_cenv f co.co_members = .OK (delta, .Full))
    (hacc : accessMode ty = .By_value chunk)
    (hload : Mem.load chunk m b (Integers.Ptrofs.unsigned (fld o delta)) = some v) :
    EvalExpr ge e le m (.Efield a f ty) v :=
  EvalExpr.Elvalue _ _ _ .Full _
    (EvalLvalue.Efield_struct a f ty b o sid co noattr delta .Full hptr hty hco hfld)
    (DerefLoc.value chunk v hacc hload)

theorem ev_deref {p sid : Ident} {b : Block} {o : P} (hle : le.get p = some (.Vptr b o)) :
    EvalExpr ge e le m (.Ederef (.Etempvar p (tptr (.Tstruct sid noattr))) (.Tstruct sid noattr))
      (.Vptr b o) :=
  Case4C.eval_deref_temp hle

abbrev dataE : Expr :=
  .Ederef (.Etempvar _data (tptr (.Tstruct _Curl_easy noattr))) (.Tstruct _Curl_easy noattr)

theorem ev_tn (hc : ge.genv_cenv = prog.prog_comp_env) {c : Ctx} {v : Val} (L : Loads c v m)
    (hd : le.get _data = some (.Vptr c.dB c.dO)) :
    EvalExpr ge e le m (.Efield (.Efield (.Efield dataE _req (.Tstruct _SingleRequest noattr))
      _p (.Tstruct __105 noattr)) _telnet (tptr (.Tstruct _TELNET noattr))) (.Vptr c.tnB c.tnO) :=
  ev_vfld (ev_sfld (ev_sfld (ev_deref hd) rfl (hc ▸ co_easy) (hc ▸ off_req))
      rfl (hc ▸ co_req) (hc ▸ off_p)) rfl (hc ▸ co_p) (hc ▸ off_telnet) rfl L.tel

theorem ev_au (hc : ge.genv_cenv = prog.prog_comp_env) {c : Ctx} {v : Val} (L : Loads c v m)
    (hd : le.get _data = some (.Vptr c.dB c.dO)) :
    EvalExpr ge e le m (.Efield (.Efield (.Efield dataE _state (.Tstruct _UrlState noattr))
      _aptr (.Tstruct _dynamically_allocated_data noattr)) _user (tptr tschar)) c.auV :=
  ev_vfld (ev_sfld (ev_sfld (ev_deref hd) rfl (hc ▸ co_easy) (hc ▸ off_state))
      rfl (hc ▸ co_state) (hc ▸ off_aptr)) rfl (hc ▸ co_aptr) (hc ▸ off_auser) rfl L.au

theorem ev_opts (hc : ge.genv_cenv = prog.prog_comp_env) {c : Ctx} {v : Val} (L : Loads c v m)
    (hd : le.get _data = some (.Vptr c.dB c.dO)) :
    EvalExpr ge e le m (.Efield (.Efield dataE _set (.Tstruct _UserDefined noattr))
      _telnet_options (tptr (.Tstruct _curl_slist noattr))) c.optV :=
  ev_vfld (ev_sfld (ev_deref hd) rfl (hc ▸ co_easy) (hc ▸ off_set))
      rfl (hc ▸ co_set) (hc ▸ off_opts) rfl L.opt

theorem ev_conn (hc : ge.genv_cenv = prog.prog_comp_env) {c : Ctx} {v : Val} (L : Loads c v m)
    (hd : le.get _data = some (.Vptr c.dB c.dO)) :
    EvalExpr ge e le m (.Efield dataE _conn (tptr (.Tstruct _connectdata noattr)))
      (.Vptr c.cnB c.cnO) :=
  ev_vfld (ev_deref hd) rfl (hc ▸ co_easy) (hc ▸ off_conn) rfl L.conn

theorem ev_user (hc : ge.genv_cenv = prog.prog_comp_env) {c : Ctx} {v : Val} (L : Loads c v m)
    {p : Ident} (hd : le.get p = some (.Vptr c.cnB c.cnO)) :
    EvalExpr ge e le m (.Efield (.Ederef (.Etempvar p (tptr (.Tstruct _connectdata noattr)))
      (.Tstruct _connectdata noattr)) _user (tptr tschar)) c.uV :=
  ev_vfld (ev_deref hd) rfl (hc ▸ co_conn) (hc ▸ off_cuser) rfl L.user

theorem ev_vars (hc : ge.genv_cenv = prog.prog_comp_env) {c : Ctx} {v : Val} (L : Loads c v m)
    (hd : le.get _tn = some (.Vptr c.tnB c.tnO)) :
    EvalExpr ge e le m (.Efield (.Ederef (.Etempvar _tn (tptr (.Tstruct _TELNET noattr)))
      (.Tstruct _TELNET noattr)) _telnet_vars (tptr (.Tstruct _curl_slist noattr))) v :=
  ev_vfld (ev_deref hd) rfl (hc ▸ co_tn) (hc ▸ off_vars) rfl L.vr

theorem ev_sdata (hc : ge.genv_cenv = prog.prog_comp_env) {p : Ident} {b : Block} {o : P} {v : Val}
    (hd : le.get p = some (.Vptr b o))
    (hl : Mem.load Mptr m b (Integers.Ptrofs.unsigned (fld o 0)) = some v) :
    EvalExpr ge e le m (.Efield (.Ederef (.Etempvar p (tptr (.Tstruct _curl_slist noattr)))
      (.Tstruct _curl_slist noattr)) _data (tptr tschar)) v :=
  ev_vfld (ev_deref hd) rfl (hc ▸ co_sl) (hc ▸ off_sdata) rfl hl

theorem ev_snext (hc : ge.genv_cenv = prog.prog_comp_env) {p : Ident} {b : Block} {o : P} {v : Val}
    (hd : le.get p = some (.Vptr b o))
    (hl : Mem.load Mptr m b (Integers.Ptrofs.unsigned (fld o 8)) = some v) :
    EvalExpr ge e le m (.Efield (.Ederef (.Etempvar p (tptr (.Tstruct _curl_slist noattr)))
      (.Tstruct _curl_slist noattr)) _next (tptr (.Tstruct _curl_slist noattr))) v :=
  ev_vfld (ev_deref hd) rfl (hc ▸ co_sl) (hc ▸ off_snext) rfl hl

end ev

end lay

/-! ## 場面のメモリ -/

theorem X_of {c : Ctx} {vars : Val} {pref : Integers.Int} {X Y : HProp} {hp : Heap} {m : Mem}
    (hH : (Hs c vars pref X ∗ Y) hp) (hag : Heap.Agrees hp m) : ∃ h, X h ∧ Heap.Agrees h m := by
  obtain ⟨h0, c0, a0⟩ := sep_l hH hag
  obtain ⟨r0, cr, ar⟩ := sep_r c0 a0
  exact sep_r cr ar

/-- 場面 U（ユーザー名）のメモリの中身。 -/
structure SU where
  auB : Block             -- data->state.aptr.user
  auO : P
  au0 : Integers.Int      -- aptr.user[0]（ポインタが有効であることを言うために所有する）
  sB : Block              -- conn->user
  sO : P
  byte : Nat → Integers.Int   -- conn->user の各文字
  j : Nat                 -- 8 ビット目の立った文字の位置
  n : Nat                 -- strlen(conn->user)

def XU (c : Ctx) (u : SU) : HProp :=
  mapsto .Mint8signed c.pm u.auB (Integers.Ptrofs.unsigned u.auO) (.Vint u.au0) ∗
  strH c.pm u.sB u.sO u.byte 0 (u.j + 1)

/-- 場面 U の前提。 -/
structure SUok (c : Ctx) (u : SU) : Prop where
  au : c.auV = .Vptr u.auB u.auO
  user : c.uV = .Vptr u.sB u.sO
  hj : u.j < u.n
  hn : u.n < 18446744073709551616
  hhi : hiBit (u.byte u.j) = true

theorem XU_valid {c : Ctx} {u : SU} {vars : Val} {pref : Integers.Int} {Y : HProp} {hp : Heap} {m : Mem}
    (hpn : permOrder c.pm .Nonempty = true)
    (hH : (Hs c vars pref (XU c u) ∗ Y) hp) (hag : Heap.Agrees hp m) :
    Mem.weakValidPointer m u.auB (Integers.Ptrofs.unsigned u.auO) = true := by
  obtain ⟨h, hX, a⟩ := X_of hH hag
  obtain ⟨h1, c1, a1⟩ := sep_l hX a
  exact mapsto_weakValid hpn c1 a1 (by decide)

theorem XU_load {c : Ctx} {u : SU} {vars : Val} {pref : Integers.Int} {Y : HProp}
    (hpr : permOrder c.pm .Readable = true) :
    ∀ k, k ≤ u.j → ∀ hp m, (Hs c vars pref (XU c u) ∗ Y) hp → Heap.Agrees hp m →
      Mem.load .Mint8signed m u.sB (Integers.Ptrofs.unsigned (offs u.sO k))
        = some (Val.loadResult .Mint8signed (.Vint (u.byte k))) := by
  intro k hk hp m hH hag
  obtain ⟨h, hX, a⟩ := X_of hH hag
  obtain ⟨h2, c2, a2⟩ := sep_r hX a
  have := strH_load hpr (u.j + 1) 0 k h2 m (by omega) c2 a2
  simpa using this

/-- 場面 O（オプション）で、リストの1つの要素のセルの持ち主。`next` は NULL。 -/
structure Nd where
  nB : Block              -- data->set.telnet_options
  nO : P
  oV : Val                -- head->data

def XN (c : Ctx) (n : Nd) : HProp :=
  mapsto Mptr c.pm n.nB (Integers.Ptrofs.unsigned (fld n.nO 0)) n.oV ∗
  mapsto Mptr c.pm n.nB (Integers.Ptrofs.unsigned (fld n.nO 8)) Deb2026_3805C.nullV

/-- 場面 O の、`Hs` の第3引数が `XN ∗ Z` のときの読み出し。 -/
theorem XN_load {c : Ctx} {n : Nd} {vars : Val} {pref : Integers.Int} {Z Y : HProp} {hp : Heap} {m : Mem}
    (hpr : permOrder c.pm .Readable = true) (hN : IsPtr n.oV)
    (hH : (Hs c vars pref (XN c n ∗ Z) ∗ Y) hp) (hag : Heap.Agrees hp m) :
    Mem.load Mptr m n.nB (Integers.Ptrofs.unsigned (fld n.nO 0)) = some n.oV
    ∧ Mem.load Mptr m n.nB (Integers.Ptrofs.unsigned (fld n.nO 8)) = some Deb2026_3805C.nullV := by
  obtain ⟨h, hX, a⟩ := X_of hH hag
  obtain ⟨h1, c1, a1⟩ := sep_l hX a
  obtain ⟨h2, c2, a2⟩ := sep_l c1 a1
  obtain ⟨h3, c3, a3⟩ := sep_r c1 a1
  have l1 := mapsto_load hpr c2 a2
  have l2 := mapsto_load hpr c3 a3
  rw [Case4C.loadResult_ptr hN] at l1
  exact ⟨l1, l2⟩

/-- `X ∗ W` の形の場面で `next` を読む。 -/
theorem XN_next2 {c : Ctx} {n : Nd} {vars : Val} {pref : Integers.Int} {Z W Y : HProp} {hp : Heap} {m : Mem}
    (hpr : permOrder c.pm .Readable = true)
    (hH : (Hs c vars pref ((XN c n ∗ Z) ∗ W) ∗ Y) hp) (hag : Heap.Agrees hp m) :
    Mem.load Mptr m n.nB (Integers.Ptrofs.unsigned (fld n.nO 8)) = some Deb2026_3805C.nullV := by
  obtain ⟨h, hX, a⟩ := X_of hH hag
  obtain ⟨h0, c0, a0⟩ := sep_l hX a
  obtain ⟨h1, c1, a1⟩ := sep_l c0 a0
  obtain ⟨h3, c3, a3⟩ := sep_r c1 a1
  exact mapsto_load hpr c3 a3

theorem fld0 (o : P) : fld o 0 = o := by
  show o + (BitVec.ofInt _ 0) = o
  exact BitVec.add_zero o

theorem XN_valid {c : Ctx} {n : Nd} {vars : Val} {pref : Integers.Int} {Z Y : HProp} {hp : Heap} {m : Mem}
    (hpn : permOrder c.pm .Nonempty = true)
    (hH : (Hs c vars pref (XN c n ∗ Z) ∗ Y) hp) (hag : Heap.Agrees hp m) :
    Mem.weakValidPointer m n.nB (Integers.Ptrofs.unsigned n.nO) = true := by
  obtain ⟨h, hX, a⟩ := X_of hH hag
  obtain ⟨h1, c1, a1⟩ := sep_l hX a
  obtain ⟨h2, c2, a2⟩ := sep_l c1 a1
  have := mapsto_weakValid hpn c2 a2 (by decide)
  rwa [fld0] at this

theorem boolVal_p {b : Block} {o : P} {m : Mem} (x : Ty)
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.boolVal (.Vptr b o) (tptr x) m = some true := by
  simp only [Cop.boolVal, hv]
  rfl

/-- オプションが1つのリストの `for`。本体を1回（`P1` から `J` へ）、増分で `P0`、本体で抜ける。 -/
theorem loop_one (ge fe f) (P1 P0 J Q : Sep.Assn) (s1 s2 : Stmt)
    (h1 : Triple ge fe f P1 s1
      { normal := J, brk := Q, cont := J, ret := fun _ _ => False })
    (h2 : Triple ge fe f J s2
      { normal := P0, brk := Q, cont := Sep.Assn.no, ret := fun _ _ => False })
    (h0 : Triple ge fe f P0 s1
      { normal := Sep.Assn.no, brk := Q, cont := Sep.Assn.no, ret := fun _ _ => False }) :
    Triple ge fe f P1 (.Sloop s1 s2) (.only Q) := by
  let I : Nat → Sep.Assn := fun n => match n with
    | 0 => P0
    | _ + 1 => P1
  let J' : Nat → Sep.Assn := fun n => match n with
    | 0 => Sep.Assn.no
    | _ + 1 => J
  refine Sep.triple_loop ge fe f (.only Q) I J' s1 s2 (fun n => ?_) (fun n => ?_) 1
  · cases n with
    | zero => exact triple_conseq ge fe f h0 (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
                (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ x => x)
    | succ n => exact triple_conseq ge fe f h1 (fun _ _ _ x => x) (fun _ _ _ x => x)
                  (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  · cases n with
    | zero => exact Sep.triple_vacuous ge fe f s2 _
    | succ n => exact triple_conseq ge fe f h2 (fun _ _ _ x => x)
                  (fun e le hp x => ⟨0, Nat.succ_pos n, x⟩) (fun _ _ _ x => x)
                  (fun _ _ _ x => x) (fun _ _ x => x)

/-- 上流のオプションの文字列: `sep` に `=`、その次から引数。 -/
structure SOU where
  nB : Block
  nO : P
  oB : Block              -- head->data（option）
  oO : P
  sepO : P                -- strchr(option, '=') が返す位置
  eqc : Integers.Int      -- option[sep]
  byte : Nat → Integers.Int   -- 引数の各文字
  j : Nat                 -- 8 ビット目の立った文字の位置
  n : Nat                 -- strlen(arg)

def SOU.nd (s : SOU) : Nd := ⟨s.nB, s.nO, .Vptr s.oB s.oO⟩

def XOU (c : Ctx) (s : SOU) : HProp :=
  XN c s.nd ∗ (mapsto .Mint8signed c.pm s.oB (Integers.Ptrofs.unsigned s.sepO) (.Vint s.eqc) ∗
    strH c.pm s.oB (nextO s.sepO) s.byte 0 (s.j + 1))

/-- 場面 O の前提（上流）。 -/
structure SOUok (c : Ctx) (s : SOU) : Prop where
  au : c.auV = Deb2026_3805C.nullV
  opt : c.optV = .Vptr s.nB s.nO
  hj : s.j < s.n
  hn : s.n < 18446744073709551616
  hhi : hiBit (s.byte s.j) = true

theorem XOU_valid {c : Ctx} {s : SOU} {vars : Val} {pref : Integers.Int} {Y : HProp} {hp : Heap} {m : Mem}
    (hpn : permOrder c.pm .Nonempty = true)
    (hH : (Hs c vars pref (XOU c s) ∗ Y) hp) (hag : Heap.Agrees hp m) :
    Mem.weakValidPointer m s.oB (Integers.Ptrofs.unsigned s.sepO) = true := by
  obtain ⟨h, hX, a⟩ := X_of hH hag
  obtain ⟨h1, c1, a1⟩ := sep_r hX a
  obtain ⟨h2, c2, a2⟩ := sep_l c1 a1
  exact mapsto_weakValid hpn c2 a2 (by decide)

theorem XOU_load {c : Ctx} {s : SOU} {vars : Val} {pref : Integers.Int} {Y : HProp}
    (hpr : permOrder c.pm .Readable = true) :
    ∀ k, k ≤ s.j → ∀ hp m, (Hs c vars pref (XOU c s) ∗ Y) hp → Heap.Agrees hp m →
      Mem.load .Mint8signed m s.oB (Integers.Ptrofs.unsigned (offs (nextO s.sepO) k))
        = some (Val.loadResult .Mint8signed (.Vint (s.byte k))) := by
  intro k hk hp m hH hag
  obtain ⟨h, hX, a⟩ := X_of hH hag
  obtain ⟨h1, c1, a1⟩ := sep_r hX a
  obtain ⟨h2, c2, a2⟩ := sep_r c1 a1
  have := strH_load hpr (s.j + 1) 0 k h2 m (by omega) c2 a2
  simpa using this

/-- 追っている一時変数を減らす。 -/
theorem tmono (ge fe f) {E : Env} {l l' : List (Ident × Val)} {H : HProp} {s : Stmt} {R : Sep.ExitConds}
    (hsub : ∀ p ∈ l', p ∈ l) (h : Triple ge fe f (LocalSt E l' H) s R) :
    Triple ge fe f (LocalSt E l H) s R :=
  triple_conseq ge fe f h (fun _ _ _ ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono hsub hT, hH⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

theorem lmono {E : Env} {l l' : List (Ident × Val)} {H : HProp} {e le hp}
    (hsub : ∀ p ∈ l', p ∈ l) (h : LocalSt E l H e le hp) : LocalSt E l' H e le hp :=
  ⟨h.1, TempsHold_mono hsub h.2.1, h.2.2⟩

/-! ## 局所の配列の初期化（D。`char a[N] = "";` は `N` 個の 1 バイトの代入になる） -/

/-- `a[i] = 0; … a[i+k-1] = 0; rest` -/
def initSeq (id : Ident) (N : Nat) : Nat → Nat → Stmt → Stmt
  | _, 0, rest => rest
  | i, k + 1, rest => .Ssequence
      (.Sassign (.Ederef (.Ebinop .Oadd (.Evar id (tarray tschar N))
          (.Econst_int (Integers.Int.repr (i : _root_.Int)) tint) (tptr tschar)) tschar)
        (.Econst_int (Integers.Int.repr 0) tint))
      (initSeq id N (i + 1) k rest)

/-- 文の並びの先頭の `n` 個を落とす。 -/
def dropS : Nat → Stmt → Stmt
  | 0, s => s
  | n + 1, .Ssequence _ s => dropS n s
  | _, s => s

theorem ev_arr {ge : CGenv} {E : Env} {le : TempEnv} {m : Mem} {x : Ident} {b : Block} {N : Nat}
    (he : E.get x = some (b, tarray tschar N)) :
    EvalExpr ge E le m (.Evar x (tarray tschar N)) (.Vptr b Integers.Ptrofs.zero) :=
  EvalExpr.Elvalue _ _ _ .Full _ (EvalLvalue.Evar_local _ _ _ he) (DerefLoc.reference rfl)

/-- `a + i`（`a` は配列、`i` は `int` の定数）の番地。 -/
def iofs (i : Nat) : P :=
  Integers.Ptrofs.add Integers.Ptrofs.zero
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr 1) (Integers.Ptrofs.of_ints (Integers.Int.repr (i : _root_.Int))))

theorem one_mul_p (x : P) : Integers.Ptrofs.mul (Integers.Ptrofs.repr 1) x = x := by
  show (BitVec.ofInt _ 1) * x = x
  have : (BitVec.ofInt Archi.ptrWordsize 1) = 1#64 := by decide
  rw [this]
  exact BitVec.one_mul x

theorem zero_add_p (x : P) : Integers.Ptrofs.add Integers.Ptrofs.zero x = x := by
  show (0 : BitVec _) + x = x
  exact BitVec.zero_add x

theorem iofs_unsigned (i : Nat) (h : i < 2147483648) : Integers.Ptrofs.unsigned (iofs i) = i := by
  unfold iofs
  rw [one_mul_p, zero_add_p]
  have hs : Integers.MI.signed (Integers.Int.repr (i : _root_.Int)) = (i : _root_.Int) := i32_signed_repr i h
  show Integers.MI.unsigned (Integers.MI.repr (Integers.MI.signed (Integers.Int.repr (i : _root_.Int))) : P) = _
  rw [hs]
  have hw : (2 : Nat) ^ Archi.ptrWordsize = 18446744073709551616 := by rw [Archi.ptrWordsize_eq]
  simp only [Integers.MI.unsigned, Integers.MI.repr, BitVec.toNat_ofInt, hw]
  rw [Int.emod_eq_of_lt (by omega) (by simp; omega)]
  simp

theorem arrN_eq (b : Block) (d k : Nat) :
    anyBytes .Freeable b 0 (d + (1 + k)) = anyBytes .Freeable b 0 d ∗ (anyBytes .Freeable b (d : _root_.Int) 1 ∗
      anyBytes .Freeable b ((d : _root_.Int) + 1) k) := by
  rw [anyBytes_split, anyBytes_split, show (0 : _root_.Int) + (d : _root_.Int) = d from by omega,
    show ((1 : Nat) : _root_.Int) = 1 from rfl]

/-- 配列の `d` 番目に `char` を書く。中身を問わないので形は変わらない。 -/
theorem store_keep (ge fe f) (E : Env) (lt : List (Ident × Val)) (R : HProp) (b : Block) (d k : Nat)
    (ofs : P) (hofs : Integers.Ptrofs.unsigned ofs = d) (vnew : Val) (a1 a2 : Expr)
    (hacc : accessMode (typeof a1) = .By_value .Mint8signed)
    (hlv : ∀ le m, TempsHold lt le → EvalLvalue ge E le m a1 b ofs .Full)
    (hrhs : ∀ le m, TempsHold lt le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew) :
    Triple ge fe f (LocalSt E lt (anyBytes .Freeable b 0 (d + (1 + k)) ∗ R)) (.Sassign a1 a2)
      (.only (LocalSt E lt (anyBytes .Freeable b 0 (d + (1 + k)) ∗ R))) := by
  have h := Deb2026_8924.store_front ge fe f E lt
    ((anyBytes .Freeable b 0 d ∗ anyBytes .Freeable b ((d : _root_.Int) + 1) k) ∗ R)
    b ofs vnew a1 a2 hacc hlv hrhs
  rw [hofs] at h
  have e : anyBytes .Freeable b 0 (d + (1 + k)) ∗ R
      = anyBytes .Freeable b (d : _root_.Int) 1 ∗
        ((anyBytes .Freeable b 0 d ∗ anyBytes .Freeable b ((d : _root_.Int) + 1) k) ∗ R) := by
    rw [arrN_eq, sep_left_comm_eq (anyBytes .Freeable b 0 d), sep_assoc_eq]
  rw [e]
  refine triple_conseq ge fe f h (fun _ _ _ x => x) ?_ (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
    (fun _ _ x => x.elim)
  intro e' le hp ⟨he, hT, h1, h2, hd, hu, hm, hr⟩
  exact ⟨he, hT, h1, h2, hd, hu, Case3C.mapsto_anyBytes hm, hr⟩

theorem init_chain (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp) (b : Block) (id : Ident) (N : Nat)
    (hE : E.get id = some (b, tarray tschar N)) (hN : N < 2147483648) :
    ∀ (k i : Nat) (rest : Stmt) (Rx : Sep.ExitConds), i + k = N →
      Triple ge fe f (LocalSt E l (anyBytes .Freeable b 0 N ∗ R)) rest Rx →
      Triple ge fe f (LocalSt E l (anyBytes .Freeable b 0 N ∗ R)) (initSeq id N i k rest) Rx
  | 0, _, _, _, _, h => h
  | k + 1, i, rest, Rx, hi, h => by
      have ih := init_chain ge fe f E l R b id N hE hN k (i + 1) rest Rx (by omega) h
      refine triple_seq_fwd ge fe f _ _ _ _ _ ?_ ih
      obtain ⟨k', hk'⟩ : ∃ k', N = i + (1 + k') := ⟨k, by omega⟩
      subst hk'
      refine store_keep ge fe f E l R b i k' (iofs i) (iofs_unsigned i (by omega))
        (.Vint (Integers.Int.sign_ext 8 (Integers.Int.repr 0))) _ _ rfl (fun le m _ => ?_)
        (fun le m _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)
      exact EvalLvalue.Ederef _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (ev_arr hE) (EvalExpr.Econst_int _ _) rfl)

/-- Debian のオプション: 要素のセルと、`sscanf` が `option_arg` に書く文字列。 -/
structure SOD where
  nd : Nd
  byte : Nat → Integers.Int   -- option_arg の各文字
  j : Nat                 -- 8 ビット目の立った文字の位置
  n : Nat                 -- strlen(option_arg)

structure SODok (c : Ctx) (s : SOD) : Prop where
  au : c.auV = Deb2026_3805C.nullV
  opt : c.optV = .Vptr s.nd.nB s.nd.nO
  oV : IsPtr s.nd.oV
  hj : s.j < s.n
  hj2 : s.j < 256
  hn : s.n < 18446744073709551616
  hhi : hiBit (s.byte s.j) = true

theorem offs_zero (i : Nat) (h : i < 18446744073709551616) :
    Integers.Ptrofs.unsigned (offs Integers.Ptrofs.zero i) = i := by
  have hw : (2 : Nat) ^ Archi.ptrWordsize = 18446744073709551616 := by rw [Archi.ptrWordsize_eq]
  induction i with
  | zero => rfl
  | succ i ih =>
      have ih' := ih (by omega)
      show Integers.Ptrofs.unsigned (nextO (offs Integers.Ptrofs.zero i)) = _
      unfold nextO
      rw [one_mul_p]
      have h1 : (Integers.Ptrofs.of_ints (Integers.Int.repr 1)).toNat = 1 := by decide
      have h2 : (offs Integers.Ptrofs.zero i).toNat = i := by
        have : (((offs Integers.Ptrofs.zero i).toNat : Nat) : _root_.Int) = (i : _root_.Int) := ih'
        omega
      simp only [Integers.Ptrofs.unsigned, Integers.Ptrofs.add, Integers.MI.unsigned, Integers.MI.add,
        BitVec.toNat_add, hw, h1, h2]
      rw [Nat.mod_eq_of_lt h]

/-- `option_arg` の先頭 `cnt` バイトは文字列で、後ろは中身を問わない。 -/
def argH (b : Block) (byte : Nat → Integers.Int) (cnt : Nat) : HProp :=
  strH .Freeable b Integers.Ptrofs.zero byte 0 cnt ∗ anyBytes .Freeable b (cnt : _root_.Int) (256 - cnt)

theorem strH_any {b : Block} {byte : Nat → Integers.Int} :
    ∀ (cnt i : Nat) (h : Heap), i + cnt < 18446744073709551616 →
      strH .Freeable b Integers.Ptrofs.zero byte i cnt h → anyBytes .Freeable b (i : _root_.Int) cnt h
  | 0, _, _, _, hs => by rw [anyBytes_zero]; exact hs
  | cnt + 1, i, h, hi, hs => by
      obtain ⟨h1, h2, hd, rfl, hm, hr⟩ := hs
      rw [show cnt + 1 = sizeChunkNat .Mint8signed + cnt by rw [Nat.add_comm]; rfl, anyBytes_split]
      refine ⟨h1, h2, hd, rfl, ?_, ?_⟩
      · have := Case3C.mapsto_anyBytes hm
        rwa [offs_zero i (by omega)] at this
      · have := strH_any cnt (i + 1) h2 (by omega) hr
        rwa [show (((i + 1 : Nat)) : _root_.Int) = (i : _root_.Int) + (sizeChunkNat .Mint8signed : Nat) by
          show _ = (i : _root_.Int) + ((1 : Nat) : _root_.Int); omega] at this

theorem argH_any {b : Block} {byte : Nat → Integers.Int} {cnt : Nat} {h : Heap} (hc : cnt ≤ 256)
    (hA : argH b byte cnt h) : anyBytes .Freeable b 0 256 h := by
  obtain ⟨h1, h2, hd, rfl, a1, a2⟩ := hA
  rw [show (256 : Nat) = cnt + (256 - cnt) by omega, anyBytes_split]
  refine ⟨h1, h2, hd, rfl, strH_any cnt 0 h1 (by omega) a1, ?_⟩
  rw [show (0 : _root_.Int) + (cnt : _root_.Int) = cnt by omega]
  exact a2

def XD (c : Ctx) (s : SOD) : HProp := XN c s.nd ∗ emp

/-- `sscanf` が書いたあとの局所変数（`option_keyword`・`option_arg`）。 -/
def YA (s : SOD) (b1 b2 : Block) : HProp :=
  anyBytes .Freeable b1 0 128 ∗ (argH b2 s.byte (s.j + 1) ∗ emp)

theorem YA_locs {s : SOD} {b1 b2 : Block} {h : Heap} (hj : s.j < 256) (hY : YA s b1 b2 h) :
    Case3C.Locs [(b1, 128), (b2, 256)] h := by
  obtain ⟨h1, h2, d, rfl, a1, h3, h4, d2, rfl, a3, he⟩ := hY
  exact ⟨h1, _, d, rfl, a1, h3, h4, d2, rfl, argH_any (by omega) a3, he⟩

theorem YA_load {c : Ctx} {s : SOD} {b1 b2 : Block} {vars : Val} {pref : Integers.Int} {X : HProp} :
    ∀ k, k ≤ s.j → ∀ hp m, (Hs c vars pref X ∗ YA s b1 b2) hp → Heap.Agrees hp m →
      Mem.load .Mint8signed m b2 (Integers.Ptrofs.unsigned (offs Integers.Ptrofs.zero k))
        = some (Val.loadResult .Mint8signed (.Vint (s.byte k))) := by
  intro k hk hp m hH hag
  obtain ⟨h0, c0, a0⟩ := sep_r hH hag
  obtain ⟨h1, c1, a1⟩ := sep_r c0 a0
  obtain ⟨h2, c2, a2⟩ := sep_l c1 a1
  obtain ⟨h3, c3, a3⟩ := sep_l c2 a2
  have := strH_load (by decide) (s.j + 1) 0 k h3 m (by omega) c3 a3
  simpa using this

/-! ## P0: `tn` に書くこと -/

/-- `curl_slist_append` が返す `nb`。指す先の1バイトを所有する（ポインタが有効であることを言うため）。 -/
def NB (c : Ctx) (nbB : Block) (nbO : P) (w : Integers.Int) : HProp :=
  mapsto .Mint8signed c.pm nbB (Integers.Ptrofs.unsigned nbO) (.Vint w)

theorem NB_valid {c : Ctx} {nbB : Block} {nbO : P} {w : Integers.Int} {X Y : HProp} {vars : Val}
    {pref : Integers.Int} {hp : Heap} {m : Mem} (hpn : permOrder c.pm .Nonempty = true)
    (hH : (Hs c vars pref (X ∗ NB c nbB nbO w) ∗ Y) hp) (hag : Heap.Agrees hp m) :
    Mem.weakValidPointer m nbB (Integers.Ptrofs.unsigned nbO) = true := by
  obtain ⟨h, hX, a⟩ := X_of hH hag
  obtain ⟨h1, c1, a1⟩ := sep_r hX a
  exact mapsto_weakValid hpn c1 a1 (by decide)

theorem notbool_p {b : Block} {o : P} {m : Mem} (x : Ty)
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.semUnaryOperation .Onotbool (.Vptr b o) (tptr x) m = some (Val.ofBool false) := by
  simp only [Cop.semUnaryOperation, Cop.semNotbool, Cop.boolVal, hv]
  rfl

theorem Hs_vars_eq (c : Ctx) (v : Val) (p : Integers.Int) (X Y : HProp) :
    (Hs c v p X ∗ Y) = mapsto Mptr c.pm c.tnB (Integers.Ptrofs.unsigned (oVars c.tnO)) v ∗
      (mapsto .Mint32 c.pm c.tnB (Integers.Ptrofs.unsigned (oPref c.tnO)) (.Vint p) ∗ ((K c ∗ X) ∗ Y)) := by
  unfold Hs T
  rw [sep_assoc_eq, sep_assoc_eq]

theorem Hs_pref_eq (c : Ctx) (v : Val) (p : Integers.Int) (X Y : HProp) :
    (Hs c v p X ∗ Y) = mapsto .Mint32 c.pm c.tnB (Integers.Ptrofs.unsigned (oPref c.tnO)) (.Vint p) ∗
      (mapsto Mptr c.pm c.tnB (Integers.Ptrofs.unsigned (oVars c.tnO)) v ∗ ((K c ∗ X) ∗ Y)) := by
  rw [Hs_vars_eq, sep_left_comm_eq]

theorem store_vars (ge fe f) (E : Env) (lt : List (Ident × Val)) (c : Ctx) (v v' : Val)
    (p : Integers.Int) (X Y : HProp) (a1 a2 : Expr)
    (hpw : permOrder c.pm .Writable = true) (hacc : accessMode (typeof a1) = .By_value Mptr)
    (hlv : ∀ le m, TempsHold lt le → EvalLvalue ge E le m a1 c.tnB (oVars c.tnO) .Full)
    (hrhs : ∀ le m, TempsHold lt le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some v') :
    Triple ge fe f (LocalSt E lt (Hs c v p X ∗ Y)) (.Sassign a1 a2)
      (.only (LocalSt E lt (Hs c v' p X ∗ Y))) := by
  rw [Hs_vars_eq, Hs_vars_eq]
  refine Sep.triple_assign ge fe f _ _ a1 a2 Mptr c.pm c.tnB (oVars c.tnO) hpw hacc (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, rfl, hm, hR⟩ := hP
  subst he
  exact ⟨v, v', h1, h2, hd, rfl, hm, hlv le m hT, hrhs le m hT,
    fun h1' hm' hd' => ⟨rfl, hT, h1', h2, hd', rfl, hm', hR⟩⟩

theorem store_pref (ge fe f) (E : Env) (lt : List (Ident × Val)) (c : Ctx) (v : Val)
    (p p' : Integers.Int) (X Y : HProp) (a1 a2 : Expr)
    (hpw : permOrder c.pm .Writable = true) (hacc : accessMode (typeof a1) = .By_value .Mint32)
    (hlv : ∀ le m, TempsHold lt le → EvalLvalue ge E le m a1 c.tnB (oPref c.tnO) .Full)
    (hrhs : ∀ le m, TempsHold lt le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some (.Vint p')) :
    Triple ge fe f (LocalSt E lt (Hs c v p X ∗ Y)) (.Sassign a1 a2)
      (.only (LocalSt E lt (Hs c v p' X ∗ Y))) := by
  rw [Hs_pref_eq, Hs_pref_eq]
  refine Sep.triple_assign ge fe f _ _ a1 a2 .Mint32 c.pm c.tnB (oPref c.tnO) hpw hacc (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, rfl, hm, hR⟩ := hP
  subst he
  exact ⟨.Vint p, .Vint p', h1, h2, hd, rfl, hm, hlv le m hT, hrhs le m hT,
    fun h1' hm' hd' => ⟨rfl, hT, h1', h2, hd', rfl, hm', hR⟩⟩

section lv
open DebBookworm2023_27533_u1
variable {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}

abbrev tnE : Expr := .Ederef (.Etempvar _tn (tptr (.Tstruct _TELNET noattr))) (.Tstruct _TELNET noattr)

theorem lv_vars (hc : ge.genv_cenv = prog.prog_comp_env) {c : Ctx}
    (hd : le.get _tn = some (.Vptr c.tnB c.tnO)) :
    EvalLvalue ge e le m (.Efield tnE _telnet_vars (tptr (.Tstruct _curl_slist noattr)))
      c.tnB (oVars c.tnO) .Full :=
  Case4debC.lv_field (ev_deref hd) rfl (hc ▸ co_tn) (hc ▸ off_vars)

theorem lv_pref (hc : ge.genv_cenv = prog.prog_comp_env) {c : Ctx}
    (hd : le.get _tn = some (.Vptr c.tnB c.tnO)) :
    EvalLvalue ge e le m
      (.Ederef (.Ebinop .Oadd (.Efield tnE _us_preferred (tarray tint 256))
        (.Econst_int (Integers.Int.repr 39) tint) (tptr tint)) tint) c.tnB (oPref c.tnO) .Full :=
  EvalLvalue.Ederef _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
    (EvalExpr.Elvalue _ _ _ .Full _ (Case4debC.lv_field (ev_deref hd) rfl (hc ▸ co_tn) (hc ▸ off_pref))
      (DerefLoc.reference rfl))
    (EvalExpr.Econst_int _ _) rfl)

end lv

/-- 修正前の事後条件: 0 を返し、`tn->telnet_vars` は `nb`、`tn->us_preferred[39]` は 1。 -/
def post0 (c : Ctx) (nb : Val) (X : HProp) : Val → HProp :=
  fun v hp => v = .Vint (Integers.Int.repr 0) ∧ Hs c nb (Integers.Int.repr 1) X hp

/-- リストが空の `for`。本体で抜ける。 -/
theorem loop_zero (ge fe f) (P0 Q : Sep.Assn) (s1 s2 : Stmt)
    (h0 : Triple ge fe f P0 s1
      { normal := Sep.Assn.no, brk := Q, cont := Sep.Assn.no, ret := fun _ _ => False }) :
    Triple ge fe f P0 (.Sloop s1 s2) (.only Q) :=
  Sep.triple_loop ge fe f (.only Q) (fun _ => P0) (fun _ => Sep.Assn.no) s1 s2
    (fun _ => triple_conseq ge fe f h0 (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
      (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ x => x))
    (fun _ => Sep.triple_vacuous ge fe f s2 _) 0

set_option hygiene false in
/-- `id = a;`（値は `v`）の証明の入口。式の値を示す目標を残す。 -/
macro "sset " v:term : tactic =>
  `(tactic| (refine triple_set_local_fwd _ _ _ _ _ _ _ _ ($v) ?_; intro le m hp hT hH hag))

set_option hygiene false in
/-- 一時変数の値 -/
macro "tv " v:term : term => `(EvalExpr.Etempvar _ _ ($v) (hT.get (by temps_get)))

/-! ## 関数の仕様 -/

/-- `check_telnet_options(data)` の仕様。 -/
def post1 (r : Z) (Pre : HProp) : Val → HProp :=
  fun v hp => v = .Vint (Integers.Int.repr r) ∧ Pre hp

def ctoSpec (c : Ctx) (Pre : HProp) (Post : Val → HProp) : FunSpec where
  tyargs := [tptr (Ty.Tstruct DebBookworm2023_27533_u1._Curl_easy noattr)]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dB c.dO] ∧ Pre hp
  post := Post
  measure := fun _ => 0

/-- 呼ばれる側の仕様の形: 引数は `args`、メモリの形 `A` を受け取り `B` にして返す。戻り値は `r`（`none` なら問わない）。 -/
def specA (tyargs : List Ty) (tyres : Ty) (args : List Val) (A B : HProp) (r : Option Val) : FunSpec where
  tyargs := tyargs
  tyres := tyres
  cc := cc_default
  pre := fun vargs hp => vargs = args ∧ A hp
  post := fun v hp => (∀ x, r = some x → v = x) ∧ B hp
  measure := fun _ => 0

theorem callA_some (ge fe f) (tyargs : List Ty) (tyres : Ty) (args : List Val) (A B : HProp) (vret : Val)
    (id : Ident) (callee : Expr) (al : List Expr) (E : Env) (l : List (Ident × Val))
    (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd (specA tyargs tyres args A B (some vret)) vs)
    (hfind : FuncPtr ge fb fd) (hty : typeOfFundef fd = .Tfunction tyargs tyres cc_default)
    (hclass : Cop.classifyFun (typeof callee) = .f tyargs tyres cc_default)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al tyargs args) :
    Triple ge fe f (LocalSt E l A) (.Scall (some id) callee al)
      (.only (LocalSt E (setLocal l id vret) B)) :=
  Deb2025_14524.callS_some ge fe f (specA tyargs tyres args A B (some vret)) A B vret id callee al E l
    args fb fd hspec hfind hty hclass hcallee hargs (fun _ h => ⟨rfl, h⟩)
    (fun v hp h => ⟨h.1 _ rfl, h.2⟩)

theorem callA_none (ge fe f) (tyargs : List Ty) (tyres : Ty) (args : List Val) (A B : HProp)
    (callee : Expr) (al : List Expr) (E : Env) (l : List (Ident × Val))
    (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd (specA tyargs tyres args A B none) vs)
    (hfind : FuncPtr ge fb fd) (hty : typeOfFundef fd = .Tfunction tyargs tyres cc_default)
    (hclass : Cop.classifyFun (typeof callee) = .f tyargs tyres cc_default)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al tyargs args) :
    Triple ge fe f (LocalSt E l A) (.Scall none callee al) (.only (LocalSt E l B)) := by
  refine Sep.triple_call ge fe f (specA tyargs tyres args A B none) none callee al _ _ fb fd hspec hfind
    hty hclass (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, hK⟩ := hP
  subst he
  refine ⟨args, hp, Heap.emp, Heap.disjoint_emp_right hp, (Heap.union_emp hp).symm,
    hcallee le m hT, hargs le m hT, ⟨rfl, hK⟩, ?_⟩
  intro v h1' hpost _
  rw [Heap.union_emp]
  exact ⟨rfl, hT, hpost.2⟩

end DebBookworm2023_27533C
