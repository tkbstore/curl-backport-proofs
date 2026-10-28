/-
Case 1: 呼ばれる側の関数の仕様と、定理の仮定（`Ext`）。

どの仕様も、呼び出しの引数を実際の値に固定し、メモリ全体 `H` を受け取って同じ形で返す。
戻り値は「型の合った何か」とだけ書く。値を決めるのは次の3つだけ:

- `curlx_dyn_len` は受信バッファの長さを返す。`curlx_dyn_ptr` はその先頭を返す
- `curlx_dyn_tail(s, t)` は長さを `t` にする（`t` が長さ以下のとき。curl の dynbuf.c と同じ）。
  `curlx_dyn_reset` は長さを 0 にする
- `memchr(p, c, k)` は NULL か、`p` から `k` バイト未満の位置を返す

**前提として置いた制限**: `Curl_conn_recv` が CURLE_OK を返すとき、読んだバイト数は 0 でない。
0 バイトの経路では `failf(data, "...%d", SOCKERRNO)` が呼ばれるが、可変長引数の呼び出しは、
宣言にない3つ目の引数の型が呼び出しの型に入らない（CompCert の C2C が宣言の型をそのまま使う）。
`EvalExprlist` は引数と型の数が合わないと成り立たないので、Clight の意味論ではこの呼び出しから先へ進めない。
この経路は、どの性質もこの道具では示せないので、前提で除いた。RESULTS に記録する。
-/
import Case1Rules
open CC CC.Sep CC.HProp
open Case1_after
open Case4C (IsPtr)

set_option maxRecDepth 20000

namespace Case1C

abbrev tyEasy : Ty := tptr (Ty.Tstruct _Curl_easy noattr)
abbrev tyDyn : Ty := tptr (Ty.Tstruct _dynbuf noattr)

/-- `sizeof(buffer)` の値。 -/
def v900 : Val := Val.Vptrofs (Integers.Ptrofs.repr 900)

/-- `gotbytes = 0;` で書かれる値。 -/
def vzero : Val := .Vlong (Integers.Int64.repr 0)

variable (c : Ctx) (DB : Nat → Val → HProp)

def recvSpec (n : Nat) (p gv : Val) : FunSpec where
  tyargs := [tyEasy, tschar, tptr tschar, tulong, tptr tulong]
  tyres := tint
  cc := cc_default
  pre := fun vargs h =>
    vargs = [.Vptr c.dataB c.dataO, c.sockV, .Vptr c.bb Integers.Ptrofs.zero, v900,
             .Vptr c.bg Integers.Ptrofs.zero] ∧ H c DB n p gv h
  post := fun v h => ∃ r g, v = .Vint r ∧ (r = Integers.Int.zero → g ≠ Integers.Int64.zero)
    ∧ H c DB n p (.Vlong g) h
  measure := fun _ => 0

def lenSpec (n : Nat) (p gv : Val) : FunSpec where
  tyargs := [tyDyn]
  tyres := tulong
  cc := cc_default
  pre := fun vargs h => vargs = [rbV c] ∧ H c DB n p gv h
  post := fun v h => v = .Vlong (Integers.Int64.repr n) ∧ H c DB n p gv h
  measure := fun _ => 0

def ptrSpec (n : Nat) (p gv : Val) : FunSpec where
  tyargs := [tyDyn]
  tyres := tptr tschar
  cc := cc_default
  pre := fun vargs h => vargs = [rbV c] ∧ H c DB n p gv h
  post := fun v h => v = p ∧ H c DB n p gv h
  measure := fun _ => 0

/-- 長さを `t` にする。`t` が今の長さより大きいときは何もしない。 -/
def tailLen (n : Nat) (t : Integers.Int64) : Nat :=
  if (Integers.Int64.unsigned t).toNat ≤ n then (Integers.Int64.unsigned t).toNat else n

def tailSpec (n : Nat) (p gv : Val) (t : Integers.Int64) : FunSpec where
  tyargs := [tyDyn, tulong]
  tyres := tint
  cc := cc_default
  pre := fun vargs h => vargs = [rbV c, .Vlong t] ∧ H c DB n p gv h
  post := fun v h => (∃ r, v = .Vint r) ∧ ∃ p', H c DB (tailLen n t) p' gv h
  measure := fun _ => 0

def resetSpec (n : Nat) (p gv : Val) : FunSpec where
  tyargs := [tyDyn]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs h => vargs = [rbV c] ∧ H c DB n p gv h
  post := fun _ h => ∃ p', H c DB 0 p' gv h
  measure := fun _ => 0

def addnSpec (n : Nat) (p gv : Val) : FunSpec where
  tyargs := [tyDyn, tptr tvoid, tulong]
  tyres := tint
  cc := cc_default
  pre := fun vargs h => vargs = [rbV c, .Vptr c.bb Integers.Ptrofs.zero, gv] ∧ H c DB n p gv h
  post := fun v h => (∃ r, v = .Vint r) ∧ ∃ n' p', H c DB n' p' gv h
  measure := fun _ => 0

/-- `memchr` の戻り値: NULL か、`p` から `k` バイト未満の位置。 -/
def InRange (p : Val) (k : Integers.Int64) (v : Val) : Prop :=
  v = .Vlong Integers.Int64.zero ∨
  ∃ (bl : Block) (ol : Integers.Ptrofs) (i : Nat), p = .Vptr bl ol ∧ (i : _root_.Int) < Integers.Int64.unsigned k
    ∧ v = .Vptr bl (Integers.Ptrofs.add ol (Integers.Ptrofs.repr i))

def memchrSpec (n : Nat) (p gv : Val) (k : Integers.Int64) (ch : Integers.Int) : FunSpec where
  tyargs := [tptr tvoid, tint, tulong]
  tyres := tptr tvoid
  cc := cc_default
  pre := fun vargs h =>
    vargs = [p, .Vint ch, .Vlong k] ∧ Integers.Int64.unsigned k ≤ n ∧ H c DB n p gv h
  post := fun v h => InRange p k v ∧ H c DB n p gv h
  measure := fun _ => 0

/-- `failf(data, "Nul byte in server response line")`（引数が宣言どおり2つの呼び出し）。 -/
def failfSpec (n : Nat) (p gv : Val) (lit : Block) : FunSpec where
  tyargs := [tyEasy, tptr tschar]
  tyres := tvoid
  cc := { cc_vararg := some 2, cc_unproto := false, cc_structret := false }
  pre := fun vargs h =>
    vargs = [.Vptr c.dataB c.dataO, .Vptr lit Integers.Ptrofs.zero] ∧ H c DB n p gv h
  post := fun _ h => H c DB n p gv h
  measure := fun _ => 0

def debugSpec (n : Nat) (p gv : Val) (len : Integers.Int64) : FunSpec where
  tyargs := [tyEasy, tint, tptr tschar, tulong]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs h =>
    vargs = [.Vptr c.dataB c.dataO, .Vint (Integers.Int.repr 1), p, .Vlong len]
    ∧ H c DB n p gv h
  post := fun _ h => H c DB n p gv h
  measure := fun _ => 0

def writeSpec (n : Nat) (p gv : Val) (len : Integers.Int64) : FunSpec where
  tyargs := [tyEasy, tint, tptr tschar, tulong]
  tyres := tint
  cc := cc_default
  pre := fun vargs h =>
    vargs = [.Vptr c.dataB c.dataO,
             .Vint (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 1)), p, .Vlong len]
    ∧ H c DB n p gv h
  post := fun v h => (∃ r, v = .Vint r) ∧ H c DB n p gv h
  measure := fun _ => 0

abbrev tyEorArgs : List Ty :=
  [tyEasy, tptr (Ty.Tstruct _connectdata noattr), tptr tschar, tulong, tptr tint]

def eorSpec (n : Nat) (p gv : Val) (len : Integers.Int64) : FunSpec where
  tyargs := tyEorArgs
  tyres := tbool
  cc := cc_default
  pre := fun vargs h =>
    vargs = [.Vptr c.dataB c.dataO, c.connV, p, .Vlong len, .Vptr c.codeB c.codeO]
    ∧ H c DB n p gv h
  post := fun v h => (∃ b, v = Val.ofBool b) ∧ H c DB n p gv h
  measure := fun _ => 0

/-- 名前で呼ぶ関数 `id` が、ブロック `b` の `fd` で、仕様の型をもつこと。 -/
structure Callee (ge : CGenv) (id : Ident) (tyargs : List Ty) (tyres : Ty) (cc : CallConv) where
  b : Block
  fd : FunDef
  sym : Genv.findSymbol ge.genv_genv id = some b
  fp : FuncPtr ge b fd
  ty : typeOfFundef fd = .Tfunction tyargs tyres cc

/-- 定理の仮定。大域環境 `ge` が、この翻訳単位と、呼ばれる側の関数の仕様を満たすこと。 -/
structure Ext (ge : CGenv) where
  cenv : ge.genv_cenv = prog.prog_comp_env
  recv : Callee ge _Curl_conn_recv [tyEasy, tschar, tptr tschar, tulong, tptr tulong] tint cc_default
  pread : Callee ge _pingpong_read [tyEasy, tschar, tptr tschar, tulong, tptr tulong] tint cc_default
  pread_fd : pread.fd = .Internal f_pingpong_read
  len : Callee ge _curlx_dyn_len [tyDyn] tulong cc_default
  ptr : Callee ge _curlx_dyn_ptr [tyDyn] (tptr tschar) cc_default
  tail : Callee ge _curlx_dyn_tail [tyDyn, tulong] tint cc_default
  reset : Callee ge _curlx_dyn_reset [tyDyn] tvoid cc_default
  addn : Callee ge _curlx_dyn_addn [tyDyn, tptr tvoid, tulong] tint cc_default
  memchr : Callee ge _memchr [tptr tvoid, tint, tulong] (tptr tvoid) cc_default
  failf : Callee ge _Curl_failf [tyEasy, tptr tschar] tvoid
    { cc_vararg := some 2, cc_unproto := false, cc_structret := false }
  debug : Callee ge _Curl_debug [tyEasy, tint, tptr tschar, tulong] tvoid cc_default
  write : Callee ge _Curl_client_write [tyEasy, tint, tptr tschar, tulong] tint cc_default
  lit : Block
  lit_sym : Genv.findSymbol ge.genv_genv ___stringlit_2 = some lit
  eorFd : FunDef
  eor_fp : FuncPtr ge c.eorB eorFd
  eor_ty : typeOfFundef eorFd = .Tfunction tyEorArgs tbool cc_default
  -- 呼ばれる側の仕様
  sRecv : ∀ n p gv vs, SatisfiesAt ge (FunctionEntry2 ge) recv.fd (recvSpec c DB n p gv) vs
  sLen : ∀ n p gv vs, SatisfiesAt ge (FunctionEntry2 ge) len.fd (lenSpec c DB n p gv) vs
  sPtr : ∀ n p gv vs, SatisfiesAt ge (FunctionEntry2 ge) ptr.fd (ptrSpec c DB n p gv) vs
  sTail : ∀ n p gv t vs, SatisfiesAt ge (FunctionEntry2 ge) tail.fd (tailSpec c DB n p gv t) vs
  sReset : ∀ n p gv vs, SatisfiesAt ge (FunctionEntry2 ge) reset.fd (resetSpec c DB n p gv) vs
  sAddn : ∀ n p gv vs, SatisfiesAt ge (FunctionEntry2 ge) addn.fd (addnSpec c DB n p gv) vs
  sMemchr : ∀ n p gv k ch vs,
    SatisfiesAt ge (FunctionEntry2 ge) memchr.fd (memchrSpec c DB n p gv k ch) vs
  sFailf : ∀ n p gv vs, SatisfiesAt ge (FunctionEntry2 ge) failf.fd (failfSpec c DB n p gv lit) vs
  sDebug : ∀ n p gv len vs, SatisfiesAt ge (FunctionEntry2 ge) debug.fd (debugSpec c DB n p gv len) vs
  sWrite : ∀ n p gv len vs, SatisfiesAt ge (FunctionEntry2 ge) write.fd (writeSpec c DB n p gv len) vs
  sEor : ∀ n p gv len vs, SatisfiesAt ge (FunctionEntry2 ge) eorFd (eorSpec c DB n p gv len) vs
  -- 受信バッファの述語について
  dbPtr : ∀ n p h, DB n p h → IsPtr p
  dbSize : ∀ n p h, DB n p h → n < 2 ^ 64
  dbValid : ∀ n bl ol h m (i : Nat), DB n (.Vptr bl ol) h → Heap.Agrees h m → i < n →
    Mem.weakValidPointer m bl
      (Integers.Ptrofs.unsigned (Integers.Ptrofs.add ol (Integers.Ptrofs.repr i))) = true
  -- 引数と所有
  connPtr : IsPtr c.connV
  sockCast : ∀ m, Cop.semCast c.sockV tschar tschar m = some c.sockV
  pmR : permOrder c.pm .Readable = true
  pmW : permOrder c.pm .Writable = true
  bgbb : c.bg ≠ c.bb

end Case1C
