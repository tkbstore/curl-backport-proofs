/-
CVE-2026-4873: `url_match_ssl_use`（と `get_protocol_family`）の4つの翻訳単位に共通の部分。
性質は `research/backport-proof-debian/cases/CVE-2026-4873.md`（証明の前にコミットした）。

U（上流）は `conn->scheme`（`struct Curl_scheme`）、D（8.14.1）は `conn->handler`（`struct Curl_handler`）を読む。
構造体の中身（protocol・family・flags）は同じ並びなので、レイアウトの事実は構造体とフィールドの名前（`sn`・`fn`）を引数にして1つで書く。
-/
import GenDeb2026_4873U1
import GenDeb2026_4873U0
import GenDeb2026_4873D1
import GenDeb2026_4873D0
import Deb2026_1965Tac
open CC CC.Sep CC.HProp
open Case5C (addr call_fwd RR flagBit bitOf sep_l sep_r)
open Case4C (IsPtr cast_ptr)

set_option maxRecDepth 20000

namespace Deb2026_4873C

/-! ## 構造体のレイアウト -/

def schMembers : List Member :=
  [Member.Member_plain (identOfString "protocol") tlong,
   Member.Member_plain (identOfString "family") tlong,
   Member.Member_plain (identOfString "flags") tuint]

def connMembers (sn fn : String) : List Member :=
  [Member.Member_plain (identOfString fn) (tptr (Ty.Tstruct (identOfString sn) noattr))]

def matchMembers : List Member :=
  [Member.Member_plain (identOfString "needle") (tptr (Ty.Tstruct (identOfString "connectdata") noattr)),
   Member.Member_bitfield (identOfString "req_tls") IntSize.I32 Signedness.Unsigned noattr 1 false]

def coSch : Composite :=
  { co_su := SU.Struct, co_members := schMembers, co_attr := noattr,
    co_sizeof := 24, co_alignof := 8, co_rank := 0 }
def coConn (sn fn : String) : Composite :=
  { co_su := SU.Struct, co_members := connMembers sn fn, co_attr := noattr,
    co_sizeof := 8, co_alignof := 8, co_rank := 0 }
def coMatch : Composite :=
  { co_su := SU.Struct, co_members := matchMembers, co_attr := noattr,
    co_sizeof := 16, co_alignof := 8, co_rank := 0 }

structure Layout (env : CompositeEnv) (sn fn : String) : Prop where
  co_sch : env.get (identOfString sn) = some coSch
  co_conn : env.get (identOfString "connectdata") = some (coConn sn fn)
  co_match : env.get (identOfString "url_conn_match") = some coMatch
  off_protocol : fieldOffset env (identOfString "protocol") schMembers = .OK (0, .Full)
  off_family : fieldOffset env (identOfString "family") schMembers = .OK (8, .Full)
  off_flags : fieldOffset env (identOfString "flags") schMembers = .OK (16, .Full)
  off_sch : fieldOffset env (identOfString fn) (connMembers sn fn) = .OK (0, .Full)
  off_needle : fieldOffset env (identOfString "needle") matchMembers = .OK (0, .Full)
  off_req : fieldOffset env (identOfString "req_tls") matchMembers
    = .OK (8, .Bits .I32 .Unsigned 0 1)

theorem layout_u1 : Layout Deb2026_4873_u1.prog.prog_comp_env "Curl_scheme" "scheme" := by
  constructor <;> decide
theorem layout_u0 : Layout Deb2026_4873_u0.prog.prog_comp_env "Curl_scheme" "scheme" := by
  constructor <;> decide
theorem layout_d1 : Layout Deb2026_4873_d1.prog.prog_comp_env "Curl_handler" "handler" := by
  constructor <;> decide
theorem layout_d0 : Layout Deb2026_4873_d0.prog.prog_comp_env "Curl_handler" "handler" := by
  constructor <;> decide

/-! ## 読むメモリ（書き込みは無い） -/

structure Ctx where
  connB : Block
  connO : Integers.Ptrofs
  mB : Block
  mO : Integers.Ptrofs
  ndlB : Block               -- m->needle
  ndlO : Integers.Ptrofs
  nschB : Block              -- m->needle->scheme（D は handler）
  nschO : Integers.Ptrofs
  cschB : Block              -- conn->scheme（D は handler）
  cschO : Integers.Ptrofs
  word : Integers.Int        -- m の req_tls を入れた 32 bit の単位
  flags : Integers.Int       -- m->needle->scheme->flags
  proto : Integers.Int64     -- m->needle->scheme->protocol
  fam : Integers.Int64       -- conn->scheme->family
  pm : Permission

/-- `needle->scheme` と `conn->scheme` は同じ構造体でもよい（読むフィールドが重ならない）。 -/
def H (c : Ctx) : HProp :=
  mapsto Mptr c.pm c.mB (addr c.mO 0) (.Vptr c.ndlB c.ndlO) ∗
  (mapsto .Mint32 c.pm c.mB (addr c.mO 8) (.Vint c.word) ∗
  (mapsto Mptr c.pm c.ndlB (addr c.ndlO 0) (.Vptr c.nschB c.nschO) ∗
  (mapsto .Mint64 c.pm c.nschB (addr c.nschO 0) (.Vlong c.proto) ∗
  (mapsto .Mint32 c.pm c.nschB (addr c.nschO 16) (.Vint c.flags) ∗
  (mapsto Mptr c.pm c.connB (addr c.connO 0) (.Vptr c.cschB c.cschO) ∗
   mapsto .Mint64 c.pm c.cschB (addr c.cschO 8) (.Vlong c.fam))))))

structure Loads (c : Ctx) (m : Mem) : Prop where
  needle : Mem.load Mptr m c.mB (addr c.mO 0) = some (.Vptr c.ndlB c.ndlO)
  word : Mem.load .Mint32 m c.mB (addr c.mO 8) = some (.Vint c.word)
  nsch : Mem.load Mptr m c.ndlB (addr c.ndlO 0) = some (.Vptr c.nschB c.nschO)
  proto : Mem.load .Mint64 m c.nschB (addr c.nschO 0) = some (.Vlong c.proto)
  flags : Mem.load .Mint32 m c.nschB (addr c.nschO 16) = some (.Vint c.flags)
  csch : Mem.load Mptr m c.connB (addr c.connO 0) = some (.Vptr c.cschB c.cschO)
  fam : Mem.load .Mint64 m c.cschB (addr c.cschO 8) = some (.Vlong c.fam)

theorem H_loads {c : Ctx} {hp : Heap} {m : Mem} (hpr : permOrder c.pm .Readable = true)
    (hH : H c hp) (hag : Heap.Agrees hp m) : Loads c m := by
  obtain ⟨h1, c1, a1⟩ := sep_l hH hag
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
  obtain ⟨h7, c7, a7⟩ := sep_r d5 b5
  exact ⟨mapsto_load hpr c1 a1, mapsto_load hpr c2 a2, mapsto_load hpr c3 a3,
         mapsto_load hpr c4 a4, mapsto_load hpr c5 a5, mapsto_load hpr c6 a6,
         mapsto_load hpr c7 a7⟩

/-! ## 戻り値（関数が読む値から決まる）

`reuse`: TLS の接続を TLS でない要求に使う分岐で `PROTOPT_SSL_REUSE` を見るか（U は見る、D は見ない）。
`req`: 修正の `else if(m->req_tls) return FALSE;` があるか（U1・D1 はある、U0・D0 は無い）。 -/

def ret (reuse req : Bool) (nssl ssl reuseOk sameFam reqBit : Bool) : Bool :=
  if nssl then ssl
  else if ssl then ((!reuse || reuseOk) && sameFam)
  else !(req && reqBit)

def retOf (reuse req : Bool) (c : Ctx) (ssl : Bool) : Bool :=
  ret reuse req (flagBit c.flags 0) ssl (flagBit c.flags 15) (Integers.Int64.eq c.fam c.proto)
    (bitOf c.word 0)

def useSpec (reuse req : Bool) (c : Ctx) (ssl : Bool) : FunSpec where
  tyargs := [tptr (Ty.Tstruct (identOfString "connectdata") noattr),
             tptr (Ty.Tstruct (identOfString "url_conn_match") noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.connB c.connO, .Vptr c.mB c.mO] ∧ H c hp
  post := fun v hp => v = Val.ofBool (retOf reuse req c ssl) ∧ H c hp
  measure := fun _ => 0

theorem post_of {reuse req : Bool} {c : Ctx} {ssl : Bool} {v : Val} {hp : Heap}
    (b : Bool) (hb : retOf reuse req c ssl = b) (hv : v = Val.ofBool b) (hH : H c hp) :
    (useSpec reuse req c ssl).post v hp := by
  subst hb
  exact ⟨hv, hH⟩

/-! ## 呼ばれる側 -/

/-- `Curl_conn_is_ssl(conn, FIRSTSOCKET)` は `ssl` を返し、メモリを変えない（C1 の Case 5 と同じ仕様）。 -/
def sslSpec (c : Ctx) (ssl : Bool) : FunSpec where
  tyargs := [tptr (Ty.Tstruct (identOfString "connectdata") noattr), tschar]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.connB c.connO, .Vint (Integers.Int.repr 0)] ∧ emp hp
  post := fun v hp => v = Val.ofBool ssl ∧ emp hp
  measure := fun _ => 0

structure SslExt (ge : CGenv) (c : Ctx) (ssl : Bool) where
  b : Block
  fd : FunDef
  hs : Genv.findSymbol ge.genv_genv (identOfString "Curl_conn_is_ssl") = some b
  hf : FuncPtr ge b fd
  hty : typeOfFundef fd = .Tfunction (sslSpec c ssl).tyargs (sslSpec c ssl).tyres (sslSpec c ssl).cc
  hsat : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd (sslSpec c ssl) vs

/-- `get_protocol_family(conn->scheme)`。仕様は各翻訳単位の本体から証明する。 -/
def gpfSpec (sn : String) (c : Ctx) : FunSpec where
  tyargs := [tptr (Ty.Tstruct (identOfString sn) noattr)]
  tyres := tlong
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.cschB c.cschO] ∧ H c hp
  post := fun v hp => v = .Vlong c.fam ∧ H c hp
  measure := fun _ => 0

structure GpfExt (ge : CGenv) (sn : String) (c : Ctx) where
  b : Block
  fd : FunDef
  hs : Genv.findSymbol ge.genv_genv (identOfString "get_protocol_family") = some b
  hf : FuncPtr ge b fd
  hty : typeOfFundef fd = .Tfunction (gpfSpec sn c).tyargs (gpfSpec sn c).tyres (gpfSpec sn c).cc
  hsat : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd (gpfSpec sn c) vs

theorem call_ssl {ge : CGenv} {f : Function} {c : Ctx} {ssl : Bool} (X : SslExt ge c ssl)
    {l : List (Ident × Val)} {Hh : HProp} {id : Ident}
    (hcn : (identOfString "conn", Val.Vptr c.connB c.connO) ∈ l) :
    Triple ge (FunctionEntry2 ge) f (LocalSt emptyEnv l Hh)
      (.Scall (some id)
        (.Evar (identOfString "Curl_conn_is_ssl")
          (.Tfunction [tptr (Ty.Tstruct (identOfString "connectdata") noattr), tschar] tbool cc_default))
        [.Etempvar (identOfString "conn") (tptr (Ty.Tstruct (identOfString "connectdata") noattr)),
         .Econst_int (Integers.Int.repr 0) tint])
      (.only (LocalSt emptyEnv (setLocal l id (Val.ofBool ssl)) Hh)) :=
  call_fwd ge _ _ (sslSpec c ssl) id _ _ emptyEnv l emp Hh emp Hh Hh
    [.Vptr c.connB c.connO, .Vint (Integers.Int.repr 0)]
    (Val.ofBool ssl) X.b X.fd X.hsat X.hf X.hty rfl
    (fun _ _ _ => eval_callee_global rfl X.hs rfl)
    (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get hcn))
      (cast_ptr (Or.inl ⟨_, _, rfl⟩) _ _ m)
      (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl EvalExprlist.nil))
    (fun _ he => ⟨rfl, he⟩) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _)

theorem call_gpf {ge : CGenv} {f : Function} {sn : String} {c : Ctx} (X : GpfExt ge sn c)
    {l : List (Ident × Val)} {id t : Ident}
    (ht : (t, Val.Vptr c.cschB c.cschO) ∈ l) :
    Triple ge (FunctionEntry2 ge) f (LocalSt emptyEnv l (H c))
      (.Scall (some id)
        (.Evar (identOfString "get_protocol_family")
          (.Tfunction [tptr (Ty.Tstruct (identOfString sn) noattr)] tlong cc_default))
        [.Etempvar t (tptr (Ty.Tstruct (identOfString sn) noattr))])
      (.only (LocalSt emptyEnv (setLocal l id (.Vlong c.fam)) (H c))) :=
  call_fwd ge _ _ (gpfSpec sn c) id _ _ emptyEnv l (H c) emp (H c) (H c) (H c)
    [.Vptr c.cschB c.cschO] (.Vlong c.fam) X.b X.fd X.hsat X.hf X.hty rfl
    (fun _ _ _ => eval_callee_global rfl X.hs rfl)
    (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get ht))
      (cast_ptr (Or.inl ⟨_, _, rfl⟩) _ _ m) EvalExprlist.nil)
    (fun _ he => ⟨rfl, he⟩) (fun _ _ hp => hp) (sep_emp_eq _).symm (sep_emp_eq _)

/-! ## 式の値 -/

section
variable {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}

theorem ev_notbool {t : Ident} {b : Bool} (hle : le.get t = some (Val.ofBool b)) :
    EvalExpr ge e le m (.Eunop .Onotbool (.Etempvar t tbool) tint) (Val.ofBool (!b)) :=
  EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hle) (Case5C.notbool_ofBool b m)

theorem ev_ne_long {t1 t2 : Ident} {x y : Integers.Int64}
    (h1 : le.get t1 = some (.Vlong x)) (h2 : le.get t2 = some (.Vlong y)) :
    EvalExpr ge e le m (.Ebinop .One (.Etempvar t1 tlong) (.Etempvar t2 tlong) tint)
      (Val.ofBool (!Integers.Int64.eq x y)) := by
  have hne : Integers.Int64.cmp .Cne x y = !Integers.Int64.eq x y := rfl
  refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ h1) (EvalExpr.Etempvar _ _ _ h2) ?_
  show _ = some (Val.ofBool (!Integers.Int64.eq x y))
  rw [← hne]
  rfl

end

theorem boolVal_notflag15 (fl : Integers.Int) (m : Mem) :
    Cop.boolVal (Val.ofBool (!flagBit fl 15)) tint m = some (!flagBit fl 15) :=
  Case5C.boolVal_ofBool_tint _ m

end Deb2026_4873C
