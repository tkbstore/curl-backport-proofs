/-
Case 1（CURL-CVE-2026-92387）: 修正後の `Curl_pp_readresp` が止まることの証明で使う部分。

止まることだけを示すので、所有するセルの中身は「型の合った何かの値」とだけ書く（`Hr`）。
値を細かく追わない代わりに、呼ばれる側の関数は、所有するセルを型を保ったまま書き換えてよいことにする
（仕様を弱く置くほど、定理は強くなる）。値を追うのは次の3つだけ:

- `gotbytes`（`H` の `gv`）: 外側のループを続けるかを決める
- 受信バッファの長さ `n` とその先頭 `p`（抽象した述語 `DB n p`）: 内側のループの減少量
- 一時変数 `maxloops`: 外側のループの減少量（修正で入ったもの）
-/
import GenCase1After
import Case2Common
open CC CC.Sep CC.HProp
open Case1_after
open Case5C (addr eval_field sep_l sep_r boolVal_ofBool_tint boolVal_ofBool_tbool)
open Case4C (IsPtr cast_ptr mapsto_weakValid lv_field eval_deref_temp)

set_option maxRecDepth 20000

namespace Case1C

/-! ## 構造体のレイアウト -/

def coOf (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_easy : prog.prog_comp_env.get _Curl_easy = some (coOf _Curl_easy) := rfl
theorem co_req : prog.prog_comp_env.get _SingleRequest = some (coOf _SingleRequest) := rfl
theorem co_pp : prog.prog_comp_env.get _pingpong = some (coOf _pingpong) := rfl

theorem off_conn :
    fieldOffset prog.prog_comp_env _conn (coOf _Curl_easy).co_members = .OK (0, .Full) := by
  decide
theorem off_req :
    fieldOffset prog.prog_comp_env _req (coOf _Curl_easy).co_members = .OK (8, .Full) := by
  decide
theorem off_hbc :
    fieldOffset prog.prog_comp_env _headerbytecount (coOf _SingleRequest).co_members
      = .OK (0, .Full) := by decide
theorem off_nread :
    fieldOffset prog.prog_comp_env _nread_resp (coOf _pingpong).co_members = .OK (0, .Full) := by
  decide
theorem off_recvbuf :
    fieldOffset prog.prog_comp_env _recvbuf (coOf _pingpong).co_members = .OK (8, .Full) := by
  decide
theorem off_overflow :
    fieldOffset prog.prog_comp_env _overflow (coOf _pingpong).co_members = .OK (24, .Full) := by
  decide
theorem off_nfinal :
    fieldOffset prog.prog_comp_env _nfinal (coOf _pingpong).co_members = .OK (32, .Full) := by
  decide
theorem off_eor :
    fieldOffset prog.prog_comp_env _endofresp (coOf _pingpong).co_members = .OK (40, .Full) := by
  decide
theorem off_pending :
    fieldOffset prog.prog_comp_env _pending_resp (coOf _pingpong).co_members
      = .OK (48, .Bits .I32 .Unsigned 0 1) := by decide

theorem sizeof_buffer : sizeof prog.prog_comp_env (tarray tschar 900) = 900 := by decide
theorem sizeof_got : sizeof prog.prog_comp_env tulong = 8 := by decide

/-! ## 局所変数の環境

`fn_vars` は `gotbytes`（`size_t`）と `buffer`（`char[900]`）。関数の入口で、この順に確保される。 -/

def envE (bg bb : Block) : Env :=
  PTree.set _buffer (bb, tarray tschar 900) (PTree.set _gotbytes (bg, tulong) PTree.empty)

theorem envE_got (bg bb : Block) : (envE bg bb).get _gotbytes = some (bg, tulong) := rfl
theorem envE_buf (bg bb : Block) : (envE bg bb).get _buffer = some (bb, tarray tschar 900) := rfl
theorem envE_lit (bg bb : Block) : (envE bg bb).get ___stringlit_2 = none := rfl

/-! ## 読み書きするメモリ -/

structure Ctx where
  dataB : Block
  dataO : Integers.Ptrofs
  ppB : Block
  ppO : Integers.Ptrofs
  codeB : Block
  codeO : Integers.Ptrofs
  sizeB : Block
  sizeO : Integers.Ptrofs
  bg : Block                 -- 局所変数 gotbytes
  bb : Block                 -- 局所変数 buffer
  connV : Val                -- data->conn
  eorB : Block               -- pp->endofresp が指す関数
  sockV : Val                -- 引数 sockindex
  pm : Permission

/-- `data->req.headerbytecount` の番地（`Efield` を2段たどった式のまま書く）。 -/
def hbcAddr (c : Ctx) : Z :=
  Integers.Ptrofs.unsigned
    (Integers.Ptrofs.add (Integers.Ptrofs.add c.dataO (Integers.Ptrofs.repr 8))
      (Integers.Ptrofs.repr 0))

/-- `&pp->recvbuf` -/
def rbV (c : Ctx) : Val := .Vptr c.ppB (Integers.Ptrofs.add c.ppO (Integers.Ptrofs.repr 8))

/-- 中身について `C` だけが分かっているセル。 -/
def cellP (ch : Chunk) (pm : Permission) (b : Block) (o : Z) (C : Val → Prop) : HProp :=
  hexists fun v => ⌜C v⌝ ∗ mapsto ch pm b o v

def IsLong (v : Val) : Prop := ∃ x, v = .Vlong x
def IsInt (v : Val) : Prop := ∃ x, v = .Vint x
def AnyV (_ : Val) : Prop := True

/-- 値を追わないセルの並び（`gotbytes` と受信バッファ以外のすべて）。 -/
def cells (c : Ctx) : List HProp :=
  [ anyBytes .Freeable c.bb 0 900,                                         -- 0 buffer
    cellP .Mint32 c.pm c.codeB (Integers.Ptrofs.unsigned c.codeO) AnyV,    -- 1 *code
    cellP .Mint64 c.pm c.sizeB (Integers.Ptrofs.unsigned c.sizeO) AnyV,    -- 2 *size
    mapsto Mptr c.pm c.dataB (addr c.dataO 0) c.connV,                     -- 3 data->conn
    cellP .Mint32 c.pm c.dataB (hbcAddr c) IsInt,                          -- 4 data->req.headerbytecount
    cellP .Mint64 c.pm c.ppB (addr c.ppO 0) IsLong,                        -- 5 pp->nread_resp
    cellP .Mint64 c.pm c.ppB (addr c.ppO 24) IsLong,                       -- 6 pp->overflow
    cellP .Mint64 c.pm c.ppB (addr c.ppO 32) IsLong,                       -- 7 pp->nfinal
    mapsto Mptr c.pm c.ppB (addr c.ppO 40) (.Vptr c.eorB Integers.Ptrofs.zero), -- 8 pp->endofresp
    cellP .Mint32 c.pm c.ppB (addr c.ppO 48) IsInt ]                       -- 9 pp->pending_resp の語

def bigSep : List HProp → HProp
  | [] => emp
  | P :: l => P ∗ bigSep l

theorem bigSep_pick : ∀ (l : List HProp) (k : Nat) (hk : k < l.length),
    bigSep l = l[k] ∗ bigSep (l.eraseIdx k)
  | [], _, hk => absurd hk (Nat.not_lt_zero _)
  | P :: l, 0, _ => rfl
  | P :: l, k + 1, hk => by
      have hk' : k < l.length := by simp at hk; omega
      show P ∗ bigSep l = l[k]'hk' ∗ (P ∗ bigSep (l.eraseIdx k))
      rw [bigSep_pick l k hk', sep_left_comm_eq]

def Hr (c : Ctx) : HProp := bigSep (cells c)

/-- 関数が所有するメモリ全体。`DB n p` は受信バッファ（長さ `n`、先頭 `p`）を表す抽象した述語。 -/
def H (c : Ctx) (DB : Nat → Val → HProp) (n : Nat) (p gv : Val) : HProp :=
  mapsto .Mint64 .Freeable c.bg 0 gv ∗ (Hr c ∗ DB n p)

/-- `k` 番目のセルを取り出す。残りは `Rk` -/
def Rk (c : Ctx) (DB : Nat → Val → HProp) (n : Nat) (p gv : Val) (k : Nat) : HProp :=
  mapsto .Mint64 .Freeable c.bg 0 gv ∗ (bigSep ((cells c).eraseIdx k) ∗ DB n p)

theorem H_pick (c : Ctx) (DB : Nat → Val → HProp) (n : Nat) (p gv : Val) (k : Nat)
    (hk : k < (cells c).length) :
    H c DB n p gv = (cells c)[k] ∗ Rk c DB n p gv k := by
  unfold H Hr Rk
  rw [bigSep_pick (cells c) k hk, sep_assoc_eq, sep_left_comm_eq]

end Case1C
