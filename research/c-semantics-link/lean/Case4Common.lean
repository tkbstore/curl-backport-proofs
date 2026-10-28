/-
Case 4（CURL-CVE-2025-13034）: 修正前・修正後の証明で共通に使う部分。

`Curl_vquic_tls_verify_peer` が読むメモリ（`Ctx4`・`H4`）、外部関数3つの仕様、式の評価の補題。
-/
import GenCase4After
import Case5Common
open CC CC.Sep CC.HProp
open Case4_after
open Case5C (addr call_fwd RR return_const skip_end eval_bitfield sep_l sep_r)

set_option maxRecDepth 20000

namespace Case4C

/-! ## 値の形 -/

/-- ポインタとして扱える値（ブロック上の番地か、64 bit の整数。NULL は `Vlong 0`）。 -/
def IsPtr (v : Val) : Prop := (∃ b o, v = .Vptr b o) ∨ (∃ n, v = .Vlong n)

theorem loadResult_ptr {v : Val} (h : IsPtr v) : Val.loadResult Mptr v = v := by
  rcases h with ⟨b, o, rfl⟩ | ⟨n, rfl⟩ <;> rfl

theorem cast_ptr {v : Val} (h : IsPtr v) (t1 t2 : Ty) (m : Mem) :
    Cop.semCast v (tptr t1) (tptr t2) m = some v := by
  rcases h with ⟨b, o, rfl⟩ | ⟨n, rfl⟩ <;> rfl

/-! ## 読むメモリ -/

structure Ctx4 where
  cfV : Val                  -- cf（関数は読まず、外部関数に渡すだけ）
  ctxB : Block               -- ctx
  ctxO : Integers.Ptrofs
  dataB : Block              -- data
  dataO : Integers.Ptrofs
  peerB : Block              -- peer
  peerO : Integers.Ptrofs
  cfgB : Block               -- Curl_ssl_cf_get_primary_config(cf) が NULL でないときの値
  cfgO : Integers.Ptrofs
  word : Integers.Int        -- conn_config の verifyhost を入れた 32 bit の単位
  sessV : Val                -- ctx->gtls.session
  pinV : Val                 -- data->set.str[STRING_SSL_PINNEDPUBLICKEY]（NULL でもよい）
  keyV : Val                 -- peer->scache_key
  pm : Permission

/-- `data->set.str[STRING_SSL_PINNEDPUBLICKEY]` の番地（`Efield`・`Oadd` が計算するのと同じ式）。 -/
def strOfs (o : Integers.Ptrofs) : Integers.Ptrofs :=
  Integers.Ptrofs.add
    (Integers.Ptrofs.add (Integers.Ptrofs.add o (Integers.Ptrofs.repr 0)) (Integers.Ptrofs.repr 8))
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr 8) (Cop.ptrofsOfInt .Signed (Integers.Int.repr 7)))

def H4 (c : Ctx4) : HProp :=
  mapsto .Mint32 c.pm c.cfgB (addr c.cfgO 0) (.Vint c.word) ∗
  (mapsto Mptr c.pm c.ctxB (addr (Integers.Ptrofs.add c.ctxO (Integers.Ptrofs.repr 0)) 0) c.sessV ∗
  (mapsto Mptr c.pm c.dataB (Integers.Ptrofs.unsigned (strOfs c.dataO)) c.pinV ∗
   mapsto Mptr c.pm c.peerB (addr c.peerO 0) c.keyV))

structure Loads4 (c : Ctx4) (m : Mem) : Prop where
  word : Mem.load .Mint32 m c.cfgB (addr c.cfgO 0) = some (.Vint c.word)
  sess : Mem.load Mptr m c.ctxB (addr (Integers.Ptrofs.add c.ctxO (Integers.Ptrofs.repr 0)) 0)
    = some c.sessV
  pin : Mem.load Mptr m c.dataB (Integers.Ptrofs.unsigned (strOfs c.dataO)) = some c.pinV
  key : Mem.load Mptr m c.peerB (addr c.peerO 0) = some c.keyV
  valid : Mem.weakValidPointer m c.cfgB (Integers.Ptrofs.unsigned c.cfgO) = true

/-- 値の形の前提（どれもポインタとして扱える）。 -/
structure Ptrs (c : Ctx4) : Prop where
  cf : IsPtr c.cfV
  sess : IsPtr c.sessV
  pin : IsPtr c.pinV
  key : IsPtr c.keyV

theorem mapsto_weakValid {chunk : Chunk} {p : Permission} {b : Block} {ofs : _root_.Int}
    {v : Val} {h : Heap} {m : Mem} (hpr : permOrder p .Nonempty = true)
    (hm : mapsto chunk p b ofs v h) (hag : Heap.Agrees h m) (hsz : 0 < sizeChunkNat chunk) :
    Mem.weakValidPointer m b ofs = true := by
  obtain ⟨_, hbytes⟩ := pure_sep_elim hm
  have hown := bytesPtsTo_ownsRange b p (encodeVal chunk v) ofs h hbytes
  have h0 := hown 0 (by rw [length_encodeVal]; exact hsz)
  rw [show ofs + ((0 : Nat) : _root_.Int) = ofs from by omega] at h0
  obtain ⟨hcur, _, _⟩ := hag b ofs _ h0
  unfold Mem.weakValidPointer Mem.validPointer Mem.perm
  rw [hcur]
  simp [permOrder', hpr]

theorem H4_loads {c : Ctx4} {hp : Heap} {m : Mem} (hpr : permOrder c.pm .Readable = true)
    (hpn : permOrder c.pm .Nonempty = true) (hptr : Ptrs c)
    (hH : H4 c hp) (hag : Heap.Agrees hp m) : Loads4 c m := by
  obtain ⟨h1, c1, a1⟩ := sep_l hH hag
  obtain ⟨r1, d1, b1⟩ := sep_r hH hag
  obtain ⟨h2, c2, a2⟩ := sep_l d1 b1
  obtain ⟨r2, d2, b2⟩ := sep_r d1 b1
  obtain ⟨h3, c3, a3⟩ := sep_l d2 b2
  obtain ⟨h4, c4, a4⟩ := sep_r d2 b2
  refine ⟨mapsto_load hpr c1 a1, ?_, ?_, ?_, ?_⟩
  · rw [mapsto_load hpr c2 a2, loadResult_ptr hptr.sess]
  · rw [mapsto_load hpr c3 a3, loadResult_ptr hptr.pin]
  · rw [mapsto_load hpr c4 a4, loadResult_ptr hptr.key]
  · have := mapsto_weakValid hpn c1 a1 (by decide)
    rwa [addr, ptrofs_add_zero] at this

/-! ## 構造体のレイアウト -/

/-- `struct Curl_easy` の composite（生成された環境から取り出す）。 -/
def coEasy : Composite :=
  match prog.prog_comp_env.get _Curl_easy with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }
theorem co_easy : prog.prog_comp_env.get _Curl_easy = some coEasy := rfl
theorem coEasy_members :
    coEasy.co_members = [Member.Member_plain _set (Ty.Tstruct _UserDefined noattr)] := by decide
theorem co_ud : prog.prog_comp_env.get _UserDefined = some
    { co_su := SU.Struct,
      co_members := [Member.Member_plain _ssl (Ty.Tstruct _ssl_config_data noattr),
                     Member.Member_plain _str (tarray (tptr tschar) 70)],
      co_attr := noattr, co_sizeof := 568, co_alignof := 8, co_rank := 2 } := by decide
theorem co_tls : prog.prog_comp_env.get _curl_tls_ctx = some
    { co_su := SU.Struct, co_members := [Member.Member_plain _gtls (Ty.Tstruct _gtls_ctx noattr)],
      co_attr := noattr, co_sizeof := 8, co_alignof := 8, co_rank := 1 } := by decide
theorem co_gtls : prog.prog_comp_env.get _gtls_ctx = some
    { co_su := SU.Struct,
      co_members := [Member.Member_plain _session (tptr (Ty.Tstruct _gnutls_session_int noattr))],
      co_attr := noattr, co_sizeof := 8, co_alignof := 8, co_rank := 0 } := by decide
theorem co_peer : prog.prog_comp_env.get _ssl_peer = some
    { co_su := SU.Struct, co_members := [Member.Member_plain _scache_key (tptr tschar)],
      co_attr := noattr, co_sizeof := 8, co_alignof := 8, co_rank := 0 } := by decide
theorem co_pc : prog.prog_comp_env.get _ssl_primary_config = some
    { co_su := SU.Struct,
      co_members := [Member.Member_bitfield _verifyhost IntSize.I32 Signedness.Unsigned noattr 1 false],
      co_attr := noattr, co_sizeof := 4, co_alignof := 4, co_rank := 0 } := by decide

theorem off_set : fieldOffset prog.prog_comp_env _set
    [Member.Member_plain _set (Ty.Tstruct _UserDefined noattr)] = .OK (0, .Full) := by decide
theorem off_ssl : fieldOffset prog.prog_comp_env _ssl
    [Member.Member_plain _ssl (Ty.Tstruct _ssl_config_data noattr),
     Member.Member_plain _str (tarray (tptr tschar) 70)] = .OK (0, .Full) := by decide
theorem off_str : fieldOffset prog.prog_comp_env _str
    [Member.Member_plain _ssl (Ty.Tstruct _ssl_config_data noattr),
     Member.Member_plain _str (tarray (tptr tschar) 70)] = .OK (8, .Full) := by decide
theorem off_gtls : fieldOffset prog.prog_comp_env _gtls
    [Member.Member_plain _gtls (Ty.Tstruct _gtls_ctx noattr)] = .OK (0, .Full) := by decide
theorem off_session : fieldOffset prog.prog_comp_env _session
    [Member.Member_plain _session (tptr (Ty.Tstruct _gnutls_session_int noattr))]
    = .OK (0, .Full) := by decide
theorem off_key : fieldOffset prog.prog_comp_env _scache_key
    [Member.Member_plain _scache_key (tptr tschar)] = .OK (0, .Full) := by decide
theorem off_vh : fieldOffset prog.prog_comp_env _verifyhost
    [Member.Member_bitfield _verifyhost IntSize.I32 Signedness.Unsigned noattr 1 false]
    = .OK (0, .Bits .I32 .Unsigned 0 1) := by decide

/-! ## 式の評価 -/

theorem eval_deref_temp {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {p sid : Ident}
    {b : Block} {o : Integers.Ptrofs} (hle : le.get p = some (.Vptr b o)) :
    EvalExpr ge e le m (.Ederef (.Etempvar p (tptr (.Tstruct sid noattr))) (.Tstruct sid noattr))
      (.Vptr b o) :=
  EvalExpr.Elvalue _ b o .Full _ (EvalLvalue.Ederef _ _ b o (EvalExpr.Etempvar p _ _ hle))
    (DerefLoc.copy rfl)

theorem lv_field {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {a : Expr} {fld sid : Ident}
    {ty : Ty} {co : Composite} {b : Block} {o : Integers.Ptrofs} {delta : Z}
    (hptr : EvalExpr ge e le m a (.Vptr b o)) (hty : typeof a = .Tstruct sid noattr)
    (hco : ge.genv_cenv.get sid = some co)
    (hfld : fieldOffset ge.genv_cenv fld co.co_members = .OK (delta, .Full)) :
    EvalLvalue ge e le m (.Efield a fld ty) b
      (Integers.Ptrofs.add o (Integers.Ptrofs.repr delta)) .Full :=
  EvalLvalue.Efield_struct a fld ty b o sid co noattr delta .Full hptr hty hco hfld

/-- `ctx->gtls.session` -/
theorem eval_session {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {c : Ctx4}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hle : le.get _ctx = some (.Vptr c.ctxB c.ctxO)) (hL : Loads4 c m) :
    EvalExpr ge e le m
      (.Efield (.Efield (.Ederef (.Etempvar _ctx (tptr (Ty.Tstruct _curl_tls_ctx noattr)))
          (Ty.Tstruct _curl_tls_ctx noattr)) _gtls (Ty.Tstruct _gtls_ctx noattr)) _session
        (tptr (Ty.Tstruct _gnutls_session_int noattr)))
      c.sessV :=
  EvalExpr.Elvalue _ _ _ .Full _
    (lv_field (EvalExpr.Elvalue _ _ _ .Full _
        (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_tls) (hcenv ▸ off_gtls))
        (DerefLoc.copy rfl))
      rfl (hcenv ▸ co_gtls) (hcenv ▸ off_session))
    (DerefLoc.value Mptr _ rfl hL.sess)

/-- `data->set.str[STRING_SSL_PINNEDPUBLICKEY]` -/
theorem eval_pin {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {c : Ctx4}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hle : le.get _data = some (.Vptr c.dataB c.dataO)) (hL : Loads4 c m) :
    EvalExpr ge e le m
      (.Ederef
        (.Ebinop .Oadd
          (.Efield (.Efield (.Ederef (.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
              (Ty.Tstruct _Curl_easy noattr)) _set (Ty.Tstruct _UserDefined noattr)) _str
            (tarray (tptr tschar) 70))
          (.Econst_int (Integers.Int.repr 7) tint) (tptr (tptr tschar))) (tptr tschar))
      c.pinV :=
  EvalExpr.Elvalue _ _ _ .Full _
    (EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Elvalue _ _ _ .Full _
          (lv_field (EvalExpr.Elvalue _ _ _ .Full _
              (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_easy) (hcenv ▸ coEasy_members ▸ off_set))
              (DerefLoc.copy rfl))
            rfl (hcenv ▸ co_ud) (hcenv ▸ off_str))
          (DerefLoc.reference rfl))
        (EvalExpr.Econst_int _ _)
        (semAdd_ptr_int _ _ _ _ _ rfl)))
    (DerefLoc.value Mptr _ rfl hL.pin)

/-- `&data->set.ssl` -/
theorem eval_sslcfg {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {c : Ctx4}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hle : le.get _data = some (.Vptr c.dataB c.dataO)) :
    EvalExpr ge e le m
      (.Eaddrof
        (.Efield (.Efield (.Ederef (.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
            (Ty.Tstruct _Curl_easy noattr)) _set (Ty.Tstruct _UserDefined noattr)) _ssl
          (Ty.Tstruct _ssl_config_data noattr))
        (tptr (Ty.Tstruct _ssl_config_data noattr)))
      (.Vptr c.dataB (Integers.Ptrofs.add
        (Integers.Ptrofs.add c.dataO (Integers.Ptrofs.repr 0)) (Integers.Ptrofs.repr 0))) :=
  EvalExpr.Eaddrof _ _ _ _
    (lv_field (EvalExpr.Elvalue _ _ _ .Full _
        (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_easy) (hcenv ▸ coEasy_members ▸ off_set))
        (DerefLoc.copy rfl))
      rfl (hcenv ▸ co_ud) (hcenv ▸ off_ssl))

/-- `peer->scache_key` -/
theorem eval_key {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {c : Ctx4}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hle : le.get _peer = some (.Vptr c.peerB c.peerO)) (hL : Loads4 c m) :
    EvalExpr ge e le m
      (.Efield (.Ederef (.Etempvar _peer (tptr (Ty.Tstruct _ssl_peer noattr)))
          (Ty.Tstruct _ssl_peer noattr)) _scache_key (tptr tschar))
      c.keyV :=
  EvalExpr.Elvalue _ _ _ .Full _
    (lv_field (eval_deref_temp hle) rfl (hcenv ▸ co_peer) (hcenv ▸ off_key))
    (DerefLoc.value Mptr _ rfl hL.key)

/-! ## 呼ばれる側の仕様（どれも引数を問わず、メモリを変えない） -/

/-- `Curl_ssl_cf_get_primary_config(cf)` は `cp`（`conn_config`）を返す。 -/
def getSpec (cp : Val) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_cfilter noattr)]
  tyres := tptr (Ty.Tstruct _ssl_primary_config noattr)
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun v hp => v = cp ∧ emp hp
  measure := fun _ => 0

/-- `Curl_gtls_verifyserver(...)` は `r` を返す（`r` は任意の CURLcode）。 -/
def vsSpec (r : Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_cfilter noattr), tptr (Ty.Tstruct _Curl_easy noattr),
             tptr (Ty.Tstruct _gnutls_session_int noattr),
             tptr (Ty.Tstruct _ssl_primary_config noattr),
             tptr (Ty.Tstruct _ssl_config_data noattr), tptr (Ty.Tstruct _ssl_peer noattr),
             tptr tschar]
  tyres := tint
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun v hp => v = .Vint r ∧ emp hp
  measure := fun _ => 0

/-- `Curl_ssl_scache_remove_all(...)` は何も返さない。 -/
def rmSpec : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_cfilter noattr), tptr (Ty.Tstruct _Curl_easy noattr),
             tptr tschar]
  tyres := tvoid
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun _ hp => emp hp
  measure := fun _ => 0

/-- 戻り値を捨てる呼び出し（`f(...);`）。 -/
theorem call_none (ge fe f) (S : FunSpec) (callee : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (Hk : HProp) (vargs : List Val) (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs)
    (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof callee) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le →
                 EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, emp h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → emp h) :
    Triple ge fe f (LocalSt E l Hk) (.Scall none callee al) (.only (LocalSt E l Hk)) := by
  refine triple_call ge fe f S none callee al _ _ fb fd hspec hfind hty hclass
    (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  refine ⟨vargs, Heap.emp, hp, Heap.disjoint_emp_left hp, (Heap.emp_union hp).symm,
    hcallee le m hT, hargs le m hT, hpre _ rfl, ?_⟩
  intro v h1' hS hd'
  have he := hpost v h1' hS
  rw [emp] at he
  subst he
  exact ⟨rfl, hT, by rw [Heap.emp_union]; exact hH⟩

end Case4C
