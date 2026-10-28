/-
Case 2（CURL-CVE-2026-86413）: C の意味論の上での P1・P0（PROTOCOL §5）。

2つの関数をつなぐ:
- `url_attach_existing` は、`Curl_cpool_find` に渡す `match` の `want_nego_http` を立てる（`attach_after`/`attach_before`）
  修正後は `rawWant && allowed`、修正前は `rawWant`
- `url_match_auth_nego` は、そのビットを `want` として H5 の `matchNego want x` と同じ判定をする（`auth_nego_eq`）

つなぎ目の前提（証明していない）: `Curl_cpool_find` は `url_match_conn` を通して、同じ `match` で
`url_match_auth_nego` を呼び、その間 `want_nego_http`・`want_proxy_nego_http` を書き換えない。
-/
import Case2NegoMain
import Case2AttachMain
import Case2AttachBefore
import Case2Witness
open CC CC.Sep CC.HProp
open Case5C (bitOf)
open Case4C (IsPtr)

set_option maxRecDepth 20000

namespace Case2C

open H5.Case2 (Verdict matchNego)

/-- C の関数の判定は、ビットが `rawWant && allowed` なら H5 の `after`、`rawWant` なら `before` と同じ。 -/
theorem vd_after (c2 : Ctx2) (c3 : Ctx3) (word : Integers.Int) (cs oe al : Bool)
    (hw : bitOf word 1 = (rawWant c3 && al)) :
    vdOf c2 word cs oe = H5.Case2.after (negInput c2 cs oe (rawWant c3) al) := by
  unfold vdOf H5.Case2.after
  rw [hw]
  rfl

theorem vd_before (c2 : Ctx2) (c3 : Ctx3) (word : Integers.Int) (cs oe al : Bool)
    (hw : bitOf word 1 = rawWant c3) :
    vdOf c2 word cs oe = H5.Case2.before (negInput c2 cs oe (rawWant c3) al) := by
  unfold vdOf H5.Case2.before
  rw [hw]
  rfl

/-- **P1（C）: 修正後の C 関数では、認証情報を送ってよくない相手への転送で、Negotiate 済みの接続を使わない。**

    `url_attach_existing` は、ビットを `rawWant && allowed` にして `Curl_cpool_find` を呼ぶ（前の連言）。
    そのビットを読む `url_match_auth_nego` の判定は H5 の `after` と同じで、`leaks` にならない（後の連言）。
    最後の段は H5 の定理 `P1` をそのまま使った。 -/
theorem P1_C (ge : CGenv) (hcenv : ge.genv_cenv = Case2_after.prog.prog_comp_env)
    -- url_attach_existing
    (c3 : Ctx3) (mm al fb : Bool)
    (hpr3 : permOrder c3.pm .Readable = true) (hpw3 : permOrder c3.pm .Writable = true)
    (hdest : IsPtr c3.destV) (hcp : IsPtr c3.cpV)
    (hnb : c3.nowBytes.length = 16) (hnowal : Integers.Ptrofs.unsigned c3.nowO % 8 = 0)
    (bInst bMs bNow bMm bPr bAl bFind bConn bRes : Block)
    (fdInst fdMs fdNow fdMm fdPr fdAl fdFind : FunDef)
    (hsInst : Genv.findSymbol ge.genv_genv Case2_after._Curl_cpool_get_instance = some bInst)
    (hsMs : Genv.findSymbol ge.genv_genv Case2_after._memset = some bMs)
    (hsNow : Genv.findSymbol ge.genv_genv Case2_after._Curl_pgrs_now = some bNow)
    (hsMm : Genv.findSymbol ge.genv_genv Case2_after._xfer_may_multiplex = some bMm)
    (hsPr : Genv.findSymbol ge.genv_genv Case2_after._Curl_cpool_prune_dead = some bPr)
    (hsAl : Genv.findSymbol ge.genv_genv Case2_after._Curl_auth_allowed_to_host = some bAl)
    (hsFind : Genv.findSymbol ge.genv_genv Case2_after._Curl_cpool_find = some bFind)
    (hsConn : Genv.findSymbol ge.genv_genv Case2_after._url_match_conn = some bConn)
    (hsRes : Genv.findSymbol ge.genv_genv Case2_after._url_match_result = some bRes)
    (hfInst : FuncPtr ge bInst fdInst) (hfMs : FuncPtr ge bMs fdMs) (hfNow : FuncPtr ge bNow fdNow)
    (hfMm : FuncPtr ge bMm fdMm) (hfPr : FuncPtr ge bPr fdPr) (hfAl : FuncPtr ge bAl fdAl)
    (hfFind : FuncPtr ge bFind fdFind)
    (htyInst : typeOfFundef fdInst
      = .Tfunction (instSpec c3.cpV).tyargs (instSpec c3.cpV).tyres (instSpec c3.cpV).cc)
    (htyMs : typeOfFundef fdMs = .Tfunction [tptr tvoid, tint, tulong] (tptr tvoid) cc_default)
    (htyNow : typeOfFundef fdNow = .Tfunction (nowSpec c3).tyargs (nowSpec c3).tyres (nowSpec c3).cc)
    (htyMm : typeOfFundef fdMm = .Tfunction (mmSpec mm).tyargs (mmSpec mm).tyres (mmSpec mm).cc)
    (htyPr : typeOfFundef fdPr = .Tfunction pruneSpec.tyargs pruneSpec.tyres pruneSpec.cc)
    (htyAl : typeOfFundef fdAl
      = .Tfunction (allowSpec al).tyargs (allowSpec al).tyres (allowSpec al).cc)
    (htyFind : typeOfFundef fdFind
      = .Tfunction (findSpec true bFind fb).tyargs (findSpec true bFind fb).tyres cc_default)
    (hInst : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdInst (instSpec c3.cpV) vs)
    (hMs : ∀ b vs, SatisfiesAt ge (FunctionEntry2 ge) fdMs (memsetSpec b) vs)
    (hNow : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdNow (nowSpec c3) vs)
    (hMm : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdMm (mmSpec mm) vs)
    (hPr : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdPr pruneSpec vs)
    (hAl : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdAl (allowSpec al) vs)
    (hFind : ∀ b vs, SatisfiesAt ge (FunctionEntry2 ge) fdFind (findSpec (rawWant c3 && al) b fb) vs)
    -- url_match_auth_nego
    (c2 : Ctx2) (cs oe : Bool)
    (hpr2 : permOrder c2.pm .Readable = true) (hpn2 : permOrder c2.pm .Nonempty = true)
    (hpw2 : permOrder c2.pm .Writable = true) (hptr2 : Ptrs2 c2)
    (bCs bPe : Block) (fdCs fdPe : FunDef)
    (hsCs : Genv.findSymbol ge.genv_genv Case2_after._Curl_creds_same = some bCs)
    (hsPe : Genv.findSymbol ge.genv_genv Case2_after._Curl_peer_equal = some bPe)
    (hfCs : FuncPtr ge bCs fdCs) (hfPe : FuncPtr ge bPe fdPe)
    (htyCs : typeOfFundef fdCs
      = .Tfunction (credsSpec cs).tyargs (credsSpec cs).tyres (credsSpec cs).cc)
    (htyPe : typeOfFundef fdPe
      = .Tfunction (peerSpec oe).tyargs (peerSpec oe).tyres (peerSpec oe).cc)
    (hCs : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCs (credsSpec cs) vs)
    (hPe : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdPe (peerSpec oe) vs) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Case2_after.f_url_attach_existing)
              (attachSpec c3) vs)
    ∧ ∀ (foundV : Val) (word : Integers.Int),
        bitOf word 1 = (rawWant c3 && al) → bitOf word 2 = false →
        (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Case2_after.f_url_match_auth_nego)
                  (negoSpec c2 foundV word cs oe) vs)
        ∧ ¬ H5.Case2.leaks (negInput c2 cs oe (rawWant c3) al) (vdOf c2 word cs oe) :=
  ⟨attach_after ge c3 mm al fb hcenv hpr3 hpw3 hdest hcp hnb hnowal bInst bMs bNow bMm bPr bAl bFind
     bConn bRes fdInst fdMs fdNow fdMm fdPr fdAl fdFind hsInst hsMs hsNow hsMm hsPr hsAl hsFind hsConn
     hsRes hfInst hfMs hfNow hfMm hfPr hfAl hfFind htyInst htyMs htyNow htyMm htyPr htyAl htyFind hInst
     hMs hNow hMm hPr hAl hFind,
   fun foundV word hw hprox =>
     ⟨auth_nego_eq ge c2 foundV word cs oe hcenv hpr2 hpn2 hpw2 hptr2 hprox bCs bPe fdCs fdPe hsCs
        hsPe hfCs hfPe htyCs htyPe hCs hPe,
      (vd_after c2 c3 word cs oe al hw) ▸ H5.Case2.P1 _⟩⟩


/-- 修正前のプログラムで、`url_attach_existing` が（外部関数の仕様のもとで）`attachSpec c3` を満たすこと。
    `Curl_cpool_find` には `findSpec (rawWant c3)` を要求する: ビットは `allowed` を見ずに `rawWant` になる。 -/
def AttachBeforeOK (c3 : Ctx3) : Prop :=
  ∀ (ge : CGenv) (mm fb : Bool) (bInst bMs bNow bMm bPr bFind bConn bRes : Block)
    (fdInst fdMs fdNow fdMm fdPr fdFind : FunDef),
    ge.genv_cenv = Case2_before.prog.prog_comp_env →
    Genv.findSymbol ge.genv_genv Case2_before._Curl_cpool_get_instance = some bInst →
    Genv.findSymbol ge.genv_genv Case2_before._memset = some bMs →
    Genv.findSymbol ge.genv_genv Case2_before._Curl_pgrs_now = some bNow →
    Genv.findSymbol ge.genv_genv Case2_before._xfer_may_multiplex = some bMm →
    Genv.findSymbol ge.genv_genv Case2_before._Curl_cpool_prune_dead = some bPr →
    Genv.findSymbol ge.genv_genv Case2_before._Curl_cpool_find = some bFind →
    Genv.findSymbol ge.genv_genv Case2_before._url_match_conn = some bConn →
    Genv.findSymbol ge.genv_genv Case2_before._url_match_result = some bRes →
    FuncPtr ge bInst fdInst → FuncPtr ge bMs fdMs → FuncPtr ge bNow fdNow →
    FuncPtr ge bMm fdMm → FuncPtr ge bPr fdPr → FuncPtr ge bFind fdFind →
    typeOfFundef fdInst
      = .Tfunction (instSpec c3.cpV).tyargs (instSpec c3.cpV).tyres (instSpec c3.cpV).cc →
    typeOfFundef fdMs = .Tfunction [tptr tvoid, tint, tulong] (tptr tvoid) cc_default →
    typeOfFundef fdNow = .Tfunction (nowSpec c3).tyargs (nowSpec c3).tyres (nowSpec c3).cc →
    typeOfFundef fdMm = .Tfunction (mmSpec mm).tyargs (mmSpec mm).tyres (mmSpec mm).cc →
    typeOfFundef fdPr = .Tfunction pruneSpec.tyargs pruneSpec.tyres pruneSpec.cc →
    typeOfFundef fdFind
      = .Tfunction (findSpec true bFind fb).tyargs (findSpec true bFind fb).tyres cc_default →
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdInst (instSpec c3.cpV) vs) →
    (∀ b vs, SatisfiesAt ge (FunctionEntry2 ge) fdMs (memsetSpec b) vs) →
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdNow (nowSpec c3) vs) →
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdMm (mmSpec mm) vs) →
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdPr pruneSpec vs) →
    (∀ b vs, SatisfiesAt ge (FunctionEntry2 ge) fdFind (findSpec (rawWant c3) b fb) vs) →
    ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Case2_before.f_url_attach_existing)
      (attachSpec c3) vs

theorem attach_before_ok (c3 : Ctx3) (hpr : permOrder c3.pm .Readable = true)
    (hpw : permOrder c3.pm .Writable = true) (hdest : IsPtr c3.destV) (hcp : IsPtr c3.cpV)
    (hnb : c3.nowBytes.length = 16) (hnowal : Integers.Ptrofs.unsigned c3.nowO % 8 = 0) :
    AttachBeforeOK c3 :=
  fun ge mm fb bInst bMs bNow bMm bPr bFind bConn bRes fdInst fdMs fdNow fdMm fdPr fdFind hcenv
    hsInst hsMs hsNow hsMm hsPr hsFind hsConn hsRes hfInst hfMs hfNow hfMm hfPr hfFind htyInst htyMs
    htyNow htyMm htyPr htyFind hInst hMs hNow hMm hPr hFind =>
  attach_before ge c3 mm fb hcenv hpr hpw hdest hcp hnb hnowal bInst bMs bNow bMm bPr bFind bConn bRes
    fdInst fdMs fdNow fdMm fdPr fdFind hsInst hsMs hsNow hsMm hsPr hsFind hsConn hsRes hfInst hfMs
    hfNow hfMm hfPr hfFind htyInst htyMs htyNow htyMm htyPr htyFind hInst hMs hNow hMm hPr hFind

/-- 修正前のプログラムで、`url_match_auth_nego` が `negoSpec` を満たすこと（関数は修正の前後で同じ）。 -/
def NegoBeforeOK (c2 : Ctx2) (foundV : Val) (word : Integers.Int) (cs oe : Bool) : Prop :=
  ∀ (ge : CGenv) (bCs bPe : Block) (fdCs fdPe : FunDef),
    ge.genv_cenv = Case2_before.prog.prog_comp_env →
    Genv.findSymbol ge.genv_genv Case2_before._Curl_creds_same = some bCs →
    Genv.findSymbol ge.genv_genv Case2_before._Curl_peer_equal = some bPe →
    FuncPtr ge bCs fdCs → FuncPtr ge bPe fdPe →
    typeOfFundef fdCs = .Tfunction (credsSpec cs).tyargs (credsSpec cs).tyres (credsSpec cs).cc →
    typeOfFundef fdPe = .Tfunction (peerSpec oe).tyargs (peerSpec oe).tyres (peerSpec oe).cc →
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCs (credsSpec cs) vs) →
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdPe (peerSpec oe) vs) →
    ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Case2_before.f_url_match_auth_nego)
      (negoSpec c2 foundV word cs oe) vs

theorem nego_before_ok (c2 : Ctx2) (foundV : Val) (word : Integers.Int) (cs oe : Bool)
    (hpr : permOrder c2.pm .Readable = true) (hpn : permOrder c2.pm .Nonempty = true)
    (hpw : permOrder c2.pm .Writable = true) (hptr : Ptrs2 c2) (hprox : bitOf word 2 = false) :
    NegoBeforeOK c2 foundV word cs oe :=
  fun ge bCs bPe fdCs fdPe hcenv hsCs hsPe hfCs hfPe htyCs htyPe hCs hPe =>
  auth_nego_eq ge c2 foundV word cs oe (hcenv.trans cenv_same2) hpr hpn hpw hptr hprox bCs bPe fdCs fdPe
    hsCs hsPe hfCs hfPe htyCs htyPe hCs hPe

/-- **P0（C）: 修正前の C 関数には、脆弱性が起きる入力がある。**

    具体的なメモリ `mW3`・`mW2` の上の値（Negotiate を要求する HTTP の転送で、送り先の許可は無く、
    Negotiate 済みで認証情報も送り先も同じ接続がある）で:
    - 前提を満たすヒープが実在する
    - 修正前の `url_attach_existing` は、ビットを `rawWant`（真）にして `Curl_cpool_find` を呼ぶ
      （`attach_before` が、どの `ge` でも外部関数の仕様のもとでこれを示す）
    - そのビットを読む `url_match_auth_nego` の判定は `forceReuse` で、`leaks` が成り立つ -/
theorem P0_C :
    ∃ (c3 : Ctx3) (c2 : Ctx2) (cs oe al : Bool) (foundV wp : Val) (word : Integers.Int),
      (∃ hp m, H3 c3 wp hp ∧ Heap.Agrees hp m)
      ∧ (∃ hp m, H2 c2 foundV word hp ∧ Heap.Agrees hp m)
      ∧ permOrder c3.pm .Writable = true ∧ permOrder c2.pm .Writable = true
      ∧ IsPtr c3.destV ∧ IsPtr c3.cpV ∧ c3.nowBytes.length = 16
      ∧ Integers.Ptrofs.unsigned c3.nowO % 8 = 0 ∧ Ptrs2 c2
      ∧ bitOf word 1 = rawWant c3 ∧ bitOf word 2 = false
      ∧ H5.Case2.leaks (negInput c2 cs oe (rawWant c3) al) (vdOf c2 word cs oe)
      ∧ AttachBeforeOK c3 ∧ NegoBeforeOK c2 foundV word cs oe := by
  obtain ⟨hp3, hH3, hag3⟩ := H3_cW3_satisfiable
  obtain ⟨hp2, hH2, hag2⟩ := H2_cW2_satisfiable
  refine ⟨cW3, cW2, true, true, false, _, _, wordW2, ⟨hp3, mW3, hH3, hag3⟩, ⟨hp2, mW2, hH2, hag2⟩,
    rfl, rfl, Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩, rfl, by decide, cW2_ptrs,
    by rw [rawWant_cW3]; exact wordW2_bits.1, wordW2_bits.2, ?_,
    attach_before_ok cW3 rfl rfl (Or.inr ⟨_, rfl⟩) (Or.inr ⟨_, rfl⟩) rfl (by decide),
    nego_before_ok cW2 _ wordW2 true true rfl rfl rfl cW2_ptrs wordW2_bits.2⟩
  rw [vd_before cW2 cW3 wordW2 true true false (by rw [rawWant_cW3]; exact wordW2_bits.1),
    rawWant_cW3]
  exact ⟨rfl, by decide, by decide⟩

end Case2C

#print axioms Case2C.P1_C
#print axioms Case2C.P0_C
#print axioms Case2C.attach_after
#print axioms Case2C.attach_before
#print axioms Case2C.auth_nego_eq
#print axioms Case2C.attach_before_ok
#print axioms Case2C.nego_before_ok
#print axioms Case2C.H3_cW3_satisfiable
#print axioms Case2C.H2_cW2_satisfiable
