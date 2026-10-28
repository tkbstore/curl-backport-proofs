/-
Case 4: CURL-CVE-2025-13034 (CWE-295 "No QUIC certificate pinning with GnuTLS")
Fix: curl 3d91ca8cdb "vquic-tls/gnutls: call Curl_gtls_verifyserver unconditionally"

C の対応:
- lib/vquic/vquic-tls.c, Curl_vquic_tls_verify_peer（USE_GNUTLS の分岐）
  - 修正前: `if(conn_config->verifyhost) { result = Curl_gtls_verifyserver(...); }`
  - 修正後: 条件を外して、常に Curl_gtls_verifyserver を呼ぶ
- lib/vtls/gtls.c, Curl_gtls_verifyserver が行う検査（gtls.c の 1645・1863・1869 行付近）:
  - verifypeer ならチェーンの検証
  - verifyhost ならホスト名の照合
  - pinned_key があれば公開鍵ピンの照合

モデルで省いたもの:
- OCSP
- 証明書が無い場合の扱い
- エラーの種類。結果は受け入れるか拒否するかの2値にした
-/
namespace H5.Case4

structure Config where
  verifypeer : Bool
  verifyhost : Bool
  pinSet     : Bool

structure Cert where
  chainOk : Bool
  hostOk  : Bool
  pinOk   : Bool

/-- Curl_gtls_verifyserver: 有効になっている検査がすべて通れば true（受け入れる）。 -/
def verifyserver (c : Config) (x : Cert) : Bool :=
  !(c.verifypeer && !x.chainOk) && !(c.verifyhost && !x.hostOk) && !(c.pinSet && !x.pinOk)

def before (c : Config) (x : Cert) : Bool := if c.verifyhost then verifyserver c x else true
def after  (c : Config) (x : Cert) : Bool := verifyserver c x

/-- 有効になっている検査のどれかに通らない証明書。 -/
def bad (c : Config) (x : Cert) : Bool :=
  (c.verifypeer && !x.chainOk) || (c.verifyhost && !x.hostOk) || (c.pinSet && !x.pinOk)

/-- P0: 修正前は、ホスト名の検証を切ってピンを設定した接続で、ピンの合わない証明書を受け入れる。 -/
theorem P0 : ∃ c x, bad c x = true ∧ before c x = true :=
  ⟨⟨false, false, true⟩, ⟨true, true, false⟩, by decide⟩

/-- P1: 修正後は、有効になっている検査のどれかに通らない証明書を受け入れない。 -/
theorem P1 (c : Config) (x : Cert) (h : bad c x = true) : after c x = false := by
  rcases c with ⟨p, hst, pin⟩
  rcases x with ⟨a, b, d⟩
  cases p <;> cases hst <;> cases pin <;> cases a <;> cases b <;> cases d <;>
    simp_all [bad, after, verifyserver]

/-- P2: ホスト名の検証が有効な接続、または問題の無い証明書では、修正前と修正後の結果が同じ。 -/
theorem P2 (c : Config) (x : Cert) (h : c.verifyhost = true ∨ bad c x = false) :
    after c x = before c x := by
  rcases c with ⟨p, hst, pin⟩
  rcases x with ⟨a, b, d⟩
  cases p <;> cases hst <;> cases pin <;> cases a <;> cases b <;> cases d <;>
    simp_all [bad, after, before, verifyserver]

end H5.Case4
