/-
Case 2: CURL-CVE-2026-86413 (CWE-201 "Negotiate credentials sent to redirected origin")
Fix: curl 43029e2ec3 "url: ntlm/negotiate, prohibit connection reuse on follows"

C の対応（lib/url.c）:
- url_attach_existing: `match.want_nego_http = (authhost.want & NEGOTIATE) && HTTP`
  修正後は、これに `&& Curl_auth_allowed_to_host(data)` が加わる
- url_match_auth_nego（ホスト側の部分）:
  - 接続が Negotiate 済み（http_negotiate_state != GSS_AUTHNONE）なら、
    `!want_nego || !creds_same || !origin_eq` のとき拒否
  - 未使用で want_nego なら、接続に認証情報があり、それが違えば拒否
  - want_nego なら、
    - Negotiate 済みの接続は「これを使え」（force_reuse, TRUE）
    - そうでなければ候補として覚えて FALSE（他を探す）
  - それ以外は TRUE

モデルで省いたもの:
- プロキシ側の Negotiate（修正で変わっていない）
- NTLM（同じ修正が入っているが、このケースでは Negotiate だけを扱う）
- 認証情報や origin の比較の中身は、真偽値の入力として扱う
-/
namespace H5.Case2

structure Input where
  rawWant    : Bool  -- (authhost.want & NEGOTIATE) && HTTP
  allowed    : Bool  -- Curl_auth_allowed_to_host(data)
  negotiated : Bool  -- conn->http_negotiate_state != GSS_AUTHNONE
  connCreds  : Bool  -- conn->creds != NULL
  credsSame  : Bool
  originEq   : Bool

inductive Verdict where
  | reject     -- FALSE: この接続は使わない
  | candidate  -- FALSE だが m->found に覚える
  | forceReuse -- TRUE かつ force_reuse
  | accept     -- TRUE
  deriving DecidableEq, Repr

def matchNego (want : Bool) (x : Input) : Verdict :=
  if x.negotiated then
    if !want || !x.credsSame || !x.originEq then .reject
    else .forceReuse
  else if want && x.connCreds && (!x.credsSame || !x.originEq) then .reject
  else if want then .candidate
  else .accept

def before (x : Input) : Verdict := matchNego x.rawWant x
def after  (x : Input) : Verdict := matchNego (x.rawWant && x.allowed) x

/-- 脆弱性: 認証情報を送ってよくない相手への転送で、Negotiate 済みの接続を使ってしまう。 -/
def leaks (x : Input) (v : Verdict) : Prop :=
  x.allowed = false ∧ x.negotiated = true ∧ v = .forceReuse

/-- P0: 修正前には、Negotiate 済みの接続を再利用してしまう入力がある。 -/
theorem P0 : ∃ x, leaks x (before x) :=
  ⟨{ rawWant := true, allowed := false, negotiated := true,
     connCreds := true, credsSame := true, originEq := true },
   by simp [leaks, before, matchNego]⟩

/-- P1: 修正後は、どの入力でも漏れない。 -/
theorem P1 (x : Input) : ¬ leaks x (after x) := by
  rcases x with ⟨w, a, n, c, s, o⟩
  cases w <;> cases a <;> cases n <;> cases c <;> cases s <;> cases o <;> simp [leaks, after, matchNego]

/-- P2: 脆弱性の条件に当たらない入力（送ってよい相手、または Negotiate を使わない）では、
修正前と修正後の判定が同じ。 -/
theorem P2 (x : Input) (h : x.allowed = true ∨ x.rawWant = false) :
    after x = before x := by
  rcases x with ⟨w, a, n, c, s, o⟩
  simp only at h
  rcases h with h | h <;> subst h <;> simp [after, before]

end H5.Case2
