/-
Case 5: CURL-CVE-2026-86411 (CWE-488 "FTP connection reuse inherits client-certificate")
Fix: curl 72352daba0 "connection reuse: check SSL configs when doing a scheme upgrade"

C の対応（lib/url.c）:
- url_match_ssl_use:
  - needle が SSL のスキームなら、conn が SSL であることを要求する
  - needle が SSL でなく conn が SSL なら、PROTOPT_SSL_REUSE と同じプロトコル族を要求する
    （修正後は、これに Curl_ssl_conn_config_match が加わる）
  - どちらでもなければ、require_tls のとき不一致
- url_match_ssl_config（修正の前後で同じ）:
  needle が SSL か may_tls（use_ssl > NONE）なら、Curl_ssl_conn_config_match を要求する
- 一致の判定は、上の2つの論理積としてモデル化する
  （他の照合条件は修正の前後で同じなので省いた）

クライアント証明書は SSL の設定に含まれる。設定が一致しない TLS 接続を再利用すると、
別の転送のクライアント証明書を引き継いでしまう。
-/
namespace H5.Case5

structure Input where
  needleSSL  : Bool -- m->needle->scheme->flags & PROTOPT_SSL
  connSSL    : Bool -- Curl_conn_is_ssl(conn, FIRSTSOCKET)
  reuseOk    : Bool -- needle->scheme->flags & PROTOPT_SSL_REUSE
  sameFamily : Bool -- get_protocol_family(conn->scheme) == needle->scheme->protocol
  requireTls : Bool -- use_ssl >= CURLUSESSL_CONTROL
  mayTls     : Bool -- use_ssl > CURLUSESSL_NONE
  cfgMatch   : Bool -- Curl_ssl_conn_config_match(data, conn, FALSE)

def sslUseB (x : Input) : Bool :=
  if x.needleSSL then x.connSSL
  else if x.connSSL then x.reuseOk && x.sameFamily
  else !x.requireTls

def sslUseA (x : Input) : Bool :=
  if x.needleSSL then x.connSSL
  else if x.connSSL then x.reuseOk && x.sameFamily && x.cfgMatch
  else !x.requireTls

def sslConfig (x : Input) : Bool := !(x.needleSSL || x.mayTls) || x.cfgMatch

def before (x : Input) : Bool := sslUseB x && sslConfig x
def after  (x : Input) : Bool := sslUseA x && sslConfig x

/-- 脆弱性: SSL の設定（クライアント証明書を含む）が一致しない TLS 接続を再利用する。 -/
def inherits (x : Input) (reuse : Bool) : Bool := reuse && x.connSSL && !x.cfgMatch

/-- P0: 修正前は、TLS を要求しない ftp:// の転送が、設定の違う FTPS 接続を再利用する。 -/
theorem P0 : ∃ x, inherits x (before x) = true :=
  ⟨⟨false, true, true, true, false, false, false⟩, by decide⟩

/-- P1: 修正後は、設定の一致しない TLS 接続を再利用しない。 -/
theorem P1 (x : Input) : inherits x (after x) = false := by
  rcases x with ⟨a, b, c, d, e, f, g⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> decide

/-- P2: 再利用の候補が、TLS でない接続か、設定の一致する接続なら、修正前と修正後の判定が同じ。 -/
theorem P2 (x : Input) (h : x.connSSL = false ∨ x.cfgMatch = true) : after x = before x := by
  rcases x with ⟨a, b, c, d, e, f, g⟩
  simp only at h
  rcases h with h | h <;> subst h <;>
    cases a <;> cases c <;> cases d <;> cases e <;> cases f <;> simp [after, before, sslUseA, sslUseB, sslConfig]

end H5.Case5
