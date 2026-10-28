# 手順書: 配布元（Debian）が出したバックポートに、上流の修正と同じ証明が通るか

作成: 2026-10-28（証明を試す前に書いた）
判断する人: TK
前提: `research/backport-proof/RESULTS.md`（Claude が作ったバックポートでは成功。次は配布元のバックポートで試す、と書いた）、
`research/c-semantics-link/RESULTS.md` の Case 4（上流の修正の上で P1・P0 が成立）

## 1. 何を確かめるか

C1 の Case 4 で示した性質が、**Debian が実際に出したバックポート**の上でも同じ形で示せるか。
前回（`backport-proof`）の限界「配布元が作ったバックポートではない」を外す。

## 2. 対象

- 脆弱性: CVE-2025-13034（QUIC＋GnuTLS で、ホスト名の検証を切ると公開鍵のピンの検査も飛ばされる）。上流の修正は 3d91ca8cdb
- 古い版: curl 8.14.1（tag `curl-8_14_1`、Debian 13 trixie の版）
- バックポート: Debian の `debian/patches/CVE-2025-13034.patch`
  （https://salsa.debian.org/debian/curl 、branch `debian/trixie`、8.14.1-2+deb13u3 で入った。作者 Matheus Souza Zanzin、Last-Update 2026-01-29）。
  手で直さずにそのまま当てる
- 構成は Case 4 と同じ（`USE_GNUTLS` を定義し、`USE_OPENSSL`・`USE_WOLFSSL` は定義しない）

試す前に分かっていること: GnuTLS の構成で、パッチを当てた 8.14.1 の関数と上流の修正後の関数の違いは、
`Curl_gtls_verifyserver` の引数に `cf` が無いこと（8.14.1 は5引数、上流は6引数）だけ。修正前どうしも同じ。

## 3. 成功の条件

- **D1**: パッチを当てた 8.14.1 の `Curl_vquic_tls_verify_peer` について、Case 4 の `verify_peer_after` と `P1_C` と同じ形の定理が成り立つ
- **D0**: パッチを当てる前の 8.14.1 について、Case 4 の `verify_peer_before` と `P0_C` と同じ形の定理が成り立つ
- 違ってよいのは、識別子の名前空間、構造体の削減の仕方、外部関数の引数の数だけ。仮定した外部仕様の数は記録する
- D1 と D0 の両方で成功。`sorry`・`admit`・`native_decide`・`bv_decide`・`axiom` の宣言は無い。`#print axioms` は Case 4 と同じ集合

## 4. 測るもの

- 時間と `lake build` の回数
- Case 4 の証明のうち、そのまま使えた部分と書き換えた部分（行数）

上限: 2時間、`lake build` 40回。超えたら、その時点の状態を記録して止める。

## 5. この試作の限界（試す前に書いておく）

- 性質を述べるのも証明するのも Claude である。バックポートだけが配布元のもの
- この件は差分が小さく、上流と 8.14.1 の違いも引数1つなので、易しい例である。バックポートで関数の形が変わる件の手間は、この件からは分からない
- 外部関数の仕様は Case 4 と同じく仮定である（`Curl_gtls_verifyserver` の強い仕様 `horacle` を含む）

## 6. 結果

`RESULTS.md` に書く（このファイルと別のコミットにする）。
