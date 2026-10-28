# 結果: 配布元（Debian）が出したバックポートに、上流の修正と同じ証明が通るか

判定日: 2026-10-28
基準: `PROTOCOL.md`（コミット f463a17、2026-10-28 02:20:48。証明を試す前）。判定のあとで基準は変えていない。

## 結論

**成功**（D1・D0 とも成立）。curl 8.14.1 に Debian trixie の `CVE-2025-13034.patch` を手を加えずに当てた関数の上で、
C1 の Case 4 と同じ形の定理が成り立った。

| | 結果 | 定理（`research/c-semantics-link/lean/`） | 仮定した外部仕様 |
|---|---|---|---|
| D1 | 成立 | `Case4debC.verify_peer_after`（`Case4debAfter.lean`）、`Case4debC.P1_C`（`Case4deb.lean`） | 2個（`getSpec`・`vsSpec`）と強い仕様1つ（`horacle`）。Case 4 と同じ |
| D0 | 成立 | `Case4debC.verify_peer_before`（`Case4debBefore.lean`）、`Case4debC.P0_C`（`Case4deb.lean`） | 同上 |

- 時間: 約2分30秒（基準のコミット 02:20:48 から、最初に通ったビルド 02:23:17 まで）。題材を選ぶ調べ（下）は、基準より前の作業なので数えていない
- `lake build`: 2回（どちらも成功。2回目は docstring を直したあと）。ほかに `#print axioms` を見るための `lake env lean` を1回（`build-log.tsv` の `case4deb-probe`）
- 上限（2時間・40回）の内

## 題材の選び方（基準より前に調べたこと）

前回（`research/backport-proof/`）は Claude が作ったバックポートだった。C1 の5件について Debian security tracker（2026-10-28）を見ると、
Debian のバックポートがあるのは CVE-2025-13034 だけだった。

| C1 の件 | CVE | trixie の状態（tracker の Notes） |
|---|---|---|
| Case 4 | CVE-2025-13034 | 修正済み。8.14.1-2+deb13u3 で `CVE-2025-13034.patch` を当てた |
| Case 3 | CVE-2026-92389 | 脆弱なまま。`<no-dsa> (Minor issue)` |
| Case 1 | CVE-2026-92387 | 脆弱なまま。`<no-dsa> (Minor issue)` |
| Case 5 | CVE-2026-86411 | `<not-affected> (Vulnerable code not present)` |
| Case 2 | CVE-2026-86413 | `<not-affected> (Vulnerable code not present)` |

パッチは salsa.debian.org の debian/curl、コミット c2a97b9ea5（debian/trixie）から取った（sha256 6d3caaf6…1e27。`case4deb/extract.py` が取得のたびに照合する）。

## Case 4 との違い

- C の関数（GnuTLS の構成でプリプロセスした範囲）: 違いは `Curl_gtls_verifyserver` の引数に `cf` が無いことだけ。
  8.14.1 は5引数、上流の修正後は6引数。修正の中身（`if(conn_config->verifyhost)` を外して必ず呼ぶ）は上流と同じ
- 前置き（`case4deb/prelude.h`）: 外部関数の宣言1つから `cf` を外した。構造体の削減は Case 4 と同じ。`enum dupstring` は
  8.14.1 の `lib/urldata.h` から機械で切り出した。`STRING_SSL_PINNEDPUBLICKEY` の添字は 7 で上流と同じ
- 証明: Case 4 の4ファイルを名前空間だけ変えて写し、次の11行を書き換えた（名前の置き換えを除いた `diff` の行数）
  - `Case4debCommon.lean` 2行: `vsSpec` の引数の型の並びから `Curl_cfilter` を外した
  - `Case4debAfter.lean` 4行・`Case4debBefore.lean` 5行: `Curl_gtls_verifyserver` の呼び出しで、引数 `cf` の評価の段を外した
  - `Case4deb.lean` 0行
- 書き換えはスクリプトで機械的に行った（名前の置き換えと、`cf` の評価の段を外すこと）。手で直した証明の行は無い

## 確認したこと

- `sorry`・`admit`・`native_decide`・`bv_decide`・`axiom` の宣言は無い（grep で確認）
- `#print axioms`: `P1_C`・`P0_C`・`verify_peer_after`・`verify_peer_before` は、Case 4 と Case 4deb で同じ集合
  （`propext`・`Classical.choice`・`Quot.sound` と、Certora/clean の `CC.externalFunctionsSem`・`CC.inlineAssemblySem`）。
  `H4_cW4_satisfiable` は `propext`・`Quot.sound` だけ
- 定理の文が、上流の関数ではなく 8.14.1 の関数を指していること: `P1_C` は `Case4deb_after.f_Curl_vquic_tls_verify_peer`、
  `P0_C` は `Case4deb_before.prog` の上で述べている（`#check` で確認）
- H5 のモデル（`H5Case4.lean`）は Case 4 と共有で、変えていない

## 読み方の注意

- **易しい例である**（PROTOCOL §5）。Debian のパッチは上流の修正をほぼそのまま写したもので、8.14.1 と上流の違いも引数1つだった。
  バックポートで関数の形が変わる件の手間は、この結果からは分からない
- 性質を述べたのも証明したのも Claude で、配布元のものはバックポートだけである
- 外部関数の仕様は Case 4 と同じく仮定である。特に P1 は、gtls.c の検査が正しいという強い仕様（`horacle`）に依存する
- 1件だけの結果で、件数は増やしていない

## 何が言えるか（事業の面）

（この節は内部の運用に関するもので、公開版では省いた）

## ファイル

- `research/c-semantics-link/case4deb/`: `extract.py`（取得・パッチ当て・切り出し）、`debian.patch`（取得したパッチの写し）、
  `prelude.h`、`enum.h`、`case4deb_before.c`・`case4deb_after.c`
- `research/c-semantics-link/lean/`: `GenCase4debAfter.lean`・`GenCase4debBefore.lean`（`clightgen -lean -normalize` の出力）、
  `Case4debCommon.lean`・`Case4debAfter.lean`・`Case4debBefore.lean`・`Case4deb.lean`
