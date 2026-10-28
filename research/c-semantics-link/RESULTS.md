# 結果: H5 の証明を C のコードにつなげられるか（C1）

基準: `PROTOCOL.md`（コミット 9e1e31f、2026-10-22 15:58:51。試す前）。判定のあとで基準は変えていない。
状態: **判定済み: 支持**（5件中3件を試し、3件とも成功。判定は残りの結果によらない）。判定のあとで、参考として Case 1 を試した（P1 は成立、P0 は不成立で、件としては不成功。判定は変わらない）。続けて Case 3 を試した（P1・P0 とも成立で、件として成功。判定は変わらない）

## 道具の段階（PROTOCOL §6 の上限は合計 1 日）

2026-10-22 16:01 に始め、16:11 に終えた（約10分）。上限の範囲に収まった。

| 手順 | 結果 |
|---|---|
| `brew install opam`（2.6.1）、`opam init --bare --disable-sandboxing` | 成功 |
| switch `compcert-4.14`（OCaml 4.14.2）、`coq.9.1.0`（Rocq 9.1.0）、`menhir` | 成功 |
| Certora/clean を `123f7f7` で clone（リポジトリの外 `~/Documents/GitHub/_vendor/certora-clean`） | 成功 |
| `./configure -clightgen aarch64-macos` → `make depend` → `make -j10 proof`（1分52秒）→ `make extraction` → `make clightgen` | 成功。`make depend` を先に回さないと `proof` が `Can't find file ./Coqlib.v` で止まる |
| `export/` で `lake build`（Lean 4.32.1、65 ジョブ） | 成功 |

## 件ごとの結果

| # | ID | P1（C） | P0（C） | 公理（自分で置いたもの） | 外部関数の仕様（仮定） | 時間 | `lake build` |
|---|---|---|---|---|---|---|---|
| 5 | CURL-CVE-2026-86411 | **成功** | **成功** | 0 | 2個（`sslSpec` 8行・`cfgSpec` 9行） | 約25分（16:12〜16:37） | 26回 |
| 4 | CURL-CVE-2025-13034 | **成功** | **成功** | 0 | 2個（`getSpec` 7行・`vsSpec` 12行）＋強い仕様1つ（`horacle`） | 約14分（16:38〜16:52） | 14回 |
| 2 | CURL-CVE-2026-86413 | **成功** | **成功** | 0 | 9個（下の表）＋つなぎ目の前提1つ | 約44分（16:53〜17:37） | 40回 |
| 1 | CURL-CVE-2026-92387 | **成功** | **不成立**（§5 の定めどおり） | 0 | 11個（計89行）＋受信バッファの述語の性質3つ。強い仕様1つ（0 バイトを返さない） | 約2時間7分（19:58〜22:05） | 35回 |
| 3 | CURL-CVE-2026-92389 | **成功**（2関数に分けて） | **成功** | 0 | P1: `tftp_tx` 0個、`tftp_receive_packet` 5個＋文字列リテラルのシンボル1つ。P0: 3個 | 約43分（P1 00:02〜00:35、P0 04:35〜04:45、10-23） | 27回 |

### Case 5（`lib/url.c` `url_match_ssl_use`・`url_match_ssl_config`）

ファイル: `case5/`（翻訳単位を作るもの）、`lean/`（証明）。

**示したこと**

- `ssl_use_after`（`lean/Case5After.lean`）: 修正後の `url_match_ssl_use` の Clight の構文木を実行すると、
  H5 のモデルの `sslUseA` と同じ値を返す
- `ssl_use_before`（`lean/Case5Before.lean`）: 修正前の同じ関数は `sslUseB` を返す
- `ssl_config_eq`（`lean/Case5Config.lean`）: `url_match_ssl_config`（修正の前後で同じ）は `sslConfig` を返す
- `P1_C`（`lean/Case5.lean`）: 上の2つの値の論理積（curl が接続を再利用する条件）は H5 の `after` と同じで、
  `inherits` は偽。最後の段は H5 の定理 `P1` をそのまま使った
- `P0_C`（同）: 具体的なメモリ `mW`（`lean/Case5Witness.lean`、80 バイトの1ブロック）の上に、
  前提を満たすヒープがある。その入力で、修正前の2つの関数の値の論理積は真になり、`inherits` も真になる
  （ftp:// の要求が、設定の違う FTPS の接続を再利用する）
- 副産物: H5 で Claude が書き起こしたモデル（`sslUseA`・`sslUseB`・`sslConfig`）が、この関数については
  C の意味論と一致することが分かった。H5 の「読み方の注意」の「モデルの忠実さは人のレビューを受けていない」に対する、
  機械での確認になる（この1件について）

**確認したこと**

- `sorry`・`admit`・`native_decide`・`bv_decide` は無い（grep で確認）。`axiom` の宣言も無い
- `#print axioms`: `P1_C`・`P0_C`・`ssl_use_after`・`ssl_use_before`・`ssl_config_eq` は
  `propext`・`Classical.choice`・`Quot.sound`（Lean の標準）と、`externalFunctionsSem`・`inlineAssemblySem`
  （Certora/clean が宣言する外部関数の公理）だけ。`H_cW_satisfiable` は `propext`・`Quot.sound` だけ
- `lean/H5Case5.lean` は `research/ai-vuln-verification/h5/H5/Case5.lean` と同一（`cmp` で確認）。
  Lean の版が違う（4.35.0 と 4.32.1）ので import できず、複製した
- 関数の本体は `case5/extract.py` が curl のソース（`gh api` で取得）から文字列として切り出した。
  修正前と修正後の差分は、修正の4行だけ

**PROTOCOL §4 からの逸脱（1件）**

- CompCert は参照されない `static` 関数を変換時に消す（`cparser/Cleanup.ml`）。対象の関数を残すため、
  それらを参照するだけの大域変数を1つ足した（`case5/epilogue.h`）。関数の宣言と本体には触れていない。
  §4 の「許す変更」の一覧には無い変更である

**外部関数の仕様の与え方**

§4 は「Lean 側で仕様を公理として与える」としていたが、`axiom` は置かず、定理の仮定（`hSsl`・`hCfg`）として与えた。
信頼の前提としては同じで、仮定の形のほうが矛盾した公理で全体が壊れる心配がない。仕様の中身は次のとおり。

- `Curl_conn_is_ssl(conn, 0)` は、任意の真偽値 `ssl` を返し、メモリを変えない
- `Curl_ssl_conn_config_match(data, conn, FALSE)` は、任意の真偽値 `cfg` を返し、メモリを変えない
- 強めている点: 同じ `conn` に対しては、何度呼んでも同じ値を返す（2つの関数をまたいでも同じ）。
  1回の照合の間に接続の状態は変わらない、という前提である

**読み方の注意（この件で分かった限界）**

- **構造体のレイアウトは減らしたもの**。§4 で許した「触るフィールドだけに減らす」により、フィールドの位置
  （`needle` が 8 バイト目、`may_tls` が bit 0 など）は実物の curl と違う。関数の本体は同じだが、
  証明は減らしたレイアウトの上の主張である
- **「その仕様どおりに終わる実行がある」の形**。Certora/clean の三つ組は全正当性で、実行の存在を述べる。
  決定性（`CCLib/Determinism.lean`）を使って「すべての実行」に持ち上げることはしていない
- **`needle` と `conn` の `connectdata` は別の領域にあると仮定している**（分離論理の前提）。
  `needle->scheme` と `conn->scheme` が同じ構造体であることは許している（読むフィールドが重ならない）
- **P2 は求めていない**（PROTOCOL §5）

### Case 4（`lib/vquic/vquic-tls.c` `Curl_vquic_tls_verify_peer`、GnuTLS の構成）

ファイル: `case4/`（翻訳単位）、`lean/Case4*.lean`（証明）。`USE_GNUTLS` を定義し、`USE_OPENSSL`・`USE_WOLFSSL` は定義しない構成でプリプロセスした。

**示したこと**

- `verify_peer_after`（`lean/Case4After.lean`）: 修正後の関数の戻り値は、`Curl_ssl_cf_get_primary_config` が NULL なら 2
  （CURLE_FAILED_INIT）、そうでなければ `Curl_gtls_verifyserver` の戻り値 `r`
- `verify_peer_before`（`lean/Case4Before.lean`）: 修正前の関数の戻り値は、NULL なら 2、
  `conn_config->verifyhost` が立っていれば `r`、立っていなければ CURLE_OK（`Curl_gtls_verifyserver` を呼ばない）
- `P1_C`（`lean/Case4.lean`）: `bad` な証明書（有効な検査のどれかに通らない）では、修正後の戻り値は CURLE_OK にならない。
  最後の段は H5 の定理 `P1` をそのまま使った
- `P0_C`（同）: 具体的なメモリ `mW4`（104 バイトの1ブロック）の上に前提を満たすヒープがあり、
  H5 の反例（ホスト名の検証を切り、ピンを設定し、ピンの合わない証明書）で、修正前の戻り値は CURLE_OK になる

**確認したこと**

- `sorry`・`admit`・`native_decide`・`bv_decide`・`axiom` の宣言は無い（grep で確認）
- `#print axioms`: `P1_C`・`P0_C`・`verify_peer_after`・`verify_peer_before` は Lean の標準の3つと
  Certora/clean の外部関数の公理2つだけ。`H4_cW4_satisfiable` は `propext`・`Quot.sound` だけ
- `lean/H5Case4.lean` は H5 の `Case4.lean` と同一（`cmp` で確認）

**強い仕様（PROTOCOL §4 の「強い仕様が要る場合」に当たる）**

H5 の性質は、`Curl_gtls_verifyserver`（gtls.c）が「有効な検査がすべて通れば CURLE_OK を返す」ことに依存する。
修正が変えたのは「この関数を呼ぶかどうか」だけで、検査の中身は gtls.c にある。そこで P1 の定理に
「`r` が CURLE_OK であることと H5 の `verifyserver` が真であることは同じ」という仮定（`horacle`）を置いた。
外部関数の仕様そのもの（`vsSpec`）は弱いまま（任意の `r` を返し、メモリを変えない）で、強い仮定は P1 の最後の段だけで使う。
P0 は `horacle` を満たす値（`r = 1`）を具体的に与えた。

**読み方の注意**

- 構造体のレイアウトは減らしたもの（Case 5 と同じ）。`enum dupstring` は curl の定義をそのまま写したので、
  `STRING_SSL_PINNEDPUBLICKEY` の添字（7）は実物と同じ
- 2つ目の `if(result)`（`Curl_ssl_scache_remove_all` の呼び出し）には、GnuTLS の構成では到達しない
  （その前の `if(result) return result;` で戻る）。そのため、この外部関数の仕様は証明に使っていない
  （`Case4Common.lean` に定義した `rmSpec`・`call_none` は未使用）
- `if(!conn_config)` はポインタの真偽を見るため、CompCert の意味論では `conn_config` が有効なポインタであることが要る。
  そのため前提 `H4` に、`conn_config` が指す4バイトの所有を入れている

### Case 2（`lib/url.c` `url_attach_existing`・`url_match_auth_nego`）

ファイル: `case2/`（翻訳単位と、証明を経路ごとに組み立てる `gen_nego.py`・`post_nego.py`）、`lean/Case2*.lean`（証明）。
ビルドの構成は、`USE_SPNEGO` を定義し、`USE_NTLM` は定義せず、`CURL_DISABLE_PROXY` を定義した（プロキシ無効）。
H5 のモデルが省いたプロキシの Negotiate は、この構成ではプリプロセスで消える。

**示したこと**

- `auth_nego_eq`（`lean/Case2NegoMain.lean`）: `url_match_auth_nego`（修正の前後で同じ）は、`match` のビットの単位の
  `want_nego_http` を `want` とすると、H5 のモデルの `matchNego want x` と同じ判定をする。
  判定は戻り値と2つの書き込み（`m->found = conn`・`m->force_reuse = TRUE`）に現れ、4つの判定すべてで一致する。
  前提は `want_proxy_nego_http` が 0 であること
- `attach_after`（`lean/Case2AttachMain.lean`）: 修正後の `url_attach_existing` は、`Curl_cpool_find` を呼ぶ時点で、
  渡す `match` の `want_nego_http` を `rawWant && allowed` に、`want_proxy_nego_http` を 0 にしている。
  `Curl_cpool_find` の仕様（`findSpec`）の前提にこのビットの値を要求し、関数全体がその仕様のもとで証明できることで示した。
  ローカル変数 `match`（48 バイト）の確保と解放、`memset`、構造体のコピー（`match.now = *Curl_pgrs_now(data)`）、
  ビットフィールドへの5回の書き込み、外部関数7つの呼び出しを、すべて C の意味論の上で通した
- `attach_before`（`lean/Case2AttachBefore.lean`）: 修正前は、ビットを `rawWant`（`allowed` を見ない）にして呼ぶ
- `P1_C`（`lean/Case2.lean`）: 2つをつなぐと、C の関数の判定は H5 の `after` と同じで、`leaks`（送ってよくない相手への
  転送で Negotiate 済みの接続を使う）にならない。最後の段は H5 の定理 `P1` をそのまま使った
- `P0_C`（同）: 具体的なメモリ `mW3`・`mW2`（`lean/Case2Witness.lean`）の上に前提を満たすヒープがあり、
  H5 の反例の値で、修正前の2つの関数（`AttachBeforeOK`・`NegoBeforeOK`）の判定は `forceReuse` になり、`leaks` が成り立つ

**確認したこと**

- `sorry`・`admit`・`native_decide`・`bv_decide`・`axiom` の宣言は無い（grep で確認）
- `#print axioms`: `P1_C`・`P0_C`・`attach_after`・`attach_before`・`auth_nego_eq` は Lean の標準の3つと
  Certora/clean の外部関数の公理2つだけ。具体的なメモリの補題は `propext`・`Quot.sound` だけ
- `lean/H5Case2.lean` は H5 の `Case2.lean` と同一（`cmp` で確認）
- 2つの定理（`attach_after`・`attach_before`）は、Lean の既定の計算量の上限（`maxHeartbeats` 200000）では
  時間切れになったため、その2つだけ上限を 4000000 にした。公理や証明の中身は変わらない

**外部関数の仕様（定理の仮定として与えた）**

| 関数 | 仕様 | 強さ |
|---|---|---|
| `Curl_creds_same`・`Curl_peer_equal` | 任意の真偽値を返し、メモリを変えない | 弱い |
| `Curl_cpool_get_instance`・`Curl_pgrs_now`・`xfer_may_multiplex`・`Curl_auth_allowed_to_host` | 任意の値を返し、メモリを変えない | 弱い |
| `Curl_cpool_prune_dead` | 何も返さず、ここで見るメモリを変えない | 弱い |
| `memset` | C の標準どおり、指定したバイトを 0 にする | 標準ライブラリの意味 |
| `Curl_cpool_find` | 前提に `match` のビットの値を要求する。任意の真偽値を返し、`match` の所有を返す（中身は変わってよい） | 前提が性質そのもの |

**つなぎ目の前提（証明していない）**

`Curl_cpool_find` は `url_match_conn` を通して同じ `match` で `url_match_auth_nego` を呼び、その間
`want_nego_http`・`want_proxy_nego_http` を書き換えない。`url_match_conn`（ほかの照合を十数個行う）と
接続プールの走査の本体は、この実験の外に置いた。H5 のモデルの `after x = matchNego (rawWant && allowed) x` に当たる段で、
C の意味論の上では、2つの関数がそれぞれその両端を満たすことまでを示した。

**PROTOCOL §4 からの逸脱**

- Case 5 と同じく、参照されない `static` 関数を残すための大域変数を1つ足した（`case2/epilogue.h`）
- ビルドの構成（SPNEGO 有効・NTLM 無効・プロキシ無効）を選んだ。プロキシ有効の構成では、関数の本体にプロキシの
  照合が入る（H5 のモデルはそれを省いていた）

**ライブラリについて分かったこと**

- Certora/clean には、ビットフィールドへの書き込みの規則が無い（`triple_assign` は `.Full` だけ）。
  意味論の `AssignLoc.bitfield` から規則（`triple_assign_bitfield`、`lean/Case2Common.lean`）を自分で足した

### Case 1（`lib/pingpong.c` `Curl_pp_readresp`。参考として、判定のあとに試した）

ファイル: `case1/`（翻訳単位を作るもの、文の切り出し `cut_stmts.py`）、`lean/Case1*.lean`（証明）。

**結果: 不成功**（P1 は成立、P0 は PROTOCOL §5 の定めどおり不成立）。成功は3件のままなので、全体の判定は変わらない。

**示したこと**

- `readresp_returns`（`lean/Case1Main.lean`）: 修正後の `Curl_pp_readresp` の本体は、受信バッファの長さがいくつでも、
  呼ばれる側の関数が仕様の範囲でどう振る舞っても、return に達する。H5 の P1（`maxloops + 1` 回以内に戻る）に当たる
  - 外側のループ（`outer_loop`、`lean/Case1Outer.lean`）: 減少量は修正で入った `maxloops`（10 から始まる）。
    ループが続くのは `gotbytes == sizeof(buffer)` のときだけで、そのときは必ずソケットから読んでいて `maxloops` が1つ減っている
  - 内側のループ（`inner_loop`、`lean/Case1Inner.lean`）: 減少量は受信バッファの長さ。1回ごとに1行（1バイト以上）を取り除くか、空にする
  - ソケットから読む部分（`ovf_ok`・`read_ok`、`lean/Case1Ovf.lean`）
- `pread_ok`（同 `Case1Main.lean`）: 同じ翻訳単位の `static` 関数 `pingpong_read` の仕様は、本体から導いた（仮定ではない）

**P0 が不成立の理由**

- §5 は、Case 1 の P0 を「修正前の状態が同じ状態に戻ることを示す。できなければ不成立」と定めている
- 修正前のループでは `pp->nread_resp`（64 ビット）が毎回 900 ずつ増え、同じ値に戻るのは 2^62 回後になる。
  加えて、外部関数の仕様（`SatisfiesAt`）は呼んだあとのメモリを完全には決めないので、「同じ状態」を言う手段が無い
- 止まらないことを示すには、Certora/clean に無い「無限に続く実行」の形（余帰納的な発散）が要る。試していない

**確認したこと**

- `sorry`・`admit`・`native_decide`・`bv_decide`・`axiom` の宣言は無い（grep で確認）
- `#print axioms`: `readresp_returns`・`pread_ok`・`outer_loop`・`inner_loop` は Lean の標準の3つと
  Certora/clean の外部関数の公理2つだけ
- 関数の本体は `case1/extract.py` が curl のソース（`gh api` で取得）から文字列として切り出した
- `lean/Case1Stmts.lean` は `case1/cut_stmts.py` が生成物 `GenCase1After.lean` から括弧の対応で切り出した文で、
  使う側では定義の展開で本体と照合される（手で書いた文ではない）
- 証明の行数は 2,343 行（`Case1Stmts.lean` と生成物の `Gen*.lean` を除く）
- 7つの定理（`nl_ok`・`inner_body`・`read_ok`・`ovf_ok`・`nfin_ok`・`outer_body`・`readresp_returns`）は、`maxHeartbeats` を 4000000 にした
- `lake build` の35回のうち1回は、`#print axioms` の出力を見るためにキャッシュから記録を出し直しただけのもの（数には入れた）

**外部関数の仕様（定理の仮定として与えた）**

どの仕様も、呼び出しの引数を実際の値に固定し、関数が所有するメモリ全体を受け取って、型を保ったまま書き換えてよいことにした
（値を追うのは `gotbytes`、受信バッファの長さと先頭、`maxloops` だけ）。

| 関数 | 仕様 | 強さ |
|---|---|---|
| `Curl_conn_recv` | 任意の結果コードと、任意の `gotbytes` を返す。**ただし結果が CURLE_OK なら `gotbytes` は 0 でない** | **強い**（下の「道具の限界」） |
| `curlx_dyn_len`・`curlx_dyn_ptr` | 受信バッファの長さ・先頭を返す | dynbuf.c の意味 |
| `curlx_dyn_tail(s, t)`・`curlx_dyn_reset` | 長さを `t` にする（`t` が長さ以下のとき）・0 にする | dynbuf.c の意味 |
| `curlx_dyn_addn` | 任意の結果コードを返し、受信バッファを任意の長さにする | 弱い |
| `memchr(p, c, k)` | NULL か、`p` から `k` バイト未満の位置を返す | 標準ライブラリの意味 |
| `Curl_failf`（引数2つの呼び出し）・`Curl_debug` | 何も返さず、メモリの形を保つ | 弱い |
| `Curl_client_write`・`pp->endofresp` | 任意の値を返し、メモリの形を保つ | 弱い |

受信バッファは抽象した述語 `DB n p`（長さ `n`、先頭 `p`）にして全称で量化し、性質3つ（先頭はポインタ、長さは 2^64 未満、
先頭から `n` バイト未満の位置は有効なポインタ）だけを仮定した。

**道具の限界（P1 を弱めたところ）**

- `if(!gotbytes) { failf(data, "...%d", SOCKERRNO); ... }` の `failf` は可変長引数で、宣言にない3つ目の引数の型が
  呼び出しの型の並びに入らない（CompCert の `C2C.ml` は宣言の型を使う）。Clight の `EvalExprlist` は引数と型の数が
  合わないと成り立たないので、意味論の上でこの呼び出しから先へ進めない（Coq 版の Clight でも同じ）
- そのため `Curl_conn_recv` の仕様で 0 バイトの経路を除いた。curl の `Curl_conn_recv` は OK のとき 0 バイトを返しうるので、
  P1 はその入力について何も言っていない
- **関数の入口は含めない**。P1 は、局所変数 `gotbytes`・`buffer` を確保したあとの本体の三つ組である

**PROTOCOL §4 からの逸脱**

- 無し（構造体の削減とマクロの展開は §4 で許した範囲。errno は glibc の定義 `*__errno_location()` にした。`case1/prelude.h` に記録）

### Case 3（`lib/tftp.c` `tftp_tx`・`tftp_receive_packet`。参考として、判定のあとに試した）

ファイル: `case3/`（翻訳単位を作るもの）、`lean/Case3*.lean`（証明）。

**結果: 成功**（P1・P0 とも成立）。判定のあとに足した件なので、全体の判定（支持）は変わらない。

**P1 の述べ方**

- 脆弱性は転送の向きの取り違え（ダウンロード中に送信用の読み出し、アップロード中に受信データの書き出しが起きる）
- `tftp.c` で `Curl_client_read`（送信するデータを読む）を呼ぶのは `tftp_tx` だけ、`Curl_client_write`（受信したデータを書く）を
  呼ぶのは `tftp_receive_packet` だけ（grep で確認。修正後 436行・1092行、修正前 433行・1083行）。
  よって「向きを取り違えない」は、この2関数の性質に分かれる
- 三つ組は全正当性で、「ある関数を呼ばない」を直接述べる手段が無い。そこで「その関数について何も仮定せずに、決まった値を返す」で述べた。
  仮定していない関数を呼ぶ経路は、仕様が無いので証明が通らない

**示したこと**

- `tx_after_illegal`（`lean/Case3TxAfter.lean`）: 修正後の `tftp_tx` は、`upload` ビットが 0（ダウンロード中）なら、
  どのイベントでも `CURLE_TFTP_ILLEGAL`（71）を返す。**呼ばれる側の関数の仮定は0**（`ge` は composite 環境が一致することだけ仮定）。
  局所変数3つ（`cb`・`buffer`・`eos`）の確保から解放までを含む、関数全体の `SatisfiesAt`
- `recv_after_illegal`（`lean/Case3RecvAfter.lean`）: 修正後の `tftp_receive_packet` は、`upload` ビットが 1（アップロード中）、
  受け取ったパケットのイベントが 3（DATA）、受信バイト数が 4 以上なら、71 か `CURLE_RECV_ERROR`（56。送信元アドレスが固定したものと違うとき）を返す。
  **`Curl_client_write` の仮定は無い**。送信元アドレスの固定の分岐（`fromlen` が 0／固定済みで長さ違い／`memcmp` が 0 でない／一致／未固定）はすべての枝を示した
- `tx_before_reads`（`lean/Case3TxBefore.lean`、**P0**）: 修正前の `tftp_tx` は、OACK のイベント（6）で呼ばれると、
  `Curl_client_read` の戻り値 `r`（0 でない任意の値）をそのまま返す。修正前の関数は `upload` ビットを読まないので、
  ダウンロード中を含む。戻り値が `Curl_client_read` の仕様だけで決まる任意の `r` なので、`Curl_client_read` を呼んでいる。
  修正後の同じ呼び出し（ダウンロード中）は、仮定なしで 71 を返す（`tx_after_illegal`）
  - 通る経路: `block = 1`、`retries = 0`、`setpacketevent`・`setpacketblock`、`block > 1` が偽、`sbytes = 0`、
    `bufptr` の計算、ループの1回目で `Curl_client_read`、`if(result) return result;`
  - 仮定した仕様3つ（`ExtB`）: `setpacketevent`・`setpacketblock` はメモリの形を保つ、`Curl_client_read` は `r` を返しメモリの形を保つ。
    値を追うセル（`state` の6つのフィールド）と局所変数のほかは、任意の述語 `R`（`data` の中身や送信バッファ）で、呼ばれる側はその中を書き換えてよい
  - P0 は具体的なメモリの証拠（Case 5 の `mW` のようなもの）を作らず、事前条件を満たすすべてのメモリについて述べた。
    事前条件はセル6つと任意の `R` なので、満たすメモリは明らかに存在する
- `tftp_send_first` は扱っていない。PROTOCOL §3 の対象に入っているが、`Curl_client_read`・`Curl_client_write` を呼ばないので、上の述べ方の P1 には要らない

**外部関数の仕様（`tftp_receive_packet` の定理の仮定 `ExtR`）**

どの仕様も、メモリの形（受信バッファ・アドレス・`fromlen` などを所有する述語 `W`）を保つことだけを述べる。
送信・受信バッファは中身を問わない領域として所有させ、書き込みを許した。

| 関数 | 仕様 | 強さ |
|---|---|---|
| `recvfrom` | 任意の値 `n` を返し（定理は `n` について全称）、`fromlen` を任意の値にする | 弱い |
| `memcmp` | 任意の値 `rc` を返す（全称） | 弱い |
| `memcpy`・`Curl_failf` | メモリの形を保つ | 弱い |
| `getrpacketevent` | 3 を返す | **定理の場合分け**（DATA を受けた経路だけを述べる） |

ほかに、`failf` の書式の文字列リテラル `___stringlit_19` のシンボルが `ge` にあることを仮定した。

**確認したこと**

- `sorry`・`admit`・`native_decide`・`bv_decide`・`axiom` の宣言は無い（grep で確認）
- `#print axioms`: `tx_after_illegal`・`recv_after_illegal`・`tx_before_reads` は Lean の標準の3つと Certora/clean の外部関数の公理2つだけ
- 証明の行数は 1,639 行（生成物の `GenCase3*.lean` を除く。P0 の `Case3TxBefore.lean` は 393 行）
- `tx_body_before` は `maxHeartbeats` を 4000000 にした
- `lake build` の27回（P1 20回・P0 7回）のうち2回は、`#print axioms` の出力を見るためにキャッシュから記録を出し直しただけのもの、
  1回は編集のスクリプトが途中で失敗し、前と同じ内容を回したもの（どれも数には入れた）。
  ほかに、`blocksOfEnv` の並びを確かめるための `lake env lean` を2回使った（`build-log.tsv` に `case3-probe` として記録）
- `recv_after_illegal` の仮定 `hn0`（受信バイト数が 0 以上）は `hn4`（4 以上）から導けるので冗長。BitVec の符号付き比較の証明を省いて仮定として置いた

**P0 の経路の選び方**

- 最初は ACK（4）の経路を考えたが、ブロック番号の照合（`getrpacketblock`）と `time` を通る。OACK（6）の経路は `block` を 1 にするだけで
  `Curl_client_read` に達し、呼ぶ外部関数が少ない。どちらも修正前は `upload` を見ないので、向きの取り違えの証拠としては同じ
- 10-23 00:40 頃、P0 に入る途中で一度作業を止め、TK の了承を得て 04:35 から再開した。時間はその間を含めていない

**PROTOCOL §4 からの逸脱**

- `case3/epilogue.h`: CompCert は参照されない `static` 関数を変換時に消すので、対象の関数を参照するだけの大域変数を置いた。
  関数の宣言と本体には触れていない。Case 5・2 と同じ逸脱
- ほかは §4 で許した範囲（構造体の削減、マクロの展開、呼ばれる `static` 関数の `extern` 化）。`case3/prelude.h` に記録

## 全体の判定

**支持**（PROTOCOL §6: 成功が3件以上）。

- 試した3件（Case 5・4・2）は3件とも成功した。判定のあとで、参考として Case 1（不成功: P1 は成立、P0 は不成立）と Case 3（成功）を試した
- §6 の表は成功した件数で決まり、成功が3件に達した時点で、残り2件の結果によらず「支持」になる。
  5件全体での成功は4件（Case 1 だけが不成功）
- §7 に従い、決定記録 0002 の前提（C の意味論との接続ができる）は保たれる。プロダクト用のリポジトリを分ける条件の1つ目がそろう

### 読み方の注意（3件に共通）

- **外部関数は仕様を仮定している**。どの件でも、呼ばれる側の関数の振る舞いは定理の仮定で与えた。
  Case 4 は gtls.c の検査が正しいこと（強い仕様）、Case 2 は接続プールの走査が同じ `match` で照合関数を呼ぶこと
  （つなぎ目の前提）に依存する
- **構造体のレイアウトは減らしたもの**（§4 で許した変更）。フィールドの位置は実物の curl と違う
- **「仕様どおりに終わる実行がある」の形**（Certora/clean の三つ組は全正当性）。決定性による「すべての実行」への持ち上げはしていない
- **書き手と証明する者が同じ**（Claude）。性質の述べ方（H5 のモデルと同じ値を返す、という形）も Claude が選んだ
- **副産物: H5 のモデルの忠実さ**。3件とも、C の関数が H5 で Claude が書き起こしたモデルと同じ値を返すことを示せた。
  H5 の「読み方の注意」の「モデルの忠実さは人のレビューを受けていない」に対する、この3件についての機械での確認になる
- **時間**: 道具の構築は約10分。3件の証明は合計で約1時間30分（16:12〜17:37）。上限（1件4時間）に対して大きく余った。
  ただし証明の行数は Case 2 が 2,598 行で、Case 5（1,614 行）・Case 4（901 行）より大きい（いずれも生成物の Gen*.lean を除く）。手間は関数の大きさとともに増える

