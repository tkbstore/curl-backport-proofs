# 件: $patch（$branch）

あなたは1件の証明を、人に何も聞かずに最後まで行う。途中で質問しない。判断に迷ったら手順書の規則に従い、規則が無ければ記録に書いて先へ進む。

## 対象

- パッチ: `$patch`（salsa debian/curl `$debian_commit`、sha256 `$patch_sha256`）
- 上流の修正: 修正後 U1 `$upstream_fixed`、修正前 U0 `$upstream_parent`（`auto/detect.py` が `curl.se/docs/$cve.json` から決めた。特定し直さない）
- 対象のファイル: `$target_file`。Debian の版 `$debian_version`（素の版 `$base_tag`）
- 4つの C ファイルと、変わった関数の切り出しは `$input_dir/` にある（`auto/build.py` の出力。`manifest.json` に sha256 と関数の一覧）。
  D1 は series でこのパッチまで、D0 はこのパッチの直前までを当てたもの。作り直さず、これを使う

## 名前（変えない）

- 件の記録: `$case_md` と `$case_json`
- Lean のモジュールと名前空間の頭: `$prefix`（例 `${prefix}After`・`${prefix}C`）。ファイルは `research/c-semantics-link/lean/` に置き、`lakefile.toml` の roots に足す
- 切り出しなどの道具: `$tool_dir/`
- ビルド: `research/c-semantics-link/lean/build.sh $case_id`。`lake build` を直接打たない（回数はこのラッパーだけが数える）

## 上限

1件 $hours 時間・`build.sh` $builds 回。回数は `build.sh` が止める（`limit reached` が出たら、それ以上は走らない）。時間を過ぎるとこのプロセスごと止められる。
止められる前に記録が残るよう、性質を書いた時点・各スロットが通った時点でコミットする。

## 手順（`research/backport-proof-debian/PROTOCOL-auto.md` §3.5〜§4 が優先）

1. 読む: `PROTOCOL-auto.md`、`PROTOCOL-trixie-batch.md`（手順と許す変更）、`RESULTS-trixie-batch.md`、
   似た件の実例（`cases/CVE-*.md` と `research/c-semantics-link/lean/Deb*.lean`。同じ CVE の trixie の件があれば、まずそれ）
2. `$case_md` に、対象の関数・構成・P1/P0 の文（日本語と Lean の定理の形）・仮定する外部仕様を書き、**証明の前にコミット**する。
   述べられる性質が無いと判断したら、判定「証明できず」と理由を書いて終える
3. `$input_dir/` の C から翻訳単位を作る（関数の本体は原文から機械で切り出す。前置きの構造体の削減とマクロの展開は書いてよい）。
   clightgen: `~/Documents/GitHub/_vendor/certora-clean/clightgen -lean -normalize <file.c>`（出力を `lean/` に `Gen${prefix}*.lean` として移す）
4. U1・U0 を証明し、D1・D0 に写す
5. 確認: `python3 research/backport-proof-debian/auto/check.py $case_json` が「合格」になること
6. `$case_md` の「結果」節に、成否（U1/U0/D1/D0）・時間（開始と終了の時刻、`date` の出力）・build の回数・外部仕様の数・
   U から D へ書き換えた行数・性質の変更の有無と理由を書く。`$case_json` を PROTOCOL-auto §3.7 の形で書く
   （`verdict` は「同じ性質」か「証明できず」。「証明できず」なら `theorems` には成立したスロットの定理だけを入れる）。両方をコミットする

## 守ること

- この worktree の外は書き換えない。git switch しない。push しない
- git に無いファイルの削除は hook に止められる。消さずに残し、`$case_md` の最後に一覧を書く
- 新しいファイルは作った時点で git add。コミットの末尾に `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`
- 数字はすべて自分で実行した出力から取る。文体は既存の `cases/*.md` に合わせる
