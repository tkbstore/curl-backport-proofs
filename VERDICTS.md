# Verdicts

Generated from the case records by `publish.py`; do not edit by hand.
Verdict words are the ones of PROTOCOL-auto.md §3.6 (Japanese):
同じ性質 = the backport has the property of the upstream fix (U1, U0, D1, D0 all proved, §4 checks passed);
証明できず = not proved within the limits; 上流と仕組みが違う = fixed differently from upstream;
対象外（大きさ） = out of scope by size; 上流の修正を特定できない = upstream fix not identified;
C の変更が無い = no C change; パッチが当たらない = the series does not apply.

Read-back = a second AI agent, not told whether the proof went through, read the stated
properties against the advisory (PROTOCOL-auto.md §3.9). 指摘なし = no issue found, 指摘あり = issues
(listed), — = not read back (the first batch, and verdicts decided by rule). It never changes the verdict.

P0 on fixed = P0, restated on the fixed function, proved in Lean (PROTOCOL-auto.md §3.10).
成立 = it holds there too, so P0 does not tell the code before the fix from the code after it
(the theorem is named); 示せず = tried and not proved, which is not a proof that P0 tells them apart;
— = not tried. Machine-checked like the other theorems (§4). It does not change the verdict.

| Release | Patch | Verdict | Scope | Assumed external specs | Read-back | P0 on fixed | Notes |
|---|---|---|---|---|---|---|---|
| bookworm | `CVE-2023-27533.patch` | 証明できず | 場面を絞った（ユーザー名の側だけ。オプションの引数の側は可変長引数の sscanf のため扱わない） | U1 1 / U0 2 / D1 1 / D0 2 | 指摘なし | — | [CVE-2023-27533.md](research/backport-proof-debian/cases/bookworm/CVE-2023-27533.md) |
| bookworm | `CVE-2023-27534.patch` | 対象外（大きさ） | — | — | — | — | `lib/curl_path.c` 75 lines |
| bookworm | `CVE-2023-27535.patch` | 対象外（大きさ） | — | — | — | — | `lib/ftp.c`, `lib/setopt.c`, `lib/url.c` 47 lines |
| bookworm | `CVE-2023-27537.patch` | C の変更が無い | — | — | — | — | 0 lines |
| bookworm | `CVE-2023-28321.patch` | 対象外（大きさ） | — | — | — | — | `lib/vtls/hostcheck.c` 50 lines |
| bookworm | `CVE-2023-28322.patch` | 対象外（大きさ） | — | — | — | — | `lib/curl_rtmp.c`, `lib/file.c`, `lib/ftp.c`, `lib/http.c`, `lib/imap.c`, `lib/rtsp.c`, `lib/setopt.c`, `lib/smb.c`, `lib/smtp.c`, `lib/tftp.c`, `lib/transfer.c`, `lib/vssh/libssh.c`, `lib/vssh/libssh2.c`, `lib/vssh/wolfssh.c` 72 lines |
| bookworm | `CVE-2023-32001.patch` | 上流の修正を特定できない | — | — | — | — | `lib/fopen.c` 12 lines |
| bookworm | `CVE-2023-38039.patch` | 対象外（大きさ） | — | — | — | — | `lib/c-hyper.c`, `lib/http.c`, `lib/http_proxy.c`, `lib/pingpong.c` 54 lines |
| bookworm | `CVE-2023-38546.patch` | 対象外（大きさ） | — | — | — | — | `lib/cookie.c`, `lib/easy.c` 17 lines |
| bookworm | `CVE-2023-46219.patch` | 対象外（大きさ） | — | — | — | — | `lib/fopen.c` 65 lines |
| bookworm | `CVE-2024-11053.patch` | 対象外（大きさ） | — | — | — | — | `lib/netrc.c`, `lib/url.c` 201 lines |
| bookworm | `CVE-2024-8096.patch` | 対象外（大きさ） | — | — | — | — | `lib/vtls/gtls.c` 146 lines |
| bookworm | `CVE-2025-14819.patch` | 同じ性質 | すべての入力 | U1 2 / U0 1 / D1 2 / D0 1 | 指摘あり (p0_states_bug) | — | [CVE-2025-14819.md](research/backport-proof-debian/cases/bookworm/CVE-2025-14819.md) |
| bookworm | `CVE-2026-5773.patch` | 上流と仕組みが違う | — | — | — | — | up_in_deb 0.00 < 0.5; `lib/smb.c` 6 lines |
| trixie | `CVE-2025-10148.patch` | 同じ性質 | 場面を絞った（payload_len が負でない、payload_remain が正でない、を前提に置いた） | U1 6 / U0 5 / D1 6 / D0 5 | 指摘なし | — | [CVE-2025-10148.md](research/backport-proof-debian/cases/CVE-2025-10148.md) |
| trixie | `CVE-2025-13034.patch` | 同じ性質 | すべての入力 | U1 2 / U0 2 / D1 2 / D0 2 | 指摘なし | 示せず | [CVE-2025-13034.md](research/backport-proof-debian/cases/trixie/CVE-2025-13034.md) |
| trixie | `CVE-2025-14524.patch` | 同じ性質 | 場面を絞った（Curl_sasl_start だけ。Debian が直した Curl_sasl_continue は証明していない。P0 に sasl_ir=1 などの前提を足した） | U1 3 / U0 5 / D1 3 / D0 4 | 指摘なし | — | [CVE-2025-14524.md](research/backport-proof-debian/cases/CVE-2025-14524.md) |
| trixie | `CVE-2025-14819.patch` | 同じ性質 | すべての入力 | U1 2 / U0 1 / D1 2 / D0 1 | 指摘なし | 成立 (`Deb2025_14819X.P0_on_after`, `Deb2025_14819X.P0_on_debian_after`) | [CVE-2025-14819.md](research/backport-proof-debian/cases/CVE-2025-14819.md) |
| trixie | `CVE-2026-1965_1.patch` | 対象外（大きさ） | — | — | — | — | `lib/url.c` 87 lines |
| trixie | `CVE-2026-1965_2.patch` | 同じ性質 | 場面を絞った（_2 が直した規則だけ。CVE の本体の資格情報の照合は _1 にあり対象外） | U1 1 / U0 1 / D1 1 / D0 1 | 指摘あり (p1_states_fix, p0_states_bug) | — | [CVE-2026-1965.md](research/backport-proof-debian/cases/CVE-2026-1965.md) |
| trixie | `CVE-2026-3783.patch` | 同じ性質 | すべての入力 | U1 1 / U0 3 / D1 1 / D0 3 | 指摘なし | — | [CVE-2026-3783.md](research/backport-proof-debian/cases/CVE-2026-3783.md) |
| trixie | `CVE-2026-3784.patch` | 同じ性質 | すべての入力 | U1 2 / U0 1 / D1 2 / D0 1 | 指摘なし | — | [CVE-2026-3784.md](research/backport-proof-debian/cases/CVE-2026-3784.md) |
| trixie | `CVE-2026-3805.patch` | 同じ性質 | すべての入力 | U1 5 / U0 4 / D1 5 / D0 4 | 指摘なし | — | [CVE-2026-3805.md](research/backport-proof-debian/cases/CVE-2026-3805.md) |
| trixie | `CVE-2026-4873.patch` | 同じ性質 | すべての入力 | U1 1 / U0 1 / D1 1 / D0 1 | 指摘なし | — | [CVE-2026-4873.md](research/backport-proof-debian/cases/CVE-2026-4873.md) |
| trixie | `CVE-2026-5545.patch` | 同じ性質 | すべての入力 | U1 1 / U0 1 / D1 1 / D0 1 | 指摘なし | — | [CVE-2026-5545.md](research/backport-proof-debian/cases/CVE-2026-5545.md) |
| trixie | `CVE-2026-5773.patch` | 上流と仕組みが違う | — | — | — | — | [CVE-2026-5773.md](research/backport-proof-debian/cases/CVE-2026-5773.md) |
| trixie | `CVE-2026-6253.patch` | 対象外（大きさ） | — | — | — | — | `lib/http.c`, `lib/transfer.c` 63 lines |
| trixie | `CVE-2026-6276.patch` | 対象外（大きさ） | — | — | — | — | `lib/http.c`, `lib/request.c`, `lib/url.c` 19 lines |
| trixie | `CVE-2026-6429.patch` | 対象外（大きさ） | — | — | — | — | `lib/http.c` 77 lines |
| trixie | `CVE-2026-7168.patch` | 同じ性質 | 場面を絞った（option が CURLOPT_PROXY で、前と新しいプロキシ文字列がどちらも NULL でない） | U1 4 / U0 1 / D1 4 / D0 1 | 指摘なし | — | [CVE-2026-7168.md](research/backport-proof-debian/cases/CVE-2026-7168.md) |
| trixie | `CVE-2026-8286.patch` | 同じ性質 | すべての入力 | U1 2 / U0 2 / D1 2 / D0 2 | 指摘なし | — | [CVE-2026-8286.md](research/backport-proof-debian/cases/CVE-2026-8286.md) |
| trixie | `CVE-2026-8924.patch` | 同じ性質 | 場面を絞った（dlen・clen を2以上にし、P0 では clen を256未満にした） | U1 8 / U0 8 / D1 8 / D0 8 | 指摘あり (p0_states_bug) | — | [CVE-2026-8924.md](research/backport-proof-debian/cases/CVE-2026-8924.md) |
| trixie | `CVE-2026-8927.patch` | 同じ性質 | 場面を絞った（環境変数から HTTP プロキシを読む経路、場面 S） | U1 7 / U0 4 / D1 7 / D0 4 | 指摘なし | — | [CVE-2026-8927.md](research/backport-proof-debian/cases/CVE-2026-8927.md) |
