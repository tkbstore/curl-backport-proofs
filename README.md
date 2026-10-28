# Proofs that Debian's curl security backports keep the upstream fix

Debian trixie ships curl 8.14.1 and backports security fixes to it as patches
in `debian/patches/`. For 14 of those patches we stated, in Lean 4, the
property each upstream fix establishes, and proved it for four C functions:

| | Function | Property |
|---|---|---|
| **U1** | upstream, after the fix | P1: the vulnerability cannot happen |
| **U0** | upstream, before the fix | P0: an input exists where it happens |
| **D1** | curl 8.14.1 with Debian's patch applied | P1, stated the same way as for U1 |
| **D0** | curl 8.14.1 before Debian's patch | P0, stated the same way as for U0 |

D1 and D0 show that the backport behaves like the upstream fix for that
property: the bug is there before Debian's patch and gone after it.

The proofs use the Clight semantics and separation logic of
[Certora/clean](https://github.com/Certora/clean) (a Lean 4 port of CompCert's
Clight). The C functions were translated with `clightgen -lean -normalize`.

Patches: salsa.debian.org `debian/curl`, commit `c2a97b9ea5`
(`debian/trixie`, 8.14.1-2+deb13u6).

## Verdicts are published automatically

**[`VERDICTS.md`](VERDICTS.md)** (and `verdicts.json`) lists every CVE patch
seen so far on `debian/trixie` and `debian/bookworm`, with its verdict. It is
regenerated on every run and is the current list; the table below is the first
batch, written by hand.

A scheduled job watches salsa `debian/curl` for new or changed
`debian/patches/CVE-*.patch`. It decides by fixed rules which ones to attempt
(the upstream fix from `curl.se/docs/<CVE>.json`, one `.c` file, at most 40
changed lines, and how much of the upstream fix's added lines Debian's patch
contains), lets Claude state and prove the properties within 4 hours and 80
`lake build`s per patch, and accepts 「同じ性質」 (same property) only when
Lean builds, the axioms are the allowed ones and the theorems name Debian's
functions. Nobody reviews a verdict before it is pushed. The rules are in
`research/backport-proof-debian/PROTOCOL-auto.md` (Japanese); `state/` records
which patches were handled.

## Results of the first batch (trixie, by hand)

13 of 14 hold (all of U1, U0, D1 and D0). 1 is out of scope.

| CVE | File | Result | What is proved |
|---|---|---|---|
| CVE-2026-1965 (`_2` patch only) | `lib/url.c` | holds | The rule the `_2` patch fixes: a request that needs Negotiate does not immediately accept a connection that has not done Negotiate. The credential check itself is in `_1`, which was not attempted |
| CVE-2026-4873 | `lib/url.c` | holds | `url_match_ssl_use`: if TLS is required (`req_tls`) and neither the scheme nor the connection is TLS, the connection is not reused |
| CVE-2026-5545 | `lib/url.c` | holds | `url_match_auth_ntlm`: a connection with different credentials that has done Negotiate is not taken as a candidate for an NTLM request |
| CVE-2026-8286 | `lib/url.c` | holds | P1 is stated on two functions; `url_match_conn` itself is not proved |
| CVE-2026-8927 | `lib/url.c` | holds | One path only: an HTTP proxy read from the environment |
| CVE-2026-7168 | `lib/setopt.c` | holds | `CURLOPT_PROXY` with old and new proxy strings both non-NULL, in a build with FTP and other options disabled (not Debian's build configuration) |
| CVE-2026-3784 | `lib/url.c` | holds | All inputs of `proxy_info_matches`. That its result decides connection reuse is assumed |
| CVE-2026-3783 | `lib/http.c` | holds | `output_auth_headers`: when Bearer is picked and the host is not allowed to receive credentials, no Bearer header is output |
| CVE-2025-14524 | `lib/curl_sasl.c` | holds | `Curl_sasl_start` only. Debian's patch also changes `Curl_sasl_continue`, which is not covered. P0 gained a precondition after it was first written |
| CVE-2026-8924 | `lib/cookie.c` | holds | Domain lengths of at least 2; P0 additionally below 256 |
| CVE-2026-3805 | `lib/smb.c` | holds | On success, `share` and `req->path` point to separately owned blocks (the aliasing behind the use-after-free). The leak fix is not covered |
| CVE-2025-14819 | `lib/vtls/openssl.c` | holds | The cached X509 store is not reused when its recorded `no_partialchain` differs from the current setting. That the recorded value is correct is assumed |
| CVE-2025-10148 | `lib/ws.c` | holds | The mask sent is the one `Curl_rand` wrote. Assumes `payload_len >= 0` and `payload_remain <= 0`: the two `failf` calls on those branches are variadic and cannot be evaluated |
| CVE-2026-5773 | `lib/smb.c` | **out of scope** | Debian fixes it differently from upstream (`smb_connect` sets `connclose`; upstream changes the table in `lib/protocol.c`), so there is no theorem of the same form |

"Holds" means the stated properties hold. How much each property covers
differs between cases, as the last column shows. It does not mean that a fix
was proved correct in general. Each case's full statement, assumptions and
counts are in `research/backport-proof-debian/cases/<CVE>.md`.

For D0, the four `lib/url.c` cases use 8.14.1 with the earlier patches in
Debian's series applied, the state just before this patch, because some
patches do not apply to plain 8.14.1.

Checks:
- `#print axioms` on the 53 main theorems gives Lean's three standard axioms,
  plus Certora/clean's `CC.externalFunctionsSem` and `CC.inlineAssemblySem`
  on 41 of them.
- No `sorry`, `admit`, `native_decide`, `bv_decide` or `axiom` declarations.

## Limits

- The properties and the proofs were written by Claude (an AI model) and
  checked by Lean. From Debian, only the patches are used.
- Functions a proved function calls are given assumed specifications, kept
  weak where possible; each case file lists them.
- `clightgen`'s translation from C to Clight is trusted, not proved.
- Only small patches were attempted: one `.c` file and at most 40 changed
  lines. Four larger patches (CVE-2026-1965 `_1`, 6253, 6276, 6429) were
  excluded before starting.

## Build

Requires [elan](https://github.com/leanprover/elan). Lake fetches the Lean
toolchain (`v4.32.1`) and Certora/clean's `export/` directory.

```sh
cd research/c-semantics-link/lean
lake build
```

To print a theorem's axioms, write a file in that directory such as:

```lean
import Deb2026_4873
#print axioms Deb2026_4873C.P1_D
```

and run `lake env lean <file>`.

Regenerating the `Gen*.lean` files requires building `clightgen` from
Certora/clean and running each `research/c-semantics-link/*/extract.py`.

## Layout

| Path | Contents |
|---|---|
| `research/backport-proof-debian/PROTOCOL-trixie-batch.md` | The procedure, written before any proof was attempted |
| `research/backport-proof-debian/RESULTS-trixie-batch.md` | Summary of the 14 cases |
| `research/backport-proof-debian/PROTOCOL-auto.md` | The rules of the automated job |
| `research/backport-proof-debian/cases/` | One file per CVE: property, assumptions, result (`cases/<release>/` for the automated runs; `*.json` is the machine-readable record) |
| `research/c-semantics-link/deb<year>_<num>/` | `extract.py` and the four C translation units per case |
| `research/c-semantics-link/lean/` | Lean proofs (`Deb*.lean`) and generated Clight (`Gen*.lean`) |

The `case1`–`case5` directories, `Case*.lean` and the files without `Deb` in
their names come from an earlier experiment on upstream curl fixes. Several
`Deb*` proofs import their lemmas.

The documents are written in Japanese. The Lean files, the C files and this
README are the parts readable without it.

## License

MIT for the files written for this repository (`LICENSE`). Material from curl
and Debian keeps curl's license, and Certora/clean is not included
(`THIRD_PARTY.md`).
