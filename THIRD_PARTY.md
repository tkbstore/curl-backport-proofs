# Third-party material

## curl

The C translation units under `research/c-semantics-link/*/` (`*.c`, and the
`debian.patch` files) contain functions cut out of curl's source, before and
after each fix, and Debian's patches to curl. They are under curl's license:

```
COPYRIGHT AND PERMISSION NOTICE

Copyright (c) 1996 - 2026, Daniel Stenberg, <daniel@haxx.se>, and many
contributors, see the THANKS file.

All rights reserved.

Permission to use, copy, modify, and distribute this software for any purpose
with or without fee is hereby granted, provided that the above copyright
notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT OF THIRD PARTY RIGHTS. IN
NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE
OR OTHER DEALINGS IN THE SOFTWARE.

Except as contained in this notice, the name of a copyright holder shall not
be used in advertising or otherwise to promote the sale, use or other dealings
in this Software without prior written authorization of the copyright holder.
```

Each `extract.py` fetches the source from curl's repository and Debian's patch
from salsa.debian.org at a fixed commit, and checks the patch's sha256.

## Certora/clean (CompCert)

The `research/c-semantics-link/lean/Gen*.lean` files were produced by
`clightgen -lean -normalize` from
[Certora/clean](https://github.com/Certora/clean) at commit
`123f7f7767e215aceb4821f0d044336d78103ade`, a derivative of the CompCert
verified compiler.

This repository does not include Certora/clean. Lake fetches its `export/`
directory (the Lean semantics `CCLib` and `Clightdefs`), which is
dual-licensed under the INRIA Non-Commercial License Agreement and the GNU
LGPL 2.1 or later. `clightgen` itself, needed only to regenerate the `Gen*`
files, includes parts that are under the INRIA Non-Commercial License only
(evaluation, research, educational and personal use). See Certora/clean's
`LICENSE`.
