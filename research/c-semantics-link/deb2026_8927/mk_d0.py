import re
src=open('Deb2026_8927D1.lean').read()
body=src[src.index("namespace Deb2026_8927.D1"):]
i=body.index("      refine triple_seq_fwd ge _ _ _\n        (LocalSt emptyEnv [(_t'15")
j=body.index("      case after =>\n")
k=body.index("    -- if(socksproxy) …: NULL", j)
after=body[j+len("      case after =>\n"):k]
after='\n'.join(l[2:] if l.startswith('  ') else l for l in after.split('\n'))
body=body[:i]+after+body[k:]
i=body.index("def digestSpec"); j=body.index("theorem entry_wf")
body=body[:i]+body[j:]
body=body.replace("D1","D0").replace("Deb2026_8927_d1","Deb2026_8927_d0").replace("cellsD1","cellsD0")
m={55: 49, 53: 47, 54: 48, 51: 45, 52: 46, 50: 44, 48: 42, 49: 43, 47: 41, 46: 40, 43: 37, 44: 38, 45: 39, 40: 34, 41: 35, 42: 36, 19: 16, 39: 33, 17: 14, 30: 27, 31: 28, 32: 29, 33: 30, 34: 31, 35: 32, 18: 15, 24: 21, 25: 22, 26: 23, 29: 26, 28: 25, 27: 24, 22: 19, 20: 17, 23: 20, 21: 18}
body=re.sub(r"_t'(\d+)\b", lambda mm: "_t'%d"%m.get(int(mm.group(1)),int(mm.group(1))), body)
sh=lambda n: n-1 if n>=4 else n
body=re.sub(r"\(ldc (\d+) ", lambda mm: "(ldc %d "%sh(int(mm.group(1))), body)
body=re.sub(r"mem_idx (\d+) rfl", lambda mm: "mem_idx %d rfl"%sh(int(mm.group(1))), body)
body=body.replace("sWD c same q","sWD c true vnull").replace("sFinD c same q","sFinD c true vnull")
body=body.replace("theorem off_envproxy : fieldOffset prog.prog_comp_env _envproxy (coOf _UrlState).co_members = .OK (0, .Full) := by decide\n","")
body=body.replace("_proxydigest (coOf _UrlState).co_members = .OK (16, .Full)","_proxydigest (coOf _UrlState).co_members = .OK (8, .Full)")
body=body.replace("def helperSpecA (c : Ctx) (same : Bool) (q : Val) : FunSpec where","def helperSpecB (c : Ctx) : FunSpec where")
body=body.replace("(helperSpecA c same q)","(helperSpecB c)")
body=body.replace("theorem helper_after (ge : CGenv) (c : Ctx) (same : Bool) (q : Val)","theorem helper_before (ge : CGenv) (c : Ctx)")
for pat in [r"    \(henv : IsPtr c\.envV\) \(hq : IsPtr q\)\n",
            r"    \(hsCmp[^\n]*\n", r"    \(hsDg[^\n]*\n", r"    \(hsDup[^\n]*\n",
            r"    \(htyCmp[^\n]*\n", r"    \(htyDg[^\n]*\n", r"    \(htyDup[^\n]*\n",
            r"    \(hCmp : [^\n]*\n[^\n]*\n", r"    \(hDg : [^\n]*\n", r"    \(hDup : [^\n]*\n[^\n]*\n",
            r"  have henvl[^\n]*\n"]:
    body,n=re.subn(pat,"",body); print(pat,n)
body=body.replace("(bNo bDet bFree bParse bCmp bDg bDup : Block)","(bNo bDet bFree bParse : Block)")
body=body.replace("(fdNo fdDet fdFree fdParse fdCmp fdDg fdDup : FunDef)","(fdNo fdDet fdFree fdParse : FunDef)")
body=body.replace("    (hfParse : FuncPtr ge bParse fdParse) (hfCmp : FuncPtr ge bCmp fdCmp)\n    (hfDg : FuncPtr ge bDg fdDg) (hfDup : FuncPtr ge bDup fdDup)\n","    (hfParse : FuncPtr ge bParse fdParse)\n")
header='''/-
CVE-2026-8927: curl 8.14.1（D0、Debian のパッチを当てる前）の `create_conn_helper_init_proxy`。
`Deb2026_8927D1.lean` の証明から、パッチで足された検査の段を除き、一時変数の番号と
`struct UrlState` のレイアウト（`envproxy` が無い）を写した。

場面 S の上で、関数は CURLE_OK を返し、`proxydigest.nonce` は元のまま（`helper_before`）。
-/
import Deb2026_8927GenD0
import Deb2026_8927D1
import Deb2026_8927U0
open CC CC.Sep CC.HProp
open Deb2026_8927_d0
open Case4C (call_none IsPtr loadResult_ptr cast_ptr)

set_option maxRecDepth 20000

namespace Deb2026_8927

abbrev cellsD0 (c : Ctx) (s : St) : List Cell :=
  cWD c s :: cHraw c s :: cHptD c s :: cNonce0 c s :: fixD c

end Deb2026_8927

'''
open('Deb2026_8927D0.lean','w').write(header+body)
