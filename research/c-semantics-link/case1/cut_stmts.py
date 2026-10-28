# 使い方: python3 case1/cut_stmts.py lean/GenCase1After.lean lean/Case1Stmts.lean
"""GenCase1{After,Before}.lean の Curl_pp_readresp の本体から、ループの文を括弧の対応で切り出す。"""
import sys, re
from pathlib import Path

def match_paren(s, i):
    assert s[i] == '('
    d = 0
    for j in range(i, len(s)):
        if s[j] == '(':
            d += 1
        elif s[j] == ')':
            d -= 1
            if d == 0:
                return j
    raise SystemExit("unbalanced")

def loops(body):
    out = []
    for m in re.finditer(r'\(Stmt\.Sloop', body):
        i = m.start()
        out.append(body[i:match_paren(body, i) + 1])
    return out

src = Path(sys.argv[1]).read_text()
start = src.index("def f_Curl_pp_readresp")
body = src[src.index("fn_body :=", start):src.index("\n}\n", start)]
ls = loops(body)
for k, l in enumerate(ls):
    print(k, len(l), l[:60].replace("\n", " "))

def split_loop(l):
    inner = l[len("(Stmt.Sloop"):-1].strip()
    j = match_paren(inner, 0)
    s1 = inner[:j + 1]
    s2 = inner[j + 1:].strip()
    return s1, s2

if len(sys.argv) > 2:
    s1, s2 = split_loop(ls[1])
    assert s2 == "Stmt.Sskip", s2
    o1, o2 = split_loop(ls[0])
    # 外側の本体の中の内側のループを名前で置き換える
    assert o1.count(ls[1]) == 1
    o1n = o1.replace(ls[1], "(Stmt.Sloop innerBody Stmt.Sskip)")
    # 内側の本体を3つに分ける（見出しの文字列から始まる文を、括弧の対応で切り出す）
    def piece(body, marker):
        i = body.index(marker)
        assert body.count(marker) == 1, marker
        return body[i:match_paren(body, i) + 1]
    tailS = piece(s1, "(Stmt.Ssequence\n" + " " * 42 + "(Stmt.Scall (some _t'15)")
    eorS = piece(s1, "(Stmt.Sifthenelse (Expr.Etempvar _t'13 tbool)")
    nlS = piece(s1, "(Stmt.Sifthenelse (Expr.Etempvar _nl (tptr tschar))")
    nlS2 = nlS.replace(tailS, "tailStmt").replace(eorS, "eorIf")
    s1 = s1.replace(nlS, "nlIf")
    # 外側の本体を分ける
    def piece_back(body, marker, head):
        """`marker` を含む文を、その直前の `head` から括弧の対応で切り出す。"""
        assert body.count(marker) == 1, marker
        i = body.rindex(head, 0, body.index(marker))
        return body[i:match_paren(body, i) + 1]
    nfinS = piece(o1n, "(Stmt.Sifthenelse (Expr.Etempvar _t'27 tulong)")
    ovfS = piece_back(o1n, "(Expr.Etempvar _t'19 tulong) tint)", "(Stmt.Sifthenelse")
    # ovfIf の読む部分（pingpong_read の呼び出しから最後まで）と、その中の3つの文
    i1 = ovfS.rindex("(Stmt.Ssequence", 0, ovfS.index("(Stmt.Scall (some _t'3)"))
    i0 = ovfS.rindex("(Stmt.Ssequence", 0, i1)
    readS = ovfS[i0:match_paren(ovfS, i0) + 1]
    assert "Stmt.Sset _t'20" in readS
    gotS = piece_back(readS, "(Stmt.Sset _t'25", "(Stmt.Ssequence")
    hbcS = piece_back(readS, "(Stmt.Sset _t'22", "(Stmt.Ssequence")
    nrS = piece_back(readS, "(Stmt.Sset _t'20", "(Stmt.Ssequence")
    readS2 = readS.replace(gotS, "gotChk").replace(hbcS, "hbcUpd").replace(nrS, "nrUpd")
    ovfS2 = ovfS.replace(readS, "readStmt")
    o1n = o1n.replace(nfinS, "nfinIf").replace(ovfS, "ovfIf")
    ovfS = ovfS2
    Path(sys.argv[2]).write_text(
        "/-\nCase 1: `Curl_pp_readresp`（修正後）の本体から切り出したループの文。\n"
        "cut.py が GenCase1After.lean から括弧の対応で機械的に切り出したもの。手で編集しない。\n"
        "使う側では、本体の該当部分と定義の上で一致する（`exact` が展開して照合する）。\n-/\n"
        "import GenCase1After\nopen CC\nopen Case1_after\n\nnamespace Case1C\n\n"
        f"def tailStmt : Stmt :=\n{tailS}\n\n"
        f"def eorIf : Stmt :=\n{eorS}\n\n"
        f"def nlIf : Stmt :=\n{nlS2}\n\n"
        f"def innerBody : Stmt :=\n{s1}\n\n"
        f"def nfinIf : Stmt :=\n{nfinS}\n\n"
        f"def gotChk : Stmt :=\n{gotS}\n\n"
        f"def hbcUpd : Stmt :=\n{hbcS}\n\n"
        f"def nrUpd : Stmt :=\n{nrS}\n\n"
        f"def readStmt : Stmt :=\n{readS2}\n\n"
        f"def ovfIf : Stmt :=\n{ovfS}\n\n"
        f"def outerBody : Stmt :=\n{o1n}\n\n"
        f"def outerCond : Stmt :=\n{o2}\n\nend Case1C\n")
