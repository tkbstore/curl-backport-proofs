# 生成した証明の後処理: 名前付きの中間条件 ?Q を使う refine を apply に替え、続く case を箇条書きにする
import re, sys
lines = sys.stdin.read().split("\n")
out = []
pending = []  # stack of case names to convert
i = 0
conv = set()
for l in lines:
    m = re.match(r"^(\s*)(?:· )?refine triple_seq(_fwd)? ge _ _ _ \?Q\w+ _ _ _ \?(\w+) \?(\w+)$", l)
    if m:
        conv.add(m.group(3)); conv.add(m.group(4))
res = []
k = 0
def sub(l):
    l = re.sub(r"refine triple_seq_fwd ge _ _ _ \?Q\w+ _ _ _ \?\w+ \?\w+$", "apply Sep.triple_seq_fwd", l)
    return re.sub(r"refine triple_seq ge _ _ _ \?Q\w+ _ _ _ \?\w+ \?\w+$", "apply Sep.triple_seq", l)
while k < len(lines):
    l = lines[k]
    l2 = sub(l)
    m = re.match(r"^(\s*)case (\w+) =>$", l2)
    if m and m.group(2) in conv:
        ind = m.group(1)
        nxt = sub(lines[k + 1])
        res.append(ind + "· " + nxt.strip())
        k += 2
        continue
    res.append(l2)
    k += 1
print("\n".join(res))
