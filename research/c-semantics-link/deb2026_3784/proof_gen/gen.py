#!/usr/bin/env python3
"""CVE-2026-3784 の4つの証明（Deb2026_3784{U1,U0,D1,D0}.lean）を書き出す。
関数の経路（修正後 6 本、修正前 4 本）ごとに同じ形の段を並べ、版ごとの差（レイアウト・一時変数の番号）を差し込む。
使い方: python3 gen.py <lean ディレクトリ>"""
import sys
from pathlib import Path

OUT = Path(sys.argv[1])
VERS = {
    "U1": ("Deb2026_3784GenU1", "Deb2026_3784_u1", True, ".Mint16unsigned", "Integers.Int.zero_ext 16 ", 8, 10, "上流の修正後（U1、curl 5f13a7645e）"),
    "U0": ("Deb2026_3784GenU0", "Deb2026_3784_u0", False, ".Mint16unsigned", "Integers.Int.zero_ext 16 ", 8, 10, "上流の修正前（U0、curl e47b6e657a）"),
    "D1": ("Deb2026_3784GenD1", "Deb2026_3784_d1", True, ".Mint32", "", 8, 12, "curl 8.14.1 に Debian の CVE-2026-3784.patch を当てたもの（D1）"),
    "D0": ("Deb2026_3784GenD0", "Deb2026_3784_d0", False, ".Mint32", "", 8, 12, "curl 8.14.1（D0）"),
}
TA = dict(ptd="_t'13", ptn="_t'14", pod="_t'15", pon="_t'16", c1="_t'4", nd="_t'11", nn="_t'12", se="_t'6", c2="_t'5",
          ud="_t'9", un="_t'10", ru="_t'1", c3="_t'2", pd="_t'7", pn="_t'8", rp="_t'3")
TB = dict(ptd="_t'6", ptn="_t'7", pod="_t'8", pon="_t'9", c1="_t'1", nd="_t'4", nn="_t'5", se="_t'3", c2="_t'2")
SEQ = "triple_seq_fwd ge _ _ _ _ _ _ _"
SETL = "triple_set_local_fwd ge _ _ emptyEnv _ _"
IFL = "triple_if_local ge _ _ emptyEnv _ _ _"
TS = lambda k: f"(ts [Val.loadResult Mptr c.{k}D, Val.loadResult Mptr c.{k}N])"
EQ = lambda a, b: f"(Integers.Int.eq {a} {b})"
Z = "Integers.Int.zero"


def load(tmp, val, lv, i, cell):
    return f"({SETL} {tmp} _ {val} (fun le m hp hT hH hag => eval_lv_load {lv} rfl (ldc3 {i} ({cell}))))"


def lv1(base, off):
    return f"(lv_f1 (tget3 (.Vptr c.{base}B c.{base}O)) (hcenv ▸ co_pi) (hcenv ▸ off_{off}))"


def lvname(base):
    return f"(lv_f2 (tget3 (.Vptr c.{base}B c.{base}O)) (hcenv ▸ co_pi) (hcenv ▸ off_host) (hcenv ▸ co_hn) (hcenv ▸ off_name))"


def args2(a, ha, b, hb):
    return (f"(fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 {a})) (cast_ptr {ha} _ _ m) "
            f"(EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 {b})) (cast_ptr {hb} _ _ m) EvalExprlist.nil))")


def ret(n, b, hyps):
    simp = "Bool.true_and, Bool.false_and, Bool.and_false, Bool.and_true, Bool.not_true, Bool.not_false"
    return (f"(triple_return_local ge _ _ _ _ _ _ (.Vint (Integers.Int.repr {n})) (Val.ofBool {b}) "
            f"(fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl) "
            f"(fun hp hH => ⟨by simp only [res, {hyps}, {simp}], hH⟩))")


def ifb(prefix, bbexpr, b, hb):
    """真偽の値 bbexpr の if を、仮定 hb（bbexpr が b であること）で片方に決める。"""
    return f"({'if_true_triple' if b else 'if_false_triple'} {hb} "


def path(after, T, pw, p):
    b1 = p[0]; b2 = p[1] if len(p) > 1 else None; b3 = p[2] if len(p) > 2 else None
    b4 = p[3] if len(p) > 3 else None; b5 = p[4] if len(p) > 4 else None
    hyps = ", ".join(f"hb{i+1}" for i in range(len(p)))
    ptd, ptn = "(Integers.Int.zero_ext 8 c.ptD)", "(Integers.Int.zero_ext 8 c.ptN)"
    pod, pon = f"({pw}c.portD)", f"({pw}c.portN)"
    L = []
    reachC = b1 and b2 and b3
    cret = reachC  # C の中で必ず return する
    if cret:
        L.append("refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?X (triple_vacuous ge _ _ _ _)")
    else:
        L.append(f"apply {SEQ} ?X")
    L.append("case X =>")
    L.append(f"  apply {SEQ} ?AB")
    L.append("  case AB =>")
    L.append(f"    apply {SEQ} ?A")
    L.append("    case A =>")
    L.append(f"      refine {SEQ} {load(T['ptd'], '(.Vint ' + ptd + ')', lv1('d', 'pt'), 0, 'cPtD lay c')} ?_")
    L.append(f"      refine {SEQ} {load(T['ptn'], '(.Vint ' + ptn + ')', lv1('n', 'pt'), 1, 'cPtN lay c')} ?_")
    if1g = (f"(fun le m hp hT _ _ => ⟨Val.ofBool {EQ(ptd, ptn)}, EvalExpr.Ebinop _ _ _ _ _ _ _ "
            f"(EvalExpr.Etempvar _ _ _ (tget3 (.Vint {ptd}))) (EvalExpr.Etempvar _ _ _ (tget3 (.Vint {ptn}))) rfl, "
            f"boolVal_ofBool _ _ m (.inl rfl)⟩)")
    if b1:
        c1set = (f"({SETL} {T['c1']} _ (Val.ofBool {EQ(pod, pon)}) (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ "
                 f"(EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (tget3 (.Vint {pod}))) "
                 f"(EvalExpr.Etempvar _ _ _ (tget3 (.Vint {pon}))) rfl) (Deb2026_7168.cast_ofBool_int_bool _ m)))")
        th = (f"({SEQ} {load(T['pod'], '(.Vint ' + pod + ')', lv1('d', 'port'), 2, 'cPortD lay c')} "
              f"({SEQ} {load(T['pon'], '(.Vint ' + pon + ')', lv1('n', 'port'), 3, 'cPortN lay c')} {c1set}))")
        L.append(f"      exact {IFL} {EQ(ptd, ptn)} _ _ _ {if1g} (if_true_triple hb1 {th})")
        c1v = f"(Val.ofBool {EQ(pod, pon)})"
    else:
        el = f"({SETL} {T['c1']} _ (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))"
        L.append(f"      exact {IFL} {EQ(ptd, ptn)} _ _ _ {if1g} (if_false_triple hb1 {el})")
        c1v = "(.Vint (Integers.Int.repr 0))"
    # B
    if b1:
        bb1, g1 = EQ(pod, pon), "boolVal_ofBool _ _ m (.inl rfl)"
        w1 = "if_true_triple hb2 " if b2 else "if_false_triple hb2 "
    else:
        bb1, g1, w1 = "false", "rfl", ""
    if b1 and b2:
        c2v = f"(Val.ofBool (!Integers.Int.eq se {Z}))"
        body = (f"({SEQ} ({SEQ} {load(T['nd'], '(Val.loadResult Mptr c.nameD)', lvname('d'), 4, 'cNameD c')} "
                f"({SEQ} {load(T['nn'], '(Val.loadResult Mptr c.nameN)', lvname('n'), 5, 'cNameN c')} "
                f"(call_ret ge _ _ _ _ _ {T['se']} _ _ emptyEnv _ _ [Val.loadResult Mptr c.nameD, Val.loadResult Mptr c.nameN] "
                f"bSe fdSe hSe hfSe htySe rfl (fun _ _ _ => eval_callee_global rfl hsSe rfl) "
                f"{args2('(Val.loadResult Mptr c.nameD)', 'hnd', '(Val.loadResult Mptr c.nameN)', 'hnn')}))) "
                f"({SETL} {T['c2']} _ {c2v} (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ "
                f"(EvalExpr.Etempvar _ _ _ (tget3 (.Vint se))) (cast_int_bool se m))))")
    else:
        c2v = "(.Vint (Integers.Int.repr 0))"
        body = f"({SETL} {T['c2']} _ {c2v} (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))"
    close = ""
    L.append(f"    exact {IFL} {bb1} _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget3 {c1v}), {g1}⟩) ({w1}{body}{close})")
    # C
    if b1 and b2:
        bb2, g2 = f"(!Integers.Int.eq se {Z})", "boolVal_ofBool _ _ m (.inl rfl)"
        w2 = f"{'if_true_triple' if b3 else 'if_false_triple'} (by rw [hb3]; rfl) "
    else:
        bb2, g2, w2 = "false", "rfl", ""
    guard2 = f"(fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget3 {c2v}), {g2}⟩)"
    if not reachC:
        L.append(f"  exact {IFL} {bb2} _ _ _ {guard2} ({w2}(triple_skip ge _ _ _))")
        L.append(f"exact {ret(0, 'false', hyps)}")
        return L
    if not after:
        L.append(f"  exact {IFL} {bb2} _ _ _ {guard2} ({w2}{ret(1, 'true', hyps)})")
        return L
    L.append(f"  refine {IFL} {bb2} _ _ _ {guard2} ({w2}?_)")
    ru, rp = TS('u'), TS('p')
    callsu = (f"({SEQ} {load(T['ud'], '(Val.loadResult Mptr c.uD)', lv1('d', 'user'), 6, 'cUD c')} "
              f"({SEQ} {load(T['un'], '(Val.loadResult Mptr c.uN)', lv1('n', 'user'), 7, 'cUN c')} "
              f"(call_ret_at ge _ _ ts hTs {T['ru']} _ _ emptyEnv _ _ [Val.loadResult Mptr c.uD, Val.loadResult Mptr c.uN] bTs "
              f"hfTs htyTs rfl (fun _ _ _ => eval_callee_global rfl hsTs rfl) "
              f"{args2('(Val.loadResult Mptr c.uD)', 'hud', '(Val.loadResult Mptr c.uN)', 'hun')})))")
    callsp = (f"({SEQ} {load(T['pd'], '(Val.loadResult Mptr c.pD)', lv1('d', 'passwd'), 8, 'cPD c')} "
              f"({SEQ} {load(T['pn'], '(Val.loadResult Mptr c.pN)', lv1('n', 'passwd'), 9, 'cPN c')} "
              f"(call_ret_at ge _ _ ts hTs {T['rp']} _ _ emptyEnv _ _ [Val.loadResult Mptr c.pD, Val.loadResult Mptr c.pN] bTs "
              f"hfTs htyTs rfl (fun _ _ _ => eval_callee_global rfl hsTs rfl) "
              f"{args2('(Val.loadResult Mptr c.pD)', 'hpd', '(Val.loadResult Mptr c.pN)', 'hpn')})))")
    gru = f"(fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget3 (.Vint {ru})), rfl⟩)"
    if not b4:  # ru ≠ 0 → t'2 = 1 → return 0
        ifru = (f"({IFL} (!Integers.Int.eq {ru} {Z}) _ _ _ {gru} (if_true_triple (by rw [hb4]; rfl) "
                f"({SETL} {T['c3']} _ (.Vint (Integers.Int.repr 1)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))))")
        c3v, bb3, g3, w3 = "(.Vint (Integers.Int.repr 1))", "true", "rfl", ""
        last_true = True
    else:
        c3v = f"(Val.ofBool (!Integers.Int.eq {rp} {Z}))"
        ifru = (f"({IFL} (!Integers.Int.eq {ru} {Z}) _ _ _ {gru} (if_false_triple (by rw [hb4]; rfl) "
                f"({SEQ} {callsp} ({SETL} {T['c3']} _ {c3v} (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ "
                f"(EvalExpr.Etempvar _ _ _ (tget3 (.Vint {rp}))) (cast_int_bool _ m))))))")
        bb3, g3 = f"(!Integers.Int.eq {rp} {Z})", "boolVal_ofBool _ _ m (.inl rfl)"
        w3 = f"{'if_true_triple' if not b5 else 'if_false_triple'} (by rw [hb5]; rfl) "
        last_true = not b5
    g3f = f"(fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (tget3 {c3v}), {g3}⟩)"
    if last_true:  # return 0 in IF2
        L.append("  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)")
        L.append(f"  refine {SEQ} ({SEQ} {callsu} {ifru}) ?_")
        close3 = ""
        L.append(f"  exact {IFL} {bb3} _ _ _ {g3f} ({w3}{ret(0, 'false', hyps)}{close3})")
    else:
        L.append(f"  refine {SEQ} ({SEQ} ({SEQ} {callsu} {ifru}) ({IFL} {bb3} _ _ _ {g3f} ({w3}(triple_skip ge _ _ _)))) ?_")
        L.append(f"  exact {ret(1, 'true', hyps)}")
    return L


def gen(name):
    mod, ns, after, pch, pw, poff, ptoff, desc = VERS[name]
    T = TA if after else TB
    paths = ([(False,), (True, False), (True, True, False), (True, True, True, False), (True, True, True, True, False),
              (True, True, True, True, True)] if after else [(False,), (True, False), (True, True, False), (True, True, True)])
    res = (f"Val.ofBool (Integers.Int.eq (Integers.Int.zero_ext 8 c.ptD) (Integers.Int.zero_ext 8 c.ptN) "
           f"&& Integers.Int.eq ({pw}c.portD) ({pw}c.portN) && !Integers.Int.eq se Integers.Int.zero")
    if after:
        res += f" && Integers.Int.eq {TS('u')} Integers.Int.zero && Integers.Int.eq {TS('p')} Integers.Int.zero"
    res += ")"
    tsp = " (ts : List Val → Integers.Int)" if after else ""
    tsa = " ts" if after else ""
    thm = "matches_after" if after else "matches_before"
    o = [f"""/-
CVE-2026-3784: {desc} の `proxy_info_matches`。生成: `research/c-semantics-link/deb2026_3784/proof_gen/gen.py`。

すべての入力について、戻り値は `res`（下の定義）で、メモリは変えない（`{thm}`）。
-/
import {mod}
import Deb2026_3784Common
open CC CC.Sep CC.HProp
open {ns}
open Deb2026_8927 (Cell Cells mem_idx ld lv_f1 lv_f2 eval_lv_load retSpec call_ret boolVal_ofBool)
open Case4C (IsPtr loadResult_ptr cast_ptr)

set_option maxRecDepth 20000

namespace Deb2026_3784.{name}
open Deb2026_3784

def coOf (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => {{ co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }}

theorem co_pi : prog.prog_comp_env.get _proxy_info = some (coOf _proxy_info) := rfl
theorem co_hn : prog.prog_comp_env.get _hostname = some (coOf _hostname) := rfl
theorem off_host : fieldOffset prog.prog_comp_env _host (coOf _proxy_info).co_members = .OK (0, .Full) := by decide
theorem off_port : fieldOffset prog.prog_comp_env _port (coOf _proxy_info).co_members = .OK ({poff}, .Full) := by decide
theorem off_pt : fieldOffset prog.prog_comp_env _proxytype (coOf _proxy_info).co_members = .OK ({ptoff}, .Full) := by decide
theorem off_user : fieldOffset prog.prog_comp_env _user (coOf _proxy_info).co_members = .OK (16, .Full) := by decide
theorem off_passwd : fieldOffset prog.prog_comp_env _passwd (coOf _proxy_info).co_members = .OK (24, .Full) := by decide
theorem off_name : fieldOffset prog.prog_comp_env _name (coOf _hostname).co_members = .OK (0, .Full) := by decide

def lay : Lay := ⟨{pch}, {poff}, {ptoff}⟩

def res (c : Ctx) (se : Integers.Int){tsp} : Val :=
  {res}

def spec (c : Ctx) (se : Integers.Int){tsp} : FunSpec where
  tyargs := [tptr (Ty.Tstruct _proxy_info noattr), tptr (Ty.Tstruct _proxy_info noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dB c.dO, .Vptr c.nB c.nO] ∧ Cells .Freeable (cells lay c) hp
  post := fun v hp => v = res c se{tsa} ∧ Cells .Freeable (cells lay c) hp
  measure := fun _ => 0

theorem entry_wf :
    listNorepet (varNames f_proxy_info_matches.fn_vars) ∧ listNorepet (varNames f_proxy_info_matches.fn_params)
    ∧ listDisjoint (varNames f_proxy_info_matches.fn_params) (varNames f_proxy_info_matches.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxHeartbeats 8000000 in
theorem {thm} (ge : CGenv) (c : Ctx) (se : Integers.Int){tsp}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hnd : IsPtr (Val.loadResult Mptr c.nameD)) (hnn : IsPtr (Val.loadResult Mptr c.nameN))"""]
    if after:
        o.append("""    (hud : IsPtr (Val.loadResult Mptr c.uD)) (hun : IsPtr (Val.loadResult Mptr c.uN))
    (hpd : IsPtr (Val.loadResult Mptr c.pD)) (hpn : IsPtr (Val.loadResult Mptr c.pN))""")
    o.append("""    (bSe : Block) (fdSe : FunDef) (hsSe : Genv.findSymbol ge.genv_genv _curl_strequal = some bSe)
    (hfSe : FuncPtr ge bSe fdSe)
    (htySe : typeOfFundef fdSe = .Tfunction [tptr tschar, tptr tschar] tint cc_default)
    (hSe : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdSe (retSpec [tptr tschar, tptr tschar] tint (.Vint se)) vs)""")
    if after:
        o.append("""    (bTs : Block) (fdTs : FunDef) (hsTs : Genv.findSymbol ge.genv_genv _Curl_timestrcmp = some bTs)
    (hfTs : FuncPtr ge bTs fdTs)
    (htyTs : typeOfFundef fdTs = .Tfunction [tptr tschar, tptr tschar] tint cc_default)
    (hTs : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdTs (retSpec [tptr tschar, tptr tschar] tint (.Vint (ts vs))) vs)""")
    o.append(f"""    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_proxy_info_matches) (spec c se{tsa}) vs := by
  by_cases hvs : vs = [.Vptr c.dB c.dO, .Vptr c.nB c.nO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hpr : permOrder Permission.Freeable .Readable = true := rfl
  obtain ⟨hnv, hnp, hdisj⟩ := entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_proxy_info_matches _ _
    (LocalSt emptyEnv [(_needle, .Vptr c.nB c.nO), (_data, .Vptr c.dB c.dO)] (Cells .Freeable (cells lay c)))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _needle (.Vptr c.nB c.nO)
              (PTree.set _data (.Vptr c.dB c.dO) (createUndefTemps f_proxy_info_matches.fn_temps)),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_nil _)), hpre.2⟩
    exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)""")
    exprs = [f"(Integers.Int.zero_ext 8 c.ptD) (Integers.Int.zero_ext 8 c.ptN)", f"({pw}c.portD) ({pw}c.portN)",
             "se Integers.Int.zero", f"{TS('u')} Integers.Int.zero", f"{TS('p')} Integers.Int.zero"]

    def emit(prefix, ind):
        if tuple(prefix) in paths:
            for st in path(after, T, pw, tuple(prefix)):
                o.append(ind + st)
            return
        k = len(prefix)
        o.append(ind + f"cases hb{k+1} : Integers.Int.eq {exprs[k]}")
        for hv in (False, True):
            b = hv if k != 2 else (not hv)
            o.append(ind + f"case {'true' if hv else 'false'} =>")
            emit(prefix + [b], ind + "  ")
    emit([], "  ")
    return "\n".join(o) + f"\n\nend Deb2026_3784.{name}\n"


for name in VERS:
    (OUT / f"Deb2026_3784{name}.lean").write_text(gen(name))
print("ok")
