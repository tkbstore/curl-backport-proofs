# url_match_auth_nego の証明を経路ごとに組み立てる（生成物は lean/Case2NegoMain.lean）
import sys
T = lambda n: chr(95) + "t" + chr(39) + str(n)
HH = "(H2 c foundV word)"
HC = "(H2 c (.Vptr c.connB c.connO) word)"
L0 = "[(_m, .Vptr c.mB c.mO), (_conn, .Vptr c.connB c.connO)]"
HSUB = "(fun p hp => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> temps_get)"

def setp(t, v, proof, H):
    return ("set", t, v, proof, H)
def render(x):
    if isinstance(x, str):
        return x
    if x[0] == "seq":
        return f"(triple_seq_fwd ge _ _ _ _ _ _ _ {render(x[1])} {render(x[2])})"
    _, t, v, proof, H = x
    return f"(triple_set_local_fwd ge _ _ emptyEnv _ {H} {t} _ ({v}) (fun le m hp hT hH hag => {proof}))"
def exact_lines(x):
    if isinstance(x, str):
        return ["exact " + x]
    if x[0] == "seq":
        return ["refine triple_seq_fwd ge _ _ _ _ _ _ _ " + render(x[1]) + " ?_"] + exact_lines(x[2])
    _, t, v, proof, H = x
    return [f"refine triple_set_local_fwd ge _ _ emptyEnv _ {H} {t} _ ({v}) ?_",
            "intro le m hp hT hH hag", "exact " + proof]
def set_field(t, v, co, off, ld, H=HH):
    return setp(t, v, f"eval_field (hT.get (by temps_get)) (hcenv ▸ {co}) (hcenv ▸ {off}) rfl "
            f"(H2_loads hpr hpn hptr hH hag).{ld}", H)
def set_state(t, v, off, ld, H=HH):
    return setp(t, v, f"eval_state_field hcenv (hT.get (by temps_get)) {off} rfl (H2_loads hpr hpn hptr hH hag).{ld}", H)
def set_bit(t, pos, off, H=HH):
    return setp(t, f".Vint (Cop.bitfieldExtract .I32 .Unsigned {pos} 1 word)",
            f"eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ {off}) "
            f"(by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word", H)
def set_const(t, n, H=HH):
    return (f"(triple_set_local_fwd ge _ _ emptyEnv _ {H} {t} _ (.Vint (Integers.Int.repr {n})) "
            f"(fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))")
def set_gen(t, v, proof, H=HH):
    return setp(t, v, proof, H)
def call(spec, t, args, ret, b, fd, h, hf, hty, hs, H=HH):
    acc = "EvalExprlist.nil"
    for (tn, v, cp) in reversed(args):
        acc = f"(EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar {tn} _ ({v}) (hT.get (by temps_get))) ({cp}) {acc})"
    vals = ", ".join(v for (_, v, _) in args)
    return (f"(call_fwd ge _ _ ({spec}) {t} _ _ emptyEnv _ emp {H} emp {H} {H} [{vals}] ({ret}) {b} {fd} {h} {hf} {hty} rfl "
            f"(fun _ _ _ => eval_callee_global rfl {hs} rfl) (fun le m hT => {acc}) "
            f"(fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))")
def seq(a, b):
    return ("seq", a, b)
def creds_chain(tc, td, ts, tr, CS):
    return seq(set_field(tc, "c.credsV", "co_conn", "off_creds", "creds"),
           seq(set_field(td, ".Vptr c.dataB c.dataO", "co_match", "off_data", "data"),
           seq(set_state(ts, "c.scredsV", "off_screds", "screds"),
               call(f"credsSpec {CS}", tr,
                    [(tc, "c.credsV", "cast_ptr (creds_isPtr hptr) _ _ m"), (ts, "c.scredsV", "cast_ptr hptr.screds _ _ m")],
                    f"Val.ofBool {CS}", "bCs", "fdCs", "hCs", "hfCs", "htyCs", "hsCs"))))
def peer_chain(tc, td, ts, tr, OE):
    return seq(set_field(tc, "c.corigV", "co_conn", "off_creds_origin", "corig"),
           seq(set_field(td, ".Vptr c.dataB c.dataO", "co_match", "off_data", "data"),
           seq(set_state(ts, "c.originV", "off_origin", "origin"),
               call(f"peerSpec {OE}", tr,
                    [(tc, "c.corigV", "cast_ptr hptr.corig _ _ m"), (ts, "c.originV", "cast_ptr hptr.origin _ _ m")],
                    f"Val.ofBool {OE}", "bPe", "fdPe", "hPe", "hfPe", "htyPe", "hsPe"))))
def set_notb(t, B, src, H=HH):
    return set_gen(t, f"Val.ofBool (!{B})",
        f"EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar {src} _ _ (hT.get (by temps_get))) "
        f"(notbool_ofBool {B} m)) (cast_ofBool_bool _ m)", H)

def iff(bb, ev, bp, H=HH, names="_ _"):
    rw = "rw [if_pos rfl]" if bb == "true" else "rw [if_neg Bool.false_ne_true]"
    return [f"refine triple_if_local ge _ _ emptyEnv _ {H} _ {bb} _ _ _ (fun le m hp hT {names} => ⟨_, {ev}, {bp}⟩) ?_", rw]
ETV = "EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))"

def ind(lines, n):
    return [" " * n + l for l in lines]

def ret(n, verdict, simps, CS="cs", OE="oe", H=HH):
    v = "true" if n == 1 else "false"
    return [f"exact return_const ge _ _ _ _ _ _ _ (Val.ofBool {v}) (fun _ => rfl)",
            f"  (fun hp hH => post_of c foundV word {CS} {OE} _ hp .{verdict} (by simp [vdOf, matchNego, negInput, {simps}]) rfl hH)"]
def fall(simps):
    return [f"exact fall_to ge _ _ _ {L0} _ _ _ {HSUB}",
            f"  (by simp [vdOf, matchNego, negInput, {simps}])"]

def sneg_prefix(Z):
    neglit = "true" if Z == "false" else "false"
    return ([f"refine triple_seq_fwd ge _ _ _ _ _ _ _ {render(set_field(chr(95)+chr(116)+chr(39)+'17', '.Vint c.ns', 'co_conn', 'off_nego', 'ns'))} ?_"]
            + iff(neglit, "EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _) (ne_zero_eval _ _ _)",
                  "(boolVal_ofBool_tint _ m).trans (by rw [hng]; rfl)"))

def neg_path(tag, W, CS, OE, simps):
    # NEG = Seq (Seq A1 A2) (Sif t3 ret0 skip)
    L = [f"refine triple_seq_fwd ge _ _ _ ?Qa{tag} _ _ _ ?a{tag} ?b{tag}", f"case a{tag} =>"]
    A = [f"refine triple_seq_fwd ge _ _ _ ?Qc{tag} _ _ _ ?c{tag} ?d{tag}", f"case c{tag} =>"]
    A1 = [f"refine triple_seq_fwd ge _ _ _ _ _ _ _ {render(set_bit(chr(95)+'t'+chr(39)+'29', 1, 'off_want'))} ?_"]
    A1 += iff("true" if W == "false" else "false",
              "EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_int _ m)",
              "(notbool_bit_val word 1 m).trans (by rw [hw]; rfl)")
    if W == "false":
        A1 += exact_lines(set_const(chr(95)+'t'+chr(39)+'1', 1))
    else:
        A1 += exact_lines(seq(creds_chain(chr(95)+'t'+chr(39)+'30', chr(95)+'t'+chr(39)+'31', chr(95)+'t'+chr(39)+'32', chr(95)+'t'+chr(39)+'2', CS), set_notb(chr(95)+'t'+chr(39)+'1', CS, chr(95)+'t'+chr(39)+'2')))
    A += ind(A1, 2) + [f"case d{tag} =>"]
    if W == "false":
        A2 = iff("true", ETV, "rfl") + exact_lines(set_const(chr(95)+'t'+chr(39)+'3', 1))
        t3 = ("true", "rfl")
    else:
        b1 = "true" if CS == "false" else "false"
        A2 = iff(b1, ETV, "boolVal_ofBool_tint _ m")
        if CS == "false":
            A2 += exact_lines(set_const(chr(95)+'t'+chr(39)+'3', 1))
            t3 = ("true", "rfl")
        else:
            A2 += exact_lines(seq(peer_chain(chr(95)+'t'+chr(39)+'26', chr(95)+'t'+chr(39)+'27', chr(95)+'t'+chr(39)+'28', chr(95)+'t'+chr(39)+'4', OE), set_notb(chr(95)+'t'+chr(39)+'3', OE, chr(95)+'t'+chr(39)+'4')))
            t3 = ("true" if OE == "false" else "false", "boolVal_ofBool_tint _ m")
    A += ind(A2, 2)
    L += ind(A, 2) + [f"case b{tag} =>"]
    B = iff(t3[0], ETV, t3[1])
    if t3[0] == "true":
        B += ret(0, "reject", simps, CS, OE)
    else:
        B += fall(simps)
    L += ind(B, 2)
    return L

def nonneg_path(tag, CR, CS, OE, simps):
    # after if t18 = true: Seq B (Sif t5 ret0 skip)
    L = [f"refine triple_seq_fwd ge _ _ _ ?Qa{tag} _ _ _ ?a{tag} ?b{tag}", f"case a{tag} =>"]
    B = [f"refine triple_seq_fwd ge _ _ _ _ _ _ _ {render(set_field(chr(95)+'t'+chr(39)+'19', 'c.credsV', 'co_conn', 'off_creds', 'creds'))} ?_"]
    B += iff("false" if CR == "null" else "true", ETV,
             "(boolVal_ptr_creds hptr (H2_loads hpr hpn hptr hH hag).valid).trans (by rw [hcr]; simp)", names="hH hag")
    if CR == "null":
        B += exact_lines(set_const(chr(95)+'t'+chr(39)+'5', 0))
        t5 = ("false", "rfl")
    else:
        B += [f"refine triple_seq_fwd ge _ _ _ _ _ _ _ {render(creds_chain(chr(95)+'t'+chr(39)+'23', chr(95)+'t'+chr(39)+'24', chr(95)+'t'+chr(39)+'25', chr(95)+'t'+chr(39)+'6', CS))} ?_"]
        B += iff("true" if CS == "false" else "false",
                 "EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_ofBool _ m)",
                 "boolVal_ofBool_tint _ m")
        if CS == "false":
            B += exact_lines(set_gen(chr(95)+'t'+chr(39)+'5', 'Val.ofBool true', 'EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl'))
            t5 = ("true", "boolVal_ofBool_tint _ m")
        else:
            inner = seq(peer_chain(chr(95)+'t'+chr(39)+'20', chr(95)+'t'+chr(39)+'21', chr(95)+'t'+chr(39)+'22', chr(95)+'t'+chr(39)+'7', OE),
                        set_notb(chr(95)+'t'+chr(39)+'5', OE, chr(95)+'t'+chr(39)+'7'))
            B += exact_lines(seq(inner, set_gen(chr(95)+'t'+chr(39)+'5', f'Val.ofBool (!{OE})', 'EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar ' + T(5) + ' _ _ (hT.get (by temps_get))) (cast_ofBool_bool _ m)')))
            t5 = ("true" if OE == "false" else "false", "boolVal_ofBool_tint _ m")
    L += ind(B, 2) + [f"case b{tag} =>"]
    C = iff(t5[0], ETV, t5[1])
    if t5[0] == "true":
        C += ret(0, "reject", simps, CS, OE)
    else:
        C += fall(simps)
    L += ind(C, 2)
    return L


def tail(tag, W, Z):
    L = ["refine triple_pure_pre ge _ _ _ _ _ _ (fun hφ => ?_)"]
    if W == "false" and Z == "false":
        L += ["exact absurd hφ (by simp [vdOf, matchNego, negInput, hw, hng])"]
        return L
    if W == "true":
        L += ["refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)"]
    else:
        L += [f"refine triple_seq ge _ _ _ ?Qt{tag} _ _ _ ?tA{tag} ?tB{tag}", f"case tA{tag} =>"]
    A = [f"refine triple_seq_fwd ge _ _ _ ?QT{tag} _ _ _ ?tC{tag} ?tD{tag}", f"case tC{tag} =>"]
    C = [f"refine triple_seq_fwd ge _ _ _ _ _ _ _ {render(set_bit(T(15), 1, 'off_want'))} ?_"]
    C += iff(W, ETV, "(boolVal_bit_val word 1 m).trans (by rw [hw])")
    if W == "true":
        C += exact_lines(set_const(T(10), 1))
    else:
        C += [f"refine triple_seq_fwd ge _ _ _ _ _ _ _ {render(set_bit(T(16), 2, 'off_proxy'))} ?_",
              ] + exact_lines(set_gen(T(10), 'Val.ofBool (bitOf word 2)', 'EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar ' + T(16) + ' _ _ (hT.get (by temps_get))) (cast_int_bool _ m)'))
    A += ind(C, 2) + [f"case tD{tag} =>"]
    if W == "false":
        D = iff("false", ETV, "(boolVal_ofBool_tint _ m).trans (by rw [hprox])") + ["exact skip_fall ge _ _ _ _"]
    else:
        D = iff("true", ETV, "rfl")
        D += [f"refine triple_seq_fwd ge _ _ _ _ _ _ _ (assign_found ge c foundV word _ hcenv hpw (by temps_get) (by temps_get)) ?_"]
        Z1 = [f"refine triple_seq_fwd ge _ _ _ _ _ _ _ {render(set_bit(T(13), 1, 'off_want', HC))} ?_"]
        Z1 += iff("true", ETV, "(boolVal_bit_val word 1 m).trans (by rw [hw])", H=HC)
        Z1 += [f"refine triple_seq_fwd ge _ _ _ _ _ _ _ {render(set_field(T(14), '.Vint c.ns', 'co_conn', 'off_nego', 'ns', HC))} ?_",
               ] + exact_lines(set_gen(T(8), '(Val.ofBool (!Integers.Int.eq c.ns Integers.Int.zero))', 'EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar ' + T(14) + ' _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _) (ne_zero_eval _ _ _)) (cast_ofBool_bool _ m)', HC))
        if Z == "false":  # negotiated: forceReuse
            D += ["refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)",
                  f"refine triple_seq_fwd ge _ _ _ ?QZ{tag} _ _ _ ?z1{tag} ?z2{tag}", f"case z1{tag} =>"]
            Zs = [f"refine triple_seq_fwd ge _ _ _ ?QY{tag} _ _ _ ?z3{tag} ?z4{tag}", f"case z3{tag} =>"] + ind(Z1, 2)
            Zs += [f"case z4{tag} =>"] + ind(iff("true", ETV, "(boolVal_ofBool_tint _ m).trans (by rw [hng]; rfl)", H=HC) + exact_lines(set_const(T(9), 1, HC)), 2)
            D += ind(Zs, 2) + [f"case z2{tag} =>"]
            Z3 = iff("true", ETV, "rfl", H=HC)
            Z3 += [f"refine triple_seq_fwd ge _ _ _ _ _ _ _ (assign_force ge c word _ hcenv hpw hpr (by temps_get)) ?_",
                   "have hvd : vdOf c word cs oe = .forceReuse := by",
                   "  revert hφ; cases cs <;> cases oe <;> simp [vdOf, matchNego, negInput, hw, hng]",
                   "exact return_const ge _ _ _ _ _ _ _ (Val.ofBool true) (fun _ => rfl)",
                   "  (fun hp hH => post_of c foundV word cs oe _ hp _ hvd rfl hH)"]
            D += ind(Z3, 2)
        else:  # not negotiated: candidate
            D += [f"refine triple_seq_fwd ge _ _ _ ?QW{tag} _ _ _ ?w1{tag} ?w2{tag}", f"case w1{tag} =>"]
            W1 = [f"refine triple_seq_fwd ge _ _ _ ?QZ{tag} _ _ _ ?z1{tag} ?z2{tag}", f"case z1{tag} =>"]
            Zs = [f"refine triple_seq_fwd ge _ _ _ ?QY{tag} _ _ _ ?z3{tag} ?z4{tag}", f"case z3{tag} =>"] + ind(Z1, 2)
            Z2 = iff("false", ETV, "(boolVal_ofBool_tint _ m).trans (by rw [hng]; rfl)", H=HC)
            Z2 += [f"refine triple_seq_fwd ge _ _ _ _ _ _ _ {render(set_bit(T(11), 2, 'off_proxy', HC))} ?_"]
            Z2 += iff("false", ETV, "(boolVal_bit_val word 2 m).trans (by rw [hprox])", H=HC)
            Z2 += exact_lines(set_gen(T(9), '.Vint (Integers.Int.repr 0)', 'EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl', HC))
            Zs += [f"case z4{tag} =>"] + ind(Z2, 2)
            W1 += ind(Zs, 2) + [f"case z2{tag} =>"] + ind(iff("false", ETV, "rfl", H=HC) + ["exact triple_skip ge _ _ _"], 2)
            D += ind(W1, 2) + [f"case w2{tag} =>"]
            W2 = ["have hvd : vdOf c word cs oe = .candidate := by",
                  "  revert hφ; cases cs <;> cases oe <;> rcases hptr.creds with hcr | hcr <;> simp [vdOf, matchNego, negInput, hw, hng, hcr]",
                  "exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)",
                  "  (fun hp hH => post_of c foundV word cs oe _ hp _ hvd rfl hH)"]
            D += ind(W2, 2)
    A += ind(D, 2)
    if W == "true":
        return L + A
    L += ind(A, 2) + [f"case tB{tag} =>"]
    if W == "false":
        B = ["have hvd : vdOf c word cs oe = .accept := by simp [vdOf, matchNego, negInput, hw, hng]",
             "exact return_const ge _ _ _ _ _ _ _ (Val.ofBool true) (fun _ => rfl)",
             "  (fun hp hH => post_of c foundV word cs oe _ hp _ hvd rfl hH)"]
    else:
        B = ["exact triple_vacuous ge _ _ _ _"]
    L += ind(B, 2)
    return L

QMID = f"(fun e le hp => vdOf c word cs oe ≠ .reject ∧ LocalSt emptyEnv {L0} {HH} e le hp)"

out = []
# goal order after `cases hw <;> cases hng`: (W,Z) = (f,f), (f,t), (t,f), (t,t)
for (W, Z) in [("false","false"), ("false","true"), ("true","false"), ("true","true")]:
    tag = W[0] + Z[0]
    G = [f"refine triple_seq ge _ _ _ {QMID} _ _ _ ?n{tag} ?t{tag}", f"case n{tag} =>"]
    N = sneg_prefix(Z)
    if Z == "false":  # negotiated
        if W == "false":
            N += neg_path(tag + "1", W, "cs", "oe", "hw, hng")
        else:
            N += ["cases cs", "· " + "-- creds が違う"]
            p2 = neg_path(tag + "2", W, "false", "oe", "hw, hng")
            N += ind(p2, 2)
            N += ["· cases oe"]
            p3 = neg_path(tag + "3", W, "true", "false", "hw, hng")
            p4 = neg_path(tag + "4", W, "true", "true", "hw, hng")
            N += ["  · " + p3[0]] + ind(p3[1:], 4) + ["  · " + p4[0]] + ind(p4[1:], 4)
    else:  # not negotiated
        N += [f"refine triple_seq_fwd ge _ _ _ _ _ _ _ {render(set_bit(T(18), 1, 'off_want'))} ?_"]
        N += iff(W, ETV, "(boolVal_bit_val word 1 m).trans (by rw [hw])")
        if W == "false":
            N += fall("hw, hng")
        else:
            N += ["rcases hptr.creds with hcr | hcr"]
            p6 = nonneg_path(tag + "6", "null", "cs", "oe", "hw, hng, hcr")
            N += ["· " + p6[0]] + ind(p6[1:], 2)
            N += ["· cases cs"]
            p7 = nonneg_path(tag + "7", "ptr", "false", "oe", "hw, hng, hcr")
            N += ["  · " + p7[0]] + ind(p7[1:], 4)
            N += ["  · cases oe"]
            p8 = nonneg_path(tag + "8", "ptr", "true", "false", "hw, hng, hcr")
            p9 = nonneg_path(tag + "9", "ptr", "true", "true", "hw, hng, hcr")
            N += ["    · " + p8[0]] + ind(p8[1:], 6) + ["    · " + p9[0]] + ind(p9[1:], 6)
    G += ind(N, 2) + [f"case t{tag} =>"] + ind(tail(tag, W, Z), 2)
    out += ["· " + G[0]] + ind(G[1:], 2)

print("\n".join(ind(out, 2)))
