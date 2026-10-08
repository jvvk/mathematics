"""Emit ShuffleBlocks/CutRR.lean from tree_R.pkl: a Lean proof by explicit case splits, omega at leaves."""
import pickle
import sys

RUNS = [(0, "L"), (1, "m"), (0, "5 * l"), (1, "2 * m"), (0, "L"), (1, "m"), (0, "2 * l"), (1, "m"),
        (0, "l"), (1, "3 * m")]
LET = {0: "false", 1: "true"}


def layout(r: int):
    c, n = RUNS[r]
    lin = [(c, f"({n} - k)")] + RUNS[r + 1:] + RUNS[:r] + [(c, "k")]
    ones = [i for i, (ci, _) in enumerate(lin) if ci == 1]
    def SA(i):
        t = [f"a{q}" for q in ones if q < i]
        return " + ".join(t) if t else "0"
    def SB(i):
        t = [f"b{q}" for q in ones if q < i]
        return " + ".join(t) if t else "0"
    return c, n, lin, ones, SA, SB


def emit(r: int, tree) -> str:
    c, n, lin, ones, SA, SB = layout(r)
    N = len(lin)
    out = []
    w = out.append
    w("import LeanProofs.ShuffleBlocks.Basic\n")
    w("set_option linter.style.longLine false")
    w("set_option linter.unusedVariables false\n")
    w("namespace Blocks\n")
    w("set_option maxHeartbeats 0 in")
    w(f"/-- Cut inside run {r} of `V`: no splitting of this rotation gives two equal copies. -/")
    args = " ".join([f"a{i} b{i}" for i in range(N)])
    w(f"theorem V_cut{r:02d} (L l m v k {args} : Nat)")
    w(f"    (hl : 1 ≤ l) (hm : m = 2 * v + 1) (hL : 9 * l ≤ L) (hk : k ≤ {n})")
    for i, (_, ni) in enumerate(lin):
        w(f"    (e{i} : a{i} + b{i} = {ni})")
    la = ", ".join(f"({LET[ci]}, a{i})" for i, (ci, _) in enumerate(lin))
    lb = ", ".join(f"({LET[ci]}, b{i})" for i, (ci, _) in enumerate(lin))
    w(f"    (E : rw [{la}] = rw [{lb}]) : False := by")
    w("  have ho := congrArg (List.count true) E")
    w("  have hz := congrArg (List.count false) E")
    w("  simp only [count_rw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,")
    w("    Bool.true_eq_false, Bool.false_eq_true] at ho hz")
    cnt = [0]

    def node(t, ind):
        pad = "  " * ind
        if t[0] == "leaf":
            w(pad + "omega")
            return
        (i, j), subs = t[0], t[1:]
        ri, rj = ones[i], ones[j]
        conds = [f"0 < a{ri}", f"0 < b{rj}", f"{SA(ri)} < {SB(rj)} + b{rj}", f"{SB(rj)} < {SA(ri)} + a{ri}"]
        hs = []
        for q, cond in enumerate(conds):
            cnt[0] += 1
            h = f"c{cnt[0]}"
            hs.append(h)
            w(pad + f"by_cases {h} : {cond}")
            w(pad + "swap")
            w(pad + "· " + ("omega" if subs[q][0] == "leaf" else ""))
            if subs[q][0] != "leaf":
                out.pop()
                w(pad + "· skip")
                out.pop()
                # emit subtree in a focused block
                w(pad + "· -- branch")
                node(subs[q], ind + 1)
        cnt[0] += 1
        f = f"f{cnt[0]}"
        w(pad + f"have {f} := pair_fact E (i := {ri}) (j := {rj}) rfl rfl {hs[0]} {hs[1]}")
        w(pad + f"  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)")
        w(pad + f"  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)")
        w(pad + f"simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at {f}")
        node(subs[-1], ind)

    node(tree, 1)
    w("\nend Blocks")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    import pathlib
    dest = pathlib.Path(__file__).resolve().parents[2] / "lean/LeanProofs/ShuffleBlocks"
    for r in map(int, sys.argv[1:]):
        t = pickle.load(open(f"tree_{r}.pkl", "rb"))
        (dest / f"Cut{r:02d}.lean").write_text(emit(r, t))
        print("wrote", r)
