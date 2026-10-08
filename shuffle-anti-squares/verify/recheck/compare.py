"""Compare the independent recheck (indep.cpp output) with the original search (results/anti_*.txt) and recompute
Table 1 (classes up to rotation, reversal and letter exchange; fewest ones of the rarer letter) without sharing code."""
import sys

TABLE1 = {24: (1, 12), 26: (26, 10), 28: (103, 10), 30: (660, 10), 32: (2758, 8), 34: (11026, 8)}


def rep(w: str) -> str:
    variants = []
    for x in (w, w[::-1]):
        for y in (x, "".join("1" if c == "0" else "0" for c in x)):
            variants += [y[i:] + y[:i] for i in range(len(y))]
    return min(variants)


def main(orig_dir: str) -> None:
    ok = True
    for n, (cls, fewest) in TABLE1.items():
        try:
            rows = [l.split() for l in open(f"anti_{n}.txt") if l.strip()]
        except FileNotFoundError:
            print(n, "not run"); continue
        mine = {r[0] for r in rows}
        two_cut_ok = all(r[1] == "1" for r in rows)
        orig = {l.strip() for l in open(f"{orig_dir}/anti_{n}.txt") if l.strip()}
        classes = {rep(w) for w in mine}
        rare = min(min(w.count("0"), w.count("1")) for w in mine)
        line_ok = mine == orig and len(classes) == cls and rare == fewest and two_cut_ok
        ok &= line_ok
        print(f"n={n} necklaces={len(mine)} same_as_original={mine == orig} classes={len(classes)} (table {cls}) "
              f"fewest={rare} (table {fewest}) all_two_cut={two_cut_ok} -> {'OK' if line_ok else 'MISMATCH'}")
    print("ALL OK" if ok else "MISMATCH FOUND")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "../results")
