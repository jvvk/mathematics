"""Compare the independent recheck (lengths 2 to 34; none below 24 may be an anti-square) (indep.cpp output) with the original search (results/anti_*.txt) and recompute
Table 1 (classes up to rotation, reversal and letter exchange; fewest ones of the rarer letter) without sharing code."""
import sys

TABLE1 = {24: (1, 12), 26: (26, 10), 28: (103, 10), 30: (660, 10), 32: (2758, 8), 34: (11026, 8)}


def rep(w: str) -> str:
    variants = []
    for x in (w, w[::-1]):
        for y in (x, "".join("1" if c == "0" else "0" for c in x)):
            variants += [y[i:] + y[:i] for i in range(len(y))]
    return min(variants)


def read_rows(path: str) -> list[list[str]]:
    rows = [l.split() for l in open(path) if l.strip()]
    if any(len(r) != 2 or r[1] not in ("0", "1") or set(r[0]) - set("01") for r in rows):
        raise ValueError(f"{path}: malformed line")
    return rows


def main(orig_dir: str) -> bool:
    ok = True
    for n in range(2, 24, 2):  # no anti-squares below length 24
        rows = read_rows(f"anti_{n}.txt")
        print(f"n={n} anti-square necklaces={len(rows)} -> {'OK' if not rows else 'MISMATCH'}")
        ok &= not rows
    for n, (cls, fewest) in TABLE1.items():
        rows = read_rows(f"anti_{n}.txt")
        if not rows:
            print(n, "empty output"); ok = False; continue
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
    return ok


if __name__ == "__main__":
    try:
        good = main(sys.argv[1] if len(sys.argv) > 1 else "../results")
    except (OSError, ValueError) as e:  # a missing or malformed input is a failure, never a skip
        print("FAILED:", e)
        sys.exit(1)
    sys.exit(0 if good else 1)
