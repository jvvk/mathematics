"""Full combinatorial pipeline for degree m: configurations -> Lemma 2 RH filter -> group law augmented with
total-ramification relations, decided exactly (grouplaw_exact.decide)."""
import json
import sys
from collections import Counter
from pathlib import Path

from grouplaw_exact import decide
from rh_filter import check
from rh_grouplaw import extra_relations

HERE = Path(__file__).parent


def main():
    m = sys.argv[1]
    data = json.loads((HERE / f"m{m}_configs.json").read_text())
    stats, out = Counter(), []
    for d in data:
        cfg = d["cfg"]
        n = len(cfg)
        base = [r[1:] for r in ([[c[1 + i] for c in cfg] for i in range(4)]) if any(r[1:])]
        if decide(base, n) == "none":
            stats["group law"] += 1; continue
        if check(cfg) != "SURVIVES":
            stats["RH"] += 1; continue
        ex = extra_relations(cfg)
        if ex is None:
            stats["r > deg"] += 1; continue
        A = [r[1:] for r in ([[c[1 + i] for c in cfg] for i in range(4)] + ex) if any(r[1:])]
        cl = decide(A, n)
        if cl == "none":
            stats["augmented group law"] += 1; continue
        stats[("SURVIVES", tuple(d["mu"]), cl.split(" N")[0])] += 1
        d2 = dict(d); d2["aug"] = cl; d2["extra"] = ex
        out.append(d2)
    for k, v in sorted(stats.items(), key=str):
        print(k, v)
    print("survivors:", len(out))
    (HERE / f"m{m}_survivors.json").write_text(json.dumps(out))


if __name__ == "__main__":
    main()
