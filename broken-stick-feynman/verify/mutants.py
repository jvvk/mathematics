"""Wrong variants of the programs must fail check.py. Each mutant patches one function or constant, runs the
check it should break, and restores the original. Usage: python3 mutants.py (about a minute on one core)."""
from __future__ import annotations

import math
import pathlib
import subprocess
import tempfile

import numpy as np

import check
import feynman_hp
import general_n
import marked


def wrong_C(n: int) -> float:  # pi^(-(N+1)/2) in place of pi^(-N/2)
    N = n * (n + 1) // 2
    return 2 ** (N - n) * math.pi ** (-(N + 1) / 2) * general_n.mgamma(n, (n + 1) / 2)


def wrong_symanzik(n: int, s: np.ndarray) -> np.ndarray:  # forgets the factor prod s: Kirchhoff, not Symanzik
    return ORIG["symanzik"](n, s) / np.prod(s, axis=1)


def wrong_f(z: np.ndarray) -> np.ndarray:  # elliptic coordinates with the wrong scale (a shift would cancel)
    return 0.55 * (1.0 + np.cosh(z))


ORIG = dict(C=general_n.C, symanzik=general_n.symanzik, cotrees=list(feynman_hp.COTREES), f=marked.f, M=marked.M)


def breaks(name: str, run) -> bool:
    try:
        run()
    except AssertionError:
        return True
    return False


def main() -> int:
    results = []
    general_n.C = wrong_C
    results.append(("C_n with one extra 1/sqrt(pi)", breaks("identity", check.identity)))
    general_n.C = ORIG["C"]

    general_n.symanzik = wrong_symanzik
    results.append(("Kirchhoff polynomial in place of Symanzik", breaks("identity", check.identity)))
    general_n.symanzik = ORIG["symanzik"]

    feynman_hp.COTREES = ORIG["cotrees"][:-1]
    results.append(("one spanning tree missing from U", breaks("sectors", check.sectors)))
    feynman_hp.COTREES = ORIG["cotrees"]

    marked.f = wrong_f
    results.append(("hinge quadrature with the wrong elliptic map", breaks("hinge", check.hinge)))
    marked.f = ORIG["f"]

    marked.M = 3.0
    results.append(("hinge quadrature truncated at mu = 3", breaks("hinge", check.hinge)))
    marked.M = ORIG["M"]

    # the C program with interval merging switched off in the unordered mode
    src = (check.HERE / "unmarked.c").read_text()
    bad = src.replace("int mode = !strcmp(argv[1], \"marked\") ? 1 : !strcmp(argv[1], \"nomerge\") ? 2",
                      "int mode = !strcmp(argv[1], \"marked\") ? 1 : !strcmp(argv[1], \"unmarked\") ? 2")
    assert bad != src
    with tempfile.TemporaryDirectory() as d:
        c, b = pathlib.Path(d) / "u.c", pathlib.Path(d) / "u"
        c.write_text(bad)
        subprocess.run(["cc", "-O2", "-o", str(b), str(c), "-lm"], check=True)
        results.append(("unordered mode without merging the 30 intervals", breaks("qmc", lambda: check.qmc(b))))

    for name, killed in results:
        print(f"{'killed' if killed else 'SURVIVED'}: {name}")
    k = sum(killed for _, killed in results)
    print(f"{k}/{len(results)} mutants killed")
    return 0 if k == len(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
