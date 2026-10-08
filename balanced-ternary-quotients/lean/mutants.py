"""Mutation tests: each mutant copies one proof file, plants a single wrong change and must fail to
compile. A control (an unchanged copy) must compile, so that a failure means the change was caught.

Run from lean/ after `lake build`:  python3 mutants.py     (one file at a time, about 20 minutes)
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "BalancedTernary"
sys.path.insert(0, str(HERE.parent / "verify"))
from reach import explore


def cert(n_a: int, n_b: int, k: int, name: str) -> str:
    """A theorem claiming a*3^k + b not in B/B, with its exact reachable carry set as certificate."""
    n = n_a * 3**k + n_b
    accept, S = explore(n)
    assert accept, "the planted claim must be false"
    b = f"+ {n_b}" if n_b > 0 else f"+ ({n_b})"
    return (
        f"theorem {name} : ¬ ∃ m N : Int, 0 < m ∧ ZF m ∧ 0 < N ∧ ZF N ∧ "
        f"N = ({n_a} * 3 ^ {k} {b}) * m :=\n  not_BB_of_cert _ {sorted(S)} (by decide)\n\n"
    )


def after(text: str, marker: str, old: str, new: str) -> str:
    """Replace the first occurrence of old after marker."""
    i = text.index(marker)
    assert old in text[i:], (marker, old)
    return text[:i] + text[i:].replace(old, new, 1)


def everywhere(text: str, old: str, new: str) -> str:
    assert old in text, old
    return text.replace(old, new)


def before(text: str, marker: str, insert: str) -> str:
    assert marker in text, marker
    return text.replace(marker, insert + marker, 1)


MUTANTS = [
    (
        "claim 8*3^k+19 instead of 8*3^k+17",
        "Fam_8_p17",
        lambda s: after(
            s, "theorem not_BB_8_p17 (k", "(8 * 3 ^ k + 17) * m", "(8 * 3 ^ k + 19) * m"
        ),
    ),
    (
        "claim 40*3^k+43 instead of 40*3^k+41",
        "Fam_40_p41_4r0",
        lambda s: after(
            s,
            "theorem not_BB_40_p41_4r0 (k",
            "(40 * 3 ^ k + 41) * m",
            "(40 * 3 ^ k + 43) * m",
        ),
    ),
    (
        "8*3^k-7: chain coefficient 10 changed to 11 throughout",
        "Fam_8_m7",
        lambda s: everywhere(s, "- 10 * 3 ^ i", "- 11 * 3 ^ i"),
    ),
    (
        "5*3^k+4: chain coefficient 2 changed to 5 throughout",
        "Fam_5_p4_4r0",
        lambda s: everywhere(
            s, "1 * 3 ^ k + 1 - 2 * 3 ^ i", "1 * 3 ^ k + 1 - 5 * 3 ^ i"
        ),
    ),
    (
        "extend 4*3^k-5 to k = 4",
        "Fam_4_m5",
        lambda s: before(s, "theorem not_BB_4_m5_k5", cert(4, -5, 4, "not_BB_4_m5_k4")),
    ),
    (
        "extend 5*3^k+4 to k = 4",
        "Fam_5_p4_4r0",
        lambda s: before(
            s, "theorem not_BB_5_p4_4r0_k8", cert(5, 4, 4, "not_BB_5_p4_4r0_k4")
        ),
    ),
    (
        "8*3^k+17: sporadic carry 8*3^(k-1)+6 shifted to +3",
        "Fam_8_p17",
        lambda s: everywhere(s, "8 * 3 ^ (k - 1) + 6", "8 * 3 ^ (k - 1) + 3"),
    ),
    (
        "claim 5*3^k+4 for k = 1 mod 4",
        "Fam_5_p4_4r0",
        lambda s: after(
            s, "theorem not_BB_5_p4_4r0 (k", "(hkr : k % 4 = 0)", "(hkr : k % 4 = 1)"
        ),
    ),
]


def compiles(name: str, text: str) -> bool:
    path = SRC / "Mutant.lean"
    path.write_text(text)
    try:
        r = subprocess.run(
            ["nice", "-n", "15", "lake", "env", "lean", str(path)],
            cwd=HERE,
            capture_output=True,
            text=True,
            timeout=1800,
        )
        return r.returncode == 0
    finally:
        path.unlink(missing_ok=True)


def main() -> None:
    ok = True
    control = (SRC / "Fam_4_p5.lean").read_text()
    if compiles("control", control):
        print("control (unchanged Fam_4_p5) compiles")
    else:
        print("CONTROL FAILED: the harness cannot compile an unchanged file")
        ok = False
    for name, target, mutate in MUTANTS:
        original = (SRC / f"{target}.lean").read_text()
        mutated = mutate(original)
        assert mutated != original
        if compiles(name, mutated):
            print("MUTANT SURVIVED:", name)
            ok = False
        else:
            print("rejected:", name)
    print("ALL MUTANTS REJECTED" if ok else "FAILURES ABOVE")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
