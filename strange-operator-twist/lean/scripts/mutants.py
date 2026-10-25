#!/usr/bin/env python3
"""Mutation tests for LeanProofs/StrangeOperator (Bogner strange operator): every wrong
variant must FAIL to check.

Each mutant copies one file to StrangeOperator/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""

import os
import pathlib
import re
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "StrangeOperator"
MUT = D / "Mut.lean"

MUTANTS = [
    (
        "L recurrence 5n^2 -> 4n^2",
        "Basic.lean",
        "    4 * (2 * n + 1) * (5 * n ^ 2 + 5 * n + 2) * u n - 48 * n",
        "    4 * (2 * n + 1) * (4 * n ^ 2 + 5 * n + 2) * u n - 48 * n",
    ),
    (
        "P recurrence 192 -> 191",
        "Basic.lean",
        "      - 192 * (2 * n - 1)",
        "      - 191 * (2 * n - 1)",
    ),
    (
        "c_p without the sign",
        "Basic.lean",
        "def cp (p : ℕ) : ℤ := jacobiSym 2 p * 2 ^ ((p - 1) / 2)",
        "def cp (p : ℕ) : ℤ := 2 ^ ((p - 1) / 2)",
    ),
    (
        "c_p^4 = 4^p",
        "Basic.lean",
        "cp p ^ 4 = 4 ^ (p - 1) := by",
        "cp p ^ 4 = 4 ^ p := by",
    ),
    (
        "odd weights without the power d",
        "Basic.lean",
        "  if k % 2 = 1 then jacobiSym 2 k ^ d * 2 ^ (d * (k - 1) / 2)",
        "  if k % 2 = 1 then jacobiSym 2 k * 2 ^ (d * (k - 1) / 2)",
    ),
    (
        "even k, odd d weight 1",
        "Basic.lean",
        "  else if d % 2 = 0 then 2 ^ (d * (k - 1) / 2) else 0",
        "  else if d % 2 = 0 then 2 ^ (d * (k - 1) / 2) else 1",
    ),
    (
        "binom(2p-2, p-2)",
        "Basic.lean",
        "p ∣ (2 * p - 2).choose (p - 1) :=",
        "p ∣ (2 * p - 2).choose (p - 2) :=",
    ),
    (
        "9 A33 = 5 + alpha",
        "Basic.lean",
        "((-114512 : ℤ) : ZMod 9) = 4",
        "((-114512 : ℤ) : ZMod 9) = 5",
    ),
    (
        "second condition 7 + 4 alpha",
        "Basic.lean",
        "¬ (4 + α = 0 ∧ 7 + 7 * α = 0)",
        "¬ (4 + α = 0 ∧ 7 + 4 * α = 0)",
    ),
]


def classify(returncode: int, output: str) -> str:
    if returncode < 0:
        return "CRASH"
    if re.search(
        r"maximum recursion depth|maxRecDepth|heartbeat|deterministic timeout|out of memory|stack overflow",
        output,
        re.IGNORECASE,
    ):
        return "RESOURCE"
    if re.search(
        r"object file .* does not exist|unknown module prefix|unknown package|failed to load|"
        r"could not resolve import|file not found",
        output,
        re.IGNORECASE,
    ):
        return "INFRA"  # an import failure is located in Mut.lean but says nothing about the mutation
    errors = re.findall(r"^(.+?):\d+:\d+:\s*error:", output, re.MULTILINE)
    diagnostics = [line for line in output.splitlines() if "error:" in line]
    local = (
        errors
        and len(errors) == len(diagnostics)
        and all((ROOT / f).resolve() == MUT.resolve() for f in errors)
    )
    if returncode == 1 and local:
        return "REJECTED"
    if returncode == 0 and "error:" not in output:
        return "ACCEPTED"
    return "INFRA"


def first_error(output: str) -> str:
    return next(
        (line for line in output.splitlines() if "error:" in line),
        next((line for line in output.splitlines() if line.strip()), "(no diagnostic)"),
    )


def check(text: str) -> tuple[str, str]:
    try:
        MUT.write_text(text)
        p = subprocess.Popen(
            ["taskpolicy", "-c", "background", "lake", "env", "lean", str(MUT)],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
    except OSError as e:
        return "INFRA", str(e)
    try:
        out, err = p.communicate(timeout=1200)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)  # lake's lean child too
        out, err = p.communicate()
        return "TIMEOUT", first_error(out + "\n" + err)
    output = out + "\n" + err
    return classify(p.returncode, output), first_error(output)


def main() -> int:
    bad = 0
    sel = [
        m for m in MUTANTS if not sys.argv[1:] or any(a in m[1] for a in sys.argv[1:])
    ]
    try:
        for f in sorted({m[1] for m in sel}):
            outcome, error = check((D / f).read_text())
            print(f"baseline {outcome}: {f}; {error}", flush=True)
            bad += outcome != "ACCEPTED"
        if bad:
            print(f"{bad} baseline problems; mutants not run")
            return 1
        for name, f, old, new in sel:
            src = (D / f).read_text()
            if src.count(old) != 1:
                print(f"MUTATION DID NOT APPLY: {name}", flush=True)
                bad += 1
                continue
            outcome, error = check(src.replace(old, new))
            print(f"{outcome}: {name}; {error}", flush=True)
            bad += outcome != "REJECTED"
    finally:
        MUT.unlink(missing_ok=True)
    print(f"{len(sel)} mutants, {bad} problems")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
