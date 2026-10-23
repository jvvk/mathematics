#!/usr/bin/env python3
"""Run a mutation suite: every planted error must make the check FAIL, and every untouched control must PASS.

    python3 -I mutate.py <suite.toml> [--only <substring>] [--list]

Works for Lean files (compile the copy) and Python verify scripts (run the copy). Single process, nice 15,
one timeout per check. Exit 0 only when all controls pass and all mutants are rejected.

Suite format (paths relative to the suite file's directory unless absolute):

    [check]
    cmd = ["lake", "env", "lean", "{file}"]   # {file} = the mutated copy
    cwd = ".."                                # where cmd runs (Lean: the Lake project root)
    timeout = 900                             # seconds per check
    mode = "copy"                             # copy: write <stem>Mut<suffix> beside the source (default)
                                              # inplace: mutate the source itself, restored afterwards
    fail_markers = ["error"]                  # stdout/stderr text that also counts as failure

    [[mutant]]
    name = "bound 1/3 instead of 1/2"
    file = "../LeanProofs/AcuteRadial.lean"
    old = "acute a b c ≤ 1 / 2 := by"       # must occur exactly once in the file
    new = "acute a b c ≤ 1 / 3 := by"
"""

from __future__ import annotations

import argparse
import signal
import subprocess
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path


@dataclass
class Check:
    cmd: list[str]
    cwd: Path
    timeout: int
    mode: str
    fail_markers: list[str]


@dataclass
class Mutant:
    name: str
    file: Path
    old: str
    new: str


def load(suite: Path) -> tuple[Check, list[Mutant]]:
    raw = tomllib.loads(suite.read_text())
    base = suite.parent
    c = raw["check"]
    check = Check(
        cmd=list(c["cmd"]),
        cwd=(base / c.get("cwd", ".")).resolve(),
        timeout=int(c.get("timeout", 900)),
        mode=c.get("mode", "copy"),
        fail_markers=list(c.get("fail_markers", [])),
    )
    if check.mode not in {"copy", "inplace"}:
        sys.exit(f"unknown mode {check.mode!r}")
    muts = [
        Mutant(m["name"], (base / m["file"]).resolve(), m["old"], m["new"])
        for m in raw.get("mutant", [])
    ]
    if not muts:
        sys.exit("suite has no [[mutant]] entries")
    return check, muts


def target(check: Check, src: Path) -> Path:
    return (
        src if check.mode == "inplace" else src.with_name(f"{src.stem}Mut{src.suffix}")
    )


def passes(check: Check, path: Path) -> tuple[bool, str]:
    cmd = ["nice", "-n", "15", *[a.replace("{file}", str(path)) for a in check.cmd]]
    try:
        r = subprocess.run(
            cmd, cwd=check.cwd, capture_output=True, text=True, timeout=check.timeout
        )
    except subprocess.TimeoutExpired:
        return False, "timeout"
    out = r.stdout + r.stderr
    marked = [m for m in check.fail_markers if m in out]
    return r.returncode == 0 and not marked, f"exit {r.returncode}" + (
        f", marker {marked[0]!r}" if marked else ""
    )


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("suite", type=Path)
    ap.add_argument("--only", help="run only mutants whose name contains this")
    ap.add_argument("--list", action="store_true")
    a = ap.parse_args()
    check, muts = load(a.suite.resolve())
    if a.only:
        muts = [m for m in muts if a.only in m.name]
    if a.list:
        for m in muts:
            print(f"{m.name}  ({m.file.name})")
        return 0

    originals = {m.file: m.file.read_text() for m in muts}
    backups: dict[Path, Path] = {}
    if check.mode == "inplace":
        for f, text in originals.items():
            bak = f.with_name(f.name + ".mutate-backup")
            if bak.exists():
                sys.exit(
                    f"{bak} exists: a previous run was interrupted. Restore the source from it first."
                )
            bak.write_text(text)
            backups[f] = bak

    def restore(*_: object) -> None:
        for f, text in originals.items():
            if check.mode == "inplace":
                f.write_text(text)
                backups[f].unlink(missing_ok=True)
            else:
                target(check, f).unlink(missing_ok=True)

    signal.signal(signal.SIGTERM, lambda *_: (restore(), sys.exit(143)))
    bad = 0
    try:
        for f, text in originals.items():
            t = target(check, f)
            t.write_text(text)
            ok, why = passes(check, t)
            print(
                f"{'control passes' if ok else 'CONTROL FAILS'}: {f.name}"
                + ("" if ok else f" ({why})")
            )
            if not ok:
                print(
                    "Fix the baseline first: a suite whose control fails proves nothing."
                )
                return 1
        for m in muts:
            text = originals[m.file]
            n = text.count(m.old)
            if n != 1 or m.old == m.new:
                print(f"SETUP ERROR ({n} matches): {m.name}")
                bad += 1
                continue
            t = target(check, m.file)
            t.write_text(text.replace(m.old, m.new))
            ok, why = passes(check, t)
            print(
                f"{'SURVIVED' if ok else 'rejected'}: {m.name}"
                + (f" ({why})" if not ok else "")
            )
            bad += ok
            if check.mode == "inplace":
                m.file.write_text(text)
    finally:
        restore()
    print(
        f"{len(muts) - bad}/{len(muts)} mutants rejected"
        + ("" if bad else ", all controls pass")
    )
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
