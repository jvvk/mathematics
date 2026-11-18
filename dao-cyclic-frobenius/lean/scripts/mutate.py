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
import os
import re
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


INFRA = re.compile(
    r"object file .* does not exist|unknown module prefix|unknown package|could not resolve import|"
    r"failed to (?:download|load)|toolchain .* not (?:found|installed)|shared librar|"
    r"exited with code (?:1[3-9]\d|2\d\d)|segmentation fault|No space left|Read-only file system|"
    r"Permission denied|Disk quota|I/O error|cannot write",
    re.IGNORECASE,
)
RESOURCE = re.compile(
    r"maximum recursion depth|maxRecDepth|heartbeat|deterministic\)? timeout|out of memory|stack overflow|"
    r"RecursionError|MemoryError",
    re.IGNORECASE,
)


# Python checks run through this runner, which records the type of the exception actually raised: only a failed
# assertion or a deliberate sys.exit counts as a rejection; any other exception (NameError, SyntaxError, a custom
# class, a bare Exception) exits PYEXC_RC and is reported as inconclusive. Assertion messages are never parsed.
PYEXC_RC = 98
PY_RUNNER = (
    "import runpy, sys, os\n"
    "p = sys.argv[1]; sys.argv = sys.argv[1:]; sys.path.insert(0, os.path.dirname(os.path.abspath(p)))\n"
    "try:\n    runpy.run_path(p, run_name='__main__')\n"
    "except AssertionError:\n    raise\n"
    "except SystemExit:\n    raise\n"
    "except BaseException as e:\n"
    "    sys.stderr.write('MUTATE-RUNNER exception type: ' + type(e).__name__ + '\\n'); sys.exit(%d)\n" % PYEXC_RC
)


def passes(check: Check, path: Path) -> tuple[bool, str]:
    args = list(check.cmd)
    if Path(args[0]).name.startswith("python") and "{file}" in args:  # wrap Python checks in the runner
        i = args.index("{file}")
        args = args[:i] + ["-c", PY_RUNNER] + args[i:]
    cmd = ["nice", "-n", "15", *[a.replace("{file}", str(path)) for a in args]]
    # Own process group, so a timeout can kill lake and every Lean child before the sources are restored.
    p = subprocess.Popen(cmd, cwd=check.cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         start_new_session=True)
    try:
        so, se = p.communicate(timeout=check.timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        p.communicate()
        return False, "INCONCLUSIVE timeout"
    r = subprocess.CompletedProcess(cmd, p.returncode, so, se)
    out = r.stdout + r.stderr
    if r.returncode < 0:
        return False, f"INCONCLUSIVE crash (signal {-r.returncode})"
    # Resource limits say nothing about the mutated claim: never count them as a rejection.
    res = RESOURCE.search(out)
    if res and r.returncode != 0:
        return False, f"INCONCLUSIVE resource limit ({res.group(0)})"
    # So do missing imports, .olean files or toolchains, even when Lean locates them in the mutated file.
    infra = INFRA.search(out)
    if infra and r.returncode != 0:
        return False, f"INCONCLUSIVE infrastructure ({infra.group(0)})"
    if r.returncode == PYEXC_RC and "MUTATE-RUNNER exception type: " in r.stderr:
        kind = r.stderr.rsplit("MUTATE-RUNNER exception type: ", 1)[1].split()[0]
        return False, f"INCONCLUSIVE python exception ({kind})"
    # A missing or non-executable tool (shell status 126/127) says nothing about the mutant.
    if r.returncode in (126, 127):
        return False, f"INCONCLUSIVE command not runnable (exit {r.returncode})"
    marked = [m for m in check.fail_markers if m in out]
    if r.returncode == 0 and not marked:
        return True, "exit 0"
    # A rejection needs a relevant diagnostic when the suite names one (e.g. a Lean "error"); any other failure is
    # inconclusive. The first diagnostic line is kept in the report so the log shows why the mutant failed.
    if check.fail_markers and not marked:
        return False, f"INCONCLUSIVE exit {r.returncode} without a {check.fail_markers[0]!r} diagnostic"
    line = next((ln.strip() for ln in out.splitlines() if marked and marked[0] in ln), "")
    return False, f"exit {r.returncode}" + (f", marker {marked[0]!r}: {line[:160]}" if marked else "")


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
    if not muts:
        print(f"no mutants selected (--only {a.only!r}); nothing was tested", file=sys.stderr)
        return 2
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
            unclear = why.startswith("INCONCLUSIVE")
            print(
                f"{'SURVIVED' if ok else ('INCONCLUSIVE' if unclear else 'rejected')}: {m.name}"
                + (f" ({why})" if not ok else "")
            )
            bad += ok or unclear
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
