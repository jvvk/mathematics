#!/usr/bin/env python3
"""Build a Lake library one module at a time, dependencies first, so at most one Lean process runs.
Usage: lake-serial <project_dir> <root_module> [more roots...]   (e.g. lake-serial . LeanProofs)
Plain `lake build` compiles independent modules in parallel and has no job limit; heavy files can
exhaust memory on a laptop (2026-11-19: ten case-split files, ~77 GB)."""
import os, re, subprocess, sys
from pathlib import Path

proj = Path(sys.argv[1]).resolve()
roots = sys.argv[2:]
deps: dict[str, list[str]] = {}

def path_of(mod: str) -> Path:
    return proj / (mod.replace(".", "/") + ".lean")

def visit(mod: str) -> None:
    if mod in deps or not path_of(mod).exists():
        return
    imps = re.findall(r"^import\s+(\S+)", path_of(mod).read_text(), re.M)
    deps[mod] = [m for m in imps if path_of(m).exists()]
    for m in deps[mod]:
        visit(m)

for r in roots:
    visit(r)
order, done = [], set()
def topo(m: str) -> None:
    if m in done:
        return
    done.add(m)
    for d in deps[m]:
        topo(d)
    order.append(m)
for m in deps:
    topo(m)
env = dict(os.environ, LEAN_NUM_THREADS="1")
for i, m in enumerate(order, 1):
    print(f"[{i}/{len(order)}] {m}", flush=True)
    # Lake's full output passes straight through; its exit status is preserved (a signal n becomes 128 + n),
    # so a caller can tell a Lean error (status 1) from a crash or a kill.
    r = subprocess.run(["nice", "-n", "15", "lake", "build", m], cwd=proj, env=env)
    if r.returncode != 0:
        print(f"FAIL {m} (lake exit {r.returncode})", file=sys.stderr, flush=True)
        sys.exit(128 - r.returncode if r.returncode < 0 else r.returncode)
print("build=0")
