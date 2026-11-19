# The 697 × 611 rectangle needs exactly fourteen squares

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/squaring.svg" width="760" alt="697 × 611 in fourteen squares"></p>

<p align="center"><b>The rectangle needs exactly fourteen squares, not seventeen, so it is not a counterexample to the minimal squaring conjecture.</b><br><sub>Open problem settled · verified by computation · Complete enumeration, checked against OEIS</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Write `f(m, n)` for the least number of integer-sided squares that tile an `m × n` rectangle. Scaling a tiling shows `f(tm, tn) ≤ f(m, n)`, and the minimal squaring conjecture says equality always holds. Answering the MathOverflow question [Tiling a rectangle with the smallest number of squares](https://mathoverflow.net/q/116382), Ed Pegg Jr [reported in 2017](https://mathoverflow.net/a/275053) that one possible counterexample remained among rectangles with sides at most 760: `697 × 611`, whose best known tiling used 17 squares, while `1394 × 1222` could be tiled with 16.

The note shows `f(697, 611) = 14` (Theorem 1), and indeed `f(697t, 611t) = 14` for every `t`, since no rectangle similar to `697 × 611` can be tiled by 13 or fewer squares. The fourteen squares have sides 371, 326, 285, 240, 172, 68, 41, 37, 35, 35, 34, 34, 33 and 4; the tiling is compound and uses equal squares, so catalogues of simple perfect squared rectangles miss it. The lower bound is a complete enumeration of squared rectangles with at most 13 squares through the electrical networks of Brooks, Smith, Stone and Tutte, generated as quadrangulations by plantri. The same enumeration reproduces every value of OEIS [A219158](https://oeis.org/A219158) (all sides up to 388) that is at most 14. So `697 × 611` is not a counterexample, and `1394 × 1222` also needs at most 14 squares.

Preprint v2, 19 November 2026 (v1: 9 October 2026), not peer reviewed. **Version 2**, after a referee review by Codex (OpenAI): the search now tests similarity to `697 × 611` directly, so the lower bound covers every multiple, and it fails on any unresolved case or count mismatch; the helper scripts fail on missing input or disagreement; results are archived with reduced square sides. The tiling was first posted as a [MathOverflow answer](https://mathoverflow.net/a/515613) on 29 September 2026, with a picture in [minimal-squaring-697x611](https://github.com/jvvk/minimal-squaring-697x611); the lower bound is new here. Computer-certified: the lower bound rests on an exhaustive search, checked against the OEIS table and by a mutation test, with no Lean formalisation. The author used an AI tool (Claude, Anthropic) in this work, as described in the note, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, and `make_fig.py`, which checks cell by cell that the fourteen squares tile the rectangle before drawing it.
- `verify/`:
  - `sqrect.c`: reads quadrangulations from plantri, takes every edge as the pole, computes exact integer currents (verified by `L N = D b`), records the fewest squares for every reduced shape with sides up to 1500, and prints every tiling of a rectangle similar to `697 × 611` (any scale). It exits with an error if any exact check fails or a numerically singular case belongs to a connected network.
  - `run.sh [K]` (run with `bash`): builds plantri 5.8 from `tools/plantri58.tar.gz` (Brinkmann and McKay, Apache 2.0) and runs the enumeration for every number of squares up to `K` (default 14). It checks that `sqrect` reads every quadrangulation plantri writes, and fails if any rectangle similar to `697 × 611` is tiled by 13 or fewer squares. With `K = 14` it proves the lower bound at every scale and finds the two 14-square tilings, in about 20 seconds; `results/summary.txt` is the log of the run to `K = 16`.
  - `check_a219158.py K`: compares the enumeration with the OEIS A219158 b-file (`b219158.txt`, CC BY-SA 4.0) for every `m ≤ n ≤ 388`.
  - `mutant.sh`: a version that drops networks with parallel edges must disagree with the OEIS table (the script fails otherwise); it does, on 42,489 of 42,862 rectangles.
  - `verify_tiling.py`: rechecks a tiling found by the enumeration without network theory (area, then an explicit bottom-left placement).
  - `scaling_scan.py K`: looks for counterexamples to the minimal squaring conjecture within the enumeration.
  - `results/`: `summary.txt` (counts per number of squares up to 16, no failed or unresolved case), `hits_17.txt` (the two 14-square tilings) and `hits_19.txt` (the 16-square run, 59,312,272 quadrangulations: 241 tilings of `697 × 611` and Pegg's 16-square tiling of `1394 × 1222`, a positive control), with square sides reduced; `run_19.log` is the timing of the 16-square stage.

## Reproduce

A C compiler and Python 3.

```
cd verify
bash run.sh 14                         # PASS: nothing similar to 697 x 611 with <= 13 squares
python3 check_a219158.py 14            # 65,231 rectangles agree, 0 mismatches
bash mutant.sh                         # 42,489 mismatches: the mutant is caught
python3 verify_tiling.py "$(grep HIT out/hits_17.txt | head -1)"
cd ../paper && python3 make_fig.py && latexmk -pdf note.tex
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
