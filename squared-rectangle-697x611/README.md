# The 697 × 611 rectangle needs exactly fourteen squares

Write `f(m, n)` for the least number of integer-sided squares that tile an `m × n` rectangle. Scaling a tiling shows `f(tm, tn) ≤ f(m, n)`, and the minimal squaring conjecture says equality always holds. Answering the MathOverflow question [Tiling a rectangle with the smallest number of squares](https://mathoverflow.net/q/116382), Ed Pegg Jr [reported in 2017](https://mathoverflow.net/a/275053) that one possible counterexample remained among rectangles with sides at most 760: `697 × 611`, whose best known tiling used 17 squares, while `1394 × 1222` could be tiled with 16.

The note shows `f(697, 611) = 14` (Theorem 1). The fourteen squares have sides 371, 326, 285, 240, 172, 68, 41, 37, 35, 35, 34, 34, 33 and 4; the tiling is compound and uses equal squares, so catalogues of simple perfect squared rectangles miss it. The lower bound is a complete enumeration of squared rectangles with at most 13 squares through the electrical networks of Brooks, Smith, Stone and Tutte, generated as quadrangulations by plantri. The same enumeration reproduces every value of OEIS [A219158](https://oeis.org/A219158) (all sides up to 388) that is at most 14. So `697 × 611` is not a counterexample, and `1394 × 1222` also needs at most 14 squares.

Preprint v1, 9 October 2026, not peer reviewed. The tiling was first posted as a [MathOverflow answer](https://mathoverflow.net/a/515613) on 29 September 2026, with a picture in [minimal-squaring-697x611](https://github.com/jvvk/minimal-squaring-697x611); the lower bound is new here. Computer-certified: the lower bound rests on an exhaustive search, checked against the OEIS table and by a mutation test, with no Lean formalisation. The author used an AI tool (Claude, Anthropic) in this work, as described in the note, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, and `make_fig.py`, which checks cell by cell that the fourteen squares tile the rectangle before drawing it.
- `verify/`:
  - `sqrect.c`: reads quadrangulations from plantri, takes every edge as the pole, computes exact integer currents (verified by `L N = D b`), records the fewest squares for every reduced shape with sides up to 1500, and prints every tiling of `697 × 611` or `1394 × 1222`.
  - `run.sh [K]`: builds plantri 5.8 from `tools/plantri58.tar.gz` (Brinkmann and McKay, Apache 2.0) and runs the enumeration for every number of squares up to `K` (default 14). With `K = 13` it proves the lower bound; with `K = 14` it finds the tiling. About 25 seconds.
  - `check_a219158.py K`: compares the enumeration with the OEIS A219158 b-file (`b219158.txt`, CC BY-SA 4.0) for every `m ≤ n ≤ 388`.
  - `mutant.sh`: a version that drops networks with parallel edges must disagree with the OEIS table; it does, on 42,489 of 42,862 rectangles.
  - `verify_tiling.py`: rechecks a tiling found by the enumeration without network theory (area, then an explicit bottom-left placement).
  - `scaling_scan.py K`: looks for counterexamples to the minimal squaring conjecture within the enumeration.
  - `results/`: the 16-square run (59,312,272 quadrangulations, 543 s): every tiling of `697 × 611` and `1394 × 1222` it found, including Pegg's 16-square tiling as a positive control.

## Reproduce

A C compiler and Python 3.

```
cd verify
sh run.sh 14
python3 check_a219158.py 14            # 65,231 rectangles agree, 0 mismatches
sh mutant.sh                           # 42,489 mismatches: the mutant is caught
python3 verify_tiling.py "$(grep HIT out/hits_17.txt | head -1)"
cd ../paper && python3 make_fig.py && latexmk -pdf note.tex
```
