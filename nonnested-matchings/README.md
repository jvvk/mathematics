# Non-nested matchings in ordered graphs: the cases k = 3 and k = 4 of the Barát–Freschi–Tóth conjecture

<!-- visual:start -->
<p align="center"><img src="visual.svg" width="760" alt="The three positions of two disjoint arcs (nested, crossing, separated), and the graph on 7 points with 14 arcs: K5 on 1 to 5 and the vertices 6, 7 joined to 1 and 2"></p>

<p align="center"><b>f<sub>3</sub>(n) = f*<sub>3</sub>(n) = 2n for n ≥ 6, f<sub>4</sub>(n) = 3n for n ≥ 8, and f*<sub>4</sub>(n) ≥ 3n + 1 for n ≥ 9: the conjecture holds exactly for k ≤ 4 in its plain form and for k ≤ 3 in its strong form.</b><br><sub>Conjecture 2.6 of Barát, Freschi and Tóth (arXiv:2512.15461), settled for every k together with de Castro (arXiv:2609.14484, k ≥ 5).</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Two disjoint edges of a graph on `[n]` are nested when one lies strictly inside the other. Let `f_k(n)` be the largest number of edges of an ordered graph on `[n]` with no `k` pairwise disjoint, pairwise non-nested edges, and `f*_k(n)` the same with only *strongly* non-nested matchings forbidden ("equal or crossing" an equivalence relation on the matching). Barát, Freschi and Tóth proved `(k−1)n ≤ f_k(n) ≤ f*_k(n) ≤ (k−1)n + C(k−1, 2)` and conjectured `f_k(n) = f*_k(n) = (k−1)n`; de Castro (arXiv:2609.14484) disproved this for every `k ≥ 5`.

This note proves `f_3(n) = f*_3(n) = 2n` for every `n ≥ 6` (Theorem 1) and `f_4(n) = 3n` for every `n ≥ 8` (Theorem 3), and shows that the strong form fails for `k = 4`: a graph on 9 vertices with 28 edges and no strongly non-nested 4-matching, extended to `3n + 1` edges for every `n ≥ 9` (Theorem 2). Both upper bounds study the equality case of the Barát–Freschi–Tóth count, in which the long edges complete a 2- or 3-triangulation. For `k = 4`, one star polygon of the 3-triangulation (Pilaud–Santos), placed next to a dense star of short edges, forces a non-nested 4-matching; when a few long edges are missing, several such stars are needed and a counting argument shows they cannot all be spoiled. Two finite configuration checks (Computations 1 and 2) are done by computer, each by two programs that share no code, with a lemma that reduces every `n` to the range checked.

Preprint v2, 26 November 2026 (v1: 25 November 2026), not peer reviewed; released before the author's line-by-line reading. Version 2 adds Theorem 3 (the plain form for `k = 4`, open in v1). Zenodo: [doi:10.5281/zenodo.24547648](https://doi.org/10.5281/zenodo.24547648) (v1: [doi:10.5281/zenodo.24543565](https://doi.org/10.5281/zenodo.24543565)), identical to this folder at the tag `nonnested-matchings-v2`.

AI use (credited by the steps each model originated; details in the paper): Codex (OpenAI) found the proof route of Theorem 1, the short-edge lemmas of Theorem 3 and the counting proofs for 17 and 18 short edges; Claude Opus 5.5 (Anthropic) found Theorem 2, the single-star method and two of the window lemmas for Theorem 3, ran the computations, wrote the Lean formalisation and drafted the text; Claude Fable 5.2 (Anthropic) checked every step independently, supplied one gap-filling argument, one weakened hypothesis and the far-vertex reduction, and wrote the independent recheck programs.

## Contents

- `paper/`: `nonnested.tex` and `nonnested.pdf`.
- `verify/` (Python 3 with `python-sat`; one C program). Each program exits nonzero if a claim fails; the certificate scripts refuse to run under `python3 -O`, which would strip their checks.
  - `values.py` with `fk.py`: every computed value stated in the note (f_3 and f*_3 for n = 6..11, f_4 for n = 8..13, f*_4 for n = 9..13, and the control f_5(11) = 45 from de Castro), each by a SAT instance at the value and an UNSAT instance one above. Output `values.out`.
  - `recheck_values.py`: the same values from a separate enumeration and solver, sharing no code. Output `recheck_values.out`.
  - `recheck_g9.py`: Theorem 2 without SAT: G9 and its extensions to n = 12 contain no strongly non-nested 4-matching. Output `recheck_g9.out`.
  - `k4_windows.py`: every certificate of Table 1 (Lemma 9, parts (a) to (f)) and of the exceptional arrangement in Lemma 12, for every n from 7 to 19, every admissible centre, all admissible edges and all star positions, without search; each long edge of a certificate is checked to be one of the six chords (4) of the star. Output `k4_windows.out`.
  - `k4_uncovered.py`: Computation 1. Enumerates all uncovered 16-edge families of span 8 to 13 by depth-first search, finds the 16 with both centre gaps at most 3, and checks the end-centre window for 0 to 7 free vertices on each side. Output `k4_uncovered.out`.
  - `k4_covered.py`: Computation 2. Enumerates the covered 16-edge families (gaps 1 to 16, ends cut off or with up to 7 free vertices) not handled by Lemma 9(c), its mirror image or Lemma 9(d): 15,984, each with a good window within distance 3 of a centre. Resumable with `--resume` (progress in `k4_covered_progress.tsv`, not shipped; a plain run starts from scratch). Output `k4_covered.out`. With `--list-only` it writes the identifiers of the 15,984 families to `k4_covered_list.tsv`.
  - `recheck_k4/`: Fable's independent programs. `run_recheck_covered.py` compiles and runs `recheck_covered.c` (Computation 2 in C; output `recheck_covered.out`, list `recheck_covered_list.tsv`), and `compare_lists.py` checks that the two lists of 15,984 families are identical (output `compare_lists.out`); `enum.py`, `make_small16.py`, `check3.py` redo Computation 1 with a different enumeration (outputs `enum.out`, `check3.out`).
  - `mutants.toml` with `mutate.py`: thirteen false variants of the stated values and claims; every one is rejected.
- `lean/`: a Lean 4 project pinned to the Mathlib version it was checked with; `lean/README.md` lists what is formalised (Theorems 1 and 2, Lemmas 4 and 5, and for Theorem 3 the window lemmas, the exceptional arrangement and the counting step) and the cited theorems that enter as hypotheses.

## Reproduce

```
cd verify
pip install python-sat
python3 values.py
python3 recheck_values.py
python3 recheck_g9.py
python3 k4_windows.py
python3 k4_uncovered.py
python3 k4_covered.py
python3 k4_covered.py --list-only
cd recheck_k4 && python3 run_recheck_covered.py && python3 compare_lists.py && python3 enum.py 3 && python3 make_small16.py && python3 check3.py 7 && cd ..
python3 mutate.py mutants.toml
cd ../lean && lake exe cache get && lake build && lake env lean CheckClaims.lean
cd ../paper && latexmk -pdf nonnested.tex
```

`values.py` takes about 10 minutes, `recheck_values.py` about 15, `k4_uncovered.py` about 10, `k4_covered.py` about an hour (resumable), the Computation 1 recheck about 7; the others under two minutes. The Lean mutation suite: `cd lean/scripts && python3 mutate.py mutants.toml`.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
