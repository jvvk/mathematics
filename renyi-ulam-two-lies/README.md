# Even splitting in the Rényi–Ulam game: optimal with two lies, not with three or more

<!-- visual:start -->
<p align="center"><img src="visual.svg" width="760" alt="An even position (2a, 2b, 0), a first question with its yes-child and no-child, and the halving child (a, a+b, b) as the midpoint of the two children; the two volumes differ from the halving child's by plus and minus delta"></p>

<p align="center"><b>From a position in which every class is even, asking about exactly half of each class is never beaten when up to two answers may be lies. With three or more lies it can be beaten.</b><br><sub>Pálvölgyi's conjecture proved for e = 2 and disproved for every e ≥ 3 · e = 2 above depth 15 and the e = 3 obstruction verified in Lean 4 · certificates checked by two independent programs</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

In the Rényi–Ulam game one finds an unknown element by yes-or-no questions, and up to `e` of the answers may be lies. A position records how many candidates are contradicted by `0, 1, ..., e` answers. Pálvölgyi asked on [MathOverflow 165093](https://mathoverflow.net/q/165093) (2014), and stated as the first conjecture of a note the same year, that from a position in which every class has even size it is always optimal to ask about exactly half of each class. He expected it to be false. The case `e = 1` follows from the work of Ellis, Ponomarenko and Yan. For two lies, Guzicki ([J. Combin. Theory Ser. A 54 (1990)](https://doi.org/10.1016/0097-3165(90)90002-E)) determined the number of questions needed from every starting position; two lemmas used here are his (padding, his Lemma 3.11, and a consequence of his Theorem 3.9), as the paper says where they are stated.

This note proves:

- **Theorem 1.2.** Let `e = 2`. If the position `(2a, 2b, 2c)` can be won in `n` questions, then its halving child `(a, a+b, b+c)` can be won in `n − 1`. In particular even splitting is optimal at every even position with at least two candidates.
- **Theorem 1.3.** Let `e = 3` and `a = (2^105 − 153920)/198592 = 204262101229170061472237061`. The even position `(2a, 52, 120, 0)` can be won in 106 questions, and its halving child `(a, a+26, 86, 60)` cannot be won in 105. So the even-splitting question costs 107 questions, while the first question `(a, 25, 112, 0)` wins in 106.
- **Corollary 7.2.** The conjecture is false for every `e ≥ 3`: put `e − 3` empty classes in front of these positions; they stay empty, and the game is the three-lie game move for move.

Above depth 15 the proof is a congruence argument: the halving child is the midpoint of the two children of any first question, whether it can be won is decided by a single congruence modulo `gcd(n − 2, C(n − 2, 2))` for a parent at depth `n`, and moving from the midpoint to either child shifts the volume and the last class by amounts that agree modulo that number and are too small to differ by a multiple of it. Depths up to 15 are settled by a certificate of 645 integers.

For three lies the halving child above has volume `2^105 − 28`, so the volume bound does not exclude 105 questions. The obstruction sits two questions deep: the first question's yes-volume modulo `C(104, 2) = 5356` leaves only two possibilities for `(w, t + λ)`, where `w`, `t` are its last two coordinates and `λ` the yes-child's slack, and in each one child then fails the analogous condition modulo 103 (it needs a remainder of 69 but has only 35 to spare). The question `(a, 25, 112, 0)` keeps the two volumes equal (`C(105, 2) = 105 · 52`) but moves 52 candidates of the last class from one child to the other, and both children can then be won; this is certified by 2,126 explicit questions. No smaller counterexample was found: none among even positions whose halving child has at most 100 candidates, and none among even positions winnable in at most 20 questions (one exact frontier computation, checked against the independent solver in 674 comparisons, reported as evidence only). The smallest counterexample remains open, for `e = 3` and every larger `e`.

Preprint v2, 24 November 2026 (v1: 24 November 2026), not peer reviewed, and released before the author's line-by-line reading. Version 2 adds the three-lie counterexample (Theorem 1.3, Section 7) and its Lean formalisation; the two-lie result is unchanged. Zenodo: v2 [doi:10.5281/zenodo.24526533](https://doi.org/10.5281/zenodo.24526533), identical to tag `renyi-ulam-two-lies-v2`; v1 [doi:10.5281/zenodo.24505094](https://doi.org/10.5281/zenodo.24505094) (tag `renyi-ulam-two-lies-v1`); all versions [doi:10.5281/zenodo.24505093](https://doi.org/10.5281/zenodo.24505093). The author used AI tools in this work (Codex, OpenAI, found the two-lie proof and certificate and the three-lie counterexample with its certificate; Claude, Anthropic, checked both, wrote the independent checkers, the frontier computation, the Lean formalisation and the text), as the paper's Section 8 describes, and is responsible for its content.

## Contents

- `paper/`: `ulam.tex`, `ulam.pdf`.
- `verify/` (Python 3 and a C compiler). Both programs exit nonzero if a checked value differs.
  - `verify_proof.py`: checks the certificate `base_frontiers.json` (the frontiers `B_0, ..., B_15`) through the frontier recurrence of Section 6, the 44 boundary cases of Lemma 3.1 at depth 12, and Theorem 1.2 at depths up to 15. Output `verify_proof.out`.
  - `recheck_frontiers.py`: an independent recheck sharing no code. It compiles `liar.c`, an exact solver that searches the game tree from the definitions of a position and a question, reproduces all 645 certificate values, agrees with Zare's seven published values from the MathOverflow comments, and checks Table 1 and the introduction's example. Output `recheck_frontiers.out`.
  - `search/`: logs of the halving searches (`liar 2 300` and `liar 3 100`), evidence quoted in Section 7.
  - `three-lies/` (Python 3 only, no packages): the counterexample of Theorem 1.3.
    - `counter_certificate.json`: 2,126 rows `[n, x0, x1, x2, x3, q0, q1, q2, q3]`, each a position at depth `n` and a winning first question.
    - `verify_counterexample.py` (Codex): replays the certificate and checks the two-level obstruction. Output `verify_counterexample.out`.
    - `claude_check_counterexample.py` (Claude): an independent checker sharing no code; it recomputes every number Section 7 states, enumerates every `(w, t, λ)` allowed at the first level from the game's definition, and replays the certificate. Output `claude_check_counterexample.out`.
    - `mutants_codex.toml`, `mutants_claude.toml`: planted errors (a changed root question, deleted rows, wrong residues); each checker rejects all of them (`mutation-codex.log`, `mutation-claude.log`).
    - `front3.c`, `front3.log`: the exact frontier computation of Section 7 for depths up to 20 (exits nonzero if it finds a violation).
    - `validate_front3.py`, `validate_front3.out`: compares `front3` with `../liar.c`'s direct game-tree search on random positions, at the least winning depth and one below (674 comparisons, all agree).
    - `run_check.py`: the mutation suites' entry point; only a failed assertion counts as a rejection, any other exception as a crash.
- `lean/`: a Lean 4 project pinned to the Mathlib version it was checked with; `lean/README.md` lists what is formalised, for two lies and for three, and the one hypothesis that is not.

## Reproduce

```
cd verify
python3 verify_proof.py
python3 recheck_frontiers.py
cc -O2 -o liar liar.c && ./liar 2 300 && ./liar 3 100
cd three-lies && python3 verify_counterexample.py && python3 claude_check_counterexample.py
cc -O2 -o front3 front3.c && ./front3 20 && python3 validate_front3.py && cd ..
cd ../lean && lake exe cache get && lake build && lake env lean CheckClaims.lean
cd ../paper && latexmk -pdf ulam.tex
```

`verify_proof.py` and the two three-lie checkers take seconds, `recheck_frontiers.py` a few minutes, `front3 20` about half an hour; the two searches take much longer and only reproduce the logs in `verify/search/`. The Lean mutation suite: `cd lean/scripts && python3 mutate.py mutants.toml`; the checker suites: `cd verify/three-lies && python3 ../../lean/scripts/mutate.py mutants_claude.toml` (and `mutants_codex.toml`).

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
