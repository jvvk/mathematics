# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the results below, and the last runs the 21 mutation tests: each plants a wrong count,
sign, rate, Jacobian entry or root interval and checks that the file no longer compiles.

| Paper | Lean |
|---|---|
| Section 5: the mass-action system of the seven-reaction network, as transcribed from its reaction list (a comment; reactions are not formalised) | `ZeroOneFour.lean`: `ZeroOneFour.f_from_network` |
| Section 5: Jacobian entries are the partial derivatives; the determinant | `ZeroOneFour.lean`: `jac_partials`, `det_jac` |
| Section 5: positive steady states lie on the rational curve | `ZeroOneFour.lean`: `on_curve` |
| Section 5: exactly four positive steady states, in the stated rational intervals, with `det Df` signs `−, +, −, +` | `ZeroOneFour.lean`: `ZeroOneFour.main` |
| Theorem 6.1: the eight-reaction system as transcribed, reaction by reaction, from the reaction list (the list is a comment; reactions are not formalised); partials; determinant | `ZeroOneFive.lean`: `ZeroOneFive.f_from_network`, `jac_partials`, `det_jac` |
| Theorem 6.1: the rational curve and the determinant identity at roots of the eliminant | `ZeroOneFive.lean`: `on_curve`, `detJ_root` |
| Theorem 6.1: exactly five positive steady states with signs `−, +, −, +, −` | `ZeroOneFive.lean`: `ZeroOneFive.main` |

Not formalised: the dichotomy (Theorem 2.1) and its corollaries, whose barrier and Brouwer-degree steps are
proved by hand in Sections 3 and 4 from standard degree theory; the stability counts (exact Routh–Hurwitz
certificates in `verify/`); and the minimality of seven reactions for four states, which rests on Tang and
Zhang's classification. Every result above uses only Lean's standard axioms (axiom-validation.txt). The folder
was compiled in an isolated build without the development cache (build-validation.log).
