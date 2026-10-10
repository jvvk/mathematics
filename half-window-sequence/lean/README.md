# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the headline results, and the last runs the mutation tests: each plants one wrong
definition, hypothesis or constant and checks that the file no longer compiles.

| Paper | Lean (namespace `WindowSeq`) |
|---|---|
| The sequence and the window `W_n = [⌈n/2⌉, n)` | `Seq.lean`: `a`, `W`, `c` |
| Lemma 2 (the window identity), positivity, identity (1) | `Seq.lean`: `window`, `a_pos`, `one_le_c`, `window_c` |
| Lemma 3 (`s_n → ln 2`) | `Harm.lean`: `s`, `s_eq`, `tendsto_s` |
| Boundedness of `c_n` | `Limit.lean`: `c_bdd` |
| Identity (2) | `Limit.lean`: `error_eq` |
| The contraction argument | `Limit.lean`: `tendsto_zero_of_contract` |
| Theorem 1 | `Limit.lean`: `tendsto_c` |

`a 0 = 0` is a placeholder; the sequence starts at `a 1 = 1`. Lemma 3 uses Mathlib's
`Real.tendsto_harmonic_sub_log` (the harmonic numbers minus `log n` tend to Euler's constant). The
contraction lemma is stated for any bounded sequence and any `q < 1`; the theorem uses `q = 3/4`.

Not formalised: the numerical rate in Remark 4. Every result uses only propext, Classical.choice and
Quot.sound (axiom-validation.txt). The folder was compiled in an isolated build without the development
cache (build-validation.log).
