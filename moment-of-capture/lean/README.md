# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 -I scripts/mutate.py scripts/mutants.toml

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the headline results, and the last runs the mutation tests: each of six mutants plants
one wrong constant, hypothesis or definition and checks that the file no longer compiles (afterwards
`lake build LeanProofs` restores the build).

| Paper | Lean (namespace `FinchCapture`, file `LeanProofs/FinchCapture/Main.lean`) |
|---|---|
| The recurrence and the rule (1) | `xs`, `x`, `x_lt`, `x_rule` |
| Runs with `g` gaps, `G = ⌈(k-1)/4⌉`, capture point, pre-period | `Run`, `G` (written `(k + 2) / 4`), `IsCapture`, `IsPreperiod` |
| Finch's Lemma 17 and the block relations (3) | `run_zero`, `block`, `block_at` |
| Step 1 (the run starts late, `s ≥ 2k − 1`) | `start_late` |
| Steps 2 and 6 (the last block agrees, nothing disagrees afterwards) | `tail` |
| Steps 3 and 4 (the stretch before the run; no backward extension) | `no_extend` |
| Step 5 and the conclusion for one run | `capture_run` |
| Theorem 1 for `k ≥ 6` | `capture` |
| Theorem 1, the counterexample `k = 2` (`z = 9`, `μ = 0`) | `two_exception` |

Not formalised: the case `k = 3` (`z = 11`, `μ = 5`), which rests on `../verify/check_proof.py`. Every result
uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was compiled in an
isolated build without the development cache (build-validation.log).
