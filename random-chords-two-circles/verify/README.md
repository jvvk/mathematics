Ancillary checks for "Random Chords of Two Circles and a Third Centre". The mathematical proofs are complete without these checks.

    python run_all.py

- `check_lemma.py`: finite-difference offset Jacobians at 1,200 points, the four-gap identity and an overlapping-circle control that must violate the disjoint-circle identity.
- `check_theorem.py`: exact rational second-moment identity used by Lemma 3, plus the fourth moment as an extra check; the axial centre classification; direct geometric simulations; and the equal-radius integral against Dan's dilogarithm expression to 40 digits.
- `check_extensions.py`: 2,400 inverse angular determinants checked by finite differences; 1,296 exact rational support/second-moment comparisons; 1,125 exact rational off-axis checks and 12 direct geometric angular quadratures; the general-ratio integral compared with six independent two-dimensional angular grids, nesting and the equal-radius specialisation.
- Deliberate false variants must each fail with AssertionError: `check_theorem.py --mutant moment|case|gp|constant` (wrong second moment, wrong case condition, radii off the progression, wrong dilogarithm coefficient) and `check_extensions.py --mutant inverse|weights|offaxis|hit` (wrong sign in the reversed Jacobian, support endpoint alone as invariant, wrong sign of the off-axis linear term, missing upper threshold in H(r)). With the overlap control in `check_lemma.py`, nine false variants in all; `run_all.py` runs them.

Requires Python 3, numpy and mpmath. Seeds are fixed. Approximate grid and simulation checks are numerical evidence, not exact proofs. The off-axis necessary condition is not a sufficiency claim.
