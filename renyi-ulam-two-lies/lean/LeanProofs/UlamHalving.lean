import LeanProofs.UlamHalving.Basic
import LeanProofs.UlamHalving.Key
import LeanProofs.UlamHalving.Mono
import LeanProofs.UlamHalving.Padding
import LeanProofs.UlamHalving.Lemma2
import LeanProofs.UlamHalving.Lemma3
import LeanProofs.UlamHalving.Main
import LeanProofs.UlamHalving.Three

/-!
# Even splitting in the Renyi-Ulam game: optimal with two lies, not with three (MO 165093)

Formalised (namespace `UlamHalving`):
* `V_conserve`, `V_le`: conservation of volume and Berlekamp's bound.
* `Solv.mono`: deleting candidates never hurts.
* `padding`, `padding'`: last-class candidates can be added while the volume bound holds (Lemma 2.1).
* `lemma2`: many last-class candidates suffice, n >= 12 (Lemma 3.1).
* `lemma3`: the congruence criterion is sufficient for the halving child, depth >= 15 (Lemma 4.1).
* `key`: a winnable even parent forces the criterion (Section 5).
* `halving_child`, `halving_optimal`: Theorem 1.2 for parent depth >= 16.

Three lies (namespace `UlamHalving.Three`):
* `V_conserve`, `V_le`: the three-lie game, conservation of volume and Berlekamp's bound.
* `V_h`, `not_solv_105`: the halving child (A, A+26, 86, 60) of (2A, 52, 120, 0) has volume 2^105 - 28 but is not
  105-solvable (Theorem 1.3, losing half). The winning half (the parent is 106-solvable) is a certificate checked
  outside Lean.

Hypothesis, not formalised: `base12`, solvability at depth 12 of the positions (a, b, c) with a <= b,
c >= 66 and volume at most 2^12; checked with depths <= 15 by the paper's certificate.
-/
