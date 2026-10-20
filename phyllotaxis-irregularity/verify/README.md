# Checks and records

Python 3 with SymPy and mpmath. Each `name.out` is the recorded output of `name.py` (or of a variant run noted in
its first lines). Times are on a laptop.

## Proof checks (reproduce in under a minute)

| Result | Script | What it checks |
|---|---|---|
| Lemma 4.4 (lattice order) | `static_lattice_order.py` | brute force over 47 front shapes: the lowest site above the front and the next gap |
| Theorem A, the (2,3) case | `static_23_proof.py` | exact first-order candidate table (SymPy) and the linear forms against exact slacks |
| Theorem A, all shapes | `static_general.py` | the window along rays for 26 shapes; 182 valid fronts agree with the simulator, invalid fronts skipped |
| Theorem A, the channel condition | `static_channel.py` | `μ_Z > 0` follows from validity; fails only when a second hinge is perturbed |
| Theorem A, independent nonlinear check | `review_independent.py` | 141 first-disk cases with a direct quadratic apex solver and exact affine-law closure; the four example histories of Table 1; ordered-field signs |
| Lemma 2.2, Lemma 7.3, the limiting tilings | `exact_limits.py`, `certify_limits.py` | candidate tables in exact rational arithmetic (ties are identities), and an interval-arithmetic recheck |
| Lemmas 3.2, 3.3 (rhombus and triangle steps) | `rhombic_step_formula.py`, `triangle_step_formula.py` | first-order formulas against exact geometry, with planted mutants |
| The two simulators | `simulators_agree.py` | `multi_step.py` and `independent_stack.py` give the same events disk for disk on the fronts of Table 1 |

## Explorations and records (not proofs)

- Section 7 burst, Conjecture C: `burst_exact.py` (first-order events in `Q(√3, √19)` with exact signs; reports 60
  unresolved clearance incidences), `burst_mp.py` + `mp_stack.py` (60-digit runs at `c = 0`), `burst_certify.py`,
  `step1_words.py`, `step2_words.py`, `step1_margins.py`, `lineage.py`.
- Section 8 ratio law: `break_probability.py`, `break_probability_consistent.py` (consistent seeds), `critical_ratio.py`,
  `multi_step.py`, `mismatch_law.py`, `kappa1_consistent.py`, `transition_scaling.py`, `tracking_irregularity.py`,
  `pentagon_margin.py`, `placement_margin.py`, `pentagon_anatomy.py`, `existence_vs_placement.py`, `local_existence.py`,
  `general_front_invariance.py`, `seed_convention.py`, `static_23.py`, `static_counterexample.py`.
- Figures: `pattern_figure.py` (Figure 1, from the simulator), `schematic_figures.py` (TikZ from the exact models).
- `review_simulator.py`: a third deterministic stacker used by `review_independent.py`.

## Open proof obligations

Uniform-in-`ε` control of the burst (Conjecture C), the transfer of the first-order event calculation to the
nonlinear dynamics, and the sharp value of the crossover ratio are open; finite samples here do not establish them.
