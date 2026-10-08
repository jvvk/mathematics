# Lean formalisation: Positivity of an alternating sum from random overlaps in C^N

Lean 4 (v4.34.0) with Mathlib `v4.34.0`. `L(u,a,b,n)` is defined in `Step1.lean` exactly as in
MathOverflow question 498232: the triple sum of factorials over the question's summation range. Every
theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`; `Audit.lean` prints the
axioms of each one when it is compiled.

## Build

```
lake exe cache get     # Mathlib build cache
lake build             # compiles every module and runs the axiom audit
./mutants.sh           # seventeen mutants, each rejected; ten unchanged controls, each compiled
```

## Where each result is

| Paper | Lean | File |
|---|---|---|
| Definition (1) of `L(u,a,b,n)`, with the question's ranges | `L`, `inRange`, `term` | `Step1.lean` |
| Proof of Theorem 1, Step 1 (factorials to binomials) | `term_eq`, `step1` | `Step1.lean` |
| Step 2 (the coefficient of `w^a z^b` in `α^s β^j`) | `coeff_alpha_beta`, `coeff_subst_ab` | `Series.lean` |
| Step 3 (a finite difference; the discrete Leibniz rule) | `leibniz`, `step3` | `Leibniz.lean` |
| Step 4 (geometric series; `(1-z)² - w² = (1-α)(1-β)`) | `subst_G`, `subst_H`, `coeff_H` | `Series.lean` |
| **Theorem 1** | `main` | `Main.lean` |
| Equations (3) and (4): the coefficients of `R^(u+1)` | `R_pow`, `coeff_R_pow` | `Coeffs.lean` |
| Corollary 2 (`L ≥ 0`; `L = 0` for odd `a`; `L > 0` exactly when `a` is even and `n ≥ a/2`) | `L_nonneg`, `L_odd`, `L_pos_iff` | `Corollaries.lean`, `Positivity.lean` |
| Corollary 3 (`G ≥ 0` for every real `N ≥ 1`) | `G_nonneg` | `Corollaries.lean` |
| Corollary 4 (Taylor's conjecture) and the degree `n - a/2` | `taylor` | `Taylor.lean` |
| The binomial-basis formula; Taylor's inner sums; Taylor's formula | `binomial_basis`, `inner_eq_Tinner`, `taylor_formula` | `Binomial.lean` |
| Hucht's ₃F₂ form, and its positivity for `μ + ν ≤ c` | `hucht_identity`, `hucht_pos` | `Hucht.lean` |
| Corollary 5 (the extreme case `n = a + b`) | `L_extreme` | `Corollaries.lean` |

Power series are Mathlib's `MvPowerSeries (Fin 2) ℚ`, with `w = X 0` and `z = X 1`; the substitution
`α = z - w`, `β = z + w` of Steps 2 and 4 is `MvPowerSeries.subst`.

Not formalised: Abdesselam's identity (2) relating the moment `G` to the numbers `L`. As in the paper,
Corollary 3 is stated for `G` defined by the right side of (2).

## Mutation tests

`./mutants.sh` copies one source file at a time, plants a single wrong change (a sign, a shift, an
exponent, a binomial, a parameter of the ₃F₂, the threshold of Corollary 2, the degree in Corollary 4)
and compiles the copy against the original earlier modules. All seventeen mutants are rejected, and
the ten unchanged copies compile.
