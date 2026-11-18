import LeanProofs.Hankel456683.Defs
import LeanProofs.Hankel456683.Walks
import LeanProofs.Hankel456683.Step1
import LeanProofs.Hankel456683.Step2
import LeanProofs.Hankel456683.Step3
import LeanProofs.Hankel456683.Headline

/-!
# Hankel determinants of path generating functions (MO 456683, Johann Cigler)

`D_{k,n}(x,c) = det (a_{i+j,k}(x,c))_{0 ≤ i,j < n}` does not depend on `c` and equals
`det H_{k,n}(x)`, for all `k` and `n`, by the route of the answer: a binomial transform in `c`
(`D = det (L A Lᵀ)`), cutting paths after `i` steps (`A = P W`, `P` unitriangular), and
`W = H U` with `U` the unitriangular ballot matrix, by induction from the local identity (2).
The quadratic recurrence in the question is open and is not formalised.

* `Hankel456683.Defs`: `walk` (the question's recursion), `a`, `ciglerS`, `hankel`, `D`, `ciglerH`
  (verbatim), `hE` (closed form of the entries), `ballot`.
* `Hankel456683.Walks`: `walk_eq_zero_of_lt`, `walk_top`, `walk_add`, `walk_succ_left`, `T`,
  `walk_eq_pow`, `T_add_const`, `pow_add_algebraMap_apply`, `walk_add_const`.
* `Hankel456683.Step1`: `E`, `binomial_eq_E`, `L`, `det_L`, `hankel_binomial`,
  `det_hankel_add_const`, `D_indep`.
* `Hankel456683.Step2`: `P`, `W`, `det_P`, `hankel_eq_P_mul_W`, `det_hankel_eq_det_W`.
* `Hankel456683.Step3`: `ciglerH_eq`, `hE_col_zero`, `hE_succ_succ`, `hE_row_zero`,
  `local_identity`, `ballot_succ`, `walk_eq_sum_hE_ballot`, `U`, `det_U`, `W_eq_H_mul_U`,
  `det_W_eq_det_ciglerH`.
* `Hankel456683.Headline`: `D_eq_det_ciglerH`, `headline`, `headline_any_weights`, and the
  illustrations `ciglerH_two_six`, `D_one_three`.
-/
