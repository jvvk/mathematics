import LeanProofs.SimmonsPartial.Basic
import LeanProofs.SimmonsPartial.Total
import LeanProofs.SimmonsPartial.Ratio
import LeanProofs.SimmonsPartial.Shape
import LeanProofs.SimmonsPartial.Main
import LeanProofs.SimmonsPartial.Bridge

/-!
# Simmons partial sums for `Bin(n, m/n)` (Fokkink-Papavassiliou-Pelekis, Conjecture 4.1; MO 384456)

`X ~ Bin(n, m/n)`, `q = n - m`, `α_i = P(X ≤ m - i) - P(X ≥ m + i)`. Everything is scaled by `n ^ n`:
`w n m j = C(n, j) m^j q^(n-j)` and `A n m i = n ^ n α_i ∈ ℤ`.

Formalised (namespace `SimmonsPartial`):
* `adjacent`: `(j + 1) q w (j + 1) = (n - j) m w j`.
* `A_succ`: `A (i + 1) = A i + d i`, `d i = w (m + i) - w (m - i)` (second term absent for `i > m`). Step (1).
* `mean`, `total`: `E X = m` and `Σ_{i=1}^{q} A i = 0` for `n ≥ 2m`. Step (2).
* `A_last`: `A q = - w n` when `q > m`. Step (3).
* `ratio`, `factor`: the multiplicative ratio identity for `β_i = w (m + i) / w (m - i)` and
  `Q_i - P_i = (q - m)((q + m) i (i + 1) - m q)`. Step (4).
* `neg_start`, `d_step`: `d i < 0` while the factor at `i - 1` is `≤ 0`; once `d i ≥ 0` (`1 ≤ i`,
  `i + 1 < q`), `d (i + 1) > 0`. Step (5).
* `up`, `down`, `neg_persists`, `partial_pos`: the abstract shape argument. Step (6).
* `partial_sum_pos`: `Σ_{i=1}^{k} A i > 0` for `n > 2m ≥ 2`, `1 ≤ k < q`.
* `one_sign_change`, `neg_persists_A`: once `A i < 0` (`i ≥ 1`) it stays negative up to `q`, hence on `[1, m]`.
* `A_symm_zero`: for `n = 2m`, `A i = 0` for `i ≤ m + 1`.
* `conjecture`: Conjecture 4.1, `Σ_{i=1}^{k} A i ≥ 0` for `n ≥ 2m ≥ 2`, `1 ≤ k ≤ m`.
* `alpha_eq`: `P(X ≤ m - i) - P(X ≥ m + i) = A n m i / n ^ n` for the real pmf with `p = m / n`.
-/
