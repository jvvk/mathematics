import LeanProofs.SimmonsPartial.Basic

/-!
# Steps (4) and (5): the ratio identity and the sign pattern of `d`

With `β_i = w (m + i) / w (m - i)` (so `β_0 = 1` and `d i < 0 ↔ β_i < 1` for `i ≤ m`), the adjacent-mass
identity gives, without division,

  `q² (m - i)(m + i + 1) w(m+i+1) w(m-i) = m² (q - i)(q + i + 1) w(m+i) w(m-i-1)`,

that is `β_{i+1} / β_i = Q_i / P_i` with `P_i = q² (m - i)(m + i + 1)`, `Q_i = m² (q - i)(q + i + 1)`, and

  `Q_i - P_i = (q - m)((q + m) i (i + 1) - m q)`.

The factor `n i (i + 1) - m q` (note `q + m = n`) increases with `i` and is negative at `i = 0`. Hence
`β` falls strictly from `β_0 = 1` while the factor is `≤ 0` (`neg_start`), so `d i < 0` there, and once
`d i ≥ 0` for some `i ≥ 1` the factor is already positive and `β` rises strictly from then on (`d_step`).
For `i > m`, `d i = w (m + i) > 0` while `m + i ≤ n`.
-/

namespace SimmonsPartial

/-- **Step (4), ratio identity** (multiplicative form, `q = n - m`). -/
theorem ratio (n m i : ℕ) (hi : i < m) (hmn : m ≤ n) :
    (n - m) ^ 2 * (m - i) * (m + i + 1) * w n m (m + i + 1) * w n m (m - i) =
      m ^ 2 * (n - m - i) * (n - m + i + 1) * w n m (m + i) * w n m (m - i - 1) := by
  have h1 := adjacent n m (m + i)
  have h2 := adjacent n m (m - i - 1)
  rw [show m - i - 1 + 1 = m - i by omega, show n - (m - i - 1) = n - m + i + 1 by omega] at h2
  rw [show n - (m + i) = n - m - i by omega] at h1
  calc _ = ((m + i + 1) * (n - m) * w n m (m + i + 1)) * ((m - i) * (n - m) * w n m (m - i)) := by ring
    _ = ((n - m - i) * m * w n m (m + i)) * ((n - m + i + 1) * m * w n m (m - i - 1)) := by rw [h1, h2]
    _ = _ := by ring

/-- **Step (4), the factor.** `Q_i - P_i = (q - m)((q + m) i (i + 1) - m q)`. -/
theorem factor (m q i : ℤ) :
    m ^ 2 * (q - i) * (q + i + 1) - q ^ 2 * (m - i) * (m + i + 1) = (q - m) * ((q + m) * i * (i + 1) - m * q) := by
  ring

lemma QP_le {n m i : ℕ} (hi : i < m) (hn : 2 * m < n) (hF : n * i * (i + 1) ≤ m * (n - m)) :
    m ^ 2 * (n - m - i) * (n - m + i + 1) ≤ (n - m) ^ 2 * (m - i) * (m + i + 1) := by
  have hfac := factor (m : ℤ) ((n : ℤ) - m) i
  have h2m : (2 * m : ℤ) < n := by exact_mod_cast hn
  have hF' : (n : ℤ) * i * (i + 1) ≤ m * ((n : ℤ) - m) := by
    have := (Nat.cast_le (α := ℤ)).2 hF; push_cast [show m ≤ n by omega] at this; linarith
  have hneg : ((n : ℤ) - m - m) * ((n - m + m) * i * (i + 1) - m * (n - m)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  zify [hi.le, show m ≤ n by omega, show i ≤ n - m by omega]
  linarith

lemma QP_lt {n m i : ℕ} (hi : i < m) (hn : 2 * m < n) (hF : n * i * (i + 1) < m * (n - m)) :
    m ^ 2 * (n - m - i) * (n - m + i + 1) < (n - m) ^ 2 * (m - i) * (m + i + 1) := by
  have hfac := factor (m : ℤ) ((n : ℤ) - m) i
  have h2m : (2 * m : ℤ) < n := by exact_mod_cast hn
  have hF' : (n : ℤ) * i * (i + 1) < m * ((n : ℤ) - m) := by
    have := (Nat.cast_lt (α := ℤ)).2 hF; push_cast [show m ≤ n by omega] at this; linarith
  have hneg : ((n : ℤ) - m - m) * ((n - m + m) * i * (i + 1) - m * (n - m)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  zify [hi.le, show m ≤ n by omega, show i ≤ n - m by omega]
  linarith

lemma PQ_lt {n m i : ℕ} (hi : i < m) (hn : 2 * m < n) (hF : m * (n - m) < n * i * (i + 1)) :
    (n - m) ^ 2 * (m - i) * (m + i + 1) < m ^ 2 * (n - m - i) * (n - m + i + 1) := by
  have hfac := factor (m : ℤ) ((n : ℤ) - m) i
  have h2m : (2 * m : ℤ) < n := by exact_mod_cast hn
  have hF' : m * ((n : ℤ) - m) < (n : ℤ) * i * (i + 1) := by
    have := (Nat.cast_lt (α := ℤ)).2 hF; push_cast [show m ≤ n by omega] at this; linarith
  have hpos : 0 < ((n : ℤ) - m - m) * ((n - m + m) * i * (i + 1) - m * (n - m)) :=
    mul_pos (by linarith) (by linarith)
  zify [hi.le, show m ≤ n by omega, show i ≤ n - m by omega]
  linarith

/-- From `P a e = Q c b` and `Q c < P e`, `a < b`. -/
lemma cmp_lt {P Q a b c e : ℕ} (h : P * a * e = Q * c * b) (h2 : Q * c < P * e) (hb : 0 < b) : a < b := by
  have h3 : Q * c * b < P * e * b := mul_lt_mul_of_pos_right h2 hb
  rw [← h] at h3
  have h4 : (P * e) * a < (P * e) * b := by
    calc (P * e) * a = P * a * e := by ring
      _ < P * e * b := h3
  exact lt_of_mul_lt_mul_left h4 (Nat.zero_le _)

/-- From `P a e = Q c b` and `P e < Q c`, `b < a`. -/
lemma cmp_gt {P Q a b c e : ℕ} (h : P * a * e = Q * c * b) (h2 : P * e < Q * c) (hb : 0 < b) : b < a := by
  have h3 : P * e * b < Q * c * b := mul_lt_mul_of_pos_right h2 hb
  rw [← h] at h3
  have h4 : (P * e) * b < (P * e) * a := by
    calc (P * e) * b < P * a * e := h3
      _ = (P * e) * a := by ring
  exact lt_of_mul_lt_mul_left h4 (Nat.zero_le _)

/-- **Step (5a).** While the factor at `i - 1` is `≤ 0`, `β_i < 1`: `w (m + i) < w (m - i)`. -/
theorem neg_start {n m : ℕ} (hm : 1 ≤ m) (hn : 2 * m < n) (i : ℕ) (hi1 : 1 ≤ i) (him : i ≤ m)
    (hF : n * (i - 1) * i ≤ m * (n - m)) : w n m (m + i) < w n m (m - i) := by
  have wp : ∀ j, j ≤ n → 0 < w n m j := fun j hj => w_pos (by omega) (by omega) hj
  induction i, hi1 using Nat.le_induction with
  | base =>
    have h := ratio n m 0 (by omega) (by omega)
    have hQP := QP_lt (n := n) (m := m) (i := 0) (by omega) hn (by rw [mul_zero, zero_mul]; exact Nat.mul_pos (by omega) (by omega))
    have hce : w n m (m + 0) = w n m (m - 0) := by simp
    have := cmp_lt h (by rw [hce]; exact mul_lt_mul_of_pos_right hQP (wp _ (by omega))) (wp _ (by omega))
    simpa using this
  | succ i hi ih =>
    have ih' := ih (by omega) (le_trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)) hF)
    have h := ratio n m i (by omega) (by omega)
    have hQP := QP_le (n := n) (m := m) (i := i) (by omega) hn (by simpa using hF)
    have hQ : 0 < m ^ 2 * (n - m - i) * (n - m + i + 1) :=
      Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (by omega)) (by omega)
    have := cmp_lt h (lt_of_lt_of_le (mul_lt_mul_of_pos_left ih' hQ) (Nat.mul_le_mul_right _ hQP))
      (wp _ (by omega))
    rwa [show m - i - 1 = m - (i + 1) by omega, show m + i + 1 = m + (i + 1) by omega] at this

/-- **Step (5b).** Once `d i ≥ 0` at some `1 ≤ i` with `i + 1 < q`, `d (i + 1) > 0`. -/
theorem d_step {n m : ℕ} (hm : 1 ≤ m) (hn : 2 * m < n) {i : ℕ} (hi : 1 ≤ i) (hiq : i + 1 < n - m)
    (hd : 0 ≤ d n m i) : 0 < d n m (i + 1) := by
  have wp : ∀ j, j ≤ n → 0 < w n m j := fun j hj => w_pos (by omega) (by omega) hj
  by_cases him : i + 1 ≤ m
  · have hdi : d n m i = (w n m (m + i) : ℤ) - w n m (m - i) := by simp [d, show i ≤ m by omega]
    have hdi1 : d n m (i + 1) = (w n m (m + (i + 1)) : ℤ) - w n m (m - (i + 1)) := by simp [d, him]
    have hge : w n m (m - i) ≤ w n m (m + i) := by rw [hdi] at hd; omega
    have hF : ¬ (n * (i - 1) * i ≤ m * (n - m)) := fun h =>
      absurd (neg_start hm hn i hi (by omega) h) (not_lt.2 hge)
    push Not at hF
    have hF' : m * (n - m) < n * i * (i + 1) :=
      lt_of_lt_of_le hF (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega))
    have h := ratio n m i (by omega) (by omega)
    have hPQ := PQ_lt (n := n) (m := m) (i := i) (by omega) hn hF'
    have := cmp_gt h (lt_of_lt_of_le (mul_lt_mul_of_pos_right hPQ (wp _ (by omega)))
      (Nat.mul_le_mul_left _ hge)) (wp _ (by omega))
    rw [show m - i - 1 = m - (i + 1) by omega, show m + i + 1 = m + (i + 1) by omega] at this
    rw [hdi1]; omega
  · have : d n m (i + 1) = w n m (m + (i + 1)) := by simp [d, him]
    rw [this]; exact_mod_cast wp _ (by omega)

end SimmonsPartial
