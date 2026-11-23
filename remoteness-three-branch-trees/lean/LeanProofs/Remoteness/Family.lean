import Mathlib

/-!
# Lemma 4.3 of the note: a three-branch tree for `D = (L, p, h^m)` loses to a starlike or two-branch tree

Branch vertices `x - y - z`, joined by the segments `L` (from `x` to `y`) and `p` (from `y` to `z`); `x, y, z` carry
`a, b, c` pendant segments of length `h`, with `a, c ≥ 2`, `b ≥ 1`, `m = a + b + c`, `N = L + p + m h`,
`f t = t (N - t)`. The leaves at `x` and `z` have values `X` and `Z` (eq. (1) of the note). The two-branch tree with
joining segment `L`, carrying `p` and `m - r` segments `h` at one end and `r` at the other, has value `H r`
(Lemma 2.3). We prove `X + Z = f L + f p + 2 f h` and that some admissible `H r` (with `2 ≤ r ≤ m - 1`), or the
starlike value `f L`, is strictly below `(X + Z) / 2`; hence `C(T) ≥ max X Z > R(D)`.

The nearest integer `j` to `r₀ = (f h + f L - f p) / (2 L h)` of the note is `⌊(K + L h) / (2 L h)⌋` with
`K = f h + f L - f p`: then `|2 L h j - K| ≤ L h`.
-/

namespace Remoteness.Family

variable (L p h a b c : ℤ)

/-- `m`, `N` and `f` for `D = (L, p, h^m)` with `m = a + b + c`. -/
def m : ℤ := a + b + c
def N : ℤ := L + p + m a b c * h
def f (t : ℤ) : ℤ := t * (N L p h a b c - t)

/-- Leaf values at the two end branch vertices (eq. (1)). -/
def X : ℤ := f L p h a b c h + L * (p + (b + c) * h) + p * c * h
def Z : ℤ := f L p h a b c h + p * (L + (a + b) * h) + L * a * h

/-- Value of the two-branch tree: `p` and `m - r` copies of `h` at one end of `L`, `r` copies at the other. -/
def H (r : ℤ) : ℤ := max (f L p h a b c p + L * r * h) (f L p h a b c h + L * (p + (m a b c - r) * h))

theorem X_add_Z : X L p h a b c + Z L p h a b c =
    f L p h a b c L + f L p h a b c p + 2 * f L p h a b c h := by
  simp only [X, Z, f, N, m]; ring

/-- `f h > L h`, the inequality used twice in the note. -/
lemma Lh_lt_fh (hh : 1 ≤ h) (hp : h ≤ p) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 2 ≤ c) :
    L * h < f L p h a b c h := by
  simp only [f, N, m]
  have : L < L + p + (a + b + c) * h - h := by nlinarith
  nlinarith

/-- **Lemma 4.3** (model form). -/
theorem three_branch_loses (hh : 1 ≤ h) (hp : h ≤ p) (hL : p ≤ L) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 2 ≤ c) :
    (∃ r : ℤ, 2 ≤ r ∧ r ≤ m a b c - 1 ∧ 2 * H L p h a b c r < X L p h a b c + Z L p h a b c) ∨
      2 * f L p h a b c L < X L p h a b c + Z L p h a b c := by
  set K := f L p h a b c h + f L p h a b c L - f L p h a b c p with hK
  have hLh : 0 < L * h := by nlinarith
  have h2 : 0 < 2 * (L * h) := by linarith
  set r := (K + L * h) / (2 * (L * h)) with hr
  -- `|2 L h r - K| ≤ L h`.
  have hlo : 2 * (L * h) * r ≤ K + L * h := by
    have := Int.ediv_mul_le (K + L * h) (ne_of_gt h2); linarith [mul_comm (2 * (L * h)) r]
  have hhi : K + L * h < 2 * (L * h) * (r + 1) := by
    have := Int.lt_ediv_add_one_mul_self (K + L * h) h2
    nlinarith [mul_comm (2 * (L * h)) (r + 1)]
  -- `K` in closed form: `K = 2 L h + (m - 1) h (L - p + h)`.
  have hKc : K = 2 * (L * h) + (m a b c - 1) * h * (L - p + h) := by
    simp only [hK, f, N, m]; ring
  -- The two pieces of `H r` sum to `f L + f p + f h` and differ by `2 L h r - K`.
  have hsum : (f L p h a b c p + L * r * h) + (f L p h a b c h + L * (p + (m a b c - r) * h)) =
      f L p h a b c L + f L p h a b c p + f L p h a b c h := by
    simp only [f, N, m]; ring
  have hdiff : (f L p h a b c p + L * r * h) - (f L p h a b c h + L * (p + (m a b c - r) * h)) =
      2 * (L * h) * r - K := by
    simp only [hK, f, N, m]; ring
  have hHr : 2 * H L p h a b c r ≤ f L p h a b c L + f L p h a b c p + f L p h a b c h + L * h := by
    simp only [H]
    rcases le_total (f L p h a b c p + L * r * h) (f L p h a b c h + L * (p + (m a b c - r) * h)) with hle | hle
    · rw [max_eq_right hle]; linarith
    · rw [max_eq_left hle]; linarith
  have hXZ := X_add_Z L p h a b c
  have hfh := Lh_lt_fh L p h a b c hh hp ha hb hc
  -- `r ≥ 1` because `r₀ > 1`, and `r ≤ m - 1` because `r₀ ≤ (m + 1) / 2`.
  have hm : 5 ≤ m a b c := by simp only [m]; linarith
  have hr1 : 1 ≤ r := by
    by_contra hcon
    push_neg at hcon
    have : r ≤ 0 := by linarith
    have hK2 : 2 * (L * h) ≤ K := by
      rw [hKc]; have : 0 ≤ (m a b c - 1) * h * (L - p + h) := by
        apply mul_nonneg; apply mul_nonneg <;> linarith; linarith
      linarith
    nlinarith
  have hrm : r ≤ m a b c - 1 := by
    by_contra hcon
    push_neg at hcon
    have hKup : K ≤ (m a b c + 1) * (L * h) := by
      rw [hKc]
      have : (m a b c - 1) * h * (L - p + h) ≤ (m a b c - 1) * (L * h) := by
        have : h * (L - p + h) ≤ L * h := by nlinarith
        nlinarith
      linarith
    nlinarith
  rcases eq_or_lt_of_le hr1 with hr_eq | hr_gt
  · -- `r = 1`: the starlike tree wins, since `f L < H 1`.
    right
    have : f L p h a b c L < H L p h a b c r := by
      simp only [H]
      apply lt_of_lt_of_le _ (le_max_right _ _)
      rw [← hr_eq]
      have : f L p h a b c h + L * (p + (m a b c - 1) * h) = f L p h a b c L + f L p h a b c h - L * h := by
        simp only [f, N, m]; ring
      linarith
    linarith
  · left
    exact ⟨r, by linarith, hrm, by linarith⟩

end Remoteness.Family
