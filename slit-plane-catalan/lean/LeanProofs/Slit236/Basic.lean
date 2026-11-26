import Mathlib

/-!
# Stanley's Problems 236–237 (walks on the slit plane): the finite identities of the combinatorial proofs

The note `slit.tex` proves the slit-plane Catalan formulas by cycle sorting of axis-to-axis pieces and
sign-reversing involutions. This file formalises the finite identities that the argument uses, following the note:

* `balanced_stop` : Lemma 5, the balanced-word count `∑_{k=1}^{r} 2·C(2r-k-1, r-1) = C(2r, r)`, written with
  `j = r - k` and `r = s + 1`;
* `return_count_step` : Lemma 5, `2r · C(2r-k, r) = 2 (2r-k) · C(2r-k-1, r-1)`, the step from the forest count to
  the stopping-time sums;
* `endpoint01` : Section 5, the elimination giving `a_{0,1}(2n+1) = H_n` from Corollary 7, Lemma 9, the closing
  step, Proposition 8 and the first-return split of `C_{2n+1}`;
* `binom_236d` : Section 6, `C(4n, 2n-2)/(2n) = C_{2n+1}/2 - C_{2n}` for `n ≥ 1`;
* `endpoint11` : Section 6, the elimination giving `2 a_{1,1}(2n) = H_n/2 + C_{2n}`;
* `cycle_weight_237d` and `count_237d` : Section 7, the decorated-bridge cycle weight equals `c_d(r, 2j)`, and the
  direct count of decorated bridges is `(i/n) C(2i,i) C(2n,n-i) 4^(n-i)`;
* `diagonal_sum`, `diag_237b` : Section 7, the diagonal closing step and 237(b) from 237(a).

Not formalised: the cycle sorting bijections (Lemma 3) and the counting formula (Lemma 4), the free-word count
`∑ 2^(k+1) C(2r-k-1, r-1) = 4^r` of Lemma 5, the marking argument and pair-splitting sum of Lemma 6, the
involutions of Proposition 8 and Lemma 9, and Shapiro's identity (cited: Hajnal and Nagy).
-/

namespace Slit236

open Finset

/-- Catalan numbers, `C n = C(2n, n)/(n+1)`, as rationals. -/
noncomputable def cat (n : ℕ) : ℚ := ((2 * n).choose n : ℚ) / (n + 1)

/-- Lemma 5, balanced words: with `r = s + 1` and `j = r - k`, the sum `∑_{k=1}^{r} 2·C(2r-k-1, r-1)` is
`∑_{j<r} 2·C(s+j, s)`, and it equals `C(2r, r)`. -/
theorem balanced_stop (s : ℕ) :
    ∑ j ∈ range (s + 1), 2 * (s + j).choose s = (2 * (s + 1)).choose (s + 1) := by
  have hock : ∑ j ∈ range (s + 1), (s + j).choose s = (2 * s + 1).choose (s + 1) := by
    have h1 := Nat.sum_Icc_choose (2 * s) s
    have h2 : Icc s (2 * s) = Ico s (2 * s + 1) := rfl
    rw [h2, Finset.sum_Ico_eq_sum_range] at h1
    have h3 : 2 * s + 1 - s = s + 1 := by omega
    rw [h3] at h1
    exact h1
  rw [← mul_sum, hock]
  have pascal : (2 * (s + 1)).choose (s + 1) = (2 * s + 1).choose s + (2 * s + 1).choose (s + 1) := by
    have : 2 * (s + 1) = (2 * s + 1) + 1 := by ring
    rw [this, Nat.choose_succ_succ]
  have symm : (2 * s + 1).choose s = (2 * s + 1).choose (s + 1) :=
    Nat.choose_symm_of_eq_add (by ring)
  rw [pascal, symm]; ring

/-- Lemma 5, the forest step: `(2r/(2r-k)) C(2r-k, r) = 2 C(2r-k-1, r-1)`, cleared of denominators, for
`1 ≤ k ≤ r`. -/
theorem return_count_step (r k : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) :
    2 * r * (2 * r - k).choose r = 2 * (2 * r - k) * (2 * r - k - 1).choose (r - 1) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, 2 * (r' + 1) - k = m + 1 := ⟨2 * (r' + 1) - k - 1, by omega⟩
  rw [hm]
  simp only [Nat.add_sub_cancel]
  have h := Nat.add_one_mul_choose_eq m r'
  calc 2 * (r' + 1) * (m + 1).choose (r' + 1) = 2 * ((m + 1).choose (r' + 1) * (r' + 1)) := by ring
    _ = 2 * ((m + 1) * m.choose r') := by rw [h]
    _ = 2 * (m + 1) * m.choose r' := by ring

/-- Section 5, proof of 236(a): with `T = C_{2n+1}` (Corollary 7), `P_{2n+2} = 2 C_{2n+1} + L_{2n}` (Lemma 9),
`P_{2n+2} = T + 2 a` (closing step), `L_{2n} = H - K` (Proposition 8) and `C_{2n+1} = H + K` (first return),
the walks to `(0,1)` number `H_n`. -/
theorem endpoint01 (a T P L H K C1 : ℤ) (hT : T = C1) (hP : P = 2 * C1 + L) (hclose : P = T + 2 * a)
    (hL : L = H - K) (hC : C1 = H + K) : a = H := by
  subst hT; linarith

/-- Section 6, the binomial identity of 236(d): `C(4n, 2n-2)/(2n) = C_{2n+1}/2 - C_{2n}` for `n ≥ 1`
(here `n = m + 1`). -/
theorem binom_236d (m : ℕ) :
    ((4 * (m + 1)).choose (2 * (m + 1) - 2) : ℚ) / (2 * (m + 1)) = cat (2 * m + 3) / 2 - cat (2 * m + 2) := by
  unfold cat
  have e1 : 2 * (m + 1) - 2 = 2 * m := by omega
  have e2 : 2 * (2 * m + 3) = 4 * m + 6 := by ring
  have e3 : 2 * (2 * m + 2) = 4 * m + 4 := by ring
  have e4 : 4 * (m + 1) = 4 * m + 4 := by ring
  rw [e1, e2, e3, e4]
  rw [Nat.cast_choose ℚ (by omega : 2 * m ≤ 4 * m + 4), Nat.cast_choose ℚ (by omega : 2 * m + 3 ≤ 4 * m + 6),
    Nat.cast_choose ℚ (by omega : 2 * m + 2 ≤ 4 * m + 4)]
  have f1 : 4 * m + 4 - 2 * m = 2 * m + 4 := by omega
  have f2 : 4 * m + 6 - (2 * m + 3) = 2 * m + 3 := by omega
  have f3 : 4 * m + 4 - (2 * m + 2) = 2 * m + 2 := by omega
  rw [f1, f2, f3]
  have g1 : (4 * m + 6).factorial = (4 * m + 6) * (4 * m + 5) * (4 * m + 4).factorial := by
    rw [show 4 * m + 6 = (4 * m + 5) + 1 by ring, Nat.factorial_succ,
      show 4 * m + 5 = (4 * m + 4) + 1 by ring, Nat.factorial_succ]; ring
  have g2 : (2 * m + 4).factorial = (2 * m + 4) * (2 * m + 3) * (2 * m + 2).factorial := by
    rw [show 2 * m + 4 = (2 * m + 3) + 1 by ring, Nat.factorial_succ,
      show 2 * m + 3 = (2 * m + 2) + 1 by ring, Nat.factorial_succ]; ring
  have g3 : (2 * m + 3).factorial = (2 * m + 3) * (2 * m + 2).factorial := by
    rw [show 2 * m + 3 = (2 * m + 2) + 1 by ring, Nat.factorial_succ]
  have g4 : (2 * m + 2).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, Nat.factorial_succ,
      show 2 * m + 1 = (2 * m) + 1 by ring, Nat.factorial_succ]; ring
  rw [g1, g2, g3]
  rw [g4]
  have hA : ((4 * m + 4).factorial : ℚ) ≠ 0 := by positivity
  have hB : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Section 6, proof of 236(d): from `C_{2n+1} = a_{2,0} + 2 a_{1,1}`, `a_{2,0} = c + K/2`,
`c = C_{2n+1}/2 - C_{2n}` and `C_{2n+1} = H + K`, one gets `2 a_{1,1} = H/2 + C_{2n}`. -/
theorem endpoint11 (a20 a11 c K H C1 C2 : ℚ) (hlast : C1 = a20 + 2 * a11) (hsort : a20 = c + K / 2)
    (hc : c = C1 / 2 - C2) (hsplit : C1 = H + K) : 2 * a11 = H / 2 + C2 := by
  linarith

/-- The forest count `F(k, e) = k/(2e+k) · C(2e+k, e)` of Lemma 5, as a rational. -/
noncomputable def forest (k e : ℕ) : ℚ := (k : ℚ) / (2 * e + k) * ((2 * e + k).choose e : ℚ)

/-- Section 7, 237(d): a cycle of decorated bridges with core semilength `j` and size `r` has weight
`h_j · 4^(r-j) · F(2j, r-j) = 4^r/(2r) · C(2r, r+j)`, which is the diagonal cyclic weight `c_d(r, 2j)`. -/
theorem cycle_weight_237d (r j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) :
    (4 : ℚ) ^ j / (2 * j) * 4 ^ (r - j) * forest (2 * j) (r - j)
      = 4 ^ r / (2 * r) * ((2 * r).choose (r + j) : ℚ) := by
  unfold forest
  have e : 2 * (r - j) + 2 * j = 2 * r := by omega
  have e' : ((2 * (r - j) : ℕ) : ℚ) + ((2 * j : ℕ) : ℚ) = 2 * r := by exact_mod_cast e
  have sym : (2 * r).choose (r - j) = (2 * r).choose (r + j) := Nat.choose_symm_of_eq_add (by omega)
  have hp : (4 : ℚ) ^ r = 4 ^ j * 4 ^ (r - j) := by rw [← pow_add]; congr 1; omega
  have hcast : (2 * ((r - j : ℕ) : ℚ) + ((2 * j : ℕ) : ℚ)) = 2 * r := by
    push_cast at e' ⊢; rw [Nat.cast_sub hjr] at e' ⊢; linarith
  rw [hcast, e, sym, hp]
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  push_cast
  field_simp

/-- Section 7, 237(d): the decorated bridges number `C(2i,i) F(2i, n-i) 4^(n-i) = (i/n) C(2i,i) C(2n,n-i) 4^(n-i)`. -/
theorem count_237d (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ((2 * i).choose i : ℚ) * forest (2 * i) (n - i) * 4 ^ (n - i)
      = (i : ℚ) / n * (2 * i).choose i * (2 * n).choose (n - i) * 4 ^ (n - i) := by
  unfold forest
  have e : 2 * (n - i) + 2 * i = 2 * n := by omega
  have hcast : (2 * ((n - i : ℕ) : ℚ) + ((2 * i : ℕ) : ℚ)) = 2 * n := by
    rw [Nat.cast_sub hin]; push_cast; ring
  rw [hcast, e]
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  push_cast
  field_simp

/-- Section 7, the diagonal closing step: `P^d_{n+1} = 4^(n+1) C_n = 2 b_{1,1} + 2 b_{-1,1}` gives
`b_{1,1} + b_{-1,1} = 2 · 4^n C_n`. -/
theorem diagonal_sum (n : ℕ) (P b11 bm11 Cn : ℚ) (hP : P = 4 ^ (n + 1) * Cn) (hclose : P = 2 * b11 + 2 * bm11) :
    b11 + bm11 = 2 * 4 ^ n * Cn := by
  rw [pow_succ] at hP; linarith

/-- 237(b) from the diagonal sum and 237(a), `b_{1,1}(2n+1) = C_{2n+1}`. -/
theorem diag_237b (n : ℕ) (b11 bm11 Cn C1 : ℚ) (hsum : b11 + bm11 = 2 * 4 ^ n * Cn) (ha : b11 = C1) :
    bm11 = 2 * 4 ^ n * Cn - C1 := by
  linarith

end Slit236
