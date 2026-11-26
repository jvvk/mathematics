import Mathlib

/-!
# Stanley's Problem 84: the elementary identities of the combinatorial proof

The note `commutator.tex` proves that for odd `n` the long cycle is a commutator `u v u⁻¹ v⁻¹` in exactly
`2n·n!/(n+1)` ways, through three counts `O_n`, `W_{n-1}`, `|F_n|`. This file formalises the elementary identities
the argument rests on, following the note:

* `choose_bridge` : the term-by-term identity of Lemma 3,
  `r s · C(i,r) C(i,s) = i² · C(i-1,r-1) C(i-1,s-1)` (from `C(i,r) = (i/r) C(i-1,r-1)`);
* `V_closed` : the endpoint count of Lemma 5, `∑_a C(n,a) C(n,n-a) a! (n-a)! = 2^n n!`;
* `endpoint_sign` : the two unpaired flags in the first count of Lemma 5 are both positive for odd `n`;
* `eliminate` : the final step, `(n+1) 2^(n+1) (n-1)! |F| = 4 n! 2^n n!` forces `(n+1) |F| = 2 n · n!`.

The sign-reversing involutions of Sections 4 and 5 and the Goupil–Schaeffer input are not formalised here.
-/

namespace Commutator84

open Finset

/-- Lemma 3, term by term: `i · C(i-1,r-1) = r · C(i,r)` for both factors. -/
theorem choose_bridge (i r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hi : 1 ≤ i) :
    r * s * (i.choose r * i.choose s) = i * i * ((i - 1).choose (r - 1) * (i - 1).choose (s - 1)) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 : (i' + 1) * i'.choose r' = (i' + 1).choose (r' + 1) * (r' + 1) := Nat.add_one_mul_choose_eq i' r'
  have h2 : (i' + 1) * i'.choose s' = (i' + 1).choose (s' + 1) * (s' + 1) := Nat.add_one_mul_choose_eq i' s'
  calc (r' + 1) * (s' + 1) * ((i' + 1).choose (r' + 1) * (i' + 1).choose (s' + 1))
      = ((i' + 1).choose (r' + 1) * (r' + 1)) * ((i' + 1).choose (s' + 1) * (s' + 1)) := by ring
    _ = ((i' + 1) * i'.choose r') * ((i' + 1) * i'.choose s') := by rw [h1, h2]
    _ = (i' + 1) * (i' + 1) * (i'.choose r' * i'.choose s') := by ring

/-- Lemma 5, the endpoint count: marked words of length `n` with `n` marks and ordered marks. -/
theorem V_closed (n : ℕ) :
    ∑ a ∈ range (n + 1), n.choose a * n.choose (n - a) * a.factorial * (n - a).factorial
      = 2 ^ n * n.factorial := by
  have key : ∀ a ∈ range (n + 1),
      n.choose a * n.choose (n - a) * a.factorial * (n - a).factorial = n.choose a * n.factorial := by
    intro a ha
    have ha' : a ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ha)
    rw [Nat.choose_symm ha']
    have := Nat.choose_mul_factorial_mul_factorial ha'
    calc n.choose a * n.choose a * a.factorial * (n - a).factorial
        = n.choose a * (n.choose a * a.factorial * (n - a).factorial) := by ring
      _ = n.choose a * n.factorial := by rw [this]
  rw [sum_congr rfl key, ← sum_mul, Nat.sum_range_choose]

/-- Lemma 5, first count: flag `L` at `n` has sign `+1` and flag `R` at `1` has sign `-(-1)^n = +1`
for odd `n`. -/
theorem endpoint_sign (n : ℕ) (hn : Odd n) : -((-1 : ℤ) ^ n) = 1 := by
  rw [hn.neg_one_pow]; norm_num

/-- The final step: combining the three identities of the note gives `(n+1)|F_n| = 2n · n!`. -/
theorem eliminate (n F : ℕ) (hn : 1 ≤ n)
    (h : (n + 1) * 2 ^ (n + 1) * (n - 1).factorial * F = 4 * n.factorial * (2 ^ n * n.factorial)) :
    (n + 1) * F = 2 * n * n.factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  rw [Nat.factorial_succ] at h
  have hpos : 0 < 2 ^ (m + 1) * 2 * m.factorial := by positivity
  have hl : (2 ^ (m + 1) * 2 * m.factorial) * ((m + 1 + 1) * F)
      = (m + 1 + 1) * (2 ^ (m + 1) * 2) * m.factorial * F := by ring
  have hr : (2 ^ (m + 1) * 2 * m.factorial) * (2 * (m + 1) * ((m + 1) * m.factorial))
      = 4 * ((m + 1) * m.factorial) * (2 ^ (m + 1) * ((m + 1) * m.factorial)) := by ring
  rw [Nat.factorial_succ]
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [hl, hr]; exact h)

end Commutator84
