import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals

/-!
  Step 3 of the paper: the discrete Leibniz rule for the forward difference
  `Δ g q = g (q + 1) - g q` on functions `ℕ → ℚ`, and the identity it gives for `c_{s,j}`.
-/

namespace Abdesselam

open Finset

/-- `Δ^[n]` on `ℕ → ℚ`. -/
abbrev D (n : ℕ) (f : ℕ → ℚ) : ℕ → ℚ := (fwdDiff 1)^[n] f

theorem D_add (n : ℕ) (F G : ℕ → ℚ) : D n (F + G) = D n F + D n G := by
  induction n generalizing F G with
  | zero => rfl
  | succ n ih =>
    simp only [D, Function.iterate_succ_apply, fwdDiff_add] at ih ⊢
    exact ih _ _

theorem D_succ (n : ℕ) (f : ℕ → ℚ) : D (n + 1) f = D n (fwdDiff 1 f) :=
  Function.iterate_succ_apply _ _ _

theorem D_succ' (n : ℕ) (f : ℕ → ℚ) : D (n + 1) f = fwdDiff 1 (D n f) :=
  Function.iterate_succ_apply' _ _ _

theorem D_shift (n : ℕ) (f : ℕ → ℚ) (x : ℕ) : D n (fun q ↦ f (q + 1)) x = D n f (x + 1) :=
  fwdDiff_iter_comp_add 1 f 1 n x

/-- The discrete Leibniz rule: `Δ^n (f g)(x) = Σ_r C(n,r) Δ^r g(x) Δ^(n-r) f(x+r)`. -/
theorem leibniz (n : ℕ) : ∀ (f g : ℕ → ℚ) (x : ℕ),
    D n (fun q ↦ f q * g q) x =
      ∑ r ∈ range (n + 1), (n.choose r : ℚ) * D r g x * D (n - r) f (x + r) := by
  induction n with
  | zero => intro f g x; simp [D]; ring
  | succ n ih =>
    intro f g x
    have hsplit : fwdDiff 1 (fun q ↦ f q * g q) =
        (fun q ↦ f (q + 1) * fwdDiff 1 g q) + (fun q ↦ fwdDiff 1 f q * g q) := by
      funext q; simp only [fwdDiff, Pi.add_apply]; ring
    rw [D_succ, hsplit, D_add, Pi.add_apply, ih, ih]
    simp only [D_shift, ← D_succ]
    -- Pascal's rule recombines the two sums
    set A := ∑ r ∈ range (n + 1), (n.choose r : ℚ) * D (r + 1) g x * D (n - r) f (x + r + 1)
    set B := ∑ r ∈ range (n + 1), (n.choose r : ℚ) * D r g x * D (n - r + 1) f (x + r)
    have hB : B = ∑ r ∈ range n, (n.choose (r + 1) : ℚ) * D (r + 1) g x * D (n - r) f (x + r + 1)
        + D 0 g x * D (n + 1) f x := by
      simp only [B]
      rw [sum_range_succ']
      congr 1
      · refine sum_congr rfl fun r hr ↦ ?_
        have : n - (r + 1) + 1 = n - r := by have := mem_range.1 hr; omega
        rw [this, add_assoc]
      · simp
    rw [hB, sum_range_succ' _ (n + 1)]
    simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib]
    rw [sum_range_succ (fun r ↦ (n.choose (r + 1) : ℚ) * _ * _), Nat.choose_succ_self]
    have e1 : ∀ r ∈ range (n + 1), (n.choose r : ℚ) * D (r + 1) g x * D (n + 1 - (r + 1)) f (x + (r + 1))
        = (n.choose r : ℚ) * D (r + 1) g x * D (n - r) f (x + r + 1) := by
      intro r _; rw [Nat.add_sub_add_right, add_assoc]
    have e2 : ∀ r ∈ range n, (n.choose (r + 1) : ℚ) * D (r + 1) g x * D (n + 1 - (r + 1)) f (x + (r + 1))
        = (n.choose (r + 1) : ℚ) * D (r + 1) g x * D (n - r) f (x + r + 1) := by
      intro r _; rw [Nat.add_sub_add_right, add_assoc]
    rw [sum_congr rfl e1, sum_congr rfl e2]
    simp only [A, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, add_zero,
      Nat.sub_zero]
    ring

theorem D_zero_fun (k : ℕ) : D k (fun _ ↦ (0 : ℚ)) = fun _ ↦ 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [D_succ', ih]; exact fwdDiff_const 1 0

/-- `Δ^r` of `q ↦ C(q+m, s)` (Pascal's rule, iterated). -/
theorem D_choose (r m s q₀ : ℕ) :
    D r (fun q ↦ (((q + m).choose s : ℕ) : ℚ)) q₀ =
      if r ≤ s then (((q₀ + m).choose (s - r) : ℕ) : ℚ) else 0 := by
  split_ifs with h
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [D, fwdDiff_iter_comp_add 1 (fun x ↦ ((x.choose (r + t) : ℕ) : ℚ)) m r q₀,
      fwdDiff_iter_choose t r, Nat.add_sub_cancel_left]
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.1 h)
    have h1 : D (s + 1) (fun q ↦ (((q + m).choose s : ℕ) : ℚ)) = fun _ ↦ 0 := by
      rw [D_succ']
      funext q
      have := congrFun (show D s (fun q ↦ (((q + m).choose s : ℕ) : ℚ)) = fun q ↦ (1 : ℚ) from by
        funext q; have := D_choose_aux s m q; simpa using this) 
      simp [fwdDiff, this]
    have : s + t + 1 = t + (s + 1) := by omega
    rw [this, D, Function.iterate_add_apply]
    change D t (D (s + 1) (fun q ↦ (((q + m).choose s : ℕ) : ℚ))) q₀ = 0
    rw [h1, D_zero_fun]
where
  D_choose_aux (s m q : ℕ) : D s (fun q ↦ (((q + m).choose s : ℕ) : ℚ)) q = 1 := by
    rw [D, fwdDiff_iter_comp_add 1 (fun x ↦ ((x.choose s : ℕ) : ℚ)) m s q]
    have := congrFun (fwdDiff_iter_choose (R := ℚ) 0 s) (q + m)
    simpa using this

/-- Step 3: the inner sum `c_{s,j}` of Step 1 equals the alternating form `Δ^ν(fg)(0)` with
`f q = C(u+q+s, s)` and `g q = C(u+q+j, j)`. Here `n + ν = s + j`. -/
theorem step3 (u ν s j n : ℕ) (hn : n + ν = s + j) :
    ∑ i ∈ range (n + 1), (if n ≤ i + s ∧ i ≤ j then
        (ν.choose (j - i) : ℚ) * ((u + j).choose i : ℚ) * ((u + s + j - i).choose (n - i) : ℚ)
      else 0) =
    ∑ p ∈ range (ν + 1), (-1 : ℚ) ^ p * (ν.choose p : ℚ) * ((u + ν - p + s).choose s : ℚ) *
      ((u + ν - p + j).choose j : ℚ) := by
  set f : ℕ → ℚ := fun q ↦ (((q + (u + s)).choose s : ℕ) : ℚ)
  set g : ℕ → ℚ := fun q ↦ (((q + (u + j)).choose j : ℕ) : ℚ)
  -- the alternating form is Newton's formula for `Δ^ν (f g) (0)`
  have hN : D ν (fun q ↦ f q * g q) 0 = ∑ p ∈ range (ν + 1), (-1 : ℚ) ^ p * (ν.choose p : ℚ) *
      ((u + ν - p + s).choose s : ℚ) * ((u + ν - p + j).choose j : ℚ) := by
    rw [D, fwdDiff_iter_eq_sum_shift, ← sum_range_reflect]
    refine sum_congr rfl fun p hp ↦ ?_
    have hp := mem_range.1 hp
    have e : ν - (ν + 1 - 1 - p) = p := by omega
    simp only [f, g, zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast, zero_add, smul_eq_mul, mul_one, e]
    have e2 : ν + 1 - 1 - p + (u + s) = u + ν - p + s := by omega
    have e3 : ν + 1 - 1 - p + (u + j) = u + ν - p + j := by omega
    have e4 : ν.choose (ν + 1 - 1 - p) = ν.choose p := by
      rw [show ν + 1 - 1 - p = ν - p by omega, Nat.choose_symm (by omega)]
    rw [e2, e3, e4]; ring
  -- the Leibniz form, reindexed by `i = j - r`
  rw [← hN, leibniz]
  simp only [g, f, D_choose, zero_add]
  have hR : ∀ x ∈ range (ν + 1), ((ν.choose x : ℚ) * if x ≤ j then (((u + j).choose (j - x) : ℕ) : ℚ)
        else 0) * (if ν - x ≤ s then (((x + (u + s)).choose (s - (ν - x)) : ℕ) : ℚ) else 0) =
      if x ≤ j ∧ ν - x ≤ s then (ν.choose x : ℚ) * ((u + j).choose (j - x) : ℚ) *
        ((x + (u + s)).choose (s - (ν - x)) : ℚ) else 0 := by
    intro x _; split_ifs <;> simp_all
  rw [sum_congr rfl hR, ← sum_filter, ← sum_filter]
  refine sum_nbij' (fun i ↦ j - i) (fun r ↦ j - r) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_filter, mem_range] at hi ⊢; omega
  · intro r hr; simp only [mem_filter, mem_range] at hr ⊢; omega
  · intro i hi; simp only [mem_filter, mem_range] at hi; omega
  · intro r hr; simp only [mem_filter, mem_range] at hr; omega
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    have e1 : j - (j - i) = i := by omega
    have e2 : j - i + (u + s) = u + s + j - i := by omega
    have e3 : s - (ν - (j - i)) = n - i := by omega
    rw [e1, e2, e3]

end Abdesselam
