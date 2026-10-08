/-
  Joint descent multiplicities and the diagonal reduction (Remark 4.1 of the paper).

  The multiplicity is the actual number of permutations with the two specified descent sets.
  Inclusion-exclusion and the proved flag-pair orbit correspondence identify its factorial
  multiple with the inner product of two signed flag characters. Finite Cauchy-Schwarz then
  proves beta(S,T)^2 <= beta(S,S) beta(T,T), and a largest multiplicity occurs on the diagonal.
  This does not prove Gessel's conjecture about which diagonal entry is largest.
-/
import LeanProofs.Stanley.RibbonChar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Stanley

open Finset Equiv
open scoped Nat

/-- The actual joint descent multiplicity beta_n(S,T), with zero-indexed descent sets. -/
def beta (n : ℕ) (S T : Finset ℕ) : ℕ :=
  ((univ : Finset (Perm (Fin n))).filter
    (fun w => descP w = S ∧ descP w⁻¹ = T)).card

@[simp] theorem beta_alternating (n : ℕ) : beta n (Alt.altS n) (Alt.altS n) = Alt.g n := rfl

/-- Positive multiplicity means that the descent pair actually occurs. -/
theorem beta_pos_iff_mem_pairs (n : ℕ) (S T : Finset ℕ) :
    0 < beta n S T ↔ (S, T) ∈ pairs n := by
  simp only [beta, Finset.card_pos, Finset.nonempty_def, Finset.mem_filter,
    Finset.mem_univ, true_and, pairs, Finset.mem_image, Prod.mk.injEq]

namespace Alt

/-- The signed flag character belonging to an arbitrary prescribed descent set. -/
def ribbonCharacter (n : ℕ) (S : Finset ℕ) (w : Perm (Fin n)) : ℤ :=
  ∑ U ∈ S.powerset, (-1 : ℤ) ^ U.card * (flagChar n (S \ U) w : ℤ)

@[simp] theorem ribbonCharacter_alternating (n : ℕ) (w : Perm (Fin n)) :
    ribbonCharacter n (altS n) w = ψ n w := rfl

/-- The joint multiplicities form a Gram matrix, scaled by n!. -/
theorem beta_mul_factorial_eq (n : ℕ) (S T : Finset ℕ) :
    (beta n S T : ℤ) * n ! =
      ∑ w : Perm (Fin n), ribbonCharacter n S w * ribbonCharacter n T w := by
  have hR : (beta n S T : ℝ) = ∑ U ∈ S.powerset, ∑ V ∈ T.powerset,
      (-1 : ℝ) ^ (U.card + V.card) * (Nat.card (FQ n (S \ U) (T \ V)) : ℝ) := by
    rw [beta, joint_descent_count]
    refine Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun V _ => ?_
    rw [card_joint_eq_orbits]
  have hinner : ∑ w : Perm (Fin n), ribbonCharacter n S w * ribbonCharacter n T w =
      ∑ U ∈ S.powerset, ∑ V ∈ T.powerset,
        (-1 : ℤ) ^ (U.card + V.card) *
          ((Nat.card (FQ n (S \ U) (T \ V)) * n ! : ℕ) : ℤ) := by
    simp_rw [ribbonCharacter, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun V _ => ?_
    rw [← flagChar_inner, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    push_cast
    rw [pow_add]
    ring
  have : ((beta n S T : ℤ) * n ! : ℝ) =
      ((∑ w : Perm (Fin n), ribbonCharacter n S w * ribbonCharacter n T w : ℤ) : ℝ) := by
    rw [hinner]
    push_cast
    rw [hR, Finset.sum_mul]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun V _ => ?_
    ring
  exact_mod_cast this

end Alt

/-- **Diagonal reduction (Remark 4.1).** Finite Cauchy-Schwarz for the actual counts. -/
theorem beta_sq_le_diagonal (n : ℕ) (S T : Finset ℕ) :
    beta n S T ^ 2 ≤ beta n S S * beta n T T := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Perm (Fin n)))
    (Alt.ribbonCharacter n S) (Alt.ribbonCharacter n T)
  simp_rw [pow_two] at h
  rw [← Alt.beta_mul_factorial_eq, ← Alt.beta_mul_factorial_eq,
    ← Alt.beta_mul_factorial_eq] at h
  have hp : (0 : ℤ) < (n ! : ℕ) := by exact_mod_cast Nat.factorial_pos n
  have hscaled : (beta n S T : ℤ) ^ 2 * (n ! : ℤ) ^ 2 ≤
      ((beta n S S : ℤ) * beta n T T) * (n ! : ℤ) ^ 2 := by
    convert h using 1 <;> ring
  exact_mod_cast le_of_mul_le_mul_right hscaled (sq_pos_of_pos hp)

/-- At least one of the two corresponding diagonal entries dominates a joint entry. -/
theorem beta_le_max_diagonal (n : ℕ) (S T : Finset ℕ) :
    beta n S T ≤ max (beta n S S) (beta n T T) := by
  have h := beta_sq_le_diagonal n S T
  have hmul := Nat.mul_le_mul
    (le_max_left (beta n S S) (beta n T T))
    (le_max_right (beta n S S) (beta n T T))
  exact (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp (h.trans (by simpa [pow_two] using hmul))

/-- A maximum among all admissible joint descent multiplicities occurs on the diagonal. -/
theorem exists_diagonal_maximum (n : ℕ) :
    ∃ S ⊆ range (n - 1), ∀ A ⊆ range (n - 1), ∀ B ⊆ range (n - 1),
      beta n A B ≤ beta n S S := by
  obtain ⟨S, hS, hmax⟩ := (range (n - 1)).powerset.exists_max_image
    (fun A => beta n A A) ⟨∅, by simp⟩
  refine ⟨S, mem_powerset.mp hS, ?_⟩
  intro A hA B hB
  exact (beta_le_max_diagonal n A B).trans
    (max_le (hmax A (mem_powerset.mpr hA)) (hmax B (mem_powerset.mpr hB)))


/-- Gessel's upper-bound conjecture reduces exactly to checking the diagonal entries.
No assertion that this conjectural bound holds is made here. -/
theorem gessel_bound_iff_diagonal (n : ℕ) :
    (∀ S ⊆ range (n - 1), ∀ T ⊆ range (n - 1), beta n S T ≤ Alt.g n) ↔
      (∀ S ⊆ range (n - 1), beta n S S ≤ Alt.g n) := by
  constructor
  · intro h S hS
    exact h S hS S hS
  · intro h S hS T hT
    exact (beta_le_max_diagonal n S T).trans (max_le (h S hS) (h T hT))

/-- The alternating pair is admissible and attains g(n), so the preceding bound
really would identify the maximum, not just give an upper estimate. -/
theorem exists_pair_attaining_g (n : ℕ) :
    ∃ S ⊆ range (n - 1), ∃ T ⊆ range (n - 1), beta n S T = Alt.g n :=
  ⟨Alt.altS n, Finset.filter_subset _ _, Alt.altS n, Finset.filter_subset _ _, rfl⟩

end Stanley
