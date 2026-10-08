/-
  Stanley, MathOverflow 486548. Part Q. Stanley's generating function for doubly alternating
  permutations (Stanley 2007, Theorem 3.1), proved; hence Theorem 2 of the paper holds unconditionally.

  `n! g(n) = Σ_w ψ(w)²` (Burnside + inclusion-exclusion), `ψ(w)² = E_m² [m even or no even cycle]`
  (Foulkes, via labellings of cycles), and the number of permutations with `m` odd cycles of the
  required kind is `cycleNumbers` (a two-point removal recurrence). Summing gives `StanleyFinite`,
  which `stanleyGF_iff_finite` turns into `StanleyGF`.
-/
import LeanProofs.Stanley.PermCount
import LeanProofs.Stanley.Alternating

namespace Stanley.Alt

open Finset Equiv
open scoped Nat

theorem oddC_le {n : ℕ} (w : Perm (Fin n)) : oddC w ≤ n := by
  unfold oddC
  calc (univ.filter (fun q : cyc w => Odd (len w q))).card ≤ Fintype.card (cyc w) :=
        Finset.card_le_univ _
    _ ≤ Fintype.card (Fin n) := Fintype.card_le_of_surjective (fun p => Quotient.mk _ p)
        (fun q => Quotient.exists_rep q |>.imp fun _ h => h)
    _ = n := Fintype.card_fin n

/-- **Stanley's identity, finite form.** -/
theorem stanleyFinite : StanleyFinite := by
  intro n
  rcases n with _ | n
  · decide
  · have h := g_mul_factorial_eq (n + 1)
    rw [Finset.sum_congr rfl (fun w _ => ψ_sq (by omega) w)] at h
    -- group the permutations by their number of odd cycles
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun w : Perm (Fin (n + 1)) => oddC w)
      (t := range (n + 1 + 1)) (fun w _ => Finset.mem_range.mpr (by have := oddC_le w; omega))] at h
    have hm : ∀ m ∈ range (n + 1 + 1),
        (∑ w ∈ univ.filter (fun w : Perm (Fin (n + 1)) => oddC w = m),
          (if Even (univ.filter (fun q : cyc w => Odd (len w q))).card ∨
              (univ.filter (fun q : cyc w => Even (len w q))).card = 0
            then (E (univ.filter (fun q : cyc w => Odd (len w q))).card : ℤ) ^ 2 else 0)) =
        (E m : ℤ) ^ 2 * (cycleNumbers (decide (Even m)) (n + 1) m : ℤ) := by
      intro m _
      rw [← Qc_fin, Qc]
      have : ∀ w ∈ univ.filter (fun w : Perm (Fin (n + 1)) => oddC w = m),
          (if Even (univ.filter (fun q : cyc w => Odd (len w q))).card ∨
              (univ.filter (fun q : cyc w => Even (len w q))).card = 0
            then (E (univ.filter (fun q : cyc w => Odd (len w q))).card : ℤ) ^ 2 else 0) =
          if Pc (decide (Even m)) m w then (E m : ℤ) ^ 2 else 0 := by
        intro w hw
        have hwm : oddC w = m := (Finset.mem_filter.mp hw).2
        change (if Even (oddC w) ∨ evenC w = 0 then (E (oddC w) : ℤ) ^ 2 else 0) = _
        have key : (Even (oddC w) ∨ evenC w = 0) ↔ Pc (decide (Even m)) m w := by
          unfold Pc; rw [hwm]; simp
        by_cases hP : Pc (decide (Even m)) m w
        · rw [if_pos hP, if_pos (key.mpr hP), hwm]
        · rw [if_neg hP, if_neg (fun h => hP (key.mp h))]
      have hf : (univ.filter (fun w : Perm (Fin (n + 1)) => oddC w = m)).filter
          (fun w => Pc (decide (Even m)) m w) =
          univ.filter (fun σ : Perm (Fin (n + 1)) => Pc (decide (Even m)) m σ) := by
        rw [Finset.filter_filter]
        exact Finset.filter_congr fun w _ => ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
      rw [Finset.sum_congr rfl this, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul, hf, mul_comm]
    rw [Finset.sum_congr rfl hm] at h
    exact_mod_cast h

/-- **Stanley's generating function (Stanley 2007, Theorem 3.1), proved.** -/
theorem stanleyGF : StanleyGF := stanleyGF_iff_finite.mpr stanleyFinite

/-- **Theorem 2 of the paper, unconditional.** -/
theorem g_asymptotics :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(g n : ℝ) * n ! / (E n : ℝ) ^ 2 - 1 - Real.pi ^ 4 / (48 * n)| ≤ C / (n : ℝ) ^ 2 :=
  g_asymp stanleyGF

/-- Theorem 2, second form, unconditional. -/
theorem g_asymptotics' :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(g n : ℝ) / (16 / Real.pi ^ 2 * (4 / Real.pi ^ 2) ^ n * n !) - 1 -
        Real.pi ^ 4 / (48 * n)| ≤ C / (n : ℝ) ^ 2 :=
  g_asymp' stanleyGF

end Stanley.Alt
