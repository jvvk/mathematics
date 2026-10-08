import Mathlib.Tactic.CasesM
import LeanProofs.Shuffle

/-!
  The family `U k = 0^(k+9) 1 0^5 1 1 0^(k+9) 1 0^2 1 0 1 1 1` (length 2k + 34, eight 1s):
  no rotation of `U k` is a shuffle square, for every `k`.
-/

def U (k : Nat) : List Bool := ofGaps [k + 9, 5, 0, k + 9, 2, 1, 0, 0, 0]

set_option maxHeartbeats 0 in
theorem U_rotation_not_square (k : Nat) (p s : List Bool) (h : p ++ s = U k) :
    ¬ IsShuffleSquare (s ++ p) := by
  intro hsq
  obtain ⟨R, hR⟩ := hsq.zs
  obtain ⟨P, x, y, S, hp, hs, hps⟩ := zruns_append p s
  rw [h, U, zruns_ofGaps] at hps
  rw [zruns_append_glue, hs, hp] at hR
  rcases P with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, _ | ⟨p8, P⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.nil_append, List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false, false_and] at hps <;>
    casesm* _ ∧ _ <;> subst_vars <;>
    simp only [glue, List.cons_append, List.nil_append] at hR <;>
    casesm* ZS _ _ _ _ _ <;> omega
#print axioms U_rotation_not_square
