import LeanProofs.ShuffleW.Defs

set_option maxHeartbeats 0 in
/-- Rotations of `W k` whose cut lies in zero run 4. -/
theorem W_cut04 (k : Nat) (p s : List Bool) (h : p ++ s = W k)
    (hlen : (zruns p).length = 5) : ¬ IsShuffleSquare (s ++ p) := by
  intro hsq
  obtain ⟨R, hR⟩ := hsq.zs
  obtain ⟨P, x, y, S, hp, hs, hps⟩ := zruns_append p s
  rw [hp, List.length_append, List.length_singleton] at hlen
  rw [h, W, zruns_ofGaps] at hps
  rw [zruns_append_glue, hs, hp] at hR
  rcases P with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, _ | ⟨p8, _ | ⟨p9, _ | ⟨p10, _ | ⟨p11, _ | ⟨p12, P⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_nil, List.length_cons] at hlen <;> (try omega) <;>
    simp only [List.nil_append, List.cons_append, List.cons.injEq, List.nil_eq,
      List.append_eq_nil_iff, reduceCtorEq, and_false, false_and] at hps <;>
    casesm* _ ∧ _ <;> subst_vars <;>
    simp only [glue, List.cons_append, List.nil_append] at hR <;>
    repeat (first | omega | casesm ZS _ _ _ _ _)
