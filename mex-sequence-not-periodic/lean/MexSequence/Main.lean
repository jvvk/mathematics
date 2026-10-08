import MexSequence.Arith

/-!
  Main theorem: the mex sequence starting `1,1,1,0,1,0,1,1` equals the closed form `F`, which is
  unbounded. So not every mex sequence is ultimately periodic (Guy, UPINT E27).
-/

namespace MexE27

theorem F_spec (k : ℕ) :
    (k = 0 ∧ F k = 1) ∨ (k ≠ 0 ∧ (k % 5 = 0 ∨ k % 5 = 3) ∧ F k = 0) ∨
      (k % 5 = 4 ∧ F k = w (k / 5)) ∨ ((k % 5 = 1 ∨ k % 5 = 2) ∧ F k = y (k / 5)) := by
  unfold F; split_ifs <;> omega

theorem F_z0 (c : ℕ) (hc : 0 < c) : F (5 * c) = 0 := by
  rcases F_spec (5 * c) with ⟨h1, _⟩ | ⟨_, _, h⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
theorem F_z3 (c : ℕ) : F (5 * c + 3) = 0 := by
  rcases F_spec (5 * c + 3) with ⟨h1, _⟩ | ⟨_, _, h⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
theorem F_y1 (c : ℕ) : F (5 * c + 1) = y c := by
  rcases F_spec (5 * c + 1) with ⟨h1, _⟩ | ⟨_, h1, _⟩ | ⟨h1, _⟩ | ⟨_, h⟩
  all_goals first | omega | (rw [h, show (5 * c + 1) / 5 = c by omega])
theorem F_y2 (c : ℕ) : F (5 * c + 2) = y c := by
  rcases F_spec (5 * c + 2) with ⟨h1, _⟩ | ⟨_, h1, _⟩ | ⟨h1, _⟩ | ⟨_, h⟩
  all_goals first | omega | (rw [h, show (5 * c + 2) / 5 = c by omega])
theorem F_w4 (c : ℕ) : F (5 * c + 4) = w c := by
  rcases F_spec (5 * c + 4) with ⟨h1, _⟩ | ⟨_, h1, _⟩ | ⟨_, h⟩ | ⟨h1, _⟩
  all_goals first | omega | (rw [h, show (5 * c + 4) / 5 = c by omega])

/-- The next term is not one of the sums. -/
theorem exclude (n : ℕ) (hn : 39 ≤ n) (i : ℕ) (hi : i < n + 1) :
    F i + F (n - i) ≠ F (n + 1) := by
  intro h
  rcases F_spec (n + 1) with ⟨h1, _⟩ | ⟨_, h2, hE⟩ | ⟨h2, hE⟩ | ⟨h2, hE⟩
  · omega
  · -- target 0: the two summands would both be 0, impossible by residues
    rcases F_spec i with ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases F_spec (n - i) with ⟨b1, b2⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    first
    | omega
    | (have := w_pos (i / 5); have := w_pos ((n - i) / 5); have := y_pos (i / 5);
       have := y_pos ((n - i) / 5); omega)
  · -- target w = 2: no two summands add up to 2
    have hw : w ((n + 1) / 5) = 2 := by
      rcases wspec ((n + 1) / 5) with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, hw⟩ <;> omega
    rcases F_spec i with ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases F_spec (n - i) with ⟨b1, b2⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    first
    | omega
    | (have p1 := w_pos (i / 5); have p2 := w_pos ((n - i) / 5); have p3 := y_pos (i / 5);
       have p4 := y_pos ((n - i) / 5)
       first
       | omega
       | (have := y_eq_one (i / 5) (by omega); have := y_eq_one ((n - i) / 5) (by omega); omega)
       | (have := w_eq_one (i / 5) (by omega); have := w_eq_one ((n - i) / 5) (by omega); omega))
  · -- target y B with B = (n+1)/5 >= 8
    have hB : 8 ≤ (n + 1) / 5 := by omega
    have hBf := yB_facts _ hB
    rcases F_spec i with ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases F_spec (n - i) with ⟨b1, b2⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    first
    | omega
    | (have := y_ne_of_lt ((n + 1) / 5) (i / 5) hB (by omega); omega)
    | (have := y_ne_of_lt ((n + 1) / 5) ((n - i) / 5) hB (by omega); omega)
    | (have := yw_ne ((n + 1) / 5) (i / 5) ((n - i) / 5) hB (by omega); omega)
    | (have := yw_ne ((n + 1) / 5) ((n - i) / 5) (i / 5) hB (by omega); omega)
    | (have e : i / 5 = (n + 1) / 5 := by omega
       have := congrArg y e; omega)
    | (have e : (n - i) / 5 = (n + 1) / 5 := by omega
       have := congrArg y e; omega)

/-- Every value below the next term is one of the sums. -/
theorem covered (n : ℕ) (hn : 39 ≤ n) (u : ℕ) (hu : u < F (n + 1)) :
    ∃ i, i < n + 1 ∧ F i + F (n - i) = u := by
  rcases F_spec (n + 1) with ⟨h1, _⟩ | ⟨_, h2, hE⟩ | ⟨h2, hE⟩ | ⟨h2, hE⟩
  · omega
  · omega
  · -- target 2 at n + 1 = 5B + 4: u is 0 or 1
    have hw : w ((n + 1) / 5) = 2 := by
      rcases wspec ((n + 1) / 5) with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, hw⟩ <;> omega
    rcases Nat.lt_or_ge u 1 with hu0 | hu1
    · refine ⟨5, by omega, ?_⟩
      rw [show (5 : ℕ) = 5 * 1 by rfl, F_z0 1 (by omega),
        show n - 5 * 1 = 5 * ((n - 8) / 5) + 3 by omega, F_z3]; omega
    · refine ⟨0, by omega, ?_⟩
      rw [show n - 0 = 5 * ((n - 3) / 5) + 3 by omega, F_z3]
      show 1 + 0 = u; omega
  · set B := (n + 1) / 5 with hBdef
    have hB : 8 ≤ B := by omega
    rcases cover B u hB (by omega) with hu01 | ⟨c, hc, hyc⟩ | ⟨c, d, hcd, hyw⟩
    · rcases h2 with h2 | h2
      · -- n = 5B
        rcases Nat.lt_or_ge u 1 with hu0 | hu1
        · refine ⟨5, by omega, ?_⟩
          rw [show (5 : ℕ) = 5 * 1 by rfl, F_z0 1 (by omega),
            show n - 5 * 1 = 5 * (B - 1) by omega, F_z0 _ (by omega)]; omega
        · refine ⟨0, by omega, ?_⟩
          rw [show n - 0 = 5 * B by omega, F_z0 _ (by omega)]
          show 1 + 0 = u; omega
      · -- n = 5B + 1
        rcases Nat.lt_or_ge u 1 with hu0 | hu1
        · refine ⟨3, by omega, ?_⟩
          rw [show (3 : ℕ) = 5 * 0 + 3 by rfl, F_z3,
            show n - (5 * 0 + 3) = 5 * (B - 1) + 3 by omega, F_z3]; omega
        · refine ⟨n - 1, by omega, ?_⟩
          rw [show n - 1 = 5 * B by omega, F_z0 _ (by omega),
            show n - 5 * B = 5 * 0 + 1 by omega, F_y1]
          show 0 + 1 = u; omega
    · rcases h2 with h2 | h2
      · refine ⟨5 * c + 2, by omega, ?_⟩
        rw [F_y2, show n - (5 * c + 2) = 5 * (B - c - 1) + 3 by omega, F_z3]; omega
      · refine ⟨5 * (B - c), by omega, ?_⟩
        rw [F_z0 _ (by omega), show n - 5 * (B - c) = 5 * c + 1 by omega, F_y1]; omega
    · rcases h2 with h2 | h2
      · refine ⟨5 * c + 1, by omega, ?_⟩
        rw [F_y1, show n - (5 * c + 1) = 5 * d + 4 by omega, F_w4]; omega
      · refine ⟨5 * c + 2, by omega, ?_⟩
        rw [F_y2, show n - (5 * c + 2) = 5 * d + 4 by omega, F_w4]; omega

theorem step (n : ℕ) (hn : 7 ≤ n) : mex (sums F n) = F (n + 1) := by
  rcases Nat.lt_or_ge n 60 with h | h
  · exact step_of_ok n (small_steps n hn h)
  · exact step_of_ok n ⟨fun i hi => exclude n (by omega) i hi, fun u hu => covered n (by omega) u hu⟩

/-- `F` is a mex sequence with the given start (so the statements below are not vacuous). -/
theorem isMex_F : IsMex F :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun n hn => (step n hn).symm⟩

/-- Any mex sequence with this start is `F`. -/
theorem eq_F (a : ℕ → ℕ) (ha : IsMex a) : ∀ n, a n = F n := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hrec⟩ := ha
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> assumption
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [hrec m (by omega), ← step m (by omega)]
      congr 1
      unfold sums
      refine Finset.image_congr ?_
      intro i hi
      simp only [Finset.coe_range, Set.mem_Iio] at hi
      simp only
      rw [ih i (by omega), ih (m - i) (by omega)]

/-- Guy E27, answered: the mex sequence starting `1,1,1,0,1,0,1,1` is unbounded, hence not
    ultimately periodic. -/
theorem unbounded (a : ℕ → ℕ) (ha : IsMex a) : ∀ M, ∃ n, M ≤ a n := by
  intro M
  refine ⟨5 * (3 * M + 3) + 1, ?_⟩
  rw [eq_F a ha, F_y1]
  rcases yspec (3 * M + 3) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem not_eventually_periodic (a : ℕ → ℕ) (ha : IsMex a) :
    ¬ ∃ p N, 0 < p ∧ ∀ n, N ≤ n → a (n + p) = a n := by
  rintro ⟨p, N, hp, hper⟩
  -- a periodic tail takes finitely many values, so it is bounded
  have hbound : ∀ n, a n ≤ (Finset.range (N + p)).sup a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n (N + p) with h | h
      · exact Finset.le_sup (f := a) (Finset.mem_range.2 h)
      · have := hper (n - p) (by omega)
        rw [show n - p + p = n by omega] at this
        rw [this]; exact ih _ (by omega)
  obtain ⟨n, hn⟩ := unbounded a ha ((Finset.range (N + p)).sup a + 1)
  have := hbound n
  omega

end MexE27
