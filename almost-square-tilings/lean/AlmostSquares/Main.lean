/-
  Friedman's problem #20: for every `n ≥ 20` (and for `n ∈ {4, 10, 12, 14, 15, 18}`) the
  `n × (n+1)` rectangle can be tiled with almost-squares `k × (k+1)` of distinct sizes `k < n`.
-/
import AlmostSquares.Explicit
import AlmostSquares.Inflations

namespace AlmostSq

theorem explicit_admissible {n : ℕ} {ts : List Tile} (h : (n, ts) ∈ explicit) :
    Admissible n ts :=
  check_sound (List.all_eq_true.mp explicit_ok _ h)

theorem inflations_pos : inflations.all (fun I => decide (0 < I.S)) = true := by decide +kernel

/-- `n = S t + V` for some `t ≥ t₀`. -/
def inflCovers (n : ℕ) (I : Infl) : Bool :=
  decide (((n : ℤ) - I.V) % I.S = 0 ∧ I.t0 * I.S ≤ (n : ℤ) - I.V)

/-- A class covering `n` tiles `R_n`: the tiling is the inflation of its squared square at the scale
    `t = (n - V)/S`, admissible by Lemma 4 (`inflOK_sound`, through `all_scales` and `inflation`). -/
theorem inflCovers_sound {n : ℕ} {I : Infl} (hm : I ∈ inflations) (h : inflCovers n I = true) :
    ∃ ts, Admissible n ts := by
  have hS : 0 < I.S := of_decide_eq_true (List.all_eq_true.mp inflations_pos _ hm)
  obtain ⟨hd, hle⟩ := of_decide_eq_true h
  set t := ((n : ℤ) - I.V) / I.S with htdef
  have hmul : I.S * t = (n : ℤ) - I.V := by
    rw [htdef]; exact Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)
  have ht : I.t0 ≤ t := by
    by_contra hc
    have : I.S * t < I.S * I.t0 := by
      exact mul_lt_mul_of_pos_left (by omega) hS
    nlinarith
  have hA := inflOK_sound (List.all_eq_true.mp inflations_ok _ hm) ht
  have hn : (t * I.S + I.V).toNat = n := by
    have : t * I.S = I.S * t := mul_comm _ _
    omega
  rw [hn] at hA
  exact ⟨_, hA⟩

/-- `n` has a certified tiling: an explicit one, or one from an inflation class. -/
def covered (n : ℕ) : Bool := (explicit.map Prod.fst).contains n || inflations.any (inflCovers n)

theorem covered_sound {n : ℕ} (h : covered n = true) : ∃ ts, Admissible n ts := by
  simp only [covered, Bool.or_eq_true, List.contains_iff_mem, List.mem_map, List.any_eq_true] at h
  rcases h with ⟨⟨m, ts⟩, he, rfl⟩ | ⟨I, hm, hc⟩
  · exact ⟨ts, explicit_admissible he⟩
  · exact inflCovers_sound hm hc

/-- Every `20 ≤ n < 600` is covered (finite check). -/
theorem covered_below : ∀ n < 600, 20 ≤ n → covered n = true := by decide +kernel

/-- Every even residue mod 112 has a class of side 112 starting by 600. -/
theorem resid112 : ∀ r : ℕ, r < 112 → r % 2 = 0 → inflations.any (fun I =>
    decide (I.S = 112 ∧ (I.V - (r : ℤ)) % 112 = 0 ∧ I.t0 * 112 + I.V ≤ 600)) = true := by
  decide +kernel

/-- Every odd residue mod 110 has a class of side 110 starting by 600. -/
theorem resid110 : ∀ r : ℕ, r < 110 → r % 2 = 1 → inflations.any (fun I =>
    decide (I.S = 110 ∧ (I.V - (r : ℤ)) % 110 = 0 ∧ I.t0 * 110 + I.V ≤ 600)) = true := by
  decide +kernel

theorem covered_above (n : ℕ) (hn : 600 ≤ n) : covered n = true := by
  simp only [covered, Bool.or_eq_true, List.any_eq_true]
  right
  rcases Nat.mod_two_eq_zero_or_one n with hp | hp
  · obtain ⟨I, hm, hF⟩ := List.any_eq_true.mp (resid112 (n % 112) (Nat.mod_lt n (by norm_num))
      (by omega))
    obtain ⟨hS, hr, hb⟩ := of_decide_eq_true hF
    refine ⟨I, hm, decide_eq_true ?_⟩
    rw [hS]; omega
  · obtain ⟨I, hm, hF⟩ := List.any_eq_true.mp (resid110 (n % 110) (Nat.mod_lt n (by norm_num))
      (by omega))
    obtain ⟨hS, hr, hb⟩ := of_decide_eq_true hF
    refine ⟨I, hm, decide_eq_true ?_⟩
    rw [hS]; omega

theorem covered_small_cases : ∀ n ∈ [4, 10, 12, 14, 15, 18], covered n = true := by decide +kernel

/-- **Friedman's problem #20** (the constructive direction of Theorem 1): if `n ≥ 20`, or
    `n ∈ {4, 10, 12, 14, 15, 18}`, then `R_n` (width `n + 1`, height `n`) has an admissible tiling:
    almost-squares of distinct sizes `1 ≤ k < n` covering every unit cell exactly once. -/
theorem friedman_twenty (n : ℕ) (h : n ∈ [4, 10, 12, 14, 15, 18] ∨ 20 ≤ n) :
    ∃ ts : List Tile, Admissible n ts := by
  apply covered_sound
  rcases h with h | h
  · exact covered_small_cases n h
  · rcases Nat.lt_or_ge n 600 with h' | h'
    · exact covered_below n h' h
    · exact covered_above n h'

end AlmostSq
