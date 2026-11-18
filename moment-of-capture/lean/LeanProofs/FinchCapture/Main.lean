import Mathlib

/-!
# Finch's Conjecture 23: the moment of capture (arXiv 2610.34300, Section 7)

`x_1 = ⋯ = x_{k-1} = 0`, `x_k = 1`, `x_n = x_{n-1} + x_{n-k}²` in `ℤ/3`. A run with `g` gaps starting at
`r ≥ k + 1` has zeros at `r, r + 4, …, r + 4g` and no other zero in between. With `G = ⌈(k-1)/4⌉`, the
capture point `z` is the least end of a run with `G` gaps, and the pre-period `μ` is the least `μ` with
`x_{n+4} = x_n` for all `n > μ`. Finch conjectured `z - μ = 6` whenever the period is 4.

`capture`: for `k ≥ 6`, `k ≡ 2, 3 (mod 4)`, whenever a capture point `z` exists, `μ = z - 6`. The proof:
inside the run the rule looks back exactly `k` places, so the run forces the values just before it; the run
starts at `s ≥ 2k - 1`; and by minimality of `z` the run cannot be extended backwards, which pins the block
before the last one. `k = 2` is an exception (`two_exception`): the sequence is periodic from the start.
-/

namespace FinchCapture

/-- `xs k n i = x_i` for `i ≤ n` (built up one value at a time, so that small cases compute). -/
def xs (k : ℕ) : ℕ → ℕ → ZMod 3
  | 0 => fun _ => 0
  | n + 1 => fun i =>
      if i = n + 1 then
        (if n + 1 < k then 0 else if n + 1 = k then 1 else xs k n n + xs k n (n + 1 - k) ^ 2)
      else xs k n i

/-- Finch's rule (A). -/
def x (k n : ℕ) : ZMod 3 := xs k n n

lemma xs_stable (k : ℕ) : ∀ n i, i ≤ n → xs k n i = x k i
  | 0, i, h => by rw [Nat.le_zero.1 h]; rfl
  | n + 1, i, h => by
    rcases Nat.lt_or_ge i (n + 1) with h' | h'
    · simp only [xs, if_neg (show i ≠ n + 1 by omega)]
      exact xs_stable k n i (by omega)
    · rw [show i = n + 1 by omega]; rfl

lemma x_lt {k n : ℕ} (h : n < k) : x k n = 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [x, xs, h]

lemma x_rule {k n : ℕ} (hk : 1 ≤ k) (h : k + 1 ≤ n) : x k n = x k (n - 1) + x k (n - k) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [x, xs, if_true, if_neg (show ¬ m + 1 < k by omega), if_neg (show m + 1 ≠ k by omega),
    Nat.add_sub_cancel]
  rw [xs_stable k m (m + 1 - k) (by omega)]
  rfl

/-- A run with `g` gaps starting at `r`. -/
def Run (k r g : ℕ) : Prop :=
  k + 1 ≤ r ∧ (∀ i ≤ g, x k (r + 4 * i) = 0) ∧ ∀ n < r + 4 * g, r < n → (n - r) % 4 ≠ 0 → x k n ≠ 0

instance (k r g : ℕ) : Decidable (Run k r g) := by unfold Run; infer_instance

/-- `G = ⌈(k-1)/4⌉`. -/
def G (k : ℕ) : ℕ := (k + 2) / 4

/-- `z` is the capture point: the least end of a run with `G` gaps. -/
def IsCapture (k z : ℕ) : Prop :=
  4 * G k ≤ z ∧ Run k (z - 4 * G k) (G k) ∧ ∀ z' < z, 4 * G k ≤ z' → ¬ Run k (z' - 4 * G k) (G k)

/-- `μ` is the pre-period. -/
def IsPreperiod (k μ : ℕ) : Prop := IsLeast {m | ∀ n, m < n → x k (n + 4) = x k n} μ

section run

variable {k s g : ℕ}

/-- Inside a run the zeros are exactly the positions `≡ s (mod 4)`. -/
lemma run_zero (hr : Run k s g) {p : ℕ} (h1 : s ≤ p) (h2 : p ≤ s + 4 * g) :
    x k p = 0 ↔ (p - s) % 4 = 0 := by
  obtain ⟨-, hz, hn⟩ := hr
  constructor
  · intro h0
    by_contra hc
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · simp at hc
    rcases Nat.eq_or_lt_of_le h2 with rfl | h2
    · simp at hc
    exact hn p h2 h1 hc h0
  · intro h
    have := hz ((p - s) / 4) (by omega)
    rwa [show s + 4 * ((p - s) / 4) = p by omega] at this

/-- One block `0, a, c, e, 0` of a run (Finch, Lemma 17), read through the rule. -/
lemma block (hk : 1 ≤ k) {m : ℕ} (hm : k ≤ m) (h0 : x k m = 0) (h4 : x k (m + 4) = 0)
    (h1 : x k (m + 1) ≠ 0) (_h2 : x k (m + 2) ≠ 0) (h3 : x k (m + 3) ≠ 0) :
    x k (m + 1) = 1 ∧ x k (m + 3) = 2 ∧ x k (m + 1 - k) ≠ 0 ∧ x k (m + 4 - k) ≠ 0 ∧
      (x k (m + 2 - k) = 0 ↔ x k (m + 3 - k) ≠ 0) ∧ (x k (m + 2) = 1 ↔ x k (m + 2 - k) = 0) := by
  have r1 := x_rule (n := m + 1) hk (by omega)
  have r2 := x_rule (n := m + 2) hk (by omega)
  have r3 := x_rule (n := m + 3) hk (by omega)
  have r4 := x_rule (n := m + 4) hk (by omega)
  simp only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega,
    show m + 4 - 1 = m + 3 by omega] at r1 r2 r3 r4
  rw [h0] at r1
  rw [h4] at r4
  have L1 : ∀ a c : ZMod 3, a = 0 + c ^ 2 → a ≠ 0 → a = 1 ∧ c ≠ 0 := by decide
  have L2 : ∀ a c : ZMod 3, (0 : ZMod 3) = a + c ^ 2 → a ≠ 0 → a = 2 ∧ c ≠ 0 := by decide
  have L3 : ∀ a c2 c3 : ZMod 3, a = 1 + c2 ^ 2 → (2 : ZMod 3) = a + c3 ^ 2 →
      (c2 = 0 ↔ c3 ≠ 0) ∧ (a = 1 ↔ c2 = 0) := by decide
  obtain ⟨e1, n1⟩ := L1 _ _ r1 h1
  obtain ⟨e3, n4⟩ := L2 _ _ r4 h3
  rw [e1] at r2
  rw [e3] at r3
  exact ⟨e1, e3, n1, n4, L3 _ _ _ r2 r3⟩

lemma block_at (hk : 1 ≤ k) (hr : Run k s g) {i : ℕ} (hi : i < g) :
    let m := s + 4 * i
    x k (m + 1) = 1 ∧ x k (m + 3) = 2 ∧ x k (m + 1 - k) ≠ 0 ∧ x k (m + 4 - k) ≠ 0 ∧
      (x k (m + 2 - k) = 0 ↔ x k (m + 3 - k) ≠ 0) ∧ (x k (m + 2) = 1 ↔ x k (m + 2 - k) = 0) := by
  intro m
  have hs := hr.1
  have nz : ∀ j, 1 ≤ j → j ≤ 3 → x k (m + j) ≠ 0 := fun j h1 h2 => by
    intro h
    have := (run_zero hr (p := m + j) (by omega) (by omega)).1 h
    omega
  refine block hk (by omega) ((run_zero hr (by omega) (by omega)).2 (by omega))
    ((run_zero hr (p := m + 4) (by omega) (by omega)).2 (by omega)) (nz 1 le_rfl (by omega))
    (nz 2 (by omega) (by omega)) (nz 3 (by omega) le_rfl)

/-- **Step 2.** The run starts late: `s ≥ 2k - 1`. -/
lemma start_late (hk : 1 ≤ k) (hr : Run k s g) (hg : 1 ≤ g) : 2 * k ≤ s + 1 := by
  have := (block_at hk hr (i := 0) (by omega)).2.2.1
  simp only [mul_zero, add_zero] at this
  by_contra h
  exact this (x_lt (by omega))

end run

/-- **The periodic tail.** If the values just before the run are nonzero, then from `z - 5` on the
sequence is 4-periodic (`z = s + 4t + 4`). -/
lemma tail {k s t : ℕ} (hk : 1 ≤ k) (hkt : k ≤ 4 * t + 4) (ht : 1 ≤ t) (hr : Run k s (t + 1))
    (hpre : ∀ p, s + 4 * t + 1 ≤ p + k → p < s → x k p ≠ 0) :
    ∀ n, s + 4 * t - 2 < n → x k (n + 4) = x k n := by
  have hs := hr.1
  have b1 := block_at hk hr (i := t) (by omega)
  have b0 := block_at hk hr (i := t - 1) (by omega)
  simp only [show s + 4 * (t - 1) = s + 4 * t - 4 by omega] at b0
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n (s + 4 * t + 1) with h | h
    · rcases (show n = s + 4 * t - 1 ∨ n = s + 4 * t by omega) with rfl | rfl
      · rw [show s + 4 * t - 1 + 4 = s + 4 * t + 3 by omega, b1.2.1,
          show s + 4 * t - 1 = s + 4 * t - 4 + 3 by omega, b0.2.1]
      · rw [(run_zero hr (by omega) (by omega)).2 (by omega), (run_zero hr (by omega) (by omega)).2 (by omega)]
    · rw [x_rule hk (show k + 1 ≤ n + 4 by omega), x_rule hk (show k + 1 ≤ n by omega),
        show n + 4 - 1 = (n - 1) + 4 by omega, ih (n - 1) (by omega) (by omega)]
      congr 1
      have hb : x k (n + 4 - k) = 0 ↔ x k (n - k) = 0 := by
        rcases Nat.lt_or_ge (s + 4 * t - 2) (n - k) with h1 | h1
        · rw [show n + 4 - k = (n - k) + 4 by omega, ih (n - k) (by omega) h1]
        · rcases Nat.lt_or_ge (n - k) s with h2 | h2
          · have e1 := hpre (n - k) (by omega) h2
            have e2 : x k (n + 4 - k) ≠ 0 := fun h0 => by
              have := (run_zero hr (p := n + 4 - k) (by omega) (by omega)).1 h0; omega
            exact ⟨fun h => absurd h e2, fun h => absurd h e1⟩
          · rw [run_zero hr (p := n + 4 - k) (by omega) (by omega), run_zero hr (p := n - k) h2 (by omega),
              show n + 4 - k - s = (n - k - s) + 4 by omega, Nat.add_mod_right]
      have hsq : ∀ a b : ZMod 3, (a = 0 ↔ b = 0) → a ^ 2 = b ^ 2 := by decide
      exact hsq _ _ hb

/-- **No backward extension.** By minimality the zero at `s - 4` would give an earlier run. -/
lemma no_extend {k s t : ℕ} (hr : Run k s (t + 1)) (hs : k + 5 ≤ s) (hmin : ¬ Run k (s - 4) (t + 1))
    (h3 : x k (s - 3) ≠ 0) (h2 : x k (s - 2) ≠ 0) (h1 : x k (s - 1) ≠ 0) : x k (s - 4) ≠ 0 := by
  intro h4
  apply hmin
  obtain ⟨-, hz, hn⟩ := hr
  refine ⟨by omega, fun i hi => ?_, fun n hn2 hn1 hn3 => ?_⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using h4
    · have := hz (i - 1) (by omega)
      rwa [show s + 4 * (i - 1) = s - 4 + 4 * i by omega] at this
  · rcases Nat.lt_or_ge n s with h | h
    · rcases (show n = s - 3 ∨ n = s - 2 ∨ n = s - 1 by omega) with rfl | rfl | rfl <;> assumption
    · rcases Nat.eq_or_lt_of_le h with rfl | h
      · omega
      · exact hn n (by omega) h (by omega)

/-- **The theorem for one run.** `z = s + 4t + 4`: the last mismatch is at `z - 2`, and the sequence is
4-periodic after `z - 6`. -/
theorem capture_run {k s t : ℕ} (ht : 1 ≤ t) (hk : k = 4 * t + 2 ∨ k = 4 * t + 3) (hr : Run k s (t + 1))
    (hmin : ¬ Run k (s - 4) (t + 1)) :
    x k (s + 4 * t + 2) ≠ x k (s + 4 * t - 2) ∧ ∀ n, s + 4 * t - 2 < n → x k (n + 4) = x k n := by
  have hk1 : 1 ≤ k := by omega
  have hs := start_late hk1 hr (by omega)
  have hrs := hr.1
  have bl := block_at hk1 hr (i := t) (by omega)
  have bp := block_at hk1 hr (i := t - 1) (by omega)
  simp only [show s + 4 * (t - 1) = s + 4 * t - 4 by omega] at bp
  have hxs : x k s = 0 := (run_zero hr le_rfl (by omega)).2 (by simp)
  have nz : ∀ j, 1 ≤ j → j ≤ 3 → x k (s + 4 * t - 4 + j) ≠ 0 := fun j h1 h2 h => by
    have := (run_zero hr (p := s + 4 * t - 4 + j) (by omega) (by omega)).1 h; omega
  rcases hk with rfl | rfl
  · -- `k = 4t + 2`: the cycle is `0, 1, 1, 2`
    have f1 : x (4 * t + 2) (s - 1) ≠ 0 := by
      have := bl.2.2.1; rwa [show s + 4 * t + 1 - (4 * t + 2) = s - 1 by omega] at this
    have f2 : x (4 * t + 2) (s - 2) ≠ 0 := by
      have := bp.2.2.2.1; rwa [show s + 4 * t - 4 + 4 - (4 * t + 2) = s - 2 by omega] at this
    have pr : x (4 * t + 2) (s - 4) = 0 ↔ x (4 * t + 2) (s - 3) ≠ 0 := by
      have := bp.2.2.2.2.1
      rwa [show s + 4 * t - 4 + 2 - (4 * t + 2) = s - 4 by omega,
        show s + 4 * t - 4 + 3 - (4 * t + 2) = s - 3 by omega] at this
    have h4 : x (4 * t + 2) (s - 4) ≠ 0 := by
      by_contra h4
      exact no_extend hr (by omega) hmin (pr.1 h4) f2 f1 h4
    refine ⟨?_, tail hk1 (by omega) ht hr fun p hp1 hp2 => ?_⟩
    · have hl : x (4 * t + 2) (s + 4 * t + 2) = 1 := by
        have := bl.2.2.2.2.2; rw [show s + 4 * t + 2 - (4 * t + 2) = s by omega] at this
        exact this.2 hxs
      have hp : x (4 * t + 2) (s + 4 * t - 2) ≠ 1 := by
        have := bp.2.2.2.2.2
        rw [show s + 4 * t - 4 + 2 - (4 * t + 2) = s - 4 by omega,
          show s + 4 * t - 4 + 2 = s + 4 * t - 2 by omega] at this
        exact fun h => h4 (this.1 h)
      rw [hl]; exact fun h => hp h.symm
    · rcases (show p = s - 1 by omega) with rfl; exact f1
  · -- `k = 4t + 3`: the cycle is `0, 1, 2, 2`
    have f1 : x (4 * t + 3) (s - 2) ≠ 0 := by
      have := bl.2.2.1; rwa [show s + 4 * t + 1 - (4 * t + 3) = s - 2 by omega] at this
    have f2 : x (4 * t + 3) (s - 3) ≠ 0 := by
      have := bp.2.2.2.1; rwa [show s + 4 * t - 4 + 4 - (4 * t + 3) = s - 3 by omega] at this
    have f3 : x (4 * t + 3) (s - 1) ≠ 0 := by
      have := bl.2.2.2.2.1
      rw [show s + 4 * t + 2 - (4 * t + 3) = s - 1 by omega,
        show s + 4 * t + 3 - (4 * t + 3) = s by omega] at this
      exact fun h => this.1 h hxs
    have pr : x (4 * t + 3) (s - 5) = 0 ↔ x (4 * t + 3) (s - 4) ≠ 0 := by
      have := bp.2.2.2.2.1
      rwa [show s + 4 * t - 4 + 2 - (4 * t + 3) = s - 5 by omega,
        show s + 4 * t - 4 + 3 - (4 * t + 3) = s - 4 by omega] at this
    have h4 : x (4 * t + 3) (s - 4) ≠ 0 := no_extend hr (by omega) hmin f2 f1 f3
    refine ⟨?_, tail hk1 (by omega) ht hr fun p hp1 hp2 => ?_⟩
    · have hl : x (4 * t + 3) (s + 4 * t + 2) = 2 := by
        have := bl.2.2.2.2.2; rw [show s + 4 * t + 2 - (4 * t + 3) = s - 1 by omega] at this
        have hne1 : x (4 * t + 3) (s + 4 * t + 2) ≠ 1 := fun h => f3 (this.1 h)
        have hne0 : x (4 * t + 3) (s + 4 * t + 2) ≠ 0 := fun h => by
          have := (run_zero hr (p := s + 4 * t + 2) (by omega) (by omega)).1 h; omega
        revert hne1 hne0; generalize x (4 * t + 3) (s + 4 * t + 2) = a; revert a; decide
      have hp : x (4 * t + 3) (s + 4 * t - 2) = 1 := by
        have := bp.2.2.2.2.2
        rw [show s + 4 * t - 4 + 2 - (4 * t + 3) = s - 5 by omega,
          show s + 4 * t - 4 + 2 = s + 4 * t - 2 by omega] at this
        exact this.2 (pr.2 h4)
      rw [hl, hp]; decide
    · rcases (show p = s - 2 ∨ p = s - 1 by omega) with rfl | rfl
      · exact f1
      · exact f3

/-- **Finch's Conjecture 23** for `k ≥ 6`: if the capture point `z` exists, the pre-period is `z - 6`. -/
theorem capture {k z : ℕ} (hk6 : 6 ≤ k) (hk : k % 4 = 2 ∨ k % 4 = 3) (hz : IsCapture k z) :
    IsPreperiod k (z - 6) := by
  obtain ⟨hzG, hrun, hmin⟩ := hz
  set t := (k - 2) / 4 with htdef
  have hGt : G k = t + 1 := by unfold G; omega
  have ht : 1 ≤ t := by omega
  have hk' : k = 4 * t + 2 ∨ k = 4 * t + 3 := by omega
  rw [hGt] at hzG hrun hmin
  set s := z - 4 * (t + 1) with hsdef
  have hs := hrun.1
  have hm : ¬ Run k (s - 4) (t + 1) := by
    have := hmin (z - 4) (by omega) (by omega)
    rwa [show z - 4 - 4 * (t + 1) = s - 4 by omega] at this
  obtain ⟨hne, hper⟩ := capture_run ht hk' hrun hm
  have hz : z = s + 4 * t + 4 := by omega
  refine ⟨fun n hn => ?_, fun m hm' => ?_⟩
  · exact hper n (by omega)
  · by_contra hlt
    have := hm' (z - 6) (by omega)
    rw [show z - 6 + 4 = s + 4 * t + 2 by omega, show z - 6 = s + 4 * t - 2 by omega] at this
    exact hne this

/-- The paper's `k = 6`: capture at `z = 24` (so `μ = 18`). -/
example : IsCapture 6 24 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`k = 2` is an exception**: `x` is periodic from the start (`μ = 0`), while `z = 9`. -/
theorem two_exception : IsCapture 2 9 ∧ IsPreperiod 2 0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨fun n _ => ?_, fun m _ => Nat.zero_le m⟩⟩
  -- `x_{n+4} = x_n` for `n ≥ 1`, by strong induction from the window `n = 1, 2, 3`
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n ≤ 2 ∨ 3 ≤ n by omega) with h | h
    · interval_cases n <;> decide
    · rw [x_rule (by norm_num) (show 3 ≤ n + 4 by omega), x_rule (by norm_num) (show 3 ≤ n by omega),
        show n + 4 - 1 = (n - 1) + 4 by omega, show n + 4 - 2 = (n - 2) + 4 by omega,
        ih (n - 1) (by omega) (by omega), ih (n - 2) (by omega) (by omega)]

end FinchCapture
