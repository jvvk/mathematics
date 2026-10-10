import Mathlib

/-!
# Matching two complete systems modulo `2^k` inside `ℤ/2^(k+1)` (MSE 2060312)

A set `A` of `2^k` residues modulo `2^(k+1)` that reduces modulo `2^k` to every residue once is
`A = {r + 2^k e r : r < 2^k}` for a bit vector `e`; likewise `B` with bits `f`. With
`p = (∑ e r + ∑ f r) mod 2`:

* `exists_matching`: there is a permutation `σ` of `{0, …, 2^k - 1}` such that the `2^k` sums
  `(r + 2^k e r) + (σ r + 2^k f (σ r))` are pairwise different modulo `2^(k+1)` and all have
  parity `p`
  (so they are exactly the residues of parity `p`);
* `parity_forced`: every matching with pairwise different sums of a single parity uses parity `p`.

The proof of `exists_matching` is the induction of the note: split `A` and `B` into even and odd
elements, halve, and match evens with evens and odds with odds when `p = 0`, evens with odds when
`p = 1`.
-/

open Finset

namespace PowerTwoMatching

/-- The element of `A` over the residue `r`. -/
def elt (k : ℕ) (e : ℕ → ℕ) (r : ℕ) : ℕ := r + 2 ^ k * e r

/-- The parity count `p`. -/
def par (k : ℕ) (e f : ℕ → ℕ) : ℕ := (∑ r ∈ range (2 ^ k), (e r + f r)) % 2

/-- `σ` is a permutation of `{0, …, 2^k - 1}` (injective and into, on a finite set). -/
def IsPerm (k : ℕ) (σ : ℕ → ℕ) : Prop :=
  Set.InjOn σ (range (2 ^ k)) ∧ Set.MapsTo σ (range (2 ^ k)) (range (2 ^ k))

/-- `σ` is a good matching of parity `q`: the sums are pairwise different modulo `2^(k+1)`, and all
have parity `q`. -/
def Good (k : ℕ) (e f σ : ℕ → ℕ) (q : ℕ) : Prop :=
  IsPerm k σ ∧
    Set.InjOn (fun r => (elt k e r + elt k f (σ r)) % 2 ^ (k + 1)) (range (2 ^ k)) ∧
    ∀ r < 2 ^ k, (elt k e r + elt k f (σ r)) % 2 = q

lemma sum_range_two_mul (g : ℕ → ℕ) (n : ℕ) :
    ∑ r ∈ range (2 * n), g r = ∑ s ∈ range n, g (2 * s) + ∑ s ∈ range n, g (2 * s + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]
    ring

/-- Halving: the parities of the four half-instances. -/
lemma par_split (k : ℕ) (e f : ℕ → ℕ) :
    (par k (fun s => e (2 * s)) (fun s => f (2 * s)) +
        par k (fun s => e (2 * s + 1)) (fun s => f (2 * s + 1))) % 2 = par (k + 1) e f ∧
      (par k (fun s => e (2 * s)) (fun s => f (2 * s + 1)) +
        par k (fun s => e (2 * s + 1)) (fun s => f (2 * s))) % 2 = par (k + 1) e f := by
  have h := sum_range_two_mul (fun r => e r + f r) (2 ^ k)
  have he := sum_range_two_mul e (2 ^ k)
  have hf := sum_range_two_mul f (2 ^ k)
  rw [show 2 * 2 ^ k = 2 ^ (k + 1) by ring] at h he hf
  simp only [par, sum_add_distrib] at *
  constructor <;> omega

/-- Doubling an element of a half-instance gives an element of the instance. -/
lemma elt_even (k : ℕ) (e : ℕ → ℕ) (s : ℕ) :
    elt (k + 1) e (2 * s) = 2 * elt k (fun s => e (2 * s)) s := by
  simp only [elt, pow_succ]; ring

lemma elt_odd (k : ℕ) (e : ℕ → ℕ) (s : ℕ) :
    elt (k + 1) e (2 * s + 1) = 2 * elt k (fun s => e (2 * s + 1)) s + 1 := by
  simp only [elt, pow_succ]; ring

/-- Halving a congruence modulo `2^(k+2)`. -/
lemma mod_double (k x y : ℕ) :
    (2 * x) % 2 ^ (k + 2) = (2 * y) % 2 ^ (k + 2) ↔ x % 2 ^ (k + 1) = y % 2 ^ (k + 1) := by
  rw [show 2 ^ (k + 2) = 2 * 2 ^ (k + 1) by ring, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  omega

lemma mod_double_add_one (k x y : ℕ) :
    (2 * x + 1) % 2 ^ (k + 2) = (2 * y + 1) % 2 ^ (k + 2) ↔ x % 2 ^ (k + 1) = y % 2 ^ (k + 1) := by
  set m := 2 ^ (k + 1)
  have hm : 0 < m := by positivity
  have e2 : 2 ^ (k + 2) = 2 * m := by simp only [m]; ring
  have hx : ∀ z, (2 * z + 1) % (2 * m) = 2 * (z % m) + 1 := by
    intro z
    have hz := Nat.div_add_mod z m
    have hlt := Nat.mod_lt z hm
    conv_lhs => rw [← hz]
    rw [show 2 * (m * (z / m) + z % m) + 1 = (2 * (z % m) + 1) + 2 * m * (z / m) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [e2, hx, hx]; omega

/-- Reducing modulo `2^(k+1)` keeps the parity. -/
lemma mod_pow_mod_two (k x : ℕ) : x % 2 ^ (k + 1) % 2 = x % 2 := by
  rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (Nat.succ_ne_zero k))]

/-- A statement about all `r < 2M` splits into the even and odd cases. -/
lemma forall_split {M : ℕ} {P : ℕ → Prop} (h0 : ∀ s < M, P (2 * s)) (h1 : ∀ s < M, P (2 * s + 1)) :
    ∀ r < 2 * M, P r := by
  intro r hr
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
  · exact h0 s (by omega)
  · exact h1 s (by omega)

/-- Injectivity on `{0, …, 2M - 1}` from the even part, the odd part and no collisions across. -/
lemma injOn_split {M : ℕ} (g : ℕ → ℕ) (h0 : ∀ s < M, ∀ s' < M, g (2 * s) = g (2 * s') → s = s')
    (h1 : ∀ s < M, ∀ s' < M, g (2 * s + 1) = g (2 * s' + 1) → s = s')
    (hx : ∀ s < M, ∀ s' < M, g (2 * s) ≠ g (2 * s' + 1)) :
    Set.InjOn g (range (2 * M)) := by
  intro r hr r' hr' h
  simp only [coe_range, Set.mem_Iio] at hr hr'
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r <;> obtain ⟨s', rfl | rfl⟩ := Nat.even_or_odd' r'
  · rw [h0 s (by omega) s' (by omega) h]
  · exact absurd h (hx s (by omega) s' (by omega))
  · exact absurd h.symm (hx s' (by omega) s (by omega))
  · rw [h1 s (by omega) s' (by omega) h]

/-- The matching exists, with sums of parity `p`. -/
theorem exists_matching (k : ℕ) (e f : ℕ → ℕ) : ∃ σ, Good k e f σ (par k e f) := by
  induction k generalizing e f with
  | zero =>
    refine ⟨id, ⟨fun _ _ _ _ h => h, fun _ h => h⟩, ?_, ?_⟩
    · intro r hr s hs _
      simp only [pow_zero, coe_range, Set.mem_Iio, Nat.lt_one_iff] at hr hs; rw [hr, hs]
    · intro r hr
      have : r = 0 := by omega
      subst this; simp [elt, par]
  | succ k ih =>
    have hsplit := par_split k e f
    have hM : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hk2 : k + 1 + 1 = k + 2 := rfl
    rcases Nat.mod_two_eq_zero_or_one (par (k + 1) e f) with hp | hp
    · -- `p = 0`: evens with evens, odds with odds
      obtain ⟨σ0, ⟨i0, m0⟩, j0, q0⟩ := ih (fun s => e (2 * s)) (fun s => f (2 * s))
      obtain ⟨σ1, ⟨i1, m1⟩, j1, q1⟩ := ih (fun s => e (2 * s + 1)) (fun s => f (2 * s + 1))
      have hp0 : par (k + 1) e f = 0 := by
        have := Nat.mod_lt (∑ r ∈ range (2 ^ (k + 1)), (e r + f r)) two_pos
        simp only [par] at hp ⊢; omega
      have hq : par k (fun s => e (2 * s)) (fun s => f (2 * s)) =
          par k (fun s => e (2 * s + 1)) (fun s => f (2 * s + 1)) := by
        have h0 := Nat.mod_lt (∑ r ∈ range (2 ^ k), (e (2 * r) + f (2 * r))) two_pos
        have h1 := Nat.mod_lt (∑ r ∈ range (2 ^ k), (e (2 * r + 1) + f (2 * r + 1))) two_pos
        have := hsplit.1; simp only [par] at *; omega
      set σ : ℕ → ℕ := fun r => if r % 2 = 0 then 2 * σ0 (r / 2) else 2 * σ1 (r / 2) + 1
      have σe : ∀ s, σ (2 * s) = 2 * σ0 s := by intro s; simp [σ]
      have σo : ∀ s, σ (2 * s + 1) = 2 * σ1 s + 1 := by
        intro s; simp only [σ]
        rw [ite_eq_right_iff.mpr (by omega), show (2 * s + 1) / 2 = s by omega]
      set T0 := fun s => elt k (fun s => e (2 * s)) s + elt k (fun s => f (2 * s)) (σ0 s)
      set T1 := fun s => elt k (fun s => e (2 * s + 1)) s + elt k (fun s => f (2 * s + 1)) (σ1 s)
      have se : ∀ s, elt (k + 1) e (2 * s) + elt (k + 1) f (σ (2 * s)) = 2 * T0 s := by
        intro s; rw [σe, elt_even, elt_even]; simp only [T0]; ring
      have so : ∀ s,
          elt (k + 1) e (2 * s + 1) + elt (k + 1) f (σ (2 * s + 1)) = 2 * (T1 s + 1) := by
        intro s; rw [σo, elt_odd, elt_odd]; simp only [T1]; ring
      have mem : ∀ s < 2 ^ k, s ∈ (range (2 ^ k) : Set ℕ) := fun s hs => by simpa using hs
      refine ⟨σ, ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [hM]
        refine injOn_split σ (fun s hs s' hs' h => ?_) (fun s hs s' hs' h => ?_)
          (fun s _ s' _ h => ?_)
        · rw [σe, σe] at h; exact i0 (mem s hs) (mem s' hs') (by omega)
        · rw [σo, σo] at h; exact i1 (mem s hs) (mem s' hs') (by omega)
        · rw [σe, σo] at h; omega
      · intro r hr
        simp only [coe_range, Set.mem_Iio] at hr ⊢
        rw [hM] at hr ⊢
        refine forall_split (P := fun r => σ r < 2 * 2 ^ k) (fun s hs => ?_) (fun s hs => ?_) r hr
        · have := m0 (mem s hs); simp only [coe_range, Set.mem_Iio] at this; rw [σe]; omega
        · have := m1 (mem s hs); simp only [coe_range, Set.mem_Iio] at this; rw [σo]; omega
      · rw [hM]
        refine injOn_split _ (fun s hs s' hs' h => ?_) (fun s hs s' hs' h => ?_)
          (fun s hs s' hs' h => ?_)
        · try simp only at h
          rw [se, se, hk2, mod_double] at h; exact j0 (mem s hs) (mem s' hs') h
        · try simp only at h
          rw [so, so, hk2, mod_double] at h
          exact j1 (mem s hs) (mem s' hs') (Nat.ModEq.add_right_cancel' 1 h)
        · try simp only at h
          rw [se, so, hk2, mod_double] at h
          have h2 := congrArg (· % 2) h; simp only [mod_pow_mod_two] at h2
          have a := q0 s hs; have b := q1 s' hs'
          rw [show elt k (fun s => e (2 * s)) s + elt k (fun s => f (2 * s)) (σ0 s) = T0 s
            from rfl] at a
          rw [show elt k (fun s => e (2 * s + 1)) s' +
              elt k (fun s => f (2 * s + 1)) (σ1 s') = T1 s'
            from rfl] at b
          omega
      · rw [hM, hp0]
        refine forall_split (P := fun r => (elt (k + 1) e r + elt (k + 1) f (σ r)) % 2 = 0)
          (fun s _ => ?_) (fun s _ => ?_)
        · try simp only
          rw [se]; omega
        · try simp only
          rw [so]; omega
    · -- `p = 1`: evens with odds, odds with evens
      obtain ⟨σ0, ⟨i0, m0⟩, j0, q0⟩ := ih (fun s => e (2 * s)) (fun s => f (2 * s + 1))
      obtain ⟨σ1, ⟨i1, m1⟩, j1, q1⟩ := ih (fun s => e (2 * s + 1)) (fun s => f (2 * s))
      have hq : par k (fun s => e (2 * s)) (fun s => f (2 * s + 1)) ≠
          par k (fun s => e (2 * s + 1)) (fun s => f (2 * s)) := by
        have := hsplit.2; simp only [par] at *; omega
      set σ : ℕ → ℕ := fun r => if r % 2 = 0 then 2 * σ0 (r / 2) + 1 else 2 * σ1 (r / 2)
      have σe : ∀ s, σ (2 * s) = 2 * σ0 s + 1 := by intro s; simp [σ]
      have σo : ∀ s, σ (2 * s + 1) = 2 * σ1 s := by
        intro s; simp only [σ]
        rw [ite_eq_right_iff.mpr (by omega), show (2 * s + 1) / 2 = s by omega]
      set T0 := fun s => elt k (fun s => e (2 * s)) s + elt k (fun s => f (2 * s + 1)) (σ0 s)
      set T1 := fun s => elt k (fun s => e (2 * s + 1)) s + elt k (fun s => f (2 * s)) (σ1 s)
      have se : ∀ s, elt (k + 1) e (2 * s) + elt (k + 1) f (σ (2 * s)) = 2 * T0 s + 1 := by
        intro s; rw [σe, elt_even, elt_odd]; simp only [T0]; ring
      have so : ∀ s, elt (k + 1) e (2 * s + 1) + elt (k + 1) f (σ (2 * s + 1)) = 2 * T1 s + 1 := by
        intro s; rw [σo, elt_odd, elt_even]; simp only [T1]; ring
      have mem : ∀ s < 2 ^ k, s ∈ (range (2 ^ k) : Set ℕ) := fun s hs => by simpa using hs
      refine ⟨σ, ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [hM]
        refine injOn_split σ (fun s hs s' hs' h => ?_) (fun s hs s' hs' h => ?_)
          (fun s _ s' _ h => ?_)
        · rw [σe, σe] at h; exact i0 (mem s hs) (mem s' hs') (by omega)
        · rw [σo, σo] at h; exact i1 (mem s hs) (mem s' hs') (by omega)
        · rw [σe, σo] at h; omega
      · intro r hr
        simp only [coe_range, Set.mem_Iio] at hr ⊢
        rw [hM] at hr ⊢
        refine forall_split (P := fun r => σ r < 2 * 2 ^ k) (fun s hs => ?_) (fun s hs => ?_) r hr
        · have := m0 (mem s hs); simp only [coe_range, Set.mem_Iio] at this; rw [σe]; omega
        · have := m1 (mem s hs); simp only [coe_range, Set.mem_Iio] at this; rw [σo]; omega
      · rw [hM]
        refine injOn_split _ (fun s hs s' hs' h => ?_) (fun s hs s' hs' h => ?_)
          (fun s hs s' hs' h => ?_)
        · try simp only at h
          rw [se, se, hk2, mod_double_add_one] at h
          exact j0 (mem s hs) (mem s' hs') h
        · try simp only at h
          rw [so, so, hk2, mod_double_add_one] at h
          exact j1 (mem s hs) (mem s' hs') h
        · try simp only at h
          rw [se, so, hk2, mod_double_add_one] at h
          have h2 := congrArg (· % 2) h; simp only [mod_pow_mod_two] at h2
          have a := q0 s hs; have b := q1 s' hs'
          rw [show elt k (fun s => e (2 * s)) s + elt k (fun s => f (2 * s + 1)) (σ0 s) = T0 s
            from rfl] at a
          rw [show elt k (fun s => e (2 * s + 1)) s' + elt k (fun s => f (2 * s)) (σ1 s') = T1 s'
            from rfl] at b
          omega
      · have hp1 : par (k + 1) e f = 1 := by unfold par at hp ⊢; rwa [Nat.mod_mod] at hp
        rw [hM, hp1]
        refine forall_split (P := fun r => (elt (k + 1) e r + elt (k + 1) f (σ r)) % 2 = 1)
          (fun s _ => ?_) (fun s _ => ?_)
        · try simp only
          rw [se]; omega
        · try simp only
          rw [so]; omega

/-- The residues below `2 n` of parity `q` are `2 s + q`, `s < n`. -/
lemma filter_parity (n q : ℕ) (hq : q < 2) :
    (range (2 * n)).filter (fun t => t % 2 = q) = (range n).image (fun s => 2 * s + q) := by
  ext t; simp only [mem_filter, mem_range, mem_image]; constructor
  · rintro ⟨h1, h2⟩; exact ⟨t / 2, by omega, by omega⟩
  · rintro ⟨s, hs, rfl⟩; omega

lemma card_parity (n q : ℕ) (hq : q < 2) :
    ((range (2 * n)).filter (fun t => t % 2 = q)).card = n := by
  rw [filter_parity n q hq, card_image_of_injOn (fun a _ b _ h => by omega),
    card_range]

lemma sum_parity (n q : ℕ) (hq : q < 2) :
    ∑ t ∈ (range (2 * n)).filter (fun t => t % 2 = q), t = n * (n - 1) + q * n := by
  rw [filter_parity n q hq, sum_image (fun a _ b _ h => by omega), sum_add_distrib,
    ← mul_sum, sum_const, card_range, smul_eq_mul,
    show 2 * ∑ i ∈ range n, i = n * (n - 1) by rw [mul_comm]; exact sum_range_id_mul_two n]
  ring

/-- A matching with pairwise different sums of a single parity `q` has `q = p`. -/
theorem parity_forced (k : ℕ) (e f σ : ℕ → ℕ) (q : ℕ) (hq : q < 2) (h : Good k e f σ q) :
    q = par k e f := by
  obtain ⟨⟨hinj, hmap⟩, hsum, hpar⟩ := h
  set M := 2 ^ k with hM
  have h2M : 2 ^ (k + 1) = 2 * M := by rw [hM]; ring
  set v := fun r => (elt k e r + elt k f (σ r)) % 2 ^ (k + 1)
  -- the values are exactly the residues of parity `q`
  have himg : (range M).image v = (range (2 * M)).filter (fun t => t % 2 = q) := by
    apply eq_of_subset_of_card_le
    · intro t ht
      obtain ⟨r, hr, rfl⟩ := mem_image.mp ht
      simp only [mem_filter, mem_range, v]
      refine ⟨by rw [← h2M]; exact Nat.mod_lt _ (by positivity), ?_⟩
      rw [mod_pow_mod_two]; exact hpar r (mem_range.mp hr)
    · rw [card_image_of_injOn hsum, card_range, card_parity M q hq]
  -- `σ` permutes `{0, …, M - 1}`
  have hσ : (range M).image σ = range M := by
    apply eq_of_subset_of_card_le
    · intro t ht; obtain ⟨r, hr, rfl⟩ := mem_image.mp ht; exact hmap hr
    · rw [card_image_of_injOn hinj]
  have hperm : ∑ r ∈ range M, elt k f (σ r) = ∑ r ∈ range M, elt k f r := by
    rw [← sum_image hinj, hσ]
  -- the total of all elements, two ways, modulo `2M`
  have htot : ∑ r ∈ range M, (elt k e r + elt k f (σ r)) ≡
      ∑ t ∈ (range (2 * M)).filter (fun t => t % 2 = q), t [MOD 2 * M] := by
    rw [← himg, sum_image hsum]
    unfold Nat.ModEq
    rw [Finset.sum_nat_mod]
    simp only [v, h2M]
  rw [sum_add_distrib, hperm, sum_parity M q hq] at htot
  simp only [elt, sum_add_distrib, ← mul_sum] at htot
  have hS : 2 * ∑ i ∈ range M, i = M * (M - 1) := by rw [mul_comm]; exact sum_range_id_mul_two M
  have hre : ∑ x ∈ range M, x + M * ∑ i ∈ range M, e i + (∑ x ∈ range M, x + M * ∑ i ∈ range M, f i)
      = M * (M - 1) + M * (∑ i ∈ range M, e i + ∑ i ∈ range M, f i) := by
    rw [← hS]; ring
  rw [hre] at htot
  have h3 := Nat.ModEq.add_left_cancel' (M * (M - 1)) htot
  rw [mul_comm q M, show 2 * M = M * 2 by ring] at h3
  have h4 := Nat.ModEq.mul_left_cancel' (by positivity : M ≠ 0) h3
  unfold Nat.ModEq at h4
  unfold par; rw [sum_add_distrib, ← hM]
  omega

/-- For `k ≥ 1` the sums `r + σ r` of a permutation are never pairwise different modulo `2^k`: they
would be all the residues, adding up to `S = 2^(k-1)(2^k - 1)`, while `∑ (r + σ r) = 2 S ≡ 0`. -/
theorem not_distinct_mod (k : ℕ) (hk : 1 ≤ k) (σ : ℕ → ℕ) (hσ : IsPerm k σ) :
    ¬ Set.InjOn (fun r => (r + σ r) % 2 ^ k) (range (2 ^ k)) := by
  intro hinj
  obtain ⟨hi, hm⟩ := hσ
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set M := 2 ^ (j + 1) with hM
  set m := 2 ^ j with hm'
  have hMm : M = 2 * m := by rw [hM, hm']; ring
  have hm0 : 0 < m := by positivity
  have himg : (range M).image (fun r => (r + σ r) % M) = range M := by
    apply eq_of_subset_of_card_le
    · intro t ht; obtain ⟨r, _, rfl⟩ := mem_image.mp ht
      exact mem_range.mpr (Nat.mod_lt _ (by positivity))
    · rw [card_image_of_injOn hinj]
  have hσ : (range M).image σ = range M := by
    apply eq_of_subset_of_card_le
    · intro t ht; obtain ⟨r, hr, rfl⟩ := mem_image.mp ht; exact hm hr
    · rw [card_image_of_injOn hi]
  set S := ∑ i ∈ range M, i with hSdef
  have hS : S * 2 = M * (M - 1) := sum_range_id_mul_two M
  have hσsum : ∑ r ∈ range M, σ r = S :=
    calc ∑ r ∈ range M, σ r = ∑ t ∈ (range M).image σ, t := (sum_image (f := fun t => t) hi).symm
      _ = S := by rw [hσ]
  have hsum : ∑ r ∈ range M, (r + σ r) = 2 * S := by rw [sum_add_distrib, hσsum]; ring
  -- reduce both totals modulo `M`
  have hw : ∑ r ∈ range M, (r + σ r) % M = S :=
    calc ∑ r ∈ range M, (r + σ r) % M
        = ∑ t ∈ (range M).image (fun r => (r + σ r) % M), t :=
          (sum_image (f := fun t => t) hinj).symm
      _ = S := by rw [himg]
  have h1 : (∑ r ∈ range M, (r + σ r)) % M = S % M := by rw [Finset.sum_nat_mod, hw]
  rw [hsum] at h1
  have hS' : S = m * (2 * m - 1) := by
    have : S * 2 = (m * (2 * m - 1)) * 2 := by rw [hS, hMm]; ring
    omega
  have e1 : 2 * S = M * (2 * m - 1) := by rw [hS', hMm]; ring
  have e2 : S = m + M * (m - 1) := by
    obtain ⟨t, ht⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
    rw [hS', hMm, ht, show 2 * (t + 1) - 1 = 2 * t + 1 by omega, show t + 1 - 1 = t by omega]
    ring
  rw [e1, Nat.mul_mod_right, e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at h1
  omega

end PowerTwoMatching
