import LeanProofs.Precarious.Basic

/-!
# Precarious necklaces (MO 515996): the lower bound

`a k` is `2m · p_m#` for `k = 2m` and `p_m# · (2m p_{m+1} + 1)` for `k = 2m + 1`, where `p_m#` (`pr m`) is
the product of the first `m` primes. `lower_bound`: every precarious word with `k` colours has length at
least `a k`.

Route. Pick for each colour `c` a prime `q c` dividing its repeat count. A prime is picked by at most two
colours (`prime_dvd_at_most_two`). Every count `n_x` is divisible by the product of the primes picked by the
other colours (`count_dvd_of_pow`), so `n_x` is at least the product of all `t` picked primes, or of all but
its own when `x` is unpaired. With `S` unpaired colours, `k + S = 2t` and
`|w| ≥ (k - S) p_t# + S p_{t-1}#` (`prod_ge_pr`: `t` distinct primes multiply to at least `p_t#`), and
`final_arith` turns this into `a k`.
-/

set_option linter.unusedSectionVars false

namespace Precarious

open Finset

/-- Product of the first `m` primes. -/
noncomputable def pr (m : ℕ) : ℕ := ∏ i ∈ range m, Nat.nth Nat.Prime i

/-- The conjectured (and here proved) minimum length. -/
noncomputable def a (k : ℕ) : ℕ :=
  if k % 2 = 0 then k * pr (k / 2) else pr (k / 2) * ((k - 1) * Nat.nth Nat.Prime (k / 2) + 1)

lemma pr_succ (m : ℕ) : pr (m + 1) = pr m * Nat.nth Nat.Prime m := by
  simp [pr, Finset.prod_range_succ]

lemma pr_pos (m : ℕ) : 0 < pr m :=
  prod_pos (fun i _ => (Nat.prime_nth_prime i).pos)

lemma pr_mono {i j : ℕ} (h : i ≤ j) : pr i ≤ pr j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    rw [pr_succ]
    exact ih.trans (Nat.le_mul_of_pos_right _ (Nat.prime_nth_prime j).pos)

/-- `t` distinct primes multiply to at least the product of the first `t` primes. -/
lemma prod_ge_pr (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) : pr T.card ≤ ∏ p ∈ T, p := by
  revert hT
  refine Finset.induction_on_max T (fun _ => by simp [pr]) ?_
  intro b s hlt ih hT
  have hb : b ∉ s := fun h => lt_irrefl b (hlt b h)
  rw [card_insert_of_notMem hb, prod_insert hb, pr_succ, mul_comm b]
  apply Nat.mul_le_mul (ih (fun p hp => hT p (mem_insert_of_mem hp)))
  -- `insert b s` holds `s.card + 1` primes, all at most `b`
  have hcount : s.card < Nat.count Nat.Prime (b + 1) := by
    rw [Nat.count_eq_card_filter_range]
    have hsub : insert b s ⊆ (range (b + 1)).filter Nat.Prime := by
      intro p hp
      simp only [mem_filter, mem_range]
      refine ⟨?_, hT p hp⟩
      rcases mem_insert.mp hp with rfl | h
      · omega
      · have := hlt p h; omega
    have h3 := card_le_card hsub
    rw [card_insert_of_notMem hb] at h3
    calc s.card < s.card + 1 := Nat.lt_succ_self _
      _ ≤ _ := by convert h3 using 2
  have := Nat.nth_lt_of_lt_count hcount
  omega

/-- The formula reproduces the known values `a(2..5) = 4, 14, 24, 126` and gives `a 6 = 180`, `a 7 = 1290`. -/
lemma a_values : a 2 = 4 ∧ a 3 = 14 ∧ a 4 = 24 ∧ a 5 = 126 ∧ a 6 = 180 ∧ a 7 = 1290 := by
  simp [a, pr, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]

/-- The final inequality, with `k + S = 2t`. -/
lemma final_arith (k t S : ℕ) (h : k + S = 2 * t) (hSt : S ≤ t) :
    a k ≤ (k - S) * pr t + S * pr (t - 1) := by
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · have hk : k % 2 = 0 := by omega
    simp [a, hk, show k / 2 = t by omega]
  -- with an unpaired colour, both terms are at least `pr (t - 1)`
  have hmono : pr (t - 1) ≤ pr t := pr_mono (by omega)
  have hlow : k * pr (t - 1) ≤ (k - S) * pr t + S * pr (t - 1) := by
    have : (k - S) * pr (t - 1) ≤ (k - S) * pr t := Nat.mul_le_mul_left _ hmono
    have hk : k * pr (t - 1) = (k - S) * pr (t - 1) + S * pr (t - 1) := by
      rw [← add_mul, Nat.sub_add_cancel (by omega)]
    omega
  by_cases hk : k % 2 = 0
  · -- `S` even, so `S ≥ 2` and `t - 1 ≥ k / 2`
    simp only [a, hk, if_true]
    exact (Nat.mul_le_mul_left k (pr_mono (by omega))).trans hlow
  · simp only [a, hk, if_false]
    set m := k / 2 with hm
    have hk1 : k = 2 * m + 1 := by omega
    rcases Nat.lt_or_ge S 3 with hS3 | hS3
    · -- `S = 1`: equality
      have hS1 : S = 1 := by omega
      subst hS1
      have ht : t = m + 1 := by omega
      rw [ht, pr_succ, show m + 1 - 1 = m by omega, show k - 1 = 2 * m by omega]
      ring_nf; omega
    · -- `S ≥ 3`: `t - 1 ≥ m + 1`
      have h1 : k * pr (m + 1) ≤ k * pr (t - 1) := Nat.mul_le_mul_left k (pr_mono (by omega))
      have h2 : pr m * ((k - 1) * Nat.nth Nat.Prime m + 1) ≤ k * pr (m + 1) := by
        rw [pr_succ, show k - 1 = 2 * m by omega, hk1]
        have hp : 1 ≤ Nat.nth Nat.Prime m := (Nat.prime_nth_prime m).one_lt.le
        nlinarith [pr_pos m]
      omega

variable {α : Type*} [DecidableEq α]

/-- **Lower bound.** A precarious word with `k` colours has length at least `a k`. -/
theorem lower_bound (w : List α) (hw : IsPrecarious w) : a w.toFinset.card ≤ w.length := by
  classical
  set C := w.toFinset with hC
  -- repeat counts
  have hsym : ∀ c ∈ w, ∃ r, 2 ≤ r ∧ IsPow (del c w) r := fun c hc => hw.2.2 c hc
  let r : α → ℕ := fun c => if h : c ∈ w then Classical.choose (hsym c h) else 2
  have hr2 : ∀ c, 2 ≤ r c := by
    intro c; dsimp only [r]; split_ifs with h
    · exact (Classical.choose_spec (hsym c h)).1
    · exact le_rfl
  have hrpow : ∀ c ∈ w, IsPow (del c w) (r c) := by
    intro c h; dsimp only [r]; rw [dif_pos h]; exact (Classical.choose_spec (hsym c h)).2
  -- one prime per colour
  let q : α → ℕ := fun c => (r c).minFac
  have hqp : ∀ c, (q c).Prime := fun c => Nat.minFac_prime (by have := hr2 c; omega)
  have hqdvd : ∀ c, q c ∣ r c := fun c => Nat.minFac_dvd _
  have hfib : ∀ p, (C.filter (fun c => q c = p)).card ≤ 2 := by
    intro p
    by_cases hp : p.Prime
    · refine le_trans (card_le_card ?_) (prime_dvd_at_most_two w hw r hrpow p hp)
      intro c hc
      simp only [mem_filter] at hc ⊢
      exact ⟨hc.1, hc.2 ▸ hqdvd c⟩
    · have : C.filter (fun c => q c = p) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro c _ hcp; exact hp (hcp ▸ hqp c)
      simp [this]
  set T := C.image q with hT
  have hTp : ∀ p ∈ T, p.Prime := by
    intro p hp; obtain ⟨c, _, rfl⟩ := mem_image.mp hp; exact hqp c
  -- `x` is unpaired when no other colour picks its prime
  let lone : α → Prop := fun x => ∀ c ∈ C, c ≠ x → q c ≠ q x
  set Sset := C.filter lone with hSset
  -- each count is at least the product of the other colours' primes
  have hcount : ∀ x ∈ C, (if lone x then ∏ p ∈ T.erase (q x), p else ∏ p ∈ T, p) ≤ w.count x := by
    intro x hxC
    have hx : x ∈ w := List.mem_toFinset.mp hxC
    have hpos : 0 < w.count x := List.count_pos_iff.mpr hx
    have hdiv : ∀ c ∈ C, c ≠ x → q c ∣ w.count x := fun c hcC hcx =>
      (hqdvd c).trans (count_dvd_of_pow (hrpow c (List.mem_toFinset.mp hcC)) (Ne.symm hcx))
    have hprod : ∀ U ⊆ T, (∀ p ∈ U, ∃ c ∈ C, c ≠ x ∧ q c = p) → ∏ p ∈ U, p ≤ w.count x := by
      intro U hU hcov
      apply Nat.le_of_dvd hpos
      apply Finset.prod_primes_dvd
      · intro p hp; exact (hTp p (hU hp)).prime
      · intro p hp; obtain ⟨c, hcC, hcx, rfl⟩ := hcov p hp; exact hdiv c hcC hcx
    split_ifs with hl
    · apply hprod _ (erase_subset _ _)
      intro p hp
      obtain ⟨hpx, hpT⟩ := mem_erase.mp hp
      obtain ⟨c, hcC, rfl⟩ := mem_image.mp hpT
      exact ⟨c, hcC, fun h => hpx (h ▸ rfl), rfl⟩
    · apply hprod _ subset_rfl
      intro p hpT
      obtain ⟨c, hcC, rfl⟩ := mem_image.mp hpT
      by_cases hcx : c = x
      · subst hcx
        simp only [lone, not_forall, not_not] at hl
        obtain ⟨d, hdC, hdx, hdq⟩ := hl
        exact ⟨d, hdC, hdx, hdq⟩
      · exact ⟨c, hcC, hcx, rfl⟩
  -- the length is the sum of the counts
  have hlen : w.length = ∑ x ∈ C, w.count x := (List.sum_toFinset_count_eq_length w).symm
  have ht1 : 1 ≤ T.card := by
    have : 2 ≤ C.card := hw.2.1
    obtain ⟨x, hx⟩ : C.Nonempty := card_pos.mp (by omega)
    exact card_pos.mpr ⟨q x, mem_image_of_mem q hx⟩
  have hsum : (C.card - Sset.card) * pr T.card + Sset.card * pr (T.card - 1) ≤ w.length := by
    rw [hlen]
    have hnot : (C.filter (fun x => ¬ lone x)).card = C.card - Sset.card := by
      have := Finset.card_filter_add_card_filter_not (s := C) lone
      rw [hSset]; omega
    have hA : Sset.card * pr (T.card - 1) ≤ ∑ x ∈ C.filter lone, w.count x := by
      rw [← hSset, ← smul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro x hx
      have hxC : x ∈ C := (mem_filter.mp hx).1
      have hl : lone x := (mem_filter.mp hx).2
      have := hcount x hxC
      rw [if_pos hl] at this
      refine le_trans ?_ this
      have hq : q x ∈ T := mem_image_of_mem q hxC
      have := prod_ge_pr (T.erase (q x)) (fun p hp => hTp p (mem_of_mem_erase hp))
      rwa [card_erase_of_mem hq] at this
    have hB : (C.card - Sset.card) * pr T.card ≤ ∑ x ∈ C.filter (fun x => ¬ lone x), w.count x := by
      rw [← hnot, ← smul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro x hx
      have hxC : x ∈ C := (mem_filter.mp hx).1
      have hl : ¬ lone x := (mem_filter.mp hx).2
      have := hcount x hxC
      rw [if_neg hl] at this
      exact (prod_ge_pr T hTp).trans this
    calc (C.card - Sset.card) * pr T.card + Sset.card * pr (T.card - 1)
        ≤ ∑ x ∈ C.filter (fun x => ¬ lone x), w.count x + ∑ x ∈ C.filter lone, w.count x :=
          Nat.add_le_add hB hA
      _ = ∑ x ∈ C, w.count x := by
          rw [add_comm]; convert Finset.sum_filter_add_sum_filter_not C lone (fun x => w.count x)
  -- `k + S = 2t`: fibres have size 1 or 2, and the unpaired colours are the size-1 fibres
  have hkS : C.card + Sset.card = 2 * T.card := by
    have hk : C.card = ∑ p ∈ T, (C.filter (fun c => q c = p)).card :=
      card_eq_sum_card_image q C
    have hS : Sset.card = ∑ p ∈ T, (Sset.filter (fun c => q c = p)).card :=
      card_eq_sum_card_fiberwise (fun x hx => mem_image_of_mem q (mem_filter.mp hx).1)
    rw [hk, hS, ← sum_add_distrib, mul_comm, ← smul_eq_mul, ← sum_const]
    apply sum_congr rfl
    intro p hp
    obtain ⟨c, hcC, rfl⟩ := mem_image.mp hp
    have hle := hfib (q c)
    have hge : 1 ≤ (C.filter (fun d => q d = q c)).card :=
      card_pos.mpr ⟨c, mem_filter.mpr ⟨hcC, rfl⟩⟩
    rcases (show (C.filter (fun d => q d = q c)).card = 1 ∨ (C.filter (fun d => q d = q c)).card = 2 by omega)
      with h1 | h2
    · -- the fibre is `{c}` and `c` is unpaired
      have hlone : lone c := by
        intro d hdC hdc hdq
        have hsub : ({c, d} : Finset α) ⊆ C.filter (fun e => q e = q c) := by
          intro e he
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with h | h
          · rw [h]; exact mem_filter.mpr ⟨hcC, rfl⟩
          · rw [h]; exact mem_filter.mpr ⟨hdC, hdq⟩
        have := card_le_card hsub
        rw [card_pair (Ne.symm hdc)] at this; omega
      have : Sset.filter (fun d => q d = q c) = C.filter (fun d => q d = q c) := by
        ext d
        simp only [hSset, mem_filter]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨hdC, hdq⟩
          refine ⟨⟨hdC, ?_⟩, hdq⟩
          by_cases hdc : d = c
          · subst hdc; exact hlone
          · exact absurd (hlone d hdC hdc hdq) (by simp)
      rw [this, h1]
    · -- two colours share the prime: neither is unpaired
      have : Sset.filter (fun d => q d = q c) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro d hd hdq
        have hdl : lone d := (mem_filter.mp hd).2
        have hdC : d ∈ C := (mem_filter.mp hd).1
        obtain ⟨e, he, hed⟩ : ∃ e ∈ C.filter (fun d' => q d' = q c), e ≠ d := by
          by_contra hno
          push Not at hno
          have : C.filter (fun d' => q d' = q c) ⊆ {d} := fun e he => mem_singleton.mpr (hno e he)
          have := card_le_card this; simp at this; omega
        exact hdl e (mem_filter.mp he).1 hed (by rw [(mem_filter.mp he).2, hdq])
      rw [this, h2]; simp
  have hSt : Sset.card ≤ T.card := by
    have : Sset.card ≤ C.card := card_le_card (filter_subset _ _)
    omega
  exact (final_arith C.card T.card Sset.card hkS hSt).trans hsum

end Precarious
