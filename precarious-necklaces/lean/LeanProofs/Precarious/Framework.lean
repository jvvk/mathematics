import LeanProofs.Precarious.Bound

/-!
# Precarious necklaces (MO 515996): keeping `s` colours

`KeepPrec s w`: `w` is not symmetric, but keeping any `s` of its colours (deleting the other `k - s`) leaves a
symmetric necklace. `s = k - 1` is the original problem.

* `keep_framework`: each kept set `S` gets a prime `c S` dividing its repeat count, so `c S` divides the count
  of every colour in `S`, and no single prime's sets contain every pair of colours (else every two-colour
  projection is a power, so `w` is, by `pow_of_pairs`).
* `keep_two_bound`: every two-colour sub-necklace symmetric and `k ≥ 3` colours give `|w| ≥ 2k + 8`.
* `keep_three_bound`: keeping any `s ≥ 3` colours gives `|w| ≥ 6k`.
-/

set_option linter.unusedSectionVars false

namespace Precarious

open List Finset

variable {α : Type*} [DecidableEq α]

/-- Keep only the colours in `S`. -/
def keep (S : Finset α) (w : List α) : List α := w.filter (fun z => z ∈ S)

/-- Not symmetric, but symmetric after keeping any `s` of the colours. -/
def KeepPrec (s : ℕ) (w : List α) : Prop :=
  ¬ Symm w ∧ ∀ S ⊆ w.toFinset, S.card = s → Symm (keep S w)

lemma count_keep {S : Finset α} {x : α} (hx : x ∈ S) (w : List α) : (keep S w).count x = w.count x := by
  simp [keep, count_filter, hx]

lemma pair_keep {S : Finset α} {x y : α} (hx : x ∈ S) (hy : y ∈ S) (w : List α) :
    pair x y (keep S w) = pair x y w := by
  unfold pair keep
  rw [List.filter_filter]
  apply List.filter_congr
  intro z _
  by_cases h : z = x ∨ z = y
  · rcases h with rfl | rfl <;> simp [hx, hy]
  · simp [h]

/-- **Framework.** A prime for every kept set, dividing the counts of its colours, with no prime's sets
covering all pairs. -/
theorem keep_framework (s : ℕ) (w : List α) (hw : KeepPrec s w) (h2 : 2 ≤ w.toFinset.card) :
    ∃ c : Finset α → ℕ,
      (∀ S, (c S).Prime) ∧
      (∀ S ⊆ w.toFinset, S.card = s → ∀ x ∈ S, c S ∣ w.count x) ∧
      (∀ q, ∃ x ∈ w, ∃ y ∈ w, x ≠ y ∧
        ∀ S ⊆ w.toFinset, S.card = s → c S = q → ¬ (x ∈ S ∧ y ∈ S)) := by
  classical
  set C := w.toFinset
  have hsym : ∀ S, S ⊆ C ∧ S.card = s → ∃ r, 2 ≤ r ∧ IsPow (keep S w) r :=
    fun S hS => hw.2 S hS.1 hS.2
  let r : Finset α → ℕ := fun S => if h : S ⊆ C ∧ S.card = s then Classical.choose (hsym S h) else 2
  have hr2 : ∀ S, 2 ≤ r S := by
    intro S; dsimp only [r]; split_ifs with h
    · exact (Classical.choose_spec (hsym S h)).1
    · exact le_rfl
  have hrpow : ∀ S, S ⊆ C → S.card = s → IsPow (keep S w) (r S) := by
    intro S h1 h2; dsimp only [r]; rw [dif_pos ⟨h1, h2⟩]; exact (Classical.choose_spec (hsym S ⟨h1, h2⟩)).2
  refine ⟨fun S => (r S).minFac, fun S => Nat.minFac_prime (by have := hr2 S; omega), ?_, ?_⟩
  · intro S hS hcard x hx
    obtain ⟨v, hv⟩ := hrpow S hS hcard
    refine (Nat.minFac_dvd _).trans ⟨v.count x, ?_⟩
    rw [← count_keep hx w, hv, count_flatten_replicate]
  · intro q
    by_contra hall
    push Not at hall
    -- two colours exist, so `q` is one of the primes
    obtain ⟨x0, hx0, y0, hy0, hxy0⟩ : ∃ x ∈ C, ∃ y ∈ C, x ≠ y := by
      obtain ⟨x, hx, y, hy, h⟩ := Finset.one_lt_card.mp (by omega : 1 < C.card)
      exact ⟨x, hx, y, hy, h⟩
    obtain ⟨S0, -, -, hS0q, -⟩ := hall x0 (List.mem_toFinset.mp hx0) y0 (List.mem_toFinset.mp hy0) hxy0
    have hqp : q.Prime := hS0q ▸ Nat.minFac_prime (by have := hr2 S0; omega)
    apply hw.1
    refine ⟨q, hqp.two_le, pow_of_pairs w q hqp.one_lt.le h2 ?_⟩
    intro x hx y hy hxy
    obtain ⟨S, hSC, hSs, hSq, hxS, hyS⟩ := hall x hx y hy hxy
    obtain ⟨U, hU⟩ := hrpow S hSC hSs
    obtain ⟨m, hm⟩ : q ∣ r S := hSq ▸ Nat.minFac_dvd _
    refine ⟨((replicate m U).flatten).filter (fun z => z = x ∨ z = y), ?_⟩
    rw [← pair_keep hxS hyS w, pair, hU, hm, flatten_replicate_mul, filter_flatten_replicate]

lemma six_le_of_two_primes {n p₁ p₂ : ℕ} (hn : 0 < n) (h1 : p₁.Prime) (h2 : p₂.Prime) (hne : p₁ ≠ p₂)
    (d1 : p₁ ∣ n) (d2 : p₂ ∣ n) : 6 ≤ n := by
  have hcop : Nat.Coprime p₁ p₂ := (Nat.coprime_primes h1 h2).mpr hne
  have := Nat.le_of_dvd hn (hcop.mul_dvd_of_dvd_of_dvd d1 d2)
  have a1 := h1.two_le; have a2 := h2.two_le
  rcases Nat.lt_or_ge p₁ 3 with h | h
  · have : p₁ = 2 := by omega
    subst this
    have : 3 ≤ p₂ := by
      rcases Nat.lt_or_ge p₂ 3 with h' | h'
      · exact absurd (by omega : p₂ = 2) (Ne.symm hne)
      · exact h'
    nlinarith
  · nlinarith

/-- **Keeping `s ≥ 3` colours.** Every count is divisible by two distinct primes, so `|w| ≥ 6k`. -/
theorem keep_three_bound (s : ℕ) (hs : 3 ≤ s) (w : List α) (hw : KeepPrec s w)
    (hsk : s ≤ w.toFinset.card) : 6 * w.toFinset.card ≤ w.length := by
  classical
  set C := w.toFinset with hC
  obtain ⟨c, hcp, hdvd, hcov⟩ := keep_framework s w hw (by rw [← hC]; omega)
  have hx6 : ∀ x ∈ C, 6 ≤ w.count x := by
    intro x hxC
    have hx : x ∈ w := List.mem_toFinset.mp hxC
    -- a kept set through `x`
    obtain ⟨S0, hxS0, hS0C, hS0s⟩ := Finset.exists_subsuperset_card_eq
      (Finset.singleton_subset_iff.mpr hxC) (by simp; omega) hsk
    have hxS0' : x ∈ S0 := hxS0 (Finset.mem_singleton_self x)
    by_cases hpure : ∀ S ⊆ C, S.card = s → x ∈ S → c S = c S0
    · exfalso
      obtain ⟨u, hu, v, hv, huv, hnot⟩ := hcov (c S0)
      have huC : u ∈ C := List.mem_toFinset.mpr hu
      have hvC : v ∈ C := List.mem_toFinset.mpr hv
      have hsub : ({x, u, v} : Finset α) ⊆ C := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl <;> assumption
      have hcard3 : ({x, u, v} : Finset α).card ≤ s := le_trans (Finset.card_le_three) hs
      obtain ⟨S, hxuvS, hSC, hSs⟩ := Finset.exists_subsuperset_card_eq hsub hcard3 hsk
      have hxS : x ∈ S := hxuvS (by simp)
      exact hnot S hSC hSs (hpure S hSC hSs hxS) ⟨hxuvS (by simp), hxuvS (by simp)⟩
    · push Not at hpure
      obtain ⟨S, hSC, hSs, hxS, hne⟩ := hpure
      exact six_le_of_two_primes (List.count_pos_iff.mpr hx) (hcp S) (hcp S0) hne
        (hdvd S hSC hSs x hxS) (hdvd S0 hS0C hS0s x hxS0')
  rw [← List.sum_toFinset_count_eq_length, ← hC, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum hx6

/-- **Keeping two colours.** With `k ≥ 3` colours, `|w| ≥ 2k + 8`. -/
theorem keep_two_bound (w : List α) (hw : KeepPrec 2 w) (h3 : 3 ≤ w.toFinset.card) :
    2 * w.toFinset.card + 8 ≤ w.length := by
  classical
  set C := w.toFinset with hC
  obtain ⟨c, hcp, hdvd, hcov⟩ := keep_framework 2 w hw (by rw [← hC]; omega)
  have hpairC : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → ({a, b} : Finset α) ⊆ C ∧ ({a, b} : Finset α).card = 2 :=
    fun a ha b hb hab => ⟨by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                             rcases hz with rfl | rfl <;> assumption, Finset.card_pair hab⟩
  -- a colour is pure when all its pairs carry one prime
  let pure : α → Prop := fun x => ∀ y ∈ C, ∀ z ∈ C, y ≠ x → z ≠ x → c {x, y} = c {x, z}
  set T := C.filter (fun x => ¬ pure x) with hT
  have hT2 : 2 ≤ T.card := by
    by_contra hlt
    push Not at hlt
    -- two pure colours `u₀ ≠ u₁`
    have hP : 2 ≤ (C.filter pure).card := by
      have := Finset.card_filter_add_card_filter_not (s := C) pure
      rw [← hT] at this; omega
    obtain ⟨u₀, hu₀, u₁, hu₁, h01⟩ := Finset.one_lt_card.mp (by omega : 1 < (C.filter pure).card)
    have hu₀C := (Finset.mem_filter.mp hu₀).1
    have hu₁C := (Finset.mem_filter.mp hu₁).1
    have pu₀ := (Finset.mem_filter.mp hu₀).2
    set p := c {u₀, u₁}
    -- every pair at a pure colour carries `p`
    have hpure_p : ∀ u ∈ C, pure u → ∀ y ∈ C, y ≠ u → c {u, y} = p := by
      intro u huC pu y hyC hyu
      by_cases h0 : u = u₀
      · subst h0; exact pu₀ y hyC u₁ hu₁C hyu (Ne.symm h01)
      · -- the pair `{u, u₀}` carries `p`, since `u₀` is pure
        have e1 : c {u, u₀} = p := by
          rw [Finset.pair_comm]; exact pu₀ u huC u₁ hu₁C h0 (Ne.symm h01)
        rw [← e1]; exact pu y hyC u₀ hu₀C hyu (Ne.symm h0)
    -- so every pair carries `p`, since at most one colour is impure
    obtain ⟨u, hu, v, hv, huv, hnot⟩ := hcov p
    have huC : u ∈ C := List.mem_toFinset.mpr hu
    have hvC : v ∈ C := List.mem_toFinset.mpr hv
    have hcuv : c {u, v} = p := by
      by_cases pu : pure u
      · exact hpure_p u huC pu v hvC (Ne.symm huv)
      · by_cases pv : pure v
        · rw [Finset.pair_comm]; exact hpure_p v hvC pv u huC huv
        · have : ({u, v} : Finset α) ⊆ T := by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨huC, pu⟩
            · exact Finset.mem_filter.mpr ⟨hvC, pv⟩
          have := Finset.card_le_card this
          rw [Finset.card_pair huv] at this; omega
    exact hnot {u, v} (hpairC u huC v hvC huv).1 (hpairC u huC v hvC huv).2 hcuv (by simp)
  -- impure colours have count `≥ 6`, all have count `≥ 2`
  have hge2 : ∀ x ∈ C, 2 ≤ w.count x := by
    intro x hxC
    obtain ⟨y, hyC, hyx⟩ : ∃ y ∈ C, y ≠ x := by
      by_contra h; push Not at h
      have : C ⊆ {x} := fun z hz => Finset.mem_singleton.mpr (h z hz)
      have := Finset.card_le_card this; simp at this; omega
    have hP := hdvd {x, y} (hpairC x hxC y hyC (Ne.symm hyx)).1 (hpairC x hxC y hyC (Ne.symm hyx)).2 x (by simp)
    exact (hcp _).two_le.trans (Nat.le_of_dvd (List.count_pos_iff.mpr (List.mem_toFinset.mp hxC)) hP)
  have hge6 : ∀ x ∈ T, 6 ≤ w.count x := by
    intro x hxT
    obtain ⟨hxC, hx⟩ := Finset.mem_filter.mp hxT
    simp only [pure, not_forall] at hx
    obtain ⟨y, hyC, z, hzC, hyx, hzx, hne⟩ := hx
    exact six_le_of_two_primes (List.count_pos_iff.mpr (List.mem_toFinset.mp hxC)) (hcp _) (hcp _) hne
      (hdvd _ (hpairC x hxC y hyC (Ne.symm hyx)).1 (hpairC x hxC y hyC (Ne.symm hyx)).2 x (by simp))
      (hdvd _ (hpairC x hxC z hzC (Ne.symm hzx)).1 (hpairC x hxC z hzC (Ne.symm hzx)).2 x (by simp))
  have hlen : w.length = ∑ x ∈ T, w.count x + ∑ x ∈ C.filter (fun x => ¬ ¬ pure x), w.count x := by
    rw [← List.sum_toFinset_count_eq_length, ← hC, hT]
    exact (Finset.sum_filter_add_sum_filter_not C (fun x => ¬ pure x) _).symm
  have hA : 6 * T.card ≤ ∑ x ∈ T, w.count x := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]; exact Finset.sum_le_sum hge6
  have hB : 2 * (C.filter (fun x => ¬ ¬ pure x)).card ≤ ∑ x ∈ C.filter (fun x => ¬ ¬ pure x), w.count x := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun x hx => hge2 x (Finset.mem_filter.mp hx).1)
  have hcard := Finset.card_filter_add_card_filter_not (s := C) (fun x => ¬ pure x)
  rw [← hT] at hcard
  omega

end Precarious
