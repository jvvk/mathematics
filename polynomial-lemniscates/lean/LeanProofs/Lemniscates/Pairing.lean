import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Lemniscates: the pairing step

The last step of the proof that two Cassini ovals meet in at most six points.

Treat `z` and `conj z` as independent: a solution is a pair `(Z, W) : ℂ × ℂ`, and the antiholomorphic
involution `σ (Z, W) = (conj W, conj Z)` permutes the solutions. Its fixed points are the pairs
`(z, conj z)`, i.e. the actual intersection points.

`fixed_card_le_six`: if a multiset of eight solutions is `σ`-invariant and its variance
`∑ (Z - m) (W - conj m)` is a negative real, then at most six of its members (with multiplicity)
are fixed by `σ`. A fixed member contributes `‖Z - m‖² ≥ 0`, so not all eight are fixed, and the
non-fixed members come in `σ`-pairs, so the fixed ones cannot number exactly seven.
-/

open ComplexConjugate

namespace Lemniscates

/-- The involution `(Z, W) ↦ (conj W, conj Z)`. -/
def σ (p : ℂ × ℂ) : ℂ × ℂ := (conj p.2, conj p.1)

@[simp] lemma σ_σ (p : ℂ × ℂ) : σ (σ p) = p := by
  simp [σ]

lemma σ_injective : Function.Injective σ := fun p q h => by
  simpa using congrArg σ h

/-- The variance summand at `p`, centred at `m`. -/
def φ (m : ℂ) (p : ℂ × ℂ) : ℂ := (p.1 - m) * (p.2 - conj m)

lemma φ_of_fixed (m : ℂ) {p : ℂ × ℂ} (hp : σ p = p) :
    φ m p = ((Complex.normSq (p.1 - m) : ℝ) : ℂ) := by
  have h2 : p.2 = conj p.1 := by
    have := congrArg Prod.fst hp
    simp only [σ] at this
    rw [← this, Complex.conj_conj]
  rw [φ, h2, Complex.normSq_eq_conj_mul_self, ← map_sub, mul_comm]

lemma count_σ {S : Multiset (ℂ × ℂ)} (hS : S.map σ = S) (p : ℂ × ℂ) :
    S.count (σ p) = S.count p := by
  conv_lhs => rw [← hS]
  rw [Multiset.count_map_eq_count' _ _ σ_injective]

/-- If every member of `S` is fixed, the variance has nonnegative real part. -/
lemma re_sum_nonneg_of_all_fixed (m : ℂ) (S : Multiset (ℂ × ℂ)) (h : ∀ p ∈ S, σ p = p) :
    0 ≤ ((S.map (φ m)).sum).re := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Complex.add_re]
    have ha : 0 ≤ (φ m a).re := by
      rw [φ_of_fixed m (h a (Multiset.mem_cons_self a s)), Complex.ofReal_re]
      exact Complex.normSq_nonneg _
    exact add_nonneg ha (ih fun p hp => h p (Multiset.mem_cons_of_mem hp))

/-- **Pairing step.** Eight `σ`-symmetric solutions whose variance is a negative real number
include at most six fixed points of `σ`, counted with multiplicity. -/
theorem fixed_card_le_six (m : ℂ) (S : Multiset (ℂ × ℂ)) (hcard : S.card = 8)
    (hσ : S.map σ = S) {v : ℝ} (hv : v < 0) (hsum : (S.map (φ m)).sum = (v : ℂ)) :
    (S.filter (fun p => σ p = p)).card ≤ 6 := by
  classical
  by_contra hc
  rw [not_le] at hc
  set N := S.filter (fun p => ¬ σ p = p) with hN
  have hsplit : S.filter (fun p => σ p = p) + N = S := Multiset.filter_add_not _ S
  have hcardN : N.card ≤ 1 := by
    have := congrArg Multiset.card hsplit
    rw [Multiset.card_add, hcard] at this
    omega
  -- the non-fixed part is empty: a non-fixed member brings its distinct partner along
  have hN0 : N = 0 := by
    by_contra hne
    obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero hne
    have hqS : q ∈ S := Multiset.mem_of_mem_filter hq
    have hqσ : σ q ≠ q := (Multiset.mem_filter.mp hq).2
    have hσqS : σ q ∈ S := by
      rw [← Multiset.count_pos, count_σ hσ]
      exact Multiset.count_pos.mpr hqS
    have hσqN : σ q ∈ N := Multiset.mem_filter.mpr ⟨hσqS, by rw [σ_σ]; exact fun h => hqσ h.symm⟩
    have hle : ({q, σ q} : Multiset (ℂ × ℂ)) ≤ N := by
      rw [Multiset.le_iff_subset (by simpa [Multiset.nodup_cons] using hqσ.symm)]
      intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hq
      · exact hσqN
    have := Multiset.card_le_card hle
    simp at this
    omega
  have hall : ∀ p ∈ S, σ p = p := by
    intro p hp
    by_contra hpf
    have : p ∈ N := Multiset.mem_filter.mpr ⟨hp, hpf⟩
    rw [hN0] at this
    exact Multiset.notMem_zero p this
  have h0 := re_sum_nonneg_of_all_fixed m S hall
  rw [hsum, Complex.ofReal_re] at h0
  linarith

end Lemniscates

namespace Lemniscates

/-- **Pairing step, any number of solutions.** Let `S` be the solutions with multiplicity, `N` of them,
closed under `σ` as a set, with variance `∑ (Z - m)(W - conj m)` a real number `≤ 0`. Then any finite set of
real points `z` (that is, `σ`-fixed solutions `(z, conj z)`) has at most `N - 2` elements. -/
theorem real_card_le (m : ℂ) (S : Multiset (ℂ × ℂ)) {N : ℕ} (hcard : S.card = N) (hN : 3 ≤ N)
    (hσ : ∀ p ∈ S, σ p ∈ S) {v : ℝ} (hv : v ≤ 0) (hsum : (S.map (φ m)).sum = (v : ℂ))
    (F : Finset ℂ) (hF : ∀ z ∈ F, (z, conj z) ∈ S) : F.card ≤ N - 2 := by
  classical
  by_contra hc
  rw [not_le] at hc
  set e : ℂ → ℂ × ℂ := fun z => (z, conj z) with he
  have he_inj : Function.Injective e := fun z w h => congrArg Prod.fst h
  have hfix : ∀ z, σ (e z) = e z := fun z => by simp [σ, he]
  set E : Multiset (ℂ × ℂ) := (F.image e).val with hE
  have hEnd : E.Nodup := (F.image e).nodup
  have hEle : E ≤ S := (Multiset.le_iff_subset hEnd).mpr fun p hp => by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    exact hF z hz
  have hEcard : E.card = F.card := by
    rw [hE, Finset.card_val, Finset.card_image_of_injective F he_inj]
  set R := S - E with hR
  have hRcard : R.card ≤ 1 := by
    have := Multiset.card_sub hEle
    rw [← hR, hcard, hEcard] at this; omega
  -- every member of `S` is fixed: a non-fixed one would bring a second non-fixed one into `R`
  have hall : ∀ p ∈ S, σ p = p := by
    intro p hp
    by_contra hpf
    have hpR : p ∈ R := by
      rw [hR, Multiset.mem_sub, Multiset.count_eq_zero_of_notMem]
      · exact Multiset.count_pos.mpr hp
      · intro hpE
        obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hpE
        exact hpf (hfix z)
    have hqR : σ p ∈ R := by
      rw [hR, Multiset.mem_sub, Multiset.count_eq_zero_of_notMem]
      · exact Multiset.count_pos.mpr (hσ p hp)
      · intro hqE
        obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hqE
        apply hpf
        have h1 : σ (σ p) = σ p := by rw [← hz, hfix]
        rw [σ_σ] at h1
        exact h1.symm
    have hle : ({p, σ p} : Multiset (ℂ × ℂ)) ≤ R := by
      rw [Multiset.le_iff_subset (by simpa [Multiset.nodup_cons] using fun h => hpf h.symm)]
      intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpR
      · exact hqR
    have := Multiset.card_le_card hle
    simp at this; omega
  -- so the variance is a sum of squares `‖z - m‖²`, which is `≤ 0`: every point is `m`
  have hsq : ∀ p ∈ S, Complex.normSq (p.1 - m) = 0 := by
    have hnn := re_sum_nonneg_of_all_fixed m S hall
    rw [hsum, Complex.ofReal_re] at hnn
    have hzero : ((S.map (φ m)).sum).re = 0 := by rw [hsum, Complex.ofReal_re]; linarith
    intro p hp
    have key : ∀ T : Multiset (ℂ × ℂ), (∀ q ∈ T, σ q = q) → ((T.map (φ m)).sum).re = 0 →
        ∀ q ∈ T, Complex.normSq (q.1 - m) = 0 := by
      intro T
      induction T using Multiset.induction_on with
      | empty => intro _ _ q hq; simp at hq
      | cons a s ih =>
        intro hT hs q hq
        rw [Multiset.map_cons, Multiset.sum_cons, Complex.add_re,
          φ_of_fixed m (hT a (Multiset.mem_cons_self a s)), Complex.ofReal_re] at hs
        have hs' := re_sum_nonneg_of_all_fixed m s fun q hq => hT q (Multiset.mem_cons_of_mem hq)
        have ha := Complex.normSq_nonneg (a.1 - m)
        rcases Multiset.mem_cons.mp hq with rfl | hq'
        · linarith
        · exact ih (fun q hq => hT q (Multiset.mem_cons_of_mem hq)) (by linarith) q hq'
    exact key S hall hzero p hp
  -- hence `F ⊆ {m}`, so `|F| ≤ 1 < N - 1`
  have hFm : F ⊆ {m} := by
    intro z hz
    have := hsq (e z) (hF z hz)
    rw [Complex.normSq_eq_zero, sub_eq_zero] at this
    simpa [he] using this
  have := Finset.card_le_card hFm
  simp at this; omega

end Lemniscates
