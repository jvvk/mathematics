import Mathlib

/-!
# A prime square cut into congruent pieces with half-turns (MO 487157)

The algebra of the note. A tiling of the `p × p` board by translates of a cell set `P` and of its image under an
involution of the board (the half-turn, or one fixed reflection) gives, in the ring `A` of integer Laurent
polynomials in two variables,

  `F * U + σ F * V = R`,   `R = Q_p(x) Q_p(y)`,

where `F` is the cell polynomial of `P`, `U, V` record the translations used for the two orientations, `σ` is the
ring automorphism induced by the involution, and `ε` is evaluation at `(1,1)`. Quoted, not formalised: that `A` is a
unique factorisation domain in which `Q_p(x)` and `Q_p(y)` are prime, and the encoding of a tiling as the identity.

* `orientation_dichotomy`: in any UFD, the identity forces `q₁ ∣ F` or `q₂ ∣ F`, for odd prime `p`.
* `bar_of_dvd`: in `ℤ[x][y]`, a `0/1` polynomial of `x`-degree `< p` and value `p` at `(1,1)` that is divisible by
  `Q_p(x)` is `Q_p(x) y^j`: the cell set is a straight bar.
* `cyclotomic_prime_irreducible`, `cyclotomic_prime_eval_one`: `Q_p` is irreducible over `ℤ` with `Q_p(1) = p`.
-/

namespace PrimeSquares

open Polynomial

section Abstract

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

/-- A nonzero nonunit dividing a product of two primes is divisible by one of them. -/
theorem prime_dvd_of_dvd_mul {q₁ q₂ d : A} (hq₁ : Prime q₁) (hq₂ : Prime q₂) (hd0 : d ≠ 0)
    (hdu : ¬ IsUnit d) (hd : d ∣ q₁ * q₂) : q₁ ∣ d ∨ q₂ ∣ d := by
  obtain ⟨r, hr, hrd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
  have hrp : Prime r := UniqueFactorizationMonoid.irreducible_iff_prime.mp hr
  rcases hrp.dvd_or_dvd (hrd.trans hd) with h | h
  · exact Or.inl ((hrp.associated_of_dvd hq₁ h).symm.dvd.trans hrd)
  · exact Or.inr ((hrp.associated_of_dvd hq₂ h).symm.dvd.trans hrd)

/-- The orientation argument. `σ` is an involutive ring automorphism fixing `R`, `ε` an evaluation to `ℤ` fixed by
`σ`; `u, v` are the numbers of copies in the two orientations. For an odd prime `p`, either orientation polynomial
shares a factor with the board (and then `q₁ ∣ F` or `q₂ ∣ F`), or one orientation is unused and again `F ∣ R`. -/
theorem orientation_dichotomy (σ : A ≃+* A) (hσσ : ∀ a, σ (σ a) = a) (ε : A →+* ℤ)
    (hε : ∀ a, ε (σ a) = ε a) {q₁ q₂ R F U V : A} (hq₁ : Prime q₁) (hq₂ : Prime q₂)
    (hR : R = q₁ * q₂) (hσR : σ R = R) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hεF : ε F = p) {u v : ℕ} (hεU : ε U = u) (hεV : ε V = v) (huv : u + v = p)
    (hU0 : u = 0 → U = 0) (hV0 : v = 0 → V = 0) (htile : F * U + σ F * V = R) :
    q₁ ∣ F ∨ q₂ ∣ F := by
  have hF0 : F ≠ 0 := by
    rintro rfl
    simp at hεF
    exact hp.ne_zero (by exact_mod_cast hεF.symm)
  have hFu : ¬ IsUnit F := by
    intro h
    have := (h.map ε)
    rw [hεF, Int.isUnit_iff] at this
    rcases this with h1 | h1
    · exact hp.one_lt.ne' (by exact_mod_cast h1)
    · have : (0 : ℤ) ≤ p := by positivity
      omega
  by_cases hrel : IsRelPrime F (σ F)
  · -- coprime orientations: F divides the board
    refine prime_dvd_of_dvd_mul hq₁ hq₂ hF0 hFu (hR ▸ ?_)
    -- apply σ to the tiling identity and subtract
    have h2 : σ F * σ U + F * σ V = R := by
      have := congrArg σ htile
      rw [map_add, map_mul, map_mul, hσσ, hσR] at this
      exact this
    have key : F * (U - σ V) = σ F * (σ U - V) := by linear_combination htile - h2
    have hdiv : F ∣ σ U - V := hrel.dvd_of_dvd_mul_left ⟨U - σ V, by rw [← key]⟩
    obtain ⟨H, hH⟩ := hdiv
    have hev : (u : ℤ) - v = p * ε H := by
      have := congrArg ε hH
      rw [map_sub, hε, hεU, hεV, map_mul, hεF] at this
      exact this
    -- p divides 2u, so u = 0 or u = p
    have h2u : (p : ℤ) ∣ 2 * u := ⟨ε H + 1, by
      have : (u : ℤ) + v = p := by exact_mod_cast huv
      linarith⟩
    have h2u' : p ∣ 2 * u := by exact_mod_cast h2u
    have hpu : p ∣ u := by
      rcases (Nat.Prime.dvd_mul hp).mp h2u' with h | h
      · have := Nat.le_of_dvd (by norm_num) h
        have := hp.two_le
        omega
      · exact h
    have hule : u ≤ p := by omega
    rcases Nat.eq_zero_or_pos u with hu | hu
    · -- only the second orientation: σ F * V = R, so F * σ V = σ R = R
      have hU : U = 0 := hU0 hu
      rw [hU, mul_zero, zero_add] at htile
      refine ⟨σ V, ?_⟩
      have := congrArg σ htile
      rw [map_mul, hσσ, hσR] at this
      exact this.symm
    · have hup : u = p := le_antisymm hule (Nat.le_of_dvd hu hpu)
      have hV : V = 0 := hV0 (by omega)
      rw [hV, mul_zero, add_zero] at htile
      exact ⟨U, htile.symm⟩
  · -- a common nonunit factor divides the board, so one of the primes divides it, hence F
    simp only [IsRelPrime, not_forall] at hrel
    obtain ⟨d, hdF, hdσF, hdu⟩ := hrel
    have hdR : d ∣ R := htile ▸ dvd_add (dvd_mul_of_dvd_left hdF U) (dvd_mul_of_dvd_left hdσF V)
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hF0 (zero_dvd_iff.mp hdF)
    rcases prime_dvd_of_dvd_mul hq₁ hq₂ hd0 hdu (hR ▸ hdR) with h | h
    · exact Or.inl (h.trans hdF)
    · exact Or.inr (h.trans hdF)

end Abstract

section Bar

/-- `Q_p` is irreducible over `ℤ`, and `Q_p(1) = p`. -/
theorem cyclotomic_prime_irreducible {p : ℕ} (hp : p.Prime) : Irreducible (cyclotomic p ℤ) :=
  cyclotomic.irreducible hp.pos

theorem cyclotomic_prime_eval_one {p : ℕ} (hp : p.Prime) : (cyclotomic p ℤ).eval 1 = p := by
  have := Fact.mk hp
  simp [eval_one_cyclotomic_prime]

/-- One row of the board: a `0/1` polynomial of degree `< p` divisible by `Q_p` is `0` or `Q_p`. -/
theorem row_eq {p : ℕ} (hp : p.Prime) {f : ℤ[X]} (h01 : ∀ i, f.coeff i = 0 ∨ f.coeff i = 1)
    (hdeg : f.natDegree < p) (hdvd : cyclotomic p ℤ ∣ f) : f = 0 ∨ f = cyclotomic p ℤ := by
  obtain ⟨g, rfl⟩ := hdvd
  by_cases hg : g = 0
  · left; simp [hg]
  have hQ : (cyclotomic p ℤ).natDegree = p - 1 := by
    rw [natDegree_cyclotomic, Nat.totient_prime hp]
  have hQ0 : cyclotomic p ℤ ≠ 0 := cyclotomic_ne_zero p ℤ
  rw [natDegree_mul hQ0 hg, hQ] at hdeg
  have hg0 : g.natDegree = 0 := by have := hp.two_le; omega
  rw [eq_C_of_natDegree_eq_zero hg0] at h01 ⊢
  have hc := h01 0
  rw [mul_comm, coeff_C_mul, cyclotomic_coeff_zero ℤ hp.one_lt, mul_one] at hc
  rcases hc with hc | hc
  · left; simp [hc]
  · right; simp [hc]

/-- The bar lemma. `F ∈ ℤ[x][y]` lists the cells of a tile (coefficient of `x^i y^k`), all in `x`-degree `< p`, with
`p` cells in all. If `Q_p(x)` divides `F`, the tile is one full row: `F = Q_p(x) y^j`. -/
theorem bar_of_dvd {p : ℕ} (hp : p.Prime) {F : ℤ[X][X]}
    (h01 : ∀ k i, (F.coeff k).coeff i = 0 ∨ (F.coeff k).coeff i = 1)
    (hdeg : ∀ k, (F.coeff k).natDegree < p)
    (hcount : ∑ k ∈ Finset.range (F.natDegree + 1), (F.coeff k).eval 1 = p)
    (hdvd : C (cyclotomic p ℤ) ∣ F) : ∃ j, F = C (cyclotomic p ℤ) * X ^ j := by
  have hrow : ∀ k, F.coeff k = 0 ∨ F.coeff k = cyclotomic p ℤ := fun k =>
    row_eq hp (h01 k) (hdeg k) ((C_dvd_iff_dvd_coeff _ _).mp hdvd k)
  set S := (Finset.range (F.natDegree + 1)).filter (fun k => F.coeff k = cyclotomic p ℤ) with hS
  have hsum : ∑ k ∈ Finset.range (F.natDegree + 1), (F.coeff k).eval 1 = p * S.card := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun k => F.coeff k = cyclotomic p ℤ)]
    have h1 : ∑ k ∈ S, (F.coeff k).eval 1 = ∑ k ∈ S, (p : ℤ) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [(Finset.mem_filter.mp hk).2, cyclotomic_prime_eval_one hp]
    have h2 : ∑ k ∈ (Finset.range (F.natDegree + 1)).filter (fun k => ¬ F.coeff k = cyclotomic p ℤ),
        (F.coeff k).eval 1 = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rcases hrow k with h | h
      · simp [h]
      · exact absurd h (Finset.mem_filter.mp hk).2
    rw [← hS, h1, h2, Finset.sum_const, nsmul_eq_mul, add_zero, mul_comm]
  have hcard : S.card = 1 := by
    have h := hcount.symm.trans hsum
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (S.card : ℤ) = 1 := by
      have := mul_left_cancel₀ hp0 (h.symm.trans (mul_one (p : ℤ)).symm)
      exact this
    exact_mod_cast this
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  refine ⟨j, ?_⟩
  ext1 k
  rw [coeff_C_mul_X_pow]
  split_ifs with hkj
  · subst hkj
    have : k ∈ S := by rw [hj]; exact Finset.mem_singleton_self k
    exact (Finset.mem_filter.mp this).2
  · rcases hrow k with h | h
    · exact h
    · exfalso
      have hk : k ∈ Finset.range (F.natDegree + 1) := by
        rw [Finset.mem_range, Nat.lt_succ_iff]
        refine le_natDegree_of_ne_zero ?_
        rw [h]; exact cyclotomic_ne_zero p ℤ
      have : k ∈ S := Finset.mem_filter.mpr ⟨hk, h⟩
      rw [hj, Finset.mem_singleton] at this
      exact hkj this

end Bar

end PrimeSquares
