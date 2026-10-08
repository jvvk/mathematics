import LeanProofs.Spans.Exchange

/-!
# Span-maximizing chains: the structure theorem (Theorem 2.1)

At an optimum, with `φ = arg Z`:
1. the lengths increase strictly to their maximum and then decrease strictly;
2. the shortest length is at an end; if it is first, `φ > T/2`;
3. (endpoint lemma) then `2φ < T + a₀`, and the last length is the second shortest;
4. the turns decrease strictly to their minimum and then increase strictly;
5. the longest segment is one of the two segments at the smallest turn;
6. with the shortest first, the first turn descends (`m ≥ 2`) and the last turn ascends (`m ≥ 3`).
-/

open Complex Finset Real

namespace Spans

variable {m : ℕ}

/-- For `x < y`, the point `y` is closer to `φ` than `x` exactly when the midpoint is below `φ`. -/
lemma closer_iff {x y φ : ℝ} (hxy : x < y) : |y - φ| < |x - φ| ↔ x + y < 2 * φ := by
  rw [← sq_lt_sq]
  constructor
  · intro hs; nlinarith
  · intro hs; nlinarith

/-- For `x < y`, the point `x` is closer to `φ` exactly when the midpoint is above `φ`. -/
lemma farther_iff {x y φ : ℝ} (hxy : x < y) : |x - φ| < |y - φ| ↔ 2 * φ < x + y := by
  rw [← sq_lt_sq]
  constructor
  · intro hs; nlinarith
  · intro hs; nlinarith

section structure_thm
variable {l : Fin (m + 1) → ℝ} {a : Fin m → ℝ} (h : Admissible l a) (hopt : Optimal l a) (hm : 1 ≤ m)
include h hopt hm

lemma abs_θ_sub_le {i : ℕ} (hi : i ≤ m) : |θ a i - arg (Z l a)| ≤ π := by
  have h1 := θ_nonneg h.apos i
  have h2 := θ_le_T h.apos hi
  have h3 := arg_pos h hm
  have h4 := arg_lt_T h hm
  rw [abs_le]; constructor <;> linarith [h.Tlt]

/-- Longer means closer to the resultant direction. -/
lemma lt_iff_closer {i j : Fin (m + 1)} (hij : i ≠ j) :
    l i < l j ↔ |θ a j - arg (Z l a)| < |θ a i - arg (Z l a)| := by
  have hc := length_cmp h hopt hm hij
  rw [← cos_lt_cos_iff_abs (abs_θ_sub_le h hopt hm (by omega)) (abs_θ_sub_le h hopt hm (by omega))]
  constructor
  · intro hl; by_contra hn; push_neg at hn; nlinarith
  · intro hcos; by_contra hn; push_neg at hn
    rcases hn.lt_or_eq with hn | hn
    · nlinarith
    · exact hij (h.linj hn.symm)

/-- Part 1: the lengths are strictly unimodal. -/
theorem lengths_unimodal : ∃ k : Fin (m + 1),
    (∀ i j : Fin (m + 1), i < j → j ≤ k → l i < l j) ∧ (∀ i j : Fin (m + 1), k ≤ i → i < j → l j < l i) := by
  obtain ⟨k, -, hk⟩ := exists_max_image univ l univ_nonempty
  set φ := arg (Z l a)
  have hmax : ∀ i, i ≠ k → l i < l k := fun i hi =>
    lt_of_le_of_ne (hk i (mem_univ _)) fun he => hi (h.linj he)
  refine ⟨k, fun i j hij hjk => ?_, fun i j hki hij => ?_⟩
  · rcases hjk.lt_or_eq with hjk | hjk
    · have hik : i ≠ k := ne_of_lt (hij.trans hjk)
      have t1 := θ_strictMono h.apos (Fin.lt_def.1 hij) (by omega : (j : ℕ) ≤ m)
      have t2 := θ_strictMono h.apos (Fin.lt_def.1 hjk) (by omega : (k : ℕ) ≤ m)
      have c1 := (closer_iff (by linarith)).1 ((lt_iff_closer h hopt hm hik).1 (hmax i hik))
      exact (lt_iff_closer h hopt hm (ne_of_lt hij)).2 ((closer_iff t1).2 (by linarith))
    · subst hjk; exact hmax i (ne_of_lt hij)
  · rcases hki.lt_or_eq with hki | hki
    · have hjk : j ≠ k := (ne_of_lt (hki.trans hij)).symm
      have t1 := θ_strictMono h.apos (Fin.lt_def.1 hij) (by omega : (j : ℕ) ≤ m)
      have t2 := θ_strictMono h.apos (Fin.lt_def.1 hki) (by omega : (i : ℕ) ≤ m)
      -- `k` is closer than `j`, with θ_k < θ_j: midpoint above φ
      have c1 : |θ a k - φ| < |θ a j - φ| := (lt_iff_closer h hopt hm hjk).1 (hmax j hjk)
      have m1 : 2 * φ < θ a k + θ a j := by
        by_contra hc; push_neg at hc
        rcases hc.lt_or_eq with hc | hc
        · have := (closer_iff (by linarith : θ a k < θ a j)).2 hc; linarith
        · have e1 : θ a j - φ = -(θ a k - φ) := by linarith
          rw [e1, abs_neg] at c1; exact lt_irrefl _ c1
      refine (lt_iff_closer h hopt hm (ne_of_lt hij).symm).2 ?_
      by_contra hc; push_neg at hc
      have := (closer_iff t1).1 (lt_of_le_of_ne hc (fun he => by
        have : |θ a i - φ| = |θ a j - φ| := he.symm
        rcases abs_eq_abs.1 this with h1 | h1 <;> linarith))
      linarith
    · subst hki; exact hmax j (ne_of_lt hij).symm

/-- Part 2: the shortest length is at an end. -/
theorem shortest_at_end {s : Fin (m + 1)} (hs : ∀ j, j ≠ s → l s < l j) :
    (s : ℕ) = 0 ∨ (s : ℕ) = m := by
  by_contra hc; push_neg at hc
  set φ := arg (Z l a)
  have h0 : (⟨0, by omega⟩ : Fin (m + 1)) ≠ s := fun he => hc.1 (by rw [← he])
  have hl : (Fin.last m) ≠ s := fun he => hc.2 (by rw [← he]; simp)
  have c0 := (lt_iff_closer h hopt hm h0.symm).1 (hs _ h0)
  have cl := (lt_iff_closer h hopt hm hl.symm).1 (hs _ hl)
  simp only [Fin.val_last, Fin.val_mk, θ_zero] at c0 cl
  have t1 := θ_strictMono h.apos (i := 0) (k := s) (by omega) (by omega)
  have t2 := θ_strictMono h.apos (i := s) (k := m) (by omega) le_rfl
  rw [θ_zero] at t1
  -- s farther than both ends is impossible
  have m0 := (farther_iff t1).1 (by simpa using c0)
  have mT := (closer_iff t2).1 cl
  have := θ_nonneg h.apos (s : ℕ)
  linarith

/-- Part 2: with the first segment shorter than the last, the resultant lies past the middle direction. -/
theorem half_lt_arg (h0 : l 0 < l (Fin.last m)) : T a / 2 < arg (Z l a) := by
  have hne : (0 : Fin (m + 1)) ≠ Fin.last m := by simp [Fin.ext_iff]; omega
  have c := (lt_iff_closer h hopt hm hne).1 h0
  simp only [Fin.val_last, Fin.val_zero, θ_zero] at c
  have := arg_pos h hm
  have := arg_lt_T h hm
  unfold T at *
  rw [abs_of_pos (by linarith), abs_of_neg (by linarith)] at c
  linarith

/-- The midpoint test of Lemma 2.4 in both directions. -/
lemma desc_mid {k : ℕ} (hk : k + 1 < m) (hd : ext a (k + 1) < ext a k) :
    θ a k + θ a (k + 2) < 2 * arg (Z l a) := by
  have := turn_cmp h hopt hm hk; nlinarith

lemma asc_mid {k : ℕ} (hk : k + 1 < m) (hd : ext a k < ext a (k + 1)) :
    2 * arg (Z l a) < θ a k + θ a (k + 2) := by
  have := turn_cmp h hopt hm hk; nlinarith

lemma ext_ne {k : ℕ} (hk : k + 1 < m) : ext a k ≠ ext a (k + 1) := by
  unfold ext; rw [dif_pos (by omega), dif_pos hk]
  intro hc; have := h.ainj hc; simp [Fin.ext_iff] at this

lemma mid_lt {k k' : ℕ} (hkk : k < k') (hk' : k' + 1 < m) :
    θ a k + θ a (k + 2) < θ a k' + θ a (k' + 2) := by
  have := θ_strictMono h.apos hkk (by omega)
  have := θ_strictMono h.apos (by omega : k + 2 < k' + 2) (by omega)
  linarith

/-- No descent follows an ascent. -/
lemma no_desc_after_asc {k k' : ℕ} (hkk : k < k') (hk' : k' + 1 < m) (ha : ext a k < ext a (k + 1)) :
    ext a k' < ext a (k' + 1) := by
  rcases lt_or_gt_of_ne (ext_ne h hopt hm hk') with hd | hd
  · exact hd
  · have := asc_mid h hopt hm (by omega) ha
    have := desc_mid h hopt hm hk' hd
    have := mid_lt h hopt hm hkk hk'
    linarith

/-- Part 4: the turns form a valley: descents (before `z`) then ascents (from `z`). -/
theorem turns_valley : ∃ z : ℕ, z < m ∧ (∀ i, i < z → ext a (i + 1) < ext a i) ∧
    (∀ i, z ≤ i → i + 1 < m → ext a i < ext a (i + 1)) := by
  classical
  by_cases hex : ∃ k, k + 1 < m ∧ ext a k < ext a (k + 1)
  · let z := Nat.find hex
    have hz := Nat.find_spec hex
    refine ⟨z, by omega, fun i hi => ?_, fun i hi hi1 => ?_⟩
    · have hnot := Nat.find_min hex hi
      push_neg at hnot
      rcases lt_or_gt_of_ne (ext_ne h hopt hm (by omega : i + 1 < m)) with hd | hd
      · exact absurd (hnot (by omega)) (not_le.2 hd)
      · exact hd
    · rcases hi.lt_or_eq with hi | hi
      · exact no_desc_after_asc h hopt hm hi hi1 hz.2
      · rw [← hi]; exact hz.2
  · push_neg at hex
    refine ⟨m - 1, by omega, fun i hi => ?_, fun i hi hi1 => by omega⟩
    rcases lt_or_gt_of_ne (ext_ne h hopt hm (by omega : i + 1 < m)) with hd | hd
    · exact absurd (hex i (by omega)) (not_le.2 hd)
    · exact hd

/-- Part 5: the longest segment is incident to the smallest turn (at position `z`). -/
theorem longest_at_smallest_turn {z : ℕ} (hzm : z < m) (hdesc : ∀ i, i < z → ext a (i + 1) < ext a i)
    (hasc : ∀ i, z ≤ i → i + 1 < m → ext a i < ext a (i + 1))
    {k : Fin (m + 1)} (hk : ∀ j, j ≠ k → l j < l k) : (k : ℕ) = z ∨ (k : ℕ) = z + 1 := by
  set φ := arg (Z l a)
  by_contra hc; push_neg at hc
  rcases lt_or_gt_of_ne hc.1 with hkz | hkz
  · -- k left of z: the segment at θ_z is closer
    have hz0 : 0 < z := by omega
    have hd := desc_mid h hopt hm (k := z - 1) (by omega) (hdesc (z - 1) (by omega))
    rw [show z - 1 + 2 = z + 1 by omega] at hd
    have hzz : θ a (z - 1) ≤ θ a z := θ_mono h.apos (by omega)
    have hz1 : θ a z < θ a (z + 1) := θ_strictMono h.apos (by omega) (by omega)
    have hkθ : θ a k ≤ θ a (z - 1) := θ_mono h.apos (by omega)
    have hkθ' : θ a k < θ a z := θ_strictMono h.apos hkz (by omega)
    have hzk : (⟨z, by omega⟩ : Fin (m + 1)) ≠ k := fun he => by
      rw [← he] at hkz; simp at hkz
    have c := (lt_iff_closer h hopt hm hzk).1 (hk _ hzk)
    simp only [Fin.val_mk] at c
    have := (farther_iff hkθ').1 c
    -- hd: θ (z-1) + θ (z+1) < 2φ
    linarith
  · -- k right of z + 1: the segment at θ_{z+1} is closer
    have hk2 : z + 1 < k := by omega
    have ha := asc_mid h hopt hm (k := z) (by omega) (hasc z le_rfl (by omega))
    have hz1 : θ a (z + 1) < θ a (z + 2) := θ_strictMono h.apos (by omega) (by omega)
    have hzz : θ a z < θ a (z + 1) := θ_strictMono h.apos (by omega) (by omega)
    have hkθ : θ a (z + 2) ≤ θ a k := θ_mono h.apos (by omega)
    have hkθ' : θ a (z + 1) < θ a k := θ_strictMono h.apos hk2 (by omega)
    have hzk : (⟨z + 1, by omega⟩ : Fin (m + 1)) ≠ k := fun he => by
      rw [← he] at hk2; simp at hk2
    have c := (lt_iff_closer h hopt hm hzk).1 (hk _ hzk)
    simp only [Fin.val_mk] at c
    have := (closer_iff hkθ').1 c
    linarith

/-- Part 6a: with the first segment shorter than the last, the first turn descends. -/
theorem first_turn_descends (hm2 : 2 ≤ m) (h0 : l 0 < l (Fin.last m)) : ext a 1 < ext a 0 := by
  have hT := half_lt_arg h hopt hm h0
  rcases lt_or_gt_of_ne (ext_ne h hopt hm (k := 0) (by omega)) with hd | hd
  · have := asc_mid h hopt hm (k := 0) (by omega) hd
    rw [θ_zero, zero_add] at this
    have := θ_le_T h.apos (i := 2) hm2
    linarith
  · exact hd

end structure_thm

/-! ## The endpoint lemma (Lemma 2.3); here the chain has `m + 2` segments -/

section endpoint
variable {l : Fin (m + 2) → ℝ} {a : Fin (m + 1) → ℝ} (h : Admissible l a) (hopt : Optimal l a)
include h hopt

/-- Lemma 2.3: with the shortest segment first, `2φ < T + a₀`. -/
theorem endpoint_arg : 2 * arg (Z l a) < T a + ext a 0 := by
  set W := Wtail l a
  set a0 := ext a 0
  set γ := (T a + a0) / 2
  set δ := (T a - a0) / 2
  have ha0 : 0 < a0 := by simp only [a0, ext]; rw [dif_pos (by omega)]; exact h.apos _
  have ha0T : a0 ≤ T a := by
    have := θ_mono h.apos (i := 1) (k := m + 1) (by omega)
    rw [θ_succ, θ_zero, zero_add] at this; exact this
  have hγ0 : 0 < γ := by simp only [γ]; linarith
  have hγπ : γ < π := by simp only [γ]; linarith [h.Tlt]
  have hsinγ : 0 < Real.sin γ := sin_pos_of_pos_of_lt_pi hγ0 hγπ
  -- optimality against moving the first segment to the end
  have hopt' := hopt (finRotate (m + 2)) (finRotate (m + 1))
  rw [Z_rot, Z_head] at hopt'
  have hsq : Complex.normSq (W + (l 0 : ℂ) * e (T a)) ≤ Complex.normSq ((l 0 : ℂ) + e a0 * W) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hopt' 2
  rw [Complex.normSq_add, Complex.normSq_add] at hsq
  have hn1 : Complex.normSq ((l 0 : ℂ) * e (T a)) = l 0 ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq, norm_e]; ring
  have hn2 : Complex.normSq (e a0 * W) = Complex.normSq W := by
    rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq (e a0), norm_e]; ring
  have hn3 : Complex.normSq (l 0 : ℂ) = l 0 ^ 2 := by rw [Complex.normSq_ofReal]; ring
  rw [hn1, hn2, hn3] at hsq
  -- in terms of V = W e^{-iδ}: Re(e^{iγ} V) ≥ Re(e^{-iγ} V)
  set V := W * e (-δ)
  have hWV : W = V * e δ := by simp only [V]; rw [mul_assoc, ← e_add, neg_add_cancel]; simp [e]
  have hcj : (starRingEnd ℂ) (e (T a)) = e (-T a) := by
    unfold e; rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  have h1 : (W * (starRingEnd ℂ) ((l 0 : ℂ) * e (T a))).re = l 0 * (e (-γ) * V).re := by
    rw [map_mul, Complex.conj_ofReal, hcj, hWV]
    rw [show V * e δ * ((l 0 : ℂ) * e (-T a)) = (l 0 : ℂ) * (e (δ + -T a) * V) by rw [e_add]; ring]
    rw [Complex.re_ofReal_mul]; congr 2; simp only [δ, γ]; ring_nf
  have h2 : ((l 0 : ℂ) * (starRingEnd ℂ) (e a0 * W)).re = l 0 * (e γ * V).re := by
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, Complex.conj_ofReal, hWV]
    rw [show (l 0 : ℂ) * (e a0 * (V * e δ)) = (l 0 : ℂ) * (e (a0 + δ) * V) by rw [e_add]; ring]
    rw [Complex.re_ofReal_mul]; congr 2; simp only [δ, γ]; ring_nf
  rw [h1, h2] at hsq
  have hl0 := h.lpos 0
  have hre : (e (-γ) * V).re ≤ (e γ * V).re := by nlinarith
  -- Re(e^{iγ}V) - Re(e^{-iγ}V) = -2 sin γ Im V
  have hdiff : (e γ * V).re - (e (-γ) * V).re = -2 * Real.sin γ * V.im := by
    simp only [Complex.mul_re, e_re, e_im, Real.cos_neg, Real.sin_neg]; ring
  have hVim : V.im ≤ 0 := by nlinarith
  -- so Z e^{-iγ} has negative imaginary part
  have hZ : (Z l a * e (-γ)).im < 0 := by
    rw [Z_head, show Wtail l a = W from rfl, hWV, add_mul, Complex.add_im]
    rw [show e a0 * (V * e δ) * e (-γ) = V * e (a0 + δ + -γ) by rw [e_add, e_add]; ring]
    rw [show a0 + δ + -γ = 0 by simp only [δ, γ]; ring]
    rw [Complex.im_ofReal_mul, e_im, Real.sin_neg]
    simp only [e, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    nlinarith
  have hpol := Z_polar h
  rw [← hpol, mul_assoc, ← e_add, Complex.im_ofReal_mul, e_im] at hZ
  have hn : 0 < ‖Z l a‖ := norm_pos_iff.2 (Z_ne_zero h (by omega))
  have hs : Real.sin (arg (Z l a) + -γ) < 0 := by
    by_contra hc; push_neg at hc; nlinarith
  have hφ0 := arg_pos h (by omega)
  have hφπ := arg_lt_pi h (by omega)
  rw [sin_neg_iff_of_abs_lt (by linarith) (by linarith)] at hs
  simp only [γ] at hs; linarith

/-- Lemma 2.3, second half: with the shortest segment first, the last segment is the second shortest. -/
theorem last_second_shortest (hmin : ∀ j, j ≠ 0 → l 0 < l j) {j : Fin (m + 2)} (hj0 : j ≠ 0)
    (hjl : j ≠ Fin.last (m + 1)) : l (Fin.last (m + 1)) < l j := by
  have hm : 1 ≤ m + 1 := by omega
  set φ := arg (Z l a)
  have hE := endpoint_arg h hopt
  have hhalf := half_lt_arg h hopt hm (hmin _ (by simp [Fin.ext_iff]))
  have hφT := arg_lt_T h hm
  have hne : j ≠ Fin.last (m + 1) := hjl
  refine (lt_iff_closer h hopt hm hne.symm).2 ?_
  simp only [Fin.val_last]
  have hj1 : 1 ≤ (j : ℕ) := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exact absurd (Fin.ext h0) hj0
    · exact h0
  have hjm : (j : ℕ) < m + 1 := by
    have := j.isLt
    rcases Nat.lt_or_ge j (m + 1) with h1 | h1
    · exact h1
    · exact absurd (Fin.ext (by simp; omega)) hjl
  have ta : ext a 0 ≤ θ a j := by
    have := θ_mono h.apos hj1; rwa [θ_succ, θ_zero, zero_add] at this
  have tT : θ a j < T a := θ_strictMono h.apos hjm le_rfl
  unfold T at *
  rw [abs_of_pos (by linarith : 0 < θ a (m + 1) - φ)]
  rcases le_or_gt φ (θ a j) with hφ | hφ
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

/-- Part 6b: with the shortest segment first and at least three turns, the last turn ascends. -/
theorem last_turn_ascends (hm3 : 2 ≤ m) (hmin : ∀ j, j ≠ 0 → l 0 < l j) :
    ext a (m - 1) < ext a m := by
  have hm : 1 ≤ m + 1 := by omega
  have hE := endpoint_arg h hopt
  rcases lt_or_gt_of_ne (ext_ne h hopt hm (k := m - 1) (by omega)) with hd | hd
  · rwa [show m - 1 + 1 = m by omega] at hd
  · exfalso
    rw [show m - 1 + 1 = m by omega] at hd
    have := desc_mid h hopt hm (k := m - 1) (by omega) (by rwa [show m - 1 + 1 = m by omega])
    rw [show m - 1 + 2 = m + 1 by omega] at this
    have t1 : θ a 1 ≤ θ a (m - 1) := θ_mono h.apos (by omega)
    rw [θ_succ, θ_zero, zero_add] at t1
    unfold T at hE
    linarith

end endpoint

end Spans
