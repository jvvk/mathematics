import Mathlib

/-!
# The cells of a regular polygon are small (MO 436753): the arithmetic core

* `coprime_sub_add`: if `a` is odd, `b` is even and `a, b` are coprime, then `b - a` and `b + a` are
  coprime.
* `lattice_exists`: every level `b v - a u = k` contains a chord `(u, v)` with `u ≡ v (mod 2)`.
* `lattice_spacing`: two such chords on one level differ by a multiple of `(2b, 2a)`.
* `inradius`: `R sin(t/2) = 1/(4 cos(t/2))` for `R = 1/(2 sin t)`, the inradius of the odd central
  cell.
* `central_gap`: `sin(3t/2) cos t - sin(t/2) = cos(3t/2) sin t > 0` for `0 < t < π/3`: no other
  chord meets the central `n`-gon.
-/

namespace PolygonCells

/-- `b - a` and `b + a` are coprime when `a` is odd, `b` is even and `gcd(a, b) = 1`. -/
theorem coprime_sub_add (a b : ℤ) (ha : Odd a) (hb : Even b) (hab : IsCoprime a b) :
    IsCoprime (b - a) (b + a) := by
  have h1 : IsCoprime (b - a) b := by
    have : IsCoprime (-a) b := hab.neg_left
    have h := this.add_mul_right_left 1
    simpa [sub_eq_add_neg, add_comm] using h
  have hodd : Odd (b - a) := hb.sub_odd ha
  have h2 : IsCoprime (b - a) 2 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    obtain ⟨m, hm⟩ := hodd
    rw [hm]
    have : Int.gcd (2 * m + 1) 2 = Int.gcd 1 2 := by
      rw [show (2 * m + 1 : ℤ) = 1 + 2 * m by ring, Int.gcd_add_mul_left_left]
    rw [this]; rfl
  have h3 : IsCoprime (b - a) (2 * b) := h2.mul_right h1
  have h4 : b + a = 2 * b - (b - a) := by ring
  rw [h4]
  have := h3.add_mul_left_right (-1)
  simpa [sub_eq_add_neg, add_comm, mul_comm] using this

/-- Every level is reached by a chord: `b v - a u = k` with `u ≡ v (mod 2)`. -/
theorem lattice_exists (a b k : ℤ) (ha : Odd a) (hb : Even b) (hab : IsCoprime a b) :
    ∃ u v : ℤ, b * v - a * u = k ∧ u ≡ v [ZMOD 2] := by
  obtain ⟨x, y, hxy⟩ := coprime_sub_add a b ha hb hab
  -- x (b - a) + y (b + a) = 1; take j = k x, i = -k y
  refine ⟨-k * y + k * x, k * x + k * y, ?_, ?_⟩
  · linear_combination k * hxy
  · rw [Int.modEq_iff_dvd]; exact ⟨k * y, by ring⟩

/-- Two chords on the same level differ by a multiple of `(2b, 2a)`. -/
theorem lattice_spacing (a b u v u' v' : ℤ) (hb : Even b) (hb0 : 0 < b) (ha : Odd a)
    (hab : IsCoprime a b)
    (h : b * v - a * u = b * v' - a * u') (hp : u ≡ v [ZMOD 2]) (hp' : u' ≡ v' [ZMOD 2]) :
    ∃ m : ℤ, u - u' = 2 * b * m ∧ v - v' = 2 * a * m := by
  have e : b * (v - v') = a * (u - u') := by linarith
  -- b divides a (u - u'), so b ∣ u - u'
  have hbd : b ∣ u - u' := hab.symm.dvd_of_dvd_mul_left ⟨v - v', by linarith⟩
  obtain ⟨m, hm⟩ := hbd
  have hv : v - v' = a * m := by
    have : b * (v - v') = b * (a * m) := by rw [e, hm]; ring
    exact mul_left_cancel₀ hb0.ne' this
  -- parity: (u - u') - (v - v') is even, i.e. (b - a) m is even; b - a is odd, so m is even
  have hev : Even ((b - a) * m) := by
    have d1 : (2 : ℤ) ∣ v - u := Int.modEq_iff_dvd.1 hp
    have d2 : (2 : ℤ) ∣ v' - u' := Int.modEq_iff_dvd.1 hp'
    rw [show (b - a) * m = (v' - u') - (v - u) by linear_combination (-1 : ℤ) * hm + hv]
    exact even_iff_two_dvd.2 (dvd_sub d2 d1)
  have hodd : Odd (b - a) := hb.sub_odd ha
  have hm2 : Even m := by
    rcases Int.even_mul.1 hev with h | h
    · exact absurd h (Int.not_even_iff_odd.2 hodd)
    · exact h
  obtain ⟨q, rfl⟩ := hm2
  exact ⟨q, by rw [hm]; ring, by rw [hv]; ring⟩

open Real

/-- The inradius of the odd central cell: `R sin(t/2) = 1/(4 cos(t/2))` with `R = 1/(2 sin t)`. -/
theorem inradius (t : ℝ) (hs : sin t ≠ 0) :
    (1 / (2 * sin t)) * sin (t / 2) = 1 / (4 * cos (t / 2)) := by
  have h2 : sin t = 2 * sin (t / 2) * cos (t / 2) := by
    rw [← sin_two_mul]; ring_nf
  have hc : cos (t / 2) ≠ 0 := by
    intro hc; rw [h2, hc] at hs; simp at hs
  have hsn : sin (t / 2) ≠ 0 := by
    intro h0; rw [h2, h0] at hs; simp at hs
  rw [h2]; field_simp; ring

/-- `sin(3t/2) cos t - sin(t/2) = cos(3t/2) sin t`, which is positive for `0 < t < π/3`. -/
theorem central_gap (t : ℝ) (h0 : 0 < t) (h1 : t < π / 3) :
    sin (3 * t / 2) * cos t - sin (t / 2) = cos (3 * t / 2) * sin t ∧
    0 < sin (3 * t / 2) * cos t - sin (t / 2) := by
  have key : sin (3 * t / 2) * cos t - cos (3 * t / 2) * sin t = sin (t / 2) := by
    rw [← sin_sub]; ring_nf
  refine ⟨by linarith, ?_⟩
  have hc : 0 < cos (3 * t / 2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
  nlinarith [mul_pos hc hs]

end PolygonCells
