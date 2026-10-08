/-
  The symmetric two-step lemma (Lemma 3.1 of the paper):
  for a symmetric irreducible Dyck word `u` of length `L ≥ 4`, `𝓖(𝓕(𝓣 u)) ≤ 𝓣(𝓕(𝓕 u))`.
-/
import HofstadterConway.Tee

namespace HofConway

variable {L : ℕ} {P : ℕ → ℕ}

/-- Step 1, the midpoint identity: with `H` symmetric of length `2L` and `W = 𝓕(H)`,
    `H (j - W j) ≤ m` for `j ≤ 2L`. -/
theorem mid_bound {H : ℕ → ℕ} (hH : Dyck (2 * L) H) (hHS : Symm (2 * L) H)
    (hE : 2 * (L / 2) = L) {j : ℕ} (hj : j ≤ 2 * L) :
    H (j - FP (2 * L) H j) ≤ L / 2 := by
  have hW := FP_dyck hH
  have hs := FP_spec hH (show 2 * L ≤ 2 * (2 * L) by omega)
  have hsub := hW.sub_le hj
  have hWj := (FP_spec hH (show j ≤ 2 * (2 * L) by omega)).2.1
  obtain ⟨_, _, h3, h4, h5, _⟩ := hs
  have hsym := hHS (FP (2 * L) H (2 * L)) h3
  have hmono := hH.mono (show j - FP (2 * L) H j ≤ 2 * L - FP (2 * L) H (2 * L) by omega)
  omega

section
variable (hD : Dyck L P) (hI : Irred L P) (hS : Symm L P) (hL : 4 ≤ L)
include hD hI hS hL

/-- Step 2, the contact claim: where `Z = 𝓖(𝓕(𝓣 u))` meets `W = 𝓕(𝓕 u)` in the first half,
    the next letter of `W` is `1`. -/
theorem contact {j : ℕ} (hj : j ≤ 2 * L)
    (hZW : GP (2 * L) (FP L (TP L P)) j = FP (2 * L) (FP L P) j) :
    FP (2 * L) (FP L P) (j + 1) = FP (2 * L) (FP L P) j + 1 := by
  have hD' := TP_dyck hD hI hS hL
  have hH := FP_dyck hD
  have hK := FP_dyck hD'
  have hKH : ∀ i, FP L (TP L P) i ≤ FP L P i := FP_mono hD' hD (TP_le hD hL)
  have hHI := FP_irred hD hI
  have hHS := FP_symm hD hS
  have hE : 2 * (L / 2) = L := by have := hD.total; omega
  have hmid := mid_bound hH hHS hE hj
  have hWs := FP_spec hH (show j ≤ 2 * (2 * L) by omega)
  have hZs := GP_spec hK (show j ≤ 2 * (2 * L) by omega)
  have hWsucc := FP_succ hH (show j + 1 ≤ 2 * (2 * L) by omega)
  have hWstep := (FP_dyck hH).step j
  rw [hZW] at hZs
  generalize ha : FP (2 * L) (FP L P) j = a at *
  have h2a := ASpec.half hH hWs
  obtain ⟨_, ha2, _, w4, _, _⟩ := hWs
  obtain ⟨_, _, _, z4, _, _⟩ := hZs
  have k1 := hKH a
  have k2 := hKH (j - a)
  have hy := FP_spec hD (show j - a ≤ 2 * L by omega)
  have hy' := FP_spec hD' (show j - a ≤ 2 * L by omega)
  have hKq : FP L (TP L P) (j - a) = FP L P (j - a) := by omega
  rw [hKq] at hy'
  have hHsucc := FP_succ hD (show j - a + 1 ≤ 2 * L by omega)
  rw [show j + 1 - a = j - a + 1 by omega] at hWsucc
  have hy2 := ASpec.half hD hy
  -- q = j - a < L, since `𝓕 u` has positive height at its interior point `L`
  have hqL : j - a < L := by
    by_contra hc
    have hq : j - a = L := by omega
    have := hHI L (by omega) (by omega)
    rw [hq] at hmid
    omega
  generalize hq : j - a = q at *
  generalize hyv : FP L P q = y at *
  by_contra hw
  have hW1 : FP (2 * L) (FP L P) (j + 1) = a := by omega
  have hHq1 : FP L P (q + 1) = y := by omega
  have hyq := hy.2.1
  rw [hHsucc, show q + 1 - y = q - y + 1 by omega] at hHq1
  have h1 := P_one hD hI (by omega)
  -- y ≥ 1
  have hy1 : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · subst h0
      have q0 : q = 0 := by omega
      subst q0
      simp [hD.zero, h1] at hHq1
    · exact h0
  -- z = q - y < m
  have hz : q - y < L / 2 := by omega
  have hyc' := hy'
  obtain ⟨_, _, hyL, y4, y5, _⟩ := hy
  obtain ⟨_, _, _, y4', y5', _⟩ := hy'
  have tz := TP_lt (P := P) hz
  have tle := TP_le hD hL y
  have my := hD.mono (show 1 ≤ y by omega)
  have mz := hD.mono (show 1 ≤ q - y + 1 by omega)
  have sy := hD.step y
  have sy1 := hD.step (y - 1)
  rw [show y - 1 + 1 = y by omega] at sy1
  -- `𝓣 u` has letter `1` at `y`
  have hup : TP L P y = TP L P (y - 1) + 1 := by
    have t1 := TP_lt (L := L) (P := P) (show y - 1 < L / 2 by omega)
    rw [show y - 1 + 1 = y by omega] at t1
    rcases Nat.lt_or_ge y (L / 2) with hlt | hge
    · have t0 := TP_lt (P := P) hlt
      omega
    · have hym : y = L / 2 := by omega
      have t0 : TP L P y = P (y - 1) := by rw [hym]; exact TP_mid
      omega
  -- but it is the first threshold with value `1`, so Lemma 2.2(5) gives letter `0`
  have he : TP L P y + TP L P (q - y) + 1 = y := by omega
  have hzero := ASpec.letter_zero hD' hyc' he (by omega)
  omega

/-- Step 3: `Z ≤ W` on the first half. -/
theorem first_half_le :
    ∀ j, j ≤ 2 * L → GP (2 * L) (FP L (TP L P)) j ≤ FP (2 * L) (FP L P) j
  | 0, _ => by simp [GP, FP, Brec, Arec]
  | j + 1, hj => by
    have ih := first_half_le j (by omega)
    have hZ := (GP_dyck (FP_dyck (TP_dyck hD hI hS hL))).step j
    have hW := (FP_dyck (FP_dyck hD)).step j
    by_cases hc : GP (2 * L) (FP L (TP L P)) j = FP (2 * L) (FP L P) j
    · have := contact hD hI hS hL (by omega) hc; omega
    · omega

/-- Lemma 3.1 (key lemma): `𝓖(𝓕(𝓣 u)) ≤ 𝓣(𝓕(𝓕 u))`. -/
theorem key (i : ℕ) :
    GP (2 * L) (FP L (TP L P)) i ≤ TP (2 * (2 * L)) (FP (2 * L) (FP L P)) i := by
  have hD' := TP_dyck hD hI hS hL
  have hH := FP_dyck hD
  have hW := FP_dyck hH
  have hWI := FP_irred hH (FP_irred hD hI)
  have hWS := FP_symm hH (FP_symm hD hS)
  have hZ := GP_dyck (FP_dyck hD')
  have hZS := GP_symm (FP_dyck hD') (FP_symm hD' (TP_symm hD hI hS hL))
  have hTW := TP_dyck hW hWI hWS (by omega)
  have hTWS := TP_symm hW hWI hWS (by omega)
  have hM : 2 * (2 * L) / 2 = 2 * L := by omega
  -- Step 4 on the first half
  have first : ∀ i, i ≤ 2 * L →
      GP (2 * L) (FP L (TP L P)) i ≤ TP (2 * (2 * L)) (FP (2 * L) (FP L P)) i := by
    intro i hi
    have hle := first_half_le hD hI hS hL i hi
    rcases Nat.lt_or_ge i (2 * L) with h | h
    · rw [TP_lt (show i < 2 * (2 * L) / 2 by omega)]
      have st := hW.step i
      by_cases hc : GP (2 * L) (FP L (TP L P)) i = FP (2 * L) (FP L P) i
      · have := contact hD hI hS hL (by omega) hc; omega
      · omega
    · have hi2 : i = 2 * L := by omega
      subst hi2
      have e : TP (2 * (2 * L)) (FP (2 * L) (FP L P)) (2 * L) = FP (2 * L) (FP L P) (2 * L - 1) := by
        have := TP_mid (L := 2 * (2 * L)) (P := FP (2 * L) (FP L P))
        rwa [hM] at this
      rw [e]
      have st := hW.step (2 * L - 1)
      rw [show 2 * L - 1 + 1 = 2 * L by omega] at st
      have sym := hWS (2 * L - 1) (by omega)
      rw [show 2 * (2 * L) - (2 * L - 1) = 2 * L + 1 by omega, hM] at sym
      by_cases hc : GP (2 * L) (FP L (TP L P)) (2 * L) = FP (2 * L) (FP L P) (2 * L)
      · have := contact hD hI hS hL le_rfl hc; omega
      · omega
  -- the second half by symmetry of both words
  have upto : ∀ i, i ≤ 2 * (2 * L) →
      GP (2 * L) (FP L (TP L P)) i ≤ TP (2 * (2 * L)) (FP (2 * L) (FP L P)) i := by
    intro i hi
    rcases Nat.lt_or_ge (2 * L) i with h | h
    · have := first (2 * (2 * L) - i) (by omega)
      have z := hZS (2 * (2 * L) - i) (by omega)
      have t := hTWS (2 * (2 * L) - i) (by omega)
      rw [show 2 * (2 * L) - (2 * (2 * L) - i) = i by omega] at z t
      omega
    · exact first i h
  rcases le_total i (2 * (2 * L)) with h | h
  · exact upto i h
  · rw [hZ.tail i h, hTW.tail i h]; exact upto _ le_rfl

end

end HofConway
