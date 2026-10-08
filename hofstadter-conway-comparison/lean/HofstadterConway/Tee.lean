/-
  The central perturbation `𝓣` (Section 2.3 of the paper, Lemma 2.4).

  `𝓣(u) = u₂ ⋯ u_m b (1-b) u_{m+1} ⋯ u_{L-1}` with `b = 1 - u_m`. In prefix form its counts are
  `P (i+1) - 1` for `i < m`, `P (m-1)` at `m`, and `P (i-1)` for `i > m`; this is formula (2.6),
  `δ(i) = P i - P' i`, read off directly.
-/
import HofstadterConway.Ops

namespace HofConway

/-- Prefix counts of `𝓣(u)` for a word of length `L = 2m`. -/
def TP (L : ℕ) (P : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < L / 2 then P (i + 1) - 1 else if i = L / 2 then P (L / 2 - 1) else P (i - 1)

variable {L : ℕ} {P : ℕ → ℕ}

theorem TP_lt {i : ℕ} (h : i < L / 2) : TP L P i = P (i + 1) - 1 := by simp [TP, h]

theorem TP_mid : TP L P (L / 2) = P (L / 2 - 1) := by simp [TP]

theorem TP_gt {i : ℕ} (h : L / 2 < i) : TP L P i = P (i - 1) := by
  simp [TP, show ¬ i < L / 2 by omega, show i ≠ L / 2 by omega]

theorem Dyck.sub_le (hD : Dyck L P) {i k : ℕ} (h : i ≤ k) : P k ≤ P i + (k - i) := by
  induction k with
  | zero => simp at h; subst h; simp
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with h | h
    · rw [h]; simp
    · have := ih (by omega); have := (hD.step k).2; omega

theorem P_one (hD : Dyck L P) (hI : Irred L P) (hL : 2 < L) : P 1 = 1 := by
  have := hI 1 (by omega) (by omega); have := hD.le_self 1; omega

/-- The last letter is `0`: `P (L - 1) = m`. -/
theorem P_pred_top (hD : Dyck L P) (hI : Irred L P) (hS : Symm L P) (hL : 2 < L) :
    P (L - 1) = L / 2 := by
  have := hS 1 (by omega); have := P_one hD hI hL; omega

/-- The value of `𝓣(u)` at `i ≠ m` and at `m`, as facts for `omega`. -/
theorem TP_cases (i : ℕ) :
    (i < L / 2 ∧ TP L P i = P (i + 1) - 1) ∨ (i = L / 2 ∧ TP L P i = P (i - 1)) ∨
      (L / 2 < i ∧ TP L P i = P (i - 1)) := by
  rcases lt_trichotomy i (L / 2) with h | h | h
  · exact Or.inl ⟨h, TP_lt h⟩
  · exact Or.inr (Or.inl ⟨h, by rw [h]; exact TP_mid⟩)
  · exact Or.inr (Or.inr ⟨h, TP_gt h⟩)

section
variable (hD : Dyck L P) (hI : Irred L P) (hS : Symm L P) (hL : 4 ≤ L)
include hD hI hS hL

/-- Lemma 2.4: `𝓣(u)` is a Dyck word of length `L`. -/
theorem TP_dyck : Dyck L (TP L P) where
  zero := by rw [TP_lt (by omega), zero_add]; have := P_one hD hI (by omega); omega
  step i := by
    have h1 := P_one hD hI (by omega)
    rcases TP_cases (L := L) (P := P) i with ⟨h, e1⟩ | ⟨h, e1⟩ | ⟨h, e1⟩ <;>
      rcases TP_cases (L := L) (P := P) (i + 1) with ⟨h', e2⟩ | ⟨h', e2⟩ | ⟨h', e2⟩
    all_goals first
      | omega
      | (have := hD.step (i + 1); have := hD.mono (show 1 ≤ i + 1 by omega); omega)
      | (rw [show i + 1 - 1 = i by omega] at e2
         have := hD.step i; have := hD.mono (show 1 ≤ i + 1 by omega); omega)
      | (rw [show i + 1 - 1 = i by omega] at e2
         have s := hD.step (i - 1); rw [show i - 1 + 1 = i by omega] at s; omega)
  tail i h := by
    have e := P_pred_top hD hI hS (by omega)
    rw [TP_gt (by omega), TP_gt (by omega)]
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [h']
    · rw [hD.tail (i - 1) (by omega)]; have := hD.total; omega
  half i h := by
    rcases TP_cases (L := L) (P := P) i with ⟨h', e⟩ | ⟨h', e⟩ | ⟨h', e⟩ <;> rw [e]
    · have := hI (i + 1) (by omega) (by omega); omega
    · have := hI (i - 1) (by omega) (by omega); omega
    · have := hI (i - 1) (by omega) (by omega); omega
  total := by
    rw [TP_gt (by omega), P_pred_top hD hI hS (by omega)]; have := hD.total; omega

omit hI hS in
/-- Lemma 2.4: `𝓣(u) ≤ u`. -/
theorem TP_le (i : ℕ) : TP L P i ≤ P i := by
  rcases TP_cases (L := L) (P := P) i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e]
  · have := hD.step i; omega
  · have s := hD.step (i - 1); rw [show i - 1 + 1 = i by omega] at s; omega
  · have s := hD.step (i - 1); rw [show i - 1 + 1 = i by omega] at s; omega

/-- Lemma 2.4: `𝓣(u)` is symmetric. -/
theorem TP_symm : Symm L (TP L P) := by
  intro i hi
  have hm : 2 * (L / 2) = L := by have := hD.total; omega
  rcases TP_cases (L := L) (P := P) i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩
  · rw [e, TP_gt (by omega), show L - i - 1 = L - (i + 1) by omega]
    have := hS (i + 1) (by omega); have := hI (i + 1) (by omega) (by omega); omega
  · rw [h, show L - L / 2 = L / 2 by omega]; omega
  · rw [e, TP_lt (by omega), show L - i + 1 = L - (i - 1) by omega]
    have := hS (i - 1) (by omega); have := hI (i - 1) (by omega) (by omega); omega

end

end HofConway
