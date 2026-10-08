/-
  The threshold operators 𝓕 and 𝓖 (Section 2 of the paper, Lemma 2.2).

  `Arec`, `Brec` are the recurrences (2.4), (2.5). `ASpec`, `BSpec` state the threshold definitions:
  with `d_j(x) = x - P x - P (j - x)` on `I_j = [j - L, min j L]`, `A(j)` is the least `x ∈ I_j` with
  `d_j(x) ≥ 0` and `B(j)` the greatest with `d_j(x) ≤ 0`. We prove the recurrences meet the threshold
  definitions, which is the content of Lemma 2.2(1)-(4).
-/
import HofstadterConway.Basic

namespace HofConway

/-- Recurrence (2.4): prefix counts of `𝓕(u)`. -/
def Arec (P : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => P (Arec P j) + P (j + 1 - Arec P j)

/-- Recurrence (2.5): prefix counts of `𝓖(u)`. -/
def Brec (P : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => P (Brec P j + 1) + P (j - Brec P j)

/-- `a` is the first threshold `A(j)`: `a ∈ I_j`, `d_j(a) ∈ {0, 1}`, and `d_j < 0` on `I_j` below `a`. -/
def ASpec (L : ℕ) (P : ℕ → ℕ) (j a : ℕ) : Prop :=
  j ≤ a + L ∧ a ≤ j ∧ a ≤ L ∧ P a + P (j - a) ≤ a ∧ a ≤ P a + P (j - a) + 1 ∧
    ∀ x, j ≤ x + L → x < a → x < P x + P (j - x)

/-- `b` is the last threshold `B(j)`: `b ∈ I_j`, `d_j(b) ∈ {-1, 0}`, and `d_j > 0` on `I_j` above `b`. -/
def BSpec (L : ℕ) (P : ℕ → ℕ) (j b : ℕ) : Prop :=
  j ≤ b + L ∧ b ≤ j ∧ b ≤ L ∧ b ≤ P b + P (j - b) ∧ P b + P (j - b) ≤ b + 1 ∧
    ∀ x, x ≤ j → x ≤ L → b < x → P x + P (j - x) < x

variable {L : ℕ} {P : ℕ → ℕ}

/-- One step of the first threshold (proof of Lemma 2.2(3) for `A`). -/
theorem A_next (hD : Dyck L P) {j a : ℕ} (hj : j + 1 ≤ 2 * L) (hA : ASpec L P j a) :
    ASpec L P (j + 1) (P a + P (j + 1 - a)) ∧
      (P a + P (j + 1 - a) = a ∨ P a + P (j + 1 - a) = a + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, hmin⟩ := hA
  have hPa := hD.half a h3
  have hPr := hD.half (j - a) (by omega)
  have hPL := hD.total
  have h2a : j ≤ 2 * a := by omega
  have hrL : j - a + 1 ≤ L := by omega
  have hr1 : j + 1 - a = j - a + 1 := by omega
  have hra := hD.le_top (j - a + 1)
  have sr := hD.step (j - a)
  have sa := hD.step a
  have low : ∀ x, j + 1 ≤ x + L → x < a → x < P x + P (j + 1 - x) := by
    intro x hx hxa
    have := hmin x (by omega) hxa
    have := hD.mono (show j - x ≤ j + 1 - x by omega)
    omega
  rw [hr1]
  by_cases he : P a + P (j - a) = a
  · rcases hD.succ_cases (j - a) with hp | hp
    · -- e = 0, next letter 0: A stays at a
      have hnew : P a + P (j - a + 1) = a := by omega
      rw [hnew]
      refine ⟨⟨by omega, by omega, h3, ?_, ?_, fun x hx hxa => ?_⟩, Or.inl rfl⟩
      · rw [hr1]; omega
      · rw [hr1]; omega
      · exact low x hx hxa
    · -- e = 0, next letter 1: A moves to a + 1
      have hal : a < L := by
        rcases Nat.lt_or_ge a L with h | h
        · exact h
        · have : a = L := by omega
          subst this; omega
      have hnew : P a + P (j - a + 1) = a + 1 := by omega
      rw [hnew]
      have hq : j + 1 - (a + 1) = j - a := by omega
      refine ⟨⟨by omega, by omega, by omega, ?_, ?_, fun x hx hxa => ?_⟩, Or.inr rfl⟩
      · rw [hq]; omega
      · rw [hq]; omega
      · rcases Nat.lt_or_ge x a with h | h
        · exact low x hx h
        · have : x = a := by omega
          subst this; rw [hr1]; omega
  · -- e = 1: the letter at a is 0 and the next letter is 1, so A stays at a
    have ha1 : 1 ≤ a := by omega
    have hm := hmin (a - 1) (by omega) (by omega)
    rw [show j - (a - 1) = j - a + 1 by omega] at hm
    have sa1 := hD.step (a - 1)
    rw [show a - 1 + 1 = a by omega] at sa1
    have hnew : P a + P (j - a + 1) = a := by omega
    rw [hnew]
    refine ⟨⟨by omega, by omega, h3, ?_, ?_, fun x hx hxa => ?_⟩, Or.inl rfl⟩
    · rw [hr1]; omega
    · rw [hr1]; omega
    · exact low x hx hxa

/-- The last threshold is at least `j / 2` (Lemma 2.2(2) for `B`). -/
theorem BSpec.half (hD : Dyck L P) {j b : ℕ} (hj : j ≤ 2 * L) (hB : BSpec L P j b) : j ≤ 2 * b := by
  obtain ⟨_, _, _, _, _, hmax⟩ := hB
  by_contra hc
  have h0 := hmax ((j + 1) / 2) (by omega) (by omega) (by omega)
  have := hD.half ((j + 1) / 2) (by omega)
  have := hD.half (j - (j + 1) / 2) (by omega)
  omega

/-- The first threshold is at least `j / 2` (Lemma 2.2(2) for `A`). -/
theorem ASpec.half (hD : Dyck L P) {j a : ℕ} (hA : ASpec L P j a) : j ≤ 2 * a := by
  obtain ⟨h1, _, h3, h4, _, _⟩ := hA
  have := hD.half a h3
  have := hD.half (j - a) (by omega)
  omega

/-- One step of the last threshold (proof of Lemma 2.2(3) for `B`). -/
theorem B_next (hD : Dyck L P) {j b : ℕ} (hj : j + 1 ≤ 2 * L) (hB : BSpec L P j b) :
    BSpec L P (j + 1) (P (b + 1) + P (j - b)) ∧
      (P (b + 1) + P (j - b) = b ∨ P (b + 1) + P (j - b) = b + 1) := by
  have h2b := BSpec.half hD (by omega) hB
  obtain ⟨h1, h2, h3, h4, h5, hmax⟩ := hB
  have hPL := hD.total
  have hPr := hD.half (j - b) (by omega)
  have sb := hD.step b
  have sr := hD.step (j - b)
  have hrt := hD.le_top (j - b)
  have high : ∀ x, x ≤ j + 1 → x ≤ L → b + 1 < x → P x + P (j + 1 - x) < x := by
    intro x hx1 hx2 hx3
    have := hmax (x - 1) (by omega) (by omega) (by omega)
    rw [show j - (x - 1) = j + 1 - x by omega] at this
    have sx := hD.step (x - 1)
    rw [show x - 1 + 1 = x by omega] at sx
    omega
  rcases Nat.lt_or_ge b L with hbL | hbL
  · by_cases he : P b + P (j - b) = b
    · rcases hD.succ_cases b with hp | hp
      · -- letter at b + 1 is 0: B stays at b
        have hnew : P (b + 1) + P (j - b) = b := by omega
        rw [hnew]
        have hr1 : j + 1 - b = j - b + 1 := by omega
        refine ⟨⟨by omega, by omega, h3, ?_, ?_, fun x hx1 hx2 hx3 => ?_⟩, Or.inl rfl⟩
        · rw [hr1]; omega
        · rw [hr1]; omega
        · rcases Nat.lt_or_ge (b + 1) x with h | h
          · exact high x hx1 hx2 h
          · have : x = b + 1 := by omega
            subst this
            rw [show j + 1 - (b + 1) = j - b by omega]; omega
      · -- letter at b + 1 is 1: B moves to b + 1
        have hnew : P (b + 1) + P (j - b) = b + 1 := by omega
        rw [hnew]
        have hq : j + 1 - (b + 1) = j - b := by omega
        refine ⟨⟨by omega, by omega, by omega, ?_, ?_, fun x hx1 hx2 hx3 => high x hx1 hx2 hx3⟩,
          Or.inr rfl⟩
        · rw [hq]; omega
        · rw [hq]; omega
    · -- d_j(b) = -1: b is not the right end, the letter at b + 1 is 0, and B moves to b + 1
      have hbj : b < j := by
        rcases Nat.lt_or_ge b j with h | h
        · exact h
        · have e0 : j - b = 0 := by omega
          have := hD.le_self b
          rw [e0, hD.zero] at he h4 h5; omega
      have hm := hmax (b + 1) (by omega) (by omega) (by omega)
      have sr1 := hD.step (j - (b + 1))
      rw [show j - (b + 1) + 1 = j - b by omega] at sr1
      have hnew : P (b + 1) + P (j - b) = b + 1 := by omega
      rw [hnew]
      have hq : j + 1 - (b + 1) = j - b := by omega
      refine ⟨⟨by omega, by omega, by omega, ?_, ?_, fun x hx1 hx2 hx3 => high x hx1 hx2 hx3⟩,
        Or.inr rfl⟩
      · rw [hq]; omega
      · rw [hq]; omega
  · -- b = L: the letter at L + 1 is 0, so B stays at L
    have hb : b = L := by omega
    subst hb
    have hbt := hD.tail (b + 1) (by omega)
    have he : P b + P (j - b) = b := by
      by_contra hne
      have := hD.le_top (j - b)
      omega
    have hnew : P (b + 1) + P (j - b) = b := by omega
    rw [hnew]
    have hr1 : j + 1 - b = j - b + 1 := by omega
    refine ⟨⟨by omega, by omega, le_rfl, ?_, ?_, fun x _ hx2 hx3 => by omega⟩, Or.inl rfl⟩
    · rw [hr1]; omega
    · rw [hr1]; omega

theorem Arec_spec (hD : Dyck L P) : ∀ j, j ≤ 2 * L → ASpec L P j (Arec P j)
  | 0, _ => by
    show ASpec L P 0 0
    exact ⟨by omega, le_rfl, Nat.zero_le _, by simp [hD.zero], by omega,
      fun _ _ hx => absurd hx (Nat.not_lt_zero _)⟩
  | j + 1, hj => (A_next hD hj (Arec_spec hD j (by omega))).1

theorem Brec_spec (hD : Dyck L P) : ∀ j, j ≤ 2 * L → BSpec L P j (Brec P j)
  | 0, _ => by
    show BSpec L P 0 0
    exact ⟨by omega, le_rfl, Nat.zero_le _, by simp, by simp [hD.zero],
      fun _ h _ h' => by omega⟩
  | j + 1, hj => (B_next hD hj (Brec_spec hD j (by omega))).1

theorem Arec_succ (hD : Dyck L P) {j : ℕ} (hj : j + 1 ≤ 2 * L) :
    Arec P (j + 1) = Arec P j ∨ Arec P (j + 1) = Arec P j + 1 :=
  (A_next hD hj (Arec_spec hD j (by omega))).2

theorem Brec_succ (hD : Dyck L P) {j : ℕ} (hj : j + 1 ≤ 2 * L) :
    Brec P (j + 1) = Brec P j ∨ Brec P (j + 1) = Brec P j + 1 :=
  (B_next hD hj (Brec_spec hD j (by omega))).2

/-- The thresholds are unique. -/
theorem ASpec.unique {j a a' : ℕ} (h : ASpec L P j a) (h' : ASpec L P j a') : a = a' := by
  obtain ⟨h1, _, _, h4, _, hmin⟩ := h
  obtain ⟨h1', _, _, h4', _, hmin'⟩ := h'
  rcases lt_trichotomy a a' with hl | hl | hl
  · have := hmin' a (by omega) hl; omega
  · exact hl
  · have := hmin a' (by omega) hl; omega

theorem BSpec.unique {j b b' : ℕ} (h : BSpec L P j b) (h' : BSpec L P j b') : b = b' := by
  obtain ⟨_, h2, h3, h4, _, hmax⟩ := h
  obtain ⟨_, h2', h3', h4', _, hmax'⟩ := h'
  rcases lt_trichotomy b b' with hl | hl | hl
  · have := hmax b' h2' h3' hl; omega
  · exact hl
  · have := hmax' b h2 h3 hl; omega

/-- Monotonicity of the first threshold in the word (Lemma 2.3(1) for `𝓕`). -/
theorem ASpec.mono {Q : ℕ → ℕ} (hPQ : ∀ i, P i ≤ Q i) {j a b : ℕ}
    (hP : ASpec L P j a) (hQ : ASpec L Q j b) : a ≤ b := by
  obtain ⟨_, _, _, _, _, hmin⟩ := hP
  obtain ⟨h1, _, _, h4, _, _⟩ := hQ
  by_contra hc
  have := hmin b (by omega) (by omega)
  have := hPQ b; have := hPQ (j - b)
  omega

/-- Monotonicity of the last threshold in the word (Lemma 2.3(1) for `𝓖`). -/
theorem BSpec.mono {Q : ℕ → ℕ} (hPQ : ∀ i, P i ≤ Q i) {j a b : ℕ}
    (hP : BSpec L P j a) (hQ : BSpec L Q j b) : a ≤ b := by
  obtain ⟨_, h2, h3, h4, _, _⟩ := hP
  obtain ⟨_, _, _, _, _, hmax⟩ := hQ
  by_contra hc
  have := hmax a h2 h3 (by omega)
  have := hPQ a; have := hPQ (j - a)
  omega

/-- Prefix counts of `𝓕(u)`, a word of length `2L`. -/
def FP (L : ℕ) (P : ℕ → ℕ) (j : ℕ) : ℕ := Arec P (min j (2 * L))

/-- Prefix counts of `𝓖(u)`, a word of length `2L`. -/
def GP (L : ℕ) (P : ℕ → ℕ) (j : ℕ) : ℕ := Brec P (min j (2 * L))

theorem FP_spec (hD : Dyck L P) {j : ℕ} (hj : j ≤ 2 * L) : ASpec L P j (FP L P j) := by
  unfold FP; rw [min_eq_left hj]; exact Arec_spec hD j hj

theorem GP_spec (hD : Dyck L P) {j : ℕ} (hj : j ≤ 2 * L) : BSpec L P j (GP L P j) := by
  unfold GP; rw [min_eq_left hj]; exact Brec_spec hD j hj

/-- Recurrence (2.4) for `𝓕(u)`. -/
theorem FP_succ (hD : Dyck L P) {j : ℕ} (hj : j + 1 ≤ 2 * L) :
    FP L P (j + 1) = P (FP L P j) + P (j + 1 - FP L P j) := by
  unfold FP; rw [min_eq_left hj, min_eq_left (by omega)]; rfl

/-- Recurrence (2.5) for `𝓖(u)`. -/
theorem GP_succ (hD : Dyck L P) {j : ℕ} (hj : j + 1 ≤ 2 * L) :
    GP L P (j + 1) = P (GP L P j + 1) + P (j - GP L P j) := by
  unfold GP; rw [min_eq_left hj, min_eq_left (by omega)]; rfl

/-- Lemma 2.2(4): `𝓕(u)` is a Dyck word of length `2L`. -/
theorem FP_dyck (hD : Dyck L P) : Dyck (2 * L) (FP L P) where
  zero := by simp [FP, Arec]
  step i := by
    rcases Nat.lt_or_ge i (2 * L) with h | h
    · unfold FP; rw [min_eq_left (by omega : i + 1 ≤ 2 * L), min_eq_left (by omega : i ≤ 2 * L)]
      rcases Arec_succ hD (j := i) (by omega) with h' | h' <;> omega
    · unfold FP; rw [min_eq_right (by omega : 2 * L ≤ i + 1), min_eq_right h]; omega
  tail i h := by unfold FP; rw [min_eq_right h, min_eq_right le_rfl]
  half i h := ASpec.half hD (FP_spec hD h)
  total := by
    obtain ⟨h1, _, h3, _, _, _⟩ := FP_spec hD (le_refl (2 * L)); omega

/-- Lemma 2.2(4): `𝓖(u)` is a Dyck word of length `2L`. -/
theorem GP_dyck (hD : Dyck L P) : Dyck (2 * L) (GP L P) where
  zero := by simp [GP, Brec]
  step i := by
    rcases Nat.lt_or_ge i (2 * L) with h | h
    · unfold GP; rw [min_eq_left (by omega : i + 1 ≤ 2 * L), min_eq_left (by omega : i ≤ 2 * L)]
      rcases Brec_succ hD (j := i) (by omega) with h' | h' <;> omega
    · unfold GP; rw [min_eq_right (by omega : 2 * L ≤ i + 1), min_eq_right h]; omega
  tail i h := by unfold GP; rw [min_eq_right h, min_eq_right le_rfl]
  half i h := BSpec.half hD (by omega) (GP_spec hD h)
  total := by
    obtain ⟨h1, _, h3, _, _, _⟩ := GP_spec hD (le_refl (2 * L)); omega

/-- Lemma 2.2(5): if `A(j) = a` has `d_j(a) = 1` and `a - 1 ∈ I_j`, then the letter `u_a` is `0`. -/
theorem ASpec.letter_zero (hD : Dyck L P) {j a : ℕ} (hA : ASpec L P j a)
    (he : P a + P (j - a) + 1 = a) (hl : j ≤ a - 1 + L) : P a = P (a - 1) := by
  obtain ⟨_, _, _, _, _, hmin⟩ := hA
  have hm := hmin (a - 1) hl (by omega)
  rw [show j - (a - 1) = j - a + 1 by omega] at hm
  have s1 := hD.step (a - 1)
  rw [show a - 1 + 1 = a by omega] at s1
  have s2 := hD.step (j - a)
  omega

/-- Lemma 2.3(2): `𝓕` preserves irreducibility. -/
theorem FP_irred (hD : Dyck L P) (hI : Irred L P) : Irred (2 * L) (FP L P) := by
  intro j hj0 hj
  have hA := FP_spec hD (le_of_lt hj)
  have h2 := ASpec.half hD hA
  by_contra hc
  obtain ⟨_, _, _, h4, _, _⟩ := hA
  set a := FP L P j
  have hja : j - a = a := by omega
  rw [hja] at h4
  have := hI a (by omega) (by omega)
  omega

/-- The reflection `a ↦ a + L - j` carries the first threshold at `j` to the one at `2L - j`
    (proof of Lemma 2.3(3)). -/
theorem ASpec.reflect (hS : Symm L P) (hE : 2 * (L / 2) = L) {j a : ℕ} (hj : j ≤ 2 * L)
    (hA : ASpec L P j a) : ASpec L P (2 * L - j) (a + L - j) := by
  obtain ⟨h1, h2, h3, h4, h5, hmin⟩ := hA
  have s1 := hS (j - a) (by omega)
  have s2 := hS a h3
  rw [show L - (j - a) = a + L - j by omega] at s1
  unfold ASpec
  rw [show 2 * L - j - (a + L - j) = L - a by omega]
  refine ⟨by omega, by omega, by omega, by omega, by omega, fun x' hx' hxa => ?_⟩
  have := hmin (x' + j - L) (by omega) (by omega)
  have t1 := hS (j - (x' + j - L)) (by omega)
  have t2 := hS (x' + j - L) (by omega)
  rw [show L - (j - (x' + j - L)) = x' by omega] at t1
  rw [show L - (x' + j - L) = 2 * L - j - x' by omega] at t2
  omega

theorem BSpec.reflect (hS : Symm L P) (hE : 2 * (L / 2) = L) {j b : ℕ} (hj : j ≤ 2 * L)
    (hB : BSpec L P j b) : BSpec L P (2 * L - j) (b + L - j) := by
  obtain ⟨h1, h2, h3, h4, h5, hmax⟩ := hB
  have s1 := hS (j - b) (by omega)
  have s2 := hS b h3
  rw [show L - (j - b) = b + L - j by omega] at s1
  unfold BSpec
  rw [show 2 * L - j - (b + L - j) = L - b by omega]
  refine ⟨by omega, by omega, by omega, by omega, by omega, fun x' hx1 hx2 hxb => ?_⟩
  have := hmax (x' + j - L) (by omega) (by omega) (by omega)
  have t1 := hS (j - (x' + j - L)) (by omega)
  have t2 := hS (x' + j - L) (by omega)
  rw [show L - (j - (x' + j - L)) = x' by omega] at t1
  rw [show L - (x' + j - L) = 2 * L - j - x' by omega] at t2
  omega

/-- Lemma 2.3(3): `𝓕` preserves symmetry. -/
theorem FP_symm (hD : Dyck L P) (hS : Symm L P) : Symm (2 * L) (FP L P) := by
  have hE : 2 * (L / 2) = L := by have := hD.total; omega
  intro j hj
  have e := ASpec.unique (FP_spec hD (by omega : 2 * L - j ≤ 2 * L))
    (ASpec.reflect hS hE hj (FP_spec hD hj))
  have := (FP_spec hD hj).1
  omega

/-- Lemma 2.3(3): `𝓖` preserves symmetry. -/
theorem GP_symm (hD : Dyck L P) (hS : Symm L P) : Symm (2 * L) (GP L P) := by
  have hE : 2 * (L / 2) = L := by have := hD.total; omega
  intro j hj
  have e := BSpec.unique (GP_spec hD (by omega : 2 * L - j ≤ 2 * L))
    (BSpec.reflect hS hE hj (GP_spec hD hj))
  have := (GP_spec hD hj).1
  omega

/-- Lemma 2.3(1): monotonicity of `𝓕` and `𝓖`. -/
theorem FP_mono {Q : ℕ → ℕ} (hP : Dyck L P) (hQ : Dyck L Q) (hPQ : ∀ i, P i ≤ Q i) (j : ℕ) :
    FP L P j ≤ FP L Q j := by
  rcases le_total j (2 * L) with h | h
  · exact ASpec.mono hPQ (FP_spec hP h) (FP_spec hQ h)
  · rw [(FP_dyck hP).tail j h, (FP_dyck hQ).tail j h]
    exact ASpec.mono hPQ (FP_spec hP le_rfl) (FP_spec hQ le_rfl)

theorem GP_mono {Q : ℕ → ℕ} (hP : Dyck L P) (hQ : Dyck L Q) (hPQ : ∀ i, P i ≤ Q i) (j : ℕ) :
    GP L P j ≤ GP L Q j := by
  rcases le_total j (2 * L) with h | h
  · exact BSpec.mono hPQ (GP_spec hP h) (GP_spec hQ h)
  · rw [(GP_dyck hP).tail j h, (GP_dyck hQ).tail j h]
    exact BSpec.mono hPQ (GP_spec hP le_rfl) (GP_spec hQ le_rfl)

end HofConway
