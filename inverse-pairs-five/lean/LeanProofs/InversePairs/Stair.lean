import LeanProofs.InversePairs.Rect

/-!
# Inverse pairs: the staircase (Lemma 2)

`inv a` is the inverse of `a` modulo `p` in `0..p-1`. `Rc X` counts `a ∈ [1, p)` with
`a · inv a ≤ X` and `Tc X = ∑_{a ∈ [1,p)} min(p - 1, X / a)` counts all pairs
`(a, b) ∈ [1, p)²` with `ab ≤ X`.
* `N_eq`: the unit count `N` is the count of `a ∈ I` with `inv a ∈ J`;
* `column`: on one column `[c, d)` the two counts differ by at most `E₁ + (d - c)(m⁺ - m⁻)/p`;
* `stair`: with columns of width `h` (`L` of them, `p ≤ 1 + L h`),
  `|Rc X - Tc X / p| ≤ L · 3 √p (1 + log p)² + h`.
-/

open Finset

namespace InversePairs

variable (p : ℕ) [hp : Fact p.Prime]

/-- The inverse of `a` modulo `p`, as a number in `0..p-1`. -/
noncomputable def inv (a : ℕ) : ℕ := ((a : ZMod p)⁻¹).val

lemma cast_ne_zero (a : ℕ) (h1 : 1 ≤ a) (h2 : a < p) : (a : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun hd => by have := Nat.le_of_dvd h1 hd; omega

lemma inv_mem (a : ℕ) (h1 : 1 ≤ a) (h2 : a < p) : 1 ≤ inv p a ∧ inv p a < p := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  refine ⟨Nat.one_le_iff_ne_zero.2 ?_, ZMod.val_lt _⟩
  rw [inv, Ne, ZMod.val_eq_zero, inv_eq_zero]
  exact cast_ne_zero p a h1 h2

/-- The unit count `N p I J` counts `a ∈ I` with `inv a ∈ J`. -/
lemma N_eq (I J : Finset ℕ) (hI : ∀ a ∈ I, 1 ≤ a ∧ a < p) : N p I J = #{a ∈ I | inv p a ∈ J} := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  unfold N
  refine Finset.card_bij' (fun x _ => (x : ZMod p).val)
    (fun a ha => Units.mk0 (a : ZMod p) (cast_ne_zero p a (hI a (mem_filter.1 ha).1).1
      (hI a (mem_filter.1 ha).1).2)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rw [inv, ZMod.natCast_zmod_val, ← Units.val_inv_eq_inv_val]; exact hx.2
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    have h := hI a ha.1
    rw [Units.val_mk0, ZMod.val_cast_of_lt h.2, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact ⟨ha.1, ha.2⟩
  · intro x _; ext; simp
  · intro a ha
    have h := hI a (mem_filter.1 ha).1
    simp [ZMod.val_cast_of_lt h.2]

/-- `Rc X`: the number of `a ∈ [1, p)` with `a · inv a ≤ X`. -/
noncomputable def Rc (X : ℕ) : ℕ := #{a ∈ Ico 1 p | a * inv p a ≤ X}

/-- `Tc X`: the number of pairs `(a, b) ∈ [1, p)²` with `ab ≤ X`. -/
def Tc (X : ℕ) : ℕ := ∑ a ∈ Ico 1 p, min (p - 1) (X / a)

/-- The rectangle error `E₁ = 3 √p (1 + log p)²`. -/
noncomputable def E1 : ℝ := 3 * Real.sqrt p * (1 + Real.log p) ^ 2

/-- One column `[c, d)`. -/
lemma column (hW : WeilBound p) (X c d : ℕ) (hc : 1 ≤ c) (hcd : c ≤ d) (hd : d ≤ p) :
    |(#{a ∈ Ico c d | a * inv p a ≤ X} : ℝ) - (∑ a ∈ Ico c d, min (p - 1) (X / a) : ℕ) / p| ≤
      E1 p + (d - c : ℕ) *
        (((min (p - 1) (X / c) : ℕ) : ℝ) - (min (p - 1) (X / (d - 1)) : ℕ)) / p := by
  set mp := min (p - 1) (X / c)
  set mm := min (p - 1) (X / (d - 1))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hcol : ∀ a ∈ Ico c d, 1 ≤ a ∧ a < p := fun a ha => by simp at ha; omega
  have hlen : c + (d - c) = d := by omega
  -- the two rectangles
  have rp := rect p hW c (d - c) 1 mp hc (by omega) le_rfl (by omega)
  have rm := rect p hW c (d - c) 1 mm hc (by omega) le_rfl (by omega)
  rw [hlen, N_eq p _ _ hcol] at rp rm
  set A := #{a ∈ Ico c d | a * inv p a ≤ X}
  set Np := #{a ∈ Ico c d | inv p a ∈ Ico 1 (1 + mp)}
  set Nm := #{a ∈ Ico c d | inv p a ∈ Ico 1 (1 + mm)}
  have hA1 : A ≤ Np := card_le_card fun a ha => by
    simp only [mem_filter, mem_Ico] at ha ⊢
    have hi := inv_mem p a (by omega) (by omega)
    refine ⟨ha.1, hi.1, ?_⟩
    have h1 : inv p a ≤ X / a := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact ha.2)
    have h2 : X / a ≤ X / c := Nat.div_le_div_left ha.1.1 (by omega)
    omega
  have hA2 : Nm ≤ A := card_le_card fun a ha => by
    simp only [mem_filter, mem_Ico] at ha ⊢
    refine ⟨ha.1, ?_⟩
    have h2 : X / (d - 1) ≤ X / a := Nat.div_le_div_left (by omega) (by omega)
    have h3 : inv p a ≤ X / a := by omega
    calc a * inv p a ≤ a * (X / a) := Nat.mul_le_mul_left _ h3
      _ ≤ X := Nat.mul_div_le X a
  -- the column of the lattice count lies between `(d - c) mm` and `(d - c) mp`
  set S := ∑ a ∈ Ico c d, min (p - 1) (X / a)
  have hS1 : S ≤ (d - c) * mp := by
    calc S ≤ ∑ a ∈ Ico c d, mp := sum_le_sum fun a ha => by
          rw [mem_Ico] at ha; exact min_le_min le_rfl (Nat.div_le_div_left ha.1 (by omega))
      _ = (d - c) * mp := by simp
  have hS2 : (d - c) * mm ≤ S := by
    calc (d - c) * mm = ∑ a ∈ Ico c d, mm := by simp
      _ ≤ S := sum_le_sum fun a ha => by
          simp at ha; exact min_le_min le_rfl (Nat.div_le_div_left (by omega) (by omega))
  have hS1' : (S : ℝ) ≤ (d - c : ℕ) * (mp : ℝ) := by exact_mod_cast hS1
  have hS2' : (d - c : ℕ) * (mm : ℝ) ≤ S := by exact_mod_cast hS2
  have hA1' : (A : ℝ) ≤ Np := by exact_mod_cast hA1
  have hA2' : (Nm : ℝ) ≤ A := by exact_mod_cast hA2
  rw [abs_le] at rp rm ⊢
  have e1 : (S : ℝ) / p ≤ (d - c : ℕ) * (mp : ℝ) / p := div_le_div_of_nonneg_right hS1' hp0.le
  have e2 : (d - c : ℕ) * (mm : ℝ) / p ≤ (S : ℝ) / p := div_le_div_of_nonneg_right hS2' hp0.le
  have e3 : ((d - c : ℕ) : ℝ) * ((mp : ℝ) - mm) / p =
      (d - c : ℕ) * (mp : ℝ) / p - (d - c : ℕ) * (mm : ℝ) / p := by ring
  constructor
  · rw [E1]; nlinarith [rm.1]
  · rw [E1]; nlinarith [rp.2]

/-- Sums over consecutive columns `[c ℓ, c (ℓ + 1))` add up to the sum over `[c 0, c L)`. -/
lemma sum_columns (f : ℕ → ℝ) (c : ℕ → ℕ) (hc : Monotone c) (L : ℕ) :
    ∑ ℓ ∈ range L, ∑ a ∈ Ico (c ℓ) (c (ℓ + 1)), f a = ∑ a ∈ Ico (c 0) (c L), f a := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, ih, sum_Ico_consecutive _ (hc (Nat.zero_le _)) (hc (Nat.le_succ _))]

/-- Lemma 2: inverse pairs against all pairs under the hyperbola `ab = X`. -/
theorem stair (hW : WeilBound p) (X h L : ℕ) (hh : 1 ≤ h) (hL : p ≤ 1 + L * h) :
    |(Rc p X : ℝ) - Tc p X / p| ≤ L * E1 p + h := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 := hp.out.one_le
  set c : ℕ → ℕ := fun ℓ => min (1 + ℓ * h) p with hcdef
  have hmono : Monotone c := fun i j hij => min_le_min (by nlinarith) le_rfl
  have hc0 : c 0 = 1 := by simp [c]; omega
  have hcL : c L = p := by simp [c]; omega
  have hc1 : ∀ ℓ, 1 ≤ c ℓ := fun ℓ => by simp [c]; omega
  have hcp : ∀ ℓ, c ℓ ≤ p := fun ℓ => min_le_right _ _
  have hstep : ∀ ℓ, c (ℓ + 1) - c ℓ ≤ h := fun ℓ => by simp only [c]; rw [add_mul, one_mul]; omega
  have hc2 : ∀ ℓ, 2 ≤ c (ℓ + 1) := fun ℓ => by
    have := hp.out.two_le
    simp only [c]; rw [add_mul, one_mul]; omega
  set mp : ℕ → ℕ := fun ℓ => min (p - 1) (X / c ℓ)
  set mm : ℕ → ℕ := fun ℓ => min (p - 1) (X / (c (ℓ + 1) - 1))
  -- both counts split over the columns
  have hR : (Rc p X : ℝ) = ∑ ℓ ∈ range L,
      (#{a ∈ Ico (c ℓ) (c (ℓ + 1)) | a * inv p a ≤ X} : ℝ) := by
    have := sum_columns (fun a => if a * inv p a ≤ X then (1 : ℝ) else 0) c hmono L
    rw [hc0, hcL] at this
    simp only [Rc, card_filter]; push_cast
    rw [← this]
  have hT : (Tc p X : ℝ) = ∑ ℓ ∈ range L,
      ((∑ a ∈ Ico (c ℓ) (c (ℓ + 1)), min (p - 1) (X / a) : ℕ) : ℝ) := by
    have := sum_columns (fun a => ((min (p - 1) (X / a) : ℕ) : ℝ)) c hmono L
    rw [hc0, hcL] at this
    simp only [Tc]; push_cast at this ⊢
    rw [← this]
  -- per column, then telescope
  have hcolumn := fun ℓ => column p hW X (c ℓ) (c (ℓ + 1)) (hc1 ℓ) (hmono (by omega : ℓ ≤ ℓ + 1))
    (hcp (ℓ + 1))
  have htel : ∀ ℓ, ((c (ℓ + 1) - c ℓ : ℕ) : ℝ) * ((mp ℓ : ℝ) - mm ℓ) ≤
      h * ((mp ℓ : ℝ) - mp (ℓ + 1)) := fun ℓ => by
    have hanti : mp (ℓ + 1) ≤ mm ℓ :=
      min_le_min le_rfl (Nat.div_le_div_left (by omega) (by have := hc2 ℓ; omega))
    have hanti' : mp (ℓ + 1) ≤ mp ℓ :=
      min_le_min le_rfl (Nat.div_le_div_left (hmono (by omega : ℓ ≤ ℓ + 1))
      (hc1 ℓ))
    rcases Nat.eq_or_lt_of_le (hmono (by omega : ℓ ≤ ℓ + 1)) with heq | hlt
    · rw [← heq, Nat.sub_self, Nat.cast_zero, zero_mul]
      have : (mp (ℓ + 1) : ℝ) ≤ mp ℓ := by exact_mod_cast hanti'
      have : (0 : ℝ) ≤ h := by positivity
      nlinarith
    · have hmm : mm ℓ ≤ mp ℓ := min_le_min le_rfl (Nat.div_le_div_left (by omega) (hc1 ℓ))
      have h1 : ((c (ℓ + 1) - c ℓ : ℕ) : ℝ) ≤ h := by exact_mod_cast hstep ℓ
      have h2 : (0 : ℝ) ≤ (mp ℓ : ℝ) - mm ℓ := by
        have : (mm ℓ : ℝ) ≤ mp ℓ := by exact_mod_cast hmm
        linarith
      have h3 : (mp ℓ : ℝ) - mm ℓ ≤ (mp ℓ : ℝ) - mp (ℓ + 1) := by
        have : (mp (ℓ + 1) : ℝ) ≤ mm ℓ := by exact_mod_cast hanti
        linarith
      have h4 : (0 : ℝ) ≤ ((c (ℓ + 1) - c ℓ : ℕ) : ℝ) := by positivity
      calc ((c (ℓ + 1) - c ℓ : ℕ) : ℝ) * ((mp ℓ : ℝ) - mm ℓ)
          ≤ h * ((mp ℓ : ℝ) - mm ℓ) := mul_le_mul_of_nonneg_right h1 h2
        _ ≤ h * ((mp ℓ : ℝ) - mp (ℓ + 1)) := mul_le_mul_of_nonneg_left h3 (by positivity)
  rw [hR, hT, sum_div, ← sum_sub_distrib]
  have hsum := (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ℓ (_ : ℓ ∈ range L) => hcolumn ℓ)
  refine hsum.trans ?_
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have htsum : ∑ ℓ ∈ range L, ((c (ℓ + 1) - c ℓ : ℕ) : ℝ) * ((mp ℓ : ℝ) - mm ℓ) / p ≤ h := by
    rw [← sum_div]
    have : ∑ ℓ ∈ range L, ((c (ℓ + 1) - c ℓ : ℕ) : ℝ) * ((mp ℓ : ℝ) - mm ℓ) ≤
        h * ((mp 0 : ℝ) - mp L) := by
      calc _ ≤ ∑ ℓ ∈ range L, (h : ℝ) * ((mp ℓ : ℝ) - mp (ℓ + 1)) := sum_le_sum fun ℓ _ => htel ℓ
        _ = h * ((mp 0 : ℝ) - mp L) := by
          rw [← mul_sum, sum_range_sub' (fun ℓ => (mp ℓ : ℝ))]
    have hmp0 : (mp 0 : ℝ) ≤ p := by
      have : mp 0 ≤ p := (min_le_left _ _).trans (Nat.sub_le _ _)
      exact_mod_cast this
    have hmpL : (0 : ℝ) ≤ mp L := by positivity
    rw [div_le_iff₀ hp0]
    have : (0 : ℝ) ≤ h := by positivity
    nlinarith
  linarith

end InversePairs
