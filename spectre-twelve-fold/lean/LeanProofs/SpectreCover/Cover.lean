import LeanProofs.SpectreCover.Shadow

/-!
# Edge cancellation forces a constant count (MO 516016)

An abstract periodic family: finitely many counterclockwise triangles `V i 0, V i 1, V i 2`
(`i : ι`), each translated by every point `lat v w m = m.1 • v + m.2 • w` of a lattice. The count
`cnt z` is the number of translated closed triangles containing `z`.

The hypothesis `Paired` says that the oriented edges cancel modulo the lattice: every
lattice-invariant function of an oriented edge has the same total over the edges as over the
reversed edges. Under it, `vmove` shows that the count is the same at any two points of a
vertical line through no vertex, off every edge. The proof writes each indicator as a sum of edge
shadows (`tri_shadow`); the change of count between the two points is then a sum over edges
of a lattice-invariant, antisymmetric quantity, which `Paired` forces to vanish.
-/

namespace SpectreCover

open Classical

/-- The lattice point `m.1 • v + m.2 • w`. -/
def lat (v w : ℝ × ℝ) (m : ℤ × ℤ) : ℝ × ℝ := (m.1 : ℝ) • v + (m.2 : ℝ) • w

theorem lat_add (v w : ℝ × ℝ) (m n : ℤ × ℤ) : lat v w (m + n) = lat v w m + lat v w n := by
  unfold lat; push_cast [Prod.fst_add, Prod.snd_add]; module

theorem orient_add (A B C t : ℝ × ℝ) : orient (A + t) (B + t) (C + t) = orient A B C := by
  unfold orient; simp only [Prod.fst_add, Prod.snd_add]; ring

/-- Only finitely many lattice points lie in a box, when `v, w` are independent. -/
theorem lat_finite {v w : ℝ × ℝ} (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) (K : ℝ) :
    {m : ℤ × ℤ | |(lat v w m).1| ≤ K ∧ |(lat v w m).2| ≤ K}.Finite := by
  set d := v.1 * w.2 - v.2 * w.1
  have hd : 0 < |d| := abs_pos.mpr hdet
  set B := K * (|v.1| + |v.2| + |w.1| + |w.2|) / |d|
  have bound : ∀ m : ℤ × ℤ, |(lat v w m).1| ≤ K → |(lat v w m).2| ≤ K →
      |(m.1 : ℝ)| ≤ B ∧ |(m.2 : ℝ)| ≤ B := by
    intro m h1 h2
    have hK : 0 ≤ K := (abs_nonneg _).trans h1
    have e1 : (m.1 : ℝ) * d = (lat v w m).1 * w.2 - (lat v w m).2 * w.1 := by
      simp only [lat, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, d]
      ring
    have e2 : (m.2 : ℝ) * d = v.1 * (lat v w m).2 - v.2 * (lat v w m).1 := by
      simp only [lat, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, d]
      ring
    have t1 : |(m.1 : ℝ)| * |d| ≤ K * (|v.1| + |v.2| + |w.1| + |w.2|) := by
      rw [← abs_mul, e1]
      calc |(lat v w m).1 * w.2 - (lat v w m).2 * w.1|
          ≤ |(lat v w m).1| * |w.2| + |(lat v w m).2| * |w.1| := by
            rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
        _ ≤ K * |w.2| + K * |w.1| := by gcongr
        _ ≤ _ := by nlinarith [abs_nonneg v.1, abs_nonneg v.2]
    have t2 : |(m.2 : ℝ)| * |d| ≤ K * (|v.1| + |v.2| + |w.1| + |w.2|) := by
      rw [← abs_mul, e2]
      calc |v.1 * (lat v w m).2 - v.2 * (lat v w m).1|
          ≤ |v.1| * |(lat v w m).2| + |v.2| * |(lat v w m).1| := by
            rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
        _ ≤ |v.1| * K + |v.2| * K := by gcongr
        _ ≤ _ := by nlinarith [abs_nonneg w.1, abs_nonneg w.2]
    exact ⟨(le_div_iff₀ hd).mpr t1, (le_div_iff₀ hd).mpr t2⟩
  set N := ⌈B⌉
  refine ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).subset ?_
  rintro m ⟨h1, h2⟩
  obtain ⟨b1, b2⟩ := bound m h1 h2
  have c1 := abs_le.mp (b1.trans (Int.le_ceil B))
  have c2 := abs_le.mp (b2.trans (Int.le_ceil B))
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> [skip; skip; skip; skip] <;>
    first
    | exact_mod_cast c1.1 | exact_mod_cast c1.2 | exact_mod_cast c2.1 | exact_mod_cast c2.2

theorem bary_shift_snd (A B C z : ℝ × ℝ) :
    orient A B C * (z.2 - A.2) = orient C A z * (B.2 - A.2) + orient A B z * (C.2 - A.2) := by
  unfold orient; ring

/-- A closed triangle lies within a box around its first vertex. -/
theorem closedTri_bound {A B C z : ℝ × ℝ} (hD : 0 < orient A B C) (hz : z ∈ closedTri A B C) :
    |z.1 - A.1| ≤ |B.1 - A.1| + |C.1 - A.1| ∧ |z.2 - A.2| ≤ |B.2 - A.2| + |C.2 - A.2| := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hs := bary_sum A B C z
  have le1 : orient C A z ≤ orient A B C := by linarith
  have le2 : orient A B z ≤ orient A B C := by linarith
  have key : ∀ u v : ℝ, |orient C A z * u + orient A B z * v| ≤ orient A B C * (|u| + |v|) := by
    intro u v
    calc |orient C A z * u + orient A B z * v| ≤ |orient C A z * u| + |orient A B z * v| :=
          abs_add_le _ _
      _ = orient C A z * |u| + orient A B z * |v| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h3, abs_of_nonneg h1]
      _ ≤ orient A B C * |u| + orient A B C * |v| := by gcongr
      _ = _ := by ring
  constructor
  · have := key (B.1 - A.1) (C.1 - A.1)
    rw [← bary_shift, abs_mul, abs_of_pos hD] at this
    exact le_of_mul_le_mul_left this hD
  · have := key (B.2 - A.2) (C.2 - A.2)
    rw [← bary_shift_snd, abs_mul, abs_of_pos hD] at this
    exact le_of_mul_le_mul_left this hD

/-- Points on one column: if the shadows at `(x, y₁)` and `(x, y₂)` differ, the edge passes
between them, so `orient P Q (x, y₁)` is at most the change of `orient` along the column. -/
theorem orient_small_of_shadow_ne {P Q : ℝ × ℝ} {x y₁ y₂ : ℝ}
    (h : shadow P Q (x, y₂) ≠ shadow P Q (x, y₁)) :
    ((P.1 < x ∧ x < Q.1) ∨ (Q.1 < x ∧ x < P.1)) ∧
      |orient P Q (x, y₁)| ≤ |Q.1 - P.1| * |y₂ - y₁| := by
  have hd : orient P Q (x, y₂) - orient P Q (x, y₁) = (Q.1 - P.1) * (y₂ - y₁) := by
    unfold orient; ring
  rw [← abs_mul, ← hd]
  by_cases r1 : P.1 < x ∧ x < Q.1
  · have e : ∀ y, shadow P Q (x, y) = if orient P Q (x, y) < 0 then -1 else 0 := fun y => by
      simp [shadow, r1.1, r1.2, not_lt.mpr r1.2.le]
    rw [e, e] at h
    refine ⟨Or.inl r1, ?_⟩
    split_ifs at h with a b c <;> simp at h
    · rw [abs_of_nonneg (not_lt.mp b), abs_of_neg (by linarith)]; linarith
    · rw [abs_of_neg c, abs_of_nonneg (by linarith [not_lt.mp a])]; linarith
  · by_cases r2 : Q.1 < x ∧ x < P.1
    · have e : ∀ y, shadow P Q (x, y) = if 0 < orient P Q (x, y) then 1 else 0 := fun y => by
        simp [shadow, r2.1, r2.2, not_lt.mpr r2.2.le]
      rw [e, e] at h
      refine ⟨Or.inr r2, ?_⟩
      split_ifs at h with a b c <;> simp at h
      · rw [abs_of_nonpos (not_lt.mp b), abs_of_pos (by linarith)]; linarith
      · rw [abs_of_pos c, abs_of_nonpos (by linarith [not_lt.mp a])]; linarith
    · exfalso; apply h
      rw [shadow_eq_zero (by rintro (h' | h') <;> [exact r1 h'; exact r2 h']),
        shadow_eq_zero (by rintro (h' | h') <;> [exact r1 h'; exact r2 h'])]

section Family

variable {ι : Type*} [Fintype ι] (V : ι → Fin 3 → ℝ × ℝ) (v w : ℝ × ℝ)

/-- The triangle `i` translated by the lattice point `m`. -/
def tri (i : ι) (m : ℤ × ℤ) : Set (ℝ × ℝ) :=
  closedTri (V i 0 + lat v w m) (V i 1 + lat v w m) (V i 2 + lat v w m)

/-- The number of translated triangles containing `z`. -/
noncomputable def cnt (z : ℝ × ℝ) : ℤ := ∑ i, ∑ᶠ m : ℤ × ℤ, if z ∈ tri V v w i m then 1 else 0

/-- The oriented edges cancel modulo the lattice. -/
def Paired : Prop :=
  ∀ H : ℝ × ℝ → ℝ × ℝ → ℤ, (∀ P Q m, H (P + lat v w m) (Q + lat v w m) = H P Q) →
    ∑ i, ∑ k : Fin 3, H (V i k) (V i (k + 1)) = ∑ i, ∑ k : Fin 3, H (V i (k + 1)) (V i k)

variable {V v w}

theorem tri_finite (hD : ∀ i, 0 < orient (V i 0) (V i 1) (V i 2))
    (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) (i : ι) (z : ℝ × ℝ) :
    Function.HasFiniteSupport fun m : ℤ × ℤ => if z ∈ tri V v w i m then (1 : ℤ) else 0 := by
  set A := V i 0; set B := V i 1; set C := V i 2
  refine (lat_finite hdet (|z.1| + |z.2| + |A.1| + |A.2| + |B.1 - A.1| + |C.1 - A.1| +
    |B.2 - A.2| + |C.2 - A.2|)).subset ?_
  intro m hm
  have hz : z ∈ tri V v w i m := by by_contra h; simp [h] at hm
  have hD' : 0 < orient (A + lat v w m) (B + lat v w m) (C + lat v w m) := by
    rw [orient_add]; exact hD i
  obtain ⟨b1, b2⟩ := closedTri_bound hD' hz
  simp only [Prod.fst_add, Prod.snd_add, add_sub_add_right_eq_sub] at b1 b2
  have := abs_nonneg z.1; have := abs_nonneg z.2; have := abs_nonneg A.1; have := abs_nonneg A.2
  have := abs_nonneg (B.1 - A.1); have := abs_nonneg (C.1 - A.1)
  have := abs_nonneg (B.2 - A.2); have := abs_nonneg (C.2 - A.2)
  constructor
  · have e : (lat v w m).1 = z.1 - A.1 - (z.1 - (A.1 + (lat v w m).1)) := by ring
    rw [e]
    calc |z.1 - A.1 - (z.1 - (A.1 + (lat v w m).1))|
        ≤ |z.1 - A.1| + |z.1 - (A.1 + (lat v w m).1)| := abs_sub _ _
      _ ≤ |z.1| + |A.1| + (|B.1 - A.1| + |C.1 - A.1|) := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  · have e : (lat v w m).2 = z.2 - A.2 - (z.2 - (A.2 + (lat v w m).2)) := by ring
    rw [e]
    calc |z.2 - A.2 - (z.2 - (A.2 + (lat v w m).2))|
        ≤ |z.2 - A.2| + |z.2 - (A.2 + (lat v w m).2)| := abs_sub _ _
      _ ≤ |z.2| + |A.2| + (|B.2 - A.2| + |C.2 - A.2|) := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith

theorem delta_finite (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) (P Q : ℝ × ℝ) (x y₁ y₂ : ℝ) :
    Function.HasFiniteSupport fun m : ℤ × ℤ =>
      shadow (P + lat v w m) (Q + lat v w m) (x, y₂) -
        shadow (P + lat v w m) (Q + lat v w m) (x, y₁) := by
  refine (lat_finite hdet (|x| + |P.1| + |Q.1 - P.1| + |y₁| + |P.2| + |y₂ - y₁| +
    |Q.2 - P.2|)).subset ?_
  intro m hm
  have hm' : shadow (P + lat v w m) (Q + lat v w m) (x, y₂) ≠
      shadow (P + lat v w m) (Q + lat v w m) (x, y₁) := fun h => hm (by simp [h])
  obtain ⟨hr, ho⟩ := orient_small_of_shadow_ne hm'
  set l := lat v w m
  simp only [Prod.fst_add, add_sub_add_right_eq_sub] at hr ho
  have hq : 0 < |Q.1 - P.1| :=
    abs_pos.mpr (by rcases hr with h | h <;> intro h' <;> linarith [h.1, h.2])
  have hu : |x - P.1 - l.1| ≤ |Q.1 - P.1| := by
    rw [abs_le]; rcases hr with h | h <;> constructor <;>
      cases abs_cases (Q.1 - P.1) <;> linarith [h.1, h.2]
  have ho' : orient (P + l) (Q + l) (x, y₁) =
      (Q.1 - P.1) * (y₁ - P.2 - l.2) - (Q.2 - P.2) * (x - P.1 - l.1) := by
    unfold orient; simp only [Prod.fst_add, Prod.snd_add]; ring
  rw [ho'] at ho
  have hv : |y₁ - P.2 - l.2| ≤ |y₂ - y₁| + |Q.2 - P.2| := by
    have k : |Q.1 - P.1| * |y₁ - P.2 - l.2| ≤ |Q.1 - P.1| * (|y₂ - y₁| + |Q.2 - P.2|) := by
      rw [← abs_mul]
      calc |(Q.1 - P.1) * (y₁ - P.2 - l.2)|
          = |((Q.1 - P.1) * (y₁ - P.2 - l.2) - (Q.2 - P.2) * (x - P.1 - l.1)) +
              (Q.2 - P.2) * (x - P.1 - l.1)| := by ring_nf
        _ ≤ |(Q.1 - P.1) * (y₁ - P.2 - l.2) - (Q.2 - P.2) * (x - P.1 - l.1)| +
              |(Q.2 - P.2) * (x - P.1 - l.1)| := abs_add_le _ _
        _ ≤ |Q.1 - P.1| * |y₂ - y₁| + |Q.2 - P.2| * |Q.1 - P.1| := by
            rw [abs_mul (Q.2 - P.2)]; gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_left k hq
  have := abs_nonneg x; have := abs_nonneg P.1; have := abs_nonneg (Q.1 - P.1)
  have := abs_nonneg y₁; have := abs_nonneg P.2; have := abs_nonneg (y₂ - y₁)
  have := abs_nonneg (Q.2 - P.2)
  constructor
  · have e : l.1 = x - P.1 - (x - P.1 - l.1) := by ring
    rw [e]
    calc |x - P.1 - (x - P.1 - l.1)| ≤ |x - P.1| + |x - P.1 - l.1| := abs_sub _ _
      _ ≤ |x| + |P.1| + |Q.1 - P.1| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  · have e : l.2 = y₁ - P.2 - (y₁ - P.2 - l.2) := by ring
    rw [e]
    calc |y₁ - P.2 - (y₁ - P.2 - l.2)| ≤ |y₁ - P.2| + |y₁ - P.2 - l.2| := abs_sub _ _
      _ ≤ |y₁| + |P.2| + (|y₂ - y₁| + |Q.2 - P.2|) := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith

/-- **Vertical move.** Along a vertical line through no vertex, the count is the same at any
two points off the edges. -/
theorem vmove (hD : ∀ i, 0 < orient (V i 0) (V i 1) (V i 2))
    (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) (hpair : Paired V v w) {x y₁ y₂ : ℝ}
    (hx : ∀ i k m, (V i k + lat v w m).1 ≠ x)
    (h₁ : ∀ i k m, ((x, y₁) : ℝ × ℝ) ∉ segment ℝ (V i k + lat v w m) (V i (k + 1) + lat v w m))
    (h₂ : ∀ i k m, ((x, y₂) : ℝ × ℝ) ∉ segment ℝ (V i k + lat v w m) (V i (k + 1) + lat v w m)) :
    cnt V v w (x, y₁) = cnt V v w (x, y₂) := by
  have ind : ∀ y, (∀ i k m, ((x, y) : ℝ × ℝ) ∉
      segment ℝ (V i k + lat v w m) (V i (k + 1) + lat v w m)) → ∀ i m,
      (if ((x, y) : ℝ × ℝ) ∈ tri V v w i m then 1 else 0 : ℤ) =
        ∑ k : Fin 3, shadow (V i k + lat v w m) (V i (k + 1) + lat v w m) (x, y) := by
    intro y hy i m
    rw [Fin.sum_univ_three]
    have e2 : ((1 : Fin 3) + 1) = 2 := rfl
    have e3 : ((2 : Fin 3) + 1) = 0 := rfl
    have s1 := hy i 1 m
    have s2 := hy i 2 m
    rw [e2] at s1 ⊢; rw [e3] at s2 ⊢
    exact tri_shadow (by rw [orient_add]; exact hD i) (hx i 0 m) (hx i 1 m) (hx i 2 m)
      (hy i 0 m) s1 s2
  set G : ℝ × ℝ → ℝ × ℝ → ℤ := fun P Q => ∑ᶠ m : ℤ × ℤ,
    (shadow (P + lat v w m) (Q + lat v w m) (x, y₂) -
      shadow (P + lat v w m) (Q + lat v w m) (x, y₁)) with hGdef
  have hG : ∀ P Q m₀, G (P + lat v w m₀) (Q + lat v w m₀) = G P Q := by
    intro P Q m₀
    simp only [hGdef]
    conv_rhs => rw [← finsum_comp_equiv (Equiv.addLeft m₀)]
    congr 1; ext m
    simp only [Equiv.coe_addLeft, lat_add, add_assoc]
  have hGswap : ∀ P Q, G Q P = -G P Q := by
    intro P Q
    simp only [hGdef]
    rw [← finsum_neg_distrib]
    congr 1; ext m
    rw [shadow_swap (Q + _), shadow_swap (Q + _)]; ring
  have total : ∑ i, ∑ k : Fin 3, G (V i k) (V i (k + 1)) = 0 := by
    have := hpair G hG
    have e : (∑ i, ∑ k : Fin 3, G (V i (k + 1)) (V i k)) =
        -(∑ i, ∑ k : Fin 3, G (V i k) (V i (k + 1))) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun k _ => hGswap _ _
    omega
  have step : ∀ i, (∑ᶠ m : ℤ × ℤ, if ((x, y₂) : ℝ × ℝ) ∈ tri V v w i m then 1 else 0 : ℤ) -
      (∑ᶠ m : ℤ × ℤ, if ((x, y₁) : ℝ × ℝ) ∈ tri V v w i m then 1 else 0 : ℤ) =
        ∑ k : Fin 3, G (V i k) (V i (k + 1)) := by
    intro i
    rw [← finsum_sub_distrib (tri_finite hD hdet i _) (tri_finite hD hdet i _)]
    simp_rw [ind y₂ h₂ i, ind y₁ h₁ i, ← Finset.sum_sub_distrib]
    exact finsum_sum_comm Finset.univ _ (fun k _ => delta_finite hdet _ _ x y₁ y₂)
  have : cnt V v w (x, y₂) - cnt V v w (x, y₁) = 0 := by
    unfold cnt
    rw [← Finset.sum_sub_distrib]
    simp_rw [step]
    exact total
  omega

end Family

end SpectreCover
