import LeanProofs.SpectreCover.Concrete
import LeanProofs.SpectreCover.Count

/-!
# A periodic 12-fold cover by Spectres (MO 516016)

**Theorem** (`spectre_twelve_fold`). Let `S` be the (straight-edged) Spectre `Tile(1,1)` and
`ρ` the rotation by `30°`. The tiles `ρ^r S + x a + y b + λ`, for the 54 placements `(r, x, y)`
of `placements` and every `λ` in the lattice `ℤ v + ℤ w`, cover almost every point of the plane
exactly 12 times. Only rotations and translations are used.

The proof: the count is almost everywhere constant (`cnt_ae_const`, from edge cancellation),
and integrating over a period cell gives `c · (27/2)(1 + √3) = 54 · (3 + 3√3)`, so `c = 12`.
-/

namespace SpectreCover

open MeasureTheory Classical

/-! ### The constant is 12 -/

theorem sum_orientZ :
    (∑ i : Fin 54 × Fin 12, (orientZ (vertZ i.1 i.2 0) (vertZ i.1 i.2 1) (vertZ i.1 i.2 2)).1,
      ∑ i : Fin 54 × Fin 12, (orientZ (vertZ i.1 i.2 0) (vertZ i.1 i.2 1) (vertZ i.1 i.2 2)).2) =
      (1296, 1296) := by
  decide +kernel

theorem sum_orient : ∑ i, orient (V i 0) (V i 1) (V i 2) / 2 = 162 * (1 + Real.sqrt 3) := by
  have h := sum_orientZ
  simp only [Prod.mk.injEq] at h
  simp only [V, orient_phys, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul]
  have h1 : (∑ i : Fin 54 × Fin 12, ((orientZ (vertZ i.1 i.2 0) (vertZ i.1 i.2 1)
      (vertZ i.1 i.2 2)).1 : ℝ)) = 1296 := by exact_mod_cast h.1
  have h2 : (∑ i : Fin 54 × Fin 12, ((orientZ (vertZ i.1 i.2 0) (vertZ i.1 i.2 1)
      (vertZ i.1 i.2 2)).2 : ℝ)) = 1296 := by exact_mod_cast h.2
  rw [h1, h2]; ring

theorem cnt_nonneg (z : ℝ × ℝ) : 0 ≤ cnt V vR wR z :=
  Finset.sum_nonneg fun _ _ => finsum_nonneg fun _ => by split_ifs <;> norm_num

/-- **The count of triangles is 12 almost everywhere.** -/
theorem cnt_ae_twelve : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), cnt V vR wR z = 12 := by
  obtain ⟨c, hc⟩ := cnt_ae_const V_ccw det_ne V_paired
  obtain ⟨z₀, hz₀⟩ := hc.exists
  have hc0 : 0 ≤ c := hz₀ ▸ cnt_nonneg z₀
  have hc' : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), cnt V vR wR z = (c.toNat : ℕ) :=
    hc.mono fun z hz => by rw [hz]; exact (Int.toNat_of_nonneg hc0).symm
  have key := count_mul_det V_ccw det_ne c.toNat hc'
  rw [sum_orient, det_eq, abs_of_pos (by positivity)] at key
  have h3 : (0 : ℝ) < 1 + Real.sqrt 3 := by positivity
  have : (c.toNat : ℝ) = 12 := by
    have := mul_right_cancel₀ h3.ne' (show (c.toNat : ℝ) * (27 / 2) * (1 + Real.sqrt 3) =
      12 * (27 / 2) * (1 + Real.sqrt 3) by linarith)
    linarith
  have : c.toNat = 12 := by exact_mod_cast this
  exact hc.mono fun z hz => by rw [hz]; omega

/-! ### From triangles to tiles -/

/-- Rotation by `30°`. -/
noncomputable def rho (z : ℝ × ℝ) : ℝ × ℝ :=
  (Real.sqrt 3 / 2 * z.1 - z.2 / 2, z.1 / 2 + Real.sqrt 3 / 2 * z.2)

theorem sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem phys_rotZ (a : Zz) : phys (rotZ a) = rho (phys a) := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  ext <;> simp only [phys, rotZ, rho] <;> push_cast <;> ring_nf <;> rw [h3] <;> ring

theorem phys_rotN (n : ℕ) (a : Zz) : phys (rotN n a) = rho^[n] (phys a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rotN, phys_rotZ, ih, Function.iterate_succ_apply']

theorem orient_rho (a b c : ℝ × ℝ) : orient (rho a) (rho b) (rho c) = orient a b c := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  unfold orient rho; ring_nf; rw [h3]; ring

theorem rho_surjective : Function.Surjective rho := fun z =>
  ⟨(Real.sqrt 3 / 2 * z.1 + z.2 / 2, -z.1 / 2 + Real.sqrt 3 / 2 * z.2), by
    have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    ext <;> simp only [rho] <;> ring_nf <;> rw [h3] <;> ring⟩

/-- A surjective map preserving orientation maps closed triangles onto closed triangles. -/
theorem image_closedTri {f : ℝ × ℝ → ℝ × ℝ} (hf : Function.Surjective f)
    (ho : ∀ a b c, orient (f a) (f b) (f c) = orient a b c) (A B C : ℝ × ℝ) :
    f '' closedTri A B C = closedTri (f A) (f B) (f C) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩; simpa [closedTri, ho] using hu
  · intro hz
    obtain ⟨u, rfl⟩ := hf z
    exact ⟨u, by simpa [closedTri, ho] using hz, rfl⟩

/-- The Spectre `Tile(1,1)`, as the union of its 12 triangles. -/
noncomputable def spectre : Set (ℝ × ℝ) :=
  ⋃ t : Fin 12, closedTri (phys (verts (tris t 0))) (phys (verts (tris t 1)))
    (phys (verts (tris t 2)))

/-- The rigid motion `z ↦ ρ^r z + x a + y b + λ` of placement `p = (j, λ)`. -/
noncomputable def motion (p : Fin 54 × (ℤ × ℤ)) (z : ℝ × ℝ) : ℝ × ℝ :=
  rho^[(placements p.1).1] z + (phys (offset p.1) + lat vR wR p.2)

/-- The tile of placement `j` translated by the lattice point `λ`. -/
noncomputable def tile (p : Fin 54 × (ℤ × ℤ)) : Set (ℝ × ℝ) := motion p '' spectre

theorem tile_eq (p : Fin 54 × (ℤ × ℤ)) : tile p = ⋃ t : Fin 12, tri V vR wR (p.1, t) p.2 := by
  have hs : Function.Surjective (motion p) := by
    intro z
    obtain ⟨u, hu⟩ := (rho_surjective.iterate (placements p.1).1) (z - (phys (offset p.1) +
      lat vR wR p.2))
    exact ⟨u, by simp [motion, hu]⟩
  have ho : ∀ a b c, orient (motion p a) (motion p b) (motion p c) = orient a b c := by
    intro a b c
    simp only [motion, orient_add]
    induction (placements p.1).1 with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', orient_rho, ih]
  rw [tile, spectre, Set.image_iUnion]
  refine Set.iUnion_congr fun t => ?_
  rw [image_closedTri hs ho]
  have hv : ∀ k, motion p (phys (verts (tris t k))) = V (p.1, t) k + lat vR wR p.2 := by
    intro k
    simp only [motion, V, vertZ, phys_add, phys_rotN, add_assoc]
  simp only [tri, hv]

/-! ### The triangles of one tile do not overlap -/

/-- A decidable test for `P + Q√3 ≤ 0`. -/
def nonposZ (x : ℤ × ℤ) : Bool := posZ (-x.1, -x.2) || (x.1 == 0 && x.2 == 0)

theorem nonposZ_spec {x : ℤ × ℤ} (h : nonposZ x = true) : (x.1 : ℝ) + x.2 * Real.sqrt 3 ≤ 0 := by
  simp only [nonposZ, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · have := posZ_spec h; push_cast at this; linarith
  · simp [h1, h2]

/-- Some edge line of one triangle has the other triangle weakly on its right. -/
def sepZ (T T' : Fin 3 → Zz) : Bool :=
  (List.finRange 3).any fun k => (List.finRange 3).all fun k' =>
    nonposZ (orientZ (T k) (T (k + 1)) (T' k'))

/-- Any two triangles of one tile are separated by an edge line of one of them. -/
theorem tiles_separated : ∀ j : Fin 54, ∀ t t' : Fin 12, t ≠ t' →
    (sepZ (vertZ j t) (vertZ j t') || sepZ (vertZ j t') (vertZ j t)) = true := by
  decide +kernel

/-- An affine function nonpositive at the vertices is nonpositive on the triangle. -/
theorem orient_nonpos_on {P Q A B C z : ℝ × ℝ} (hD : 0 < orient A B C)
    (hA : orient P Q A ≤ 0) (hB : orient P Q B ≤ 0) (hC : orient P Q C ≤ 0)
    (hz : z ∈ closedTri A B C) : orient P Q z ≤ 0 := by
  obtain ⟨h1, h2, h3⟩ := hz
  have e : orient A B C * orient P Q z =
      orient B C z * orient P Q A + orient C A z * orient P Q B + orient A B z * orient P Q C := by
    unfold orient; ring
  have : orient A B C * orient P Q z ≤ 0 := by
    rw [e]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h2 hA, mul_nonpos_of_nonneg_of_nonpos h3 hB,
      mul_nonpos_of_nonneg_of_nonpos h1 hC]
  exact nonpos_of_mul_nonpos_right (by linarith) hD |> fun h => by nlinarith

/-- A point of a closed triangle on the line of the edge `AB` lies on that edge. -/
theorem mem_segment_of_tri {A B C z : ℝ × ℝ} (hD : 0 < orient A B C) (hz : z ∈ closedTri A B C)
    (h0 : orient A B z = 0) : z ∈ segment ℝ A B := by
  obtain ⟨-, h2, h3⟩ := hz
  have k1 := bary_shift A B C z
  have k2 := bary_shift_snd A B C z
  have hs := bary_sum A B C z
  rw [h0] at k1 k2 hs
  set s := orient C A z / orient A B C
  refine ⟨1 - s, s, ?_, div_nonneg h3 hD.le, by ring, ?_⟩
  · rw [sub_nonneg, div_le_one hD]; linarith
  · ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, s]; field_simp; linear_combination -k1
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, s]; field_simp; linear_combination -k2

theorem tri_edge_nonneg {A B C z : ℝ × ℝ} (hz : z ∈ closedTri A B C) (k : Fin 3) :
    0 ≤ orient (![A, B, C] k) (![A, B, C] (k + 1)) z := by
  obtain ⟨h1, h2, h3⟩ := hz
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · exact h1
  · exact h2
  · exact h3

theorem tri_edge_segment {A B C z : ℝ × ℝ} (hD : 0 < orient A B C) (hz : z ∈ closedTri A B C)
    (k : Fin 3) (h0 : orient (![A, B, C] k) (![A, B, C] (k + 1)) z = 0) :
    z ∈ segment ℝ (![A, B, C] k) (![A, B, C] (k + 1)) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · exact mem_segment_of_tri hD hz h0
  · exact mem_segment_of_tri (by rwa [orient_cycle]) (mem_closedTri_cycle.mpr hz) h0
  · exact mem_segment_of_tri (by rwa [orient_cycle, orient_cycle])
      (mem_closedTri_cycle.mpr (mem_closedTri_cycle.mpr hz)) h0

theorem vtx (i : Fin 54 × Fin 12) (m : ℤ × ℤ) (k : Fin 3) :
    ![V i 0 + lat vR wR m, V i 1 + lat vR wR m, V i 2 + lat vR wR m] k = V i k + lat vR wR m := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  all_goals rfl

theorem no_overlap_of_sep {z : ℝ × ℝ} (hg : z ∈ Good V vR wR) {j : Fin 54} {t t' : Fin 12}
    {m : ℤ × ℤ} (hsep : sepZ (vertZ j t) (vertZ j t') = true)
    (h1 : z ∈ tri V vR wR (j, t) m) (h2 : z ∈ tri V vR wR (j, t') m) : False := by
  simp only [sepZ, List.any_eq_true, List.all_eq_true, List.mem_finRange, true_and,
    forall_const] at hsep
  obtain ⟨k, hk⟩ := hsep
  set l := lat vR wR m
  have hv : ∀ k', orient (V (j, t) k + l) (V (j, t) (k + 1) + l) (V (j, t') k' + l) ≤ 0 := by
    intro k'
    rw [orient_add]
    simp only [V, orient_phys]
    have := nonposZ_spec (hk k'); linarith
  have hD' : 0 < orient (V (j, t') 0 + l) (V (j, t') 1 + l) (V (j, t') 2 + l) := by
    rw [orient_add]; exact V_ccw _
  have le := orient_nonpos_on hD' (hv 0) (hv 1) (hv 2) h2
  have ge := tri_edge_nonneg h1 k
  rw [vtx, vtx] at ge
  have hD : 0 < orient (V (j, t) 0 + l) (V (j, t) 1 + l) (V (j, t) 2 + l) := by
    rw [orient_add]; exact V_ccw _
  have h0 : orient (![V (j, t) 0 + l, V (j, t) 1 + l, V (j, t) 2 + l] k)
      (![V (j, t) 0 + l, V (j, t) 1 + l, V (j, t) 2 + l] (k + 1)) z = 0 := by
    rw [vtx, vtx]; linarith
  have hs := tri_edge_segment hD h1 k h0
  rw [vtx, vtx] at hs
  exact hg.2.2 (j, t) k m hs

theorem unique_tri {z : ℝ × ℝ} (hg : z ∈ Good V vR wR) {j : Fin 54} {t t' : Fin 12}
    {m : ℤ × ℤ} (h1 : z ∈ tri V vR wR (j, t) m) (h2 : z ∈ tri V vR wR (j, t') m) : t = t' := by
  by_contra hne
  rcases Bool.or_eq_true _ _ |>.mp (tiles_separated j t t' hne) with h | h
  · exact no_overlap_of_sep hg h h1 h2
  · exact no_overlap_of_sep hg h h2 h1

/-! ### The theorem -/

/-- **A periodic 12-fold cover by Spectres.** Almost every point of the plane lies in exactly 12
of the tiles `ρ^r S + x a + y b + λ`. -/
theorem spectre_twelve_fold :
    ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), {p : Fin 54 × (ℤ × ℤ) | z ∈ tile p}.ncard = 12 := by
  filter_upwards [cnt_ae_twelve, good_ae (V := V) (v := vR) (w := wR)] with z hz hg
  set A := {q : (Fin 54 × Fin 12) × (ℤ × ℤ) | z ∈ tri V vR wR q.1 q.2}
  have himg : {p : Fin 54 × (ℤ × ℤ) | z ∈ tile p} = (fun q => (q.1.1, q.2)) '' A := by
    ext ⟨j, m⟩
    constructor
    · intro h
      rw [Set.mem_setOf_eq, tile_eq, Set.mem_iUnion] at h
      obtain ⟨t, ht⟩ := h
      exact ⟨((j, t), m), ht, rfl⟩
    · rintro ⟨⟨⟨j', t⟩, m'⟩, ht, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      show z ∈ tile (j', m')
      rw [tile_eq, Set.mem_iUnion]
      exact ⟨t, ht⟩
  have hinj : Set.InjOn (fun q : (Fin 54 × Fin 12) × (ℤ × ℤ) => (q.1.1, q.2)) A := by
    rintro ⟨⟨j, t⟩, m⟩ h ⟨⟨j', t'⟩, m'⟩ h' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [unique_tri hg h h']
  rw [himg, hinj.ncard_image]
  have hfin : ∀ i, {m | z ∈ tri V vR wR i m}.Finite := fun i => by
    refine (tri_finite V_ccw det_ne i z).subset fun m hm => ?_
    simp only [Set.mem_setOf_eq] at hm
    simp [hm]
  have hA : A.ncard = ∑ i, {m | z ∈ tri V vR wR i m}.ncard := by
    rw [← Nat.card_coe_set_eq]
    have hcard : Nat.card A = Nat.card (Σ i, {m // z ∈ tri V vR wR i m}) :=
      Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun i m => z ∈ tri V vR wR i m)
    have : ∀ i, Finite {m // z ∈ tri V vR wR i m} := fun i => (hfin i).to_subtype
    rw [hcard, Nat.card_sigma]
    rfl
  have hc : cnt V vR wR z = ((∑ i, {m | z ∈ tri V vR wR i m}.ncard : ℕ) : ℤ) := by
    unfold cnt; push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finsum_ite_tri (hfin i), Set.ncard_eq_toFinset_card _ (hfin i)]
  rw [hA]
  have := hc.symm.trans hz
  exact_mod_cast this

end SpectreCover
