import LeanProofs.SpectreCover.Ae
import LeanProofs.SpectreCover.Data

/-!
# The concrete Spectre family satisfies the hypotheses (MO 516016)

`phys` embeds `ℤ[ζ]` in the plane. Orientations of `ℤ[ζ]` points are `(P + Q√3)/4` with integers
`P, Q` (`orient_phys`), so their signs are decided by integer comparisons (`posZ`). From the
kernel checks in `Data` this file derives, for the 648 triangles `V`:

* `V_ccw`: every triangle is counterclockwise;
* `det_ne`: the period vectors are independent;
* `V_paired`: the hypothesis `Paired` of the abstract theorem, from the sorted-key certificate.
-/

namespace SpectreCover

open Classical

/-- The point of the plane represented by `a₀ + a₁ζ + a₂ζ² + a₃ζ³`. -/
noncomputable def phys (a : Zz) : ℝ × ℝ :=
  ((a.1 : ℝ) + (a.2.2.1 : ℝ) / 2 + Real.sqrt 3 / 2 * a.2.1,
    (a.2.1 : ℝ) / 2 + Real.sqrt 3 / 2 * a.2.2.1 + a.2.2.2)

theorem phys_add (a b : Zz) : phys (a + b) = phys a + phys b := by
  ext <;> simp [phys] <;> ring

theorem phys_zsmul (n : ℤ) (a : Zz) : phys (n • a) = (n : ℝ) • phys a := by
  ext <;> simp [phys] <;> ring

theorem phys_zero : phys 0 = 0 := by ext <;> simp [phys]

/-- Twice the signed area in `ℤ[ζ]`, as `(P, Q)` with `orient = (P + Q√3)/4`. -/
def orientZ (p q r : Zz) : ℤ × ℤ :=
  let u := q - p
  let u' := r - p
  let X0 := 2 * u.1 + u.2.2.1
  let X1 := u.2.1
  let Y0 := u.2.1 + 2 * u.2.2.2
  let Y1 := u.2.2.1
  let X0' := 2 * u'.1 + u'.2.2.1
  let X1' := u'.2.1
  let Y0' := u'.2.1 + 2 * u'.2.2.2
  let Y1' := u'.2.2.1
  (X0 * Y0' + 3 * X1 * Y1' - Y0 * X0' - 3 * Y1 * X1', X0 * Y1' + X1 * Y0' - Y0 * X1' - Y1 * X0')

theorem orient_phys (p q r : Zz) :
    orient (phys p) (phys q) (phys r) =
      ((orientZ p q r).1 + (orientZ p q r).2 * Real.sqrt 3) / 4 := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  simp only [orient, phys, orientZ, Prod.fst_sub, Prod.snd_sub]
  push_cast
  linear_combination ((q.2.1 - p.2.1) * (r.2.2.1 - p.2.2.1) -
    (q.2.2.1 - p.2.2.1) * (r.2.1 - p.2.1) : ℝ) / 4 * hs

/-- A decidable test for `0 < P + Q√3`. -/
def posZ (x : ℤ × ℤ) : Bool :=
  (0 ≤ x.1 && 0 ≤ x.2 && (0 < x.1 || 0 < x.2)) || (0 < x.1 && x.2 < 0 && 3 * x.2 ^ 2 < x.1 ^ 2) ||
    (x.1 < 0 && 0 < x.2 && x.1 ^ 2 < 3 * x.2 ^ 2)

theorem posZ_spec {x : ℤ × ℤ} (h : posZ x = true) : 0 < (x.1 : ℝ) + x.2 * Real.sqrt 3 := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h0 : 0 < Real.sqrt 3 := by positivity
  simp only [posZ, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩
  · have : (0 : ℝ) < x.1 := by exact_mod_cast h3
    have : (0 : ℝ) ≤ x.2 := by exact_mod_cast h2
    positivity
  · have : (0 : ℝ) ≤ x.1 := by exact_mod_cast h1
    have : (0 : ℝ) < x.2 := by exact_mod_cast h3
    positivity
  · have a1 : (0 : ℝ) < x.1 := by exact_mod_cast h1
    have a2 : (x.2 : ℝ) < 0 := by exact_mod_cast h2
    have a3 : 3 * (x.2 : ℝ) ^ 2 < (x.1 : ℝ) ^ 2 := by exact_mod_cast h3
    have k : ((x.1 : ℝ) + x.2 * Real.sqrt 3) * (x.1 - x.2 * Real.sqrt 3) =
        (x.1 : ℝ) ^ 2 - 3 * (x.2 : ℝ) ^ 2 := by linear_combination -(x.2 : ℝ) ^ 2 * hs
    have hb : (0 : ℝ) < x.1 - x.2 * Real.sqrt 3 := by nlinarith
    exact (pos_iff_pos_of_mul_pos (by rw [k]; linarith)).mpr hb
  · have a1 : (x.1 : ℝ) < 0 := by exact_mod_cast h1
    have a2 : (0 : ℝ) < x.2 := by exact_mod_cast h2
    have a3 : (x.1 : ℝ) ^ 2 < 3 * (x.2 : ℝ) ^ 2 := by exact_mod_cast h3
    have k : ((x.1 : ℝ) + x.2 * Real.sqrt 3) * (x.2 * Real.sqrt 3 - x.1) =
        3 * (x.2 : ℝ) ^ 2 - (x.1 : ℝ) ^ 2 := by linear_combination (x.2 : ℝ) ^ 2 * hs
    have hb : (0 : ℝ) < x.2 * Real.sqrt 3 - x.1 := by nlinarith
    exact (pos_iff_pos_of_mul_pos (by rw [k]; linarith)).mpr hb

theorem orient_pos_of {p q r : Zz} (h : posZ (orientZ p q r) = true) :
    0 < orient (phys p) (phys q) (phys r) := by
  rw [orient_phys]; have := posZ_spec h; linarith

/-! ### The concrete family -/

/-- The 648 triangles: triangle `t` of placement `j`. -/
noncomputable def V (i : Fin 54 × Fin 12) (k : Fin 3) : ℝ × ℝ := phys (vertZ i.1 i.2 k)

noncomputable def vR : ℝ × ℝ := phys vZ
noncomputable def wR : ℝ × ℝ := phys wZ

theorem all_ccw : ∀ j : Fin 54, ∀ t : Fin 12,
    posZ (orientZ (vertZ j t 0) (vertZ j t 1) (vertZ j t 2)) = true := by decide +kernel

theorem V_ccw (i : Fin 54 × Fin 12) : 0 < orient (V i 0) (V i 1) (V i 2) :=
  orient_pos_of (all_ccw i.1 i.2)

theorem det_eq : vR.1 * wR.2 - vR.2 * wR.1 = 27 / 2 * (1 + Real.sqrt 3) := by
  have h := orient_phys 0 vZ wZ
  simp only [phys_zero, orient, Prod.fst_zero, Prod.snd_zero, sub_zero] at h
  rw [show (orientZ 0 vZ wZ) = (54, 54) by decide] at h
  simp only [vR, wR, h]; push_cast; ring

theorem det_ne : vR.1 * wR.2 - vR.2 * wR.1 ≠ 0 := by
  rw [det_eq]; positivity

theorem lat_phys (m : ℤ × ℤ) : lat vR wR m = phys (m.1 • vZ + m.2 • wZ) := by
  rw [phys_add, phys_zsmul, phys_zsmul]; rfl

/-- Every `P` splits as `base (K P)` plus a lattice vector. -/
def baseZ (κ : ℤ × ℤ) : Zz := κ.1 • aZ + κ.2 • bZ

def coordL (a : Zz) : ℤ × ℤ := (a.1 + 2 * a.2.2.1 - 2 * a.2.2.2, -a.2.1 - a.2.2.1 + a.2.2.2)

theorem decomp (a : Zz) : a = baseZ (kZ a) + ((coordL a).1 • vZ + (coordL a).2 • wZ) := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  simp only [baseZ, kZ, coordL, aZ, bZ, vZ, wZ, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
    Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem sum_edges (f : Fin 54 × Fin 12 × Fin 3 → ℤ) :
    ∑ i : Fin 54 × Fin 12, ∑ k : Fin 3, f (i.1, i.2, k) = (edges.map f).sum := by
  rw [Fintype.sum_prod_type]
  simp [edges, Fin.sum_univ_def, List.flatMap_def, List.sum_flatten, List.map_map,
    Function.comp_def]

theorem V_paired : Paired V vR wR := by
  intro H hH
  set Ht : (ℤ × ℤ) × Zz → ℤ := fun κd => H (phys (baseZ κd.1)) (phys (baseZ κd.1 + κd.2))
  have reduce : ∀ P Q : Zz, H (phys P) (phys Q) = Ht (kZ P, Q - P) := by
    intro P Q
    have hP := decomp P
    set B := baseZ (kZ P) with hB
    set L := (coordL P).1 • vZ + (coordL P).2 • wZ with hL
    have hQ : Q = B + (Q - P) + L := by
      calc Q = (Q - P) + P := by abel
        _ = (Q - P) + (B + L) := by rw [← hP]
        _ = B + (Q - P) + L := by abel
    have e1 : phys P = phys B + lat vR wR (coordL P) := by rw [lat_phys, ← phys_add, ← hL, ← hP]
    have e2 : phys Q = phys (B + (Q - P)) + lat vR wR (coordL P) := by
      rw [lat_phys, ← phys_add, ← hL, ← hQ]
    rw [e1, e2, hH]
  have l : ∀ i : Fin 54 × Fin 12, ∀ k : Fin 3, H (V i k) (V i (k + 1)) = Ht (key (i.1, i.2, k)) :=
    fun i k => reduce _ _
  have r : ∀ i : Fin 54 × Fin 12, ∀ k : Fin 3, H (V i (k + 1)) (V i k) = Ht (rkey (i.1, i.2, k)) :=
    fun i k => reduce _ _
  simp only [l, r]
  rw [sum_edges (fun e => Ht (key e)), sum_edges (fun e => Ht (rkey e))]
  simpa only [List.map_map, Function.comp_def] using (keys_perm.map Ht).sum_eq

end SpectreCover
