import Mathlib

/-!
# A broken stick and a Feynman diagram (MO 142983)

The algebra behind the identity
`p_n = C_n ∫ ∏ β_e^((n-2)/2) e^(-Σβ) / U(β)^((n+1)/2) dβ`, `C_n = 2^(N-n) π^(-N/2) Γ_n((n+1)/2)`,
for the probability `p_n` that `N = n(n+1)/2` pieces of a randomly broken stick are the edge lengths of an
`n`-simplex, for the triangle (`n = 2`, graph `K₃`) and the tetrahedron (`n = 3`, graph `K₄`).

Analytic inputs quoted in the note, not formalised here: exponential spacings (Devroye V.2.2), Schoenberg's
criterion, the Schwinger representation `e^(-ℓ)/ℓ = π^(-1/2) ∫ t^(-1/2) exp(-ℓ² t - 1/(4t)) dt`, and Siegel's
integral `∫_{G ≻ 0} exp(-tr(LG)) dG = Γ_n((n+1)/2) (det L)^(-(n+1)/2)`.

Edges of `K₄` on vertices `0,1,2,3` are written `01, 02, 03, 12, 13, 23`; vertex `0` is the origin, and the
Gram matrix `G` of the other three vertices has entries `g11, g22, g33, g12, g13, g23`.
-/

namespace BrokenStick

open Matrix Real

/-! ## The Gram matrix and the squared lengths (equation (2)) -/

/-- Squared lengths of `K₄` from the Gram matrix: `ℓ₀ᵢ² = gᵢᵢ`, `ℓᵢⱼ² = gᵢᵢ + gⱼⱼ - 2gᵢⱼ`. -/
def sqLengths (g11 g22 g33 g12 g13 g23 : ℝ) : Fin 6 → ℝ :=
  ![g11, g22, g33, g11 + g22 - 2 * g12, g11 + g33 - 2 * g13, g22 + g33 - 2 * g23]

/-- The linear map `G ↦ (ℓ_e²)` of equation (2) for `n = 3`, in the coordinates
`(g11, g22, g33, g12, g13, g23) ↦ (q01, q02, q03, q12, q13, q23)`. -/
def gramMap3 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     1, 1, 0, -2, 0, 0;
     1, 0, 1, 0, -2, 0;
     0, 1, 1, 0, 0, -2]

theorem gramMap3_apply (g11 g22 g33 g12 g13 g23 : ℝ) :
    gramMap3 *ᵥ ![g11, g22, g33, g12, g13, g23] = sqLengths g11 g22 g33 g12 g13 g23 := by
  ext i; fin_cases i <;> simp [gramMap3, sqLengths, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The change of variables `dq = 2^(n(n-1)/2) dG` for `n = 3`: the map has determinant `-8`. -/
theorem det_gramMap3 : gramMap3.det = -8 := by
  simp [gramMap3, det_succ_row_zero, Fin.sum_univ_succ]
  norm_num

/-- The same for `n = 2`: `(g11, g22, g12) ↦ (q01, q02, q12)` has determinant `-2`. -/
theorem det_gramMap2 : (!![1, 0, 0; 0, 1, 0; 1, 1, -2] : Matrix (Fin 3) (Fin 3) ℝ).det = -2 := by
  simp [det_fin_three]

/-- Bookkeeping of the change of variables: `N - n(n-1)/2 = n`, so `dℓ = 2^(-n) dG / ∏ ℓ_e`. -/
theorem edges_minus_offdiag (n : ℕ) : n * (n + 1) / 2 - n * (n - 1) / 2 = n := by
  rcases n with _ | n
  · simp
  · have h1 : (n + 1) * (n + 1 + 1) = (n + 1) * n + 2 * (n + 1) := by ring
    simp only [Nat.add_sub_cancel, h1]
    rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    omega

/-! ## The weighted Laplacian (equation (4)) -/

/-- Reduced weighted Laplacian of `K₄` (vertex `0` removed). -/
def lap3 (t01 t02 t03 t12 t13 t23 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![t01 + t12 + t13, -t12, -t13;
     -t12, t02 + t12 + t23, -t23;
     -t13, -t23, t03 + t13 + t23]

/-- Equation (4) for the tetrahedron: `Σ t_e ℓ_e² = tr(L_t G)`. -/
theorem trace_identity3 (t01 t02 t03 t12 t13 t23 g11 g22 g33 g12 g13 g23 : ℝ) :
    t01 * g11 + t02 * g22 + t03 * g33 + t12 * (g11 + g22 - 2 * g12) + t13 * (g11 + g33 - 2 * g13)
        + t23 * (g22 + g33 - 2 * g23)
      = trace (lap3 t01 t02 t03 t12 t13 t23 * !![g11, g12, g13; g12, g22, g23; g13, g23, g33]) := by
  simp [lap3, trace, Fin.sum_univ_three]
  ring

/-- Equation (4) for the triangle. -/
theorem trace_identity2 (t01 t02 t12 g11 g22 g12 : ℝ) :
    t01 * g11 + t02 * g22 + t12 * (g11 + g22 - 2 * g12)
      = trace (!![t01 + t12, -t12; -t12, t02 + t12] * !![g11, g12; g12, g22]) := by
  simp [trace, Fin.sum_univ_two]
  ring

/-! ## Spanning trees, the Kirchhoff polynomial `Ψ` and the Symanzik polynomial `U` -/

/-- The four triangles of `K₄`, as sets of edge indices (`01,02,03,12,13,23` ↦ `0,…,5`). -/
def triangles : Finset (Finset (Fin 6)) := {{0, 1, 3}, {0, 2, 4}, {1, 2, 5}, {3, 4, 5}}

/-- A set of three edges of `K₄` is a spanning tree exactly when it is not a triangle; there are `16`. -/
theorem card_spanning_trees :
    ((Finset.univ.powersetCard 3).filter (fun s : Finset (Fin 6) => s ∉ triangles)).card = 16 := by
  decide

/-- Kirchhoff polynomial of `K₄`: the sum over the 16 spanning trees of the product of their weights. -/
def kirchhoff3 (t01 t02 t03 t12 t13 t23 : ℝ) : ℝ :=
  -- the 20 three-edge sets ...
  (t01*t02*t03 + t01*t02*t12 + t01*t02*t13 + t01*t02*t23 + t01*t03*t12 + t01*t03*t13 + t01*t03*t23
    + t01*t12*t13 + t01*t12*t23 + t01*t13*t23 + t02*t03*t12 + t02*t03*t13 + t02*t03*t23 + t02*t12*t13
    + t02*t12*t23 + t02*t13*t23 + t03*t12*t13 + t03*t12*t23 + t03*t13*t23 + t12*t13*t23)
  -- ... minus the four triangles
  - (t01*t02*t12 + t01*t03*t13 + t02*t03*t23 + t12*t13*t23)

/-- First Symanzik polynomial of `K₄`: the sum over spanning trees of the product of the OMITTED weights.
The complement of a triangle is the star at the fourth vertex. -/
def symanzik3 (b01 b02 b03 b12 b13 b23 : ℝ) : ℝ :=
  (b01*b02*b03 + b01*b02*b12 + b01*b02*b13 + b01*b02*b23 + b01*b03*b12 + b01*b03*b13 + b01*b03*b23
    + b01*b12*b13 + b01*b12*b23 + b01*b13*b23 + b02*b03*b12 + b02*b03*b13 + b02*b03*b23 + b02*b12*b13
    + b02*b12*b23 + b02*b13*b23 + b03*b12*b13 + b03*b12*b23 + b03*b13*b23 + b12*b13*b23)
  - (b03*b13*b23 + b02*b12*b23 + b01*b12*b13 + b01*b02*b03)

/-- Matrix-tree theorem for `K₄`: `det L_t = Ψ(t)`. -/
theorem det_lap3 (t01 t02 t03 t12 t13 t23 : ℝ) :
    (lap3 t01 t02 t03 t12 t13 t23).det = kirchhoff3 t01 t02 t03 t12 t13 t23 := by
  simp [lap3, kirchhoff3, det_fin_three]
  ring

/-- Matrix-tree theorem for `K₃`: `det L_t = t01 t02 + t01 t12 + t02 t12`. -/
theorem det_lap2 (t01 t02 t12 : ℝ) :
    (!![t01 + t12, -t12; -t12, t02 + t12] : Matrix (Fin 2) (Fin 2) ℝ).det
      = t01 * t02 + t01 * t12 + t02 * t12 := by
  simp [det_fin_two]
  ring

/-- Equation (6) for `K₄`: `Ψ(t) = (∏ t) U(1/t)`. -/
theorem duality3 (t01 t02 t03 t12 t13 t23 : ℝ) (h01 : t01 ≠ 0) (h02 : t02 ≠ 0) (h03 : t03 ≠ 0)
    (h12 : t12 ≠ 0) (h13 : t13 ≠ 0) (h23 : t23 ≠ 0) :
    kirchhoff3 t01 t02 t03 t12 t13 t23
      = t01 * t02 * t03 * t12 * t13 * t23
        * symanzik3 t01⁻¹ t02⁻¹ t03⁻¹ t12⁻¹ t13⁻¹ t23⁻¹ := by
  simp only [kirchhoff3, symanzik3]
  field_simp
  ring

/-- Equation (6) for `K₃`: `Ψ(t) = (∏ t) U(1/t)` with `U(β) = β₁ + β₂ + β₃`. -/
theorem duality2 (t01 t02 t12 : ℝ) (h01 : t01 ≠ 0) (h02 : t02 ≠ 0) (h12 : t12 ≠ 0) :
    t01 * t02 + t01 * t12 + t02 * t12 = t01 * t02 * t12 * (t01⁻¹ + t02⁻¹ + t12⁻¹) := by
  field_simp
  ring

/-- The substitution `t_e = 1/(4β_e)` for `K₄`: `Ψ = 4^(-3) U(β) / ∏ β`. -/
theorem kirchhoff3_quarter_inv (b01 b02 b03 b12 b13 b23 : ℝ) (h01 : b01 ≠ 0) (h02 : b02 ≠ 0)
    (h03 : b03 ≠ 0) (h12 : b12 ≠ 0) (h13 : b13 ≠ 0) (h23 : b23 ≠ 0) :
    kirchhoff3 (1 / (4 * b01)) (1 / (4 * b02)) (1 / (4 * b03)) (1 / (4 * b12)) (1 / (4 * b13))
        (1 / (4 * b23))
      = symanzik3 b01 b02 b03 b12 b13 b23 / (4 ^ 3 * (b01 * b02 * b03 * b12 * b13 * b23)) := by
  simp only [kirchhoff3, symanzik3]
  field_simp
  ring

/-! ## The substitution `t = 1/(4β)` on one variable, and the collected powers -/

/-- `t^(-1/2) |dt/dβ| = (1/2) β^(-3/2)` at `t = 1/(4β)`: with `t^(-1/2) = 2√β` and `|dt/dβ| = 1/(4β²)`. -/
theorem schwinger_jacobian (β : ℝ) (hβ : 0 < β) :
    2 * sqrt β * (1 / (4 * β ^ 2)) = 1 / (2 * (β * sqrt β)) := by
  have hs : 0 < sqrt β := sqrt_pos.mpr hβ
  have hsq : sqrt β * sqrt β = β := mul_self_sqrt hβ.le
  field_simp
  nlinarith [hsq]

/-- `(1/(4β))^(-1/2) = 2√β`. -/
theorem inv_sqrt_quarter_inv (β : ℝ) (hβ : 0 < β) : (sqrt (1 / (4 * β)))⁻¹ = 2 * sqrt β := by
  rw [sqrt_div' 1 (by positivity : (0:ℝ) ≤ 4 * β), sqrt_mul (by norm_num : (0:ℝ) ≤ 4) β]
  have : sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  rw [this, sqrt_one]
  field_simp

/-- Collected powers of `β_e`: `(n+1)/2 - 3/2 = (n-2)/2`, and `4^N 2^(-N) = 2^N`. -/
theorem exponent_collect (n : ℝ) : (n + 1) / 2 - 3 / 2 = (n - 2) / 2 := by ring

theorem four_pow_half (N : ℕ) : (4 : ℝ) ^ N / 2 ^ N = 2 ^ N := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, pow_mul']
  field_simp

/-- Homogeneity: with `2N = n(n+1)`, the degree of `∏ β^((n-2)/2) U^(-(n+1)/2)` is `-N/2`
(`U` has degree `N - n`). This gives the factor `Γ(N/2)` of the simplex form (7). -/
theorem homogeneity_degree (n N : ℝ) (hN : 2 * N = n * (n + 1)) :
    N * ((n - 2) / 2) - (N - n) * ((n + 1) / 2) = -N / 2 := by
  linear_combination (-1 / 2 : ℝ) * hN

/-! ## The constants -/

theorem gamma_three_halves : Gamma (3 / 2) = sqrt π / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Gamma_add_one (by norm_num), Gamma_one_half_eq]
  ring

/-- `C₂ = 2^(3-2) π^(-3/2) Γ₂(3/2)` with `Γ₂(3/2) = π^(1/2) Γ(3/2) Γ(1)`. -/
noncomputable def C2 : ℝ := 2 / (π * sqrt π) * (sqrt π * Gamma (3 / 2) * Gamma 1)

/-- `C₃ = 2^(6-3) π^(-3) Γ₃(2)` with `Γ₃(2) = π^(3/2) Γ(2) Γ(3/2) Γ(1)`. -/
noncomputable def C3 : ℝ := 8 / π ^ 3 * (π * sqrt π * Gamma 2 * Gamma (3 / 2) * Gamma 1)

theorem C2_eq : C2 = 1 / sqrt π := by
  have hp : 0 < sqrt π := sqrt_pos.mpr pi_pos
  have hs : sqrt π * sqrt π = π := mul_self_sqrt pi_pos.le
  rw [C2, gamma_three_halves, Gamma_one]
  field_simp
  nlinarith [hs]

theorem C3_eq : C3 = 4 / π := by
  have hp : 0 < sqrt π := sqrt_pos.mpr pi_pos
  have hs : sqrt π * sqrt π = π := mul_self_sqrt pi_pos.le
  have hpi : π ≠ 0 := pi_ne_zero
  rw [C3, gamma_three_halves, Gamma_one, show (2 : ℝ) = 1 + 1 by norm_num, Gamma_add_one one_ne_zero,
    Gamma_one]
  field_simp
  nlinarith [hs, pi_pos]

/-- The Feynman normalisation for the tetrahedron: `C₃ Γ(3/2)^6 = π²/16`, so `p₃ = (π²/16) T`. -/
theorem C3_feynman : C3 * Gamma (3 / 2) ^ 6 = π ^ 2 / 16 := by
  have hs : sqrt π ^ 2 = π := sq_sqrt pi_pos.le
  rw [C3_eq, gamma_three_halves]
  have hpi : π ≠ 0 := pi_ne_zero
  have : sqrt π ^ 6 = π ^ 3 := by rw [show 6 = 2 * 3 by norm_num, pow_mul, hs]
  rw [div_pow, this]
  field_simp
  ring

/-- The triangle: in the simplex form (7) with `n = 2`, `U = 1` on the simplex, whose measure is `1/2!`,
so `p₂ = C₂ Γ(3/2) / 2 = 1/4`. -/
theorem p2_eq_quarter : C2 * Gamma (3 / 2) / 2 = 1 / 4 := by
  have hp : 0 < sqrt π := sqrt_pos.mpr pi_pos
  rw [C2_eq, gamma_three_halves]
  field_simp
  ring

/-- The triangle in Feynman form: `C₂ Γ(1)^3 T₂ = 1/4` with `T₂ = Γ(3/2)/Γ(3) = √π/4`. -/
theorem p2_feynman : C2 * Gamma 1 ^ 3 * (Gamma (3 / 2) / Gamma 3) = 1 / 4 := by
  have hp : 0 < sqrt π := sqrt_pos.mpr pi_pos
  have g3 : Gamma 3 = 2 := by
    rw [show (3 : ℝ) = 2 + 1 by norm_num, Gamma_add_one (by norm_num),
      show (2 : ℝ) = 1 + 1 by norm_num, Gamma_add_one one_ne_zero, Gamma_one]
    norm_num
  rw [C2_eq, gamma_three_halves, Gamma_one, g3]
  field_simp
  ring

end BrokenStick
