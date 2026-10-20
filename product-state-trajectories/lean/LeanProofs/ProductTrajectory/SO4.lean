import Mathlib

/-!
# Product trajectories (Physics SE 816017), part 8: the quaternion structure on `2 × 2` matrices

* `ip X Y = ∑ conj(X_ij) Y_ij` (Frobenius inner product).
* `tau X = !![conj X₁₁, -conj X₁₀; -conj X₀₁, conj X₀₀]`: antiunitary involution whose fixed points
  are the
  real multiples of `SU(2)` (the quaternions).
* `tau_fixed`: if `X Xᴴ = r • 1` and `det X = r` (`r ≠ 0`) then `tau X = X`.
* `E 0 = 1, E 1 = iZ, E 2 = iY, E 3 = iX`: an orthogonal basis (norm² 2) of `τ`-fixed matrices.
* `split`: if `T` is linear and its matrix `⟪E a, T (E b)⟫ = 2i ω a b` with `ω` real antisymmetric,
  then
  `T X = A X + X C` for explicit Hermitian `A, C` (this is `so(4) = su(2) ⊕ su(2)`).
-/

namespace ProductTrajectory.SO4

open Complex Matrix

abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Frobenius inner product. -/
def ip (X Y : M2) : ℂ := ∑ i, ∑ j, star (X i j) * Y i j

/-- The quaternion structure. -/
def tau (X : M2) : M2 := !![star (X 1 1), -star (X 1 0); -star (X 0 1), star (X 0 0)]

theorem tau_tau (X : M2) : tau (tau X) = X := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tau]

theorem tau_add (X Y : M2) : tau (X + Y) = tau X + tau Y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tau] <;> ring

theorem tau_smul (c : ℂ) (X : M2) : tau (c • X) = star c • tau X := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tau]

theorem ip_tau (X Y : M2) : ip (tau X) (tau Y) = star (ip X Y) := by
  simp only [ip, tau, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, star_neg, star_star, star_add, star_mul']
  ring

theorem ip_add_right (X Y Z : M2) : ip X (Y + Z) = ip X Y + ip X Z := by
  simp only [ip, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem ip_smul_right (X Y : M2) (c : ℂ) : ip X (c • Y) = c * ip X Y := by
  simp only [ip, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem ip_sum_right {ι : Type*} (s : Finset ι) (X : M2) (Y : ι → M2) :
    ip X (∑ k ∈ s, Y k) = ∑ k ∈ s, ip X (Y k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ip_add_right, ih]

/-- `X Xᴴ = r • 1` and `det X = r ≠ 0` force `tau X = X` (the adjugate equals the adjoint). -/
theorem tau_fixed (X : M2) (r : ℂ) (hr : r ≠ 0) (hXX : X * Xᴴ = r • 1) (hdet : X.det = r) :
    tau X = X := by
  have hadj : X.adjugate = Xᴴ := by
    have h1 : X.adjugate * X = r • 1 := by rw [adjugate_mul, hdet]
    calc X.adjugate = X.adjugate * (X * (r⁻¹ • Xᴴ)) := by
          rw [Matrix.mul_smul, hXX, smul_smul, inv_mul_cancel₀ hr, one_smul, Matrix.mul_one]
      _ = (X.adjugate * X) * (r⁻¹ • Xᴴ) := by rw [Matrix.mul_assoc]
      _ = Xᴴ := by rw [h1, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hr, one_smul]
  rw [adjugate_fin_two] at hadj
  have e00 := congrFun (congrFun hadj 0) 0
  have e01 := congrFun (congrFun hadj 0) 1
  have e10 := congrFun (congrFun hadj 1) 0
  have e11 := congrFun (congrFun hadj 1) 1
  simp [conjTranspose_apply] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tau]
  · rw [← e11]
  · rw [← e01, neg_neg]
  · rw [← e10, neg_neg]
  · rw [← e00]

/-- The basis `1, iZ, iY, iX`. -/
def E : Fin 4 → M2
  | 0 => 1
  | 1 => !![I, 0; 0, -I]
  | 2 => !![0, 1; -1, 0]
  | 3 => !![0, I; I, 0]

theorem tau_E (a : Fin 4) : tau (E a) = E a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [tau, E]

/-- Every matrix expands in the basis `E` with coefficients `⟪E a, Y⟫ / 2`. -/
theorem expand (Y : M2) : Y = ∑ a, (ip (E a) Y / 2) • E a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ip, E, Fin.sum_univ_four, Fin.sum_univ_two,
        one_apply] <;> ring_nf <;> simp [I_sq] <;> ring

def σx : M2 := !![0, 1; 1, 0]
def σy : M2 := !![0, -I; I, 0]
def σz : M2 := !![1, 0; 0, -1]

/-- The left generator. -/
noncomputable def Aof (ω : Fin 4 → Fin 4 → ℝ) : M2 :=
  (((ω 0 3 + ω 1 2) / 2 : ℝ) : ℂ) • σx + (((ω 0 2 - ω 1 3) / 2 : ℝ) : ℂ) • σy +
    (((ω 0 1 + ω 2 3) / 2 : ℝ) : ℂ) • σz

/-- The right generator. -/
noncomputable def Cof (ω : Fin 4 → Fin 4 → ℝ) : M2 :=
  (((ω 0 3 - ω 1 2) / 2 : ℝ) : ℂ) • σx + (((ω 0 2 + ω 1 3) / 2 : ℝ) : ℂ) • σy +
    (((ω 0 1 - ω 2 3) / 2 : ℝ) : ℂ) • σz

theorem Aof_herm (ω : Fin 4 → Fin 4 → ℝ) : (Aof ω).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Aof, σx, σy, σz, conjTranspose_apply]

theorem Cof_herm (ω : Fin 4 → Fin 4 → ℝ) : (Cof ω).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Cof, σx, σy, σz, conjTranspose_apply]

/-- **so(4) = su(2) ⊕ su(2)**, on the basis. -/
theorem split_basis (ω : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, ω a b = -ω b a) (b : Fin 4) :
    ∑ a, (I * (ω a b : ℂ)) • E a = Aof ω * E b + E b * Cof ω := by
  have h00 := hanti 0 0; have h11 := hanti 1 1; have h22 := hanti 2 2; have h33 := hanti 3 3
  have h10 := hanti 1 0; have h20 := hanti 2 0; have h30 := hanti 3 0
  have h21 := hanti 2 1; have h31 := hanti 3 1; have h32 := hanti 3 2
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E, Aof, Cof, σx, σy, σz, Fin.sum_univ_four, Complex.ext_iff] <;> constructor <;> linarith

end ProductTrajectory.SO4
