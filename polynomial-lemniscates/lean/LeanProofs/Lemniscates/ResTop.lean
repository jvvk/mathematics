import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The top coefficient of a resultant (Lemma 4(a), algebraic part)

If the columns of a square matrix over `K[X]` have degrees at most `d j`, its determinant has
degree at most `∑ d j`, and the coefficient there is the determinant of the matrix of
`d j`-th coefficients (`det_top`).

For the Sylvester matrix of `p, q : K[X][Y]` (sizes `m, n`) whose coefficients have `X`-degree at
most `d₁`, `d₂`, this gives: `Res_Y(p, q)` has `X`-degree at most `m d₂ + n d₁`, with top
coefficient `Res(pt, qt)`, where `pt, qt` collect the top coefficients (`resultant_top`).
-/

open Polynomial

namespace Lemniscates.ResTop

variable {K : Type*} [CommRing K]

lemma coeff_mul_top {p q : K[X]} {a b : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  rw [coeff_mul, Finset.sum_eq_single (a, b)]
  · rintro ⟨i, j⟩ hij hne
    have hij' : i + j = a + b := Finset.mem_antidiagonal.mp hij
    rcases lt_trichotomy i a with h | h | h
    · have hj : b < j := by omega
      rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt hj), mul_zero]
    · exact absurd (Prod.ext h (by omega)) hne
    · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt h), zero_mul]
  · simp

lemma prod_top {ι : Type*} (s : Finset ι) (f : ι → K[X]) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih₁, ih₂⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h₀ := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨natDegree_mul_le.trans (add_le_add h₀ ih₁), by rw [coeff_mul_top h₀ ih₁, ih₂]⟩

/-- **Column degrees.** -/
theorem det_top {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K[X]) (d : n → ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.natDegree ≤ ∑ j, d j ∧
      M.det.coeff (∑ j, d j) = (Matrix.of fun i j => (M i j).coeff (d j)).det := by
  rw [Matrix.det_apply, Matrix.det_apply]
  have hσ : ∀ σ : Equiv.Perm n, (∏ j, M (σ j) j).natDegree ≤ ∑ j, d j ∧
      (∏ j, M (σ j) j).coeff (∑ j, d j) = ∏ j, (M (σ j) j).coeff (d j) :=
    fun σ => prod_top _ _ _ fun j _ => h _ _
  refine ⟨natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_, ?_⟩
  · rw [Units.smul_def]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] <;>
      simp [(hσ σ).1]
  · rw [finsetSum_coeff]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, Units.smul_def]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] <;>
      simp [(hσ σ).2]

/-- **Top coefficient of a resultant.** -/
theorem resultant_top (p q : K[X][X]) (m n d₁ d₂ : ℕ) (pt qt : K[X])
    (hp : ∀ k, (p.coeff k).natDegree ≤ d₁) (hq : ∀ k, (q.coeff k).natDegree ≤ d₂)
    (hpt : ∀ k, (p.coeff k).coeff d₁ = pt.coeff k) (hqt : ∀ k, (q.coeff k).coeff d₂ = qt.coeff k) :
    (p.resultant q m n).natDegree ≤ m * d₂ + n * d₁ ∧
      (p.resultant q m n).coeff (m * d₂ + n * d₁) = pt.resultant qt m n := by
  let d : Fin (m + n) → ℕ := fun j => Fin.addCases (fun _ => d₂) (fun _ => d₁) j
  have hsum : ∑ j, d j = m * d₂ + n * d₁ := by
    rw [Fin.sum_univ_add]; simp [d]
  have hcol : ∀ i j, ((sylvester p q m n) i j).natDegree ≤ d j := by
    intro i j
    induction j using Fin.addCases with
    | left j => simp only [sylvester, Matrix.of_apply, Fin.addCases_left, d]; split_ifs <;> simp [hq]
    | right j => simp only [sylvester, Matrix.of_apply, Fin.addCases_right, d]; split_ifs <;> simp [hp]
  have htop : (Matrix.of fun i j => ((sylvester p q m n) i j).coeff (d j)) = sylvester pt qt m n := by
    ext i j
    induction j using Fin.addCases with
    | left j => simp only [sylvester, Matrix.of_apply, Fin.addCases_left, d]; split_ifs <;> simp [hqt]
    | right j => simp only [sylvester, Matrix.of_apply, Fin.addCases_right, d]; split_ifs <;> simp [hpt]
  obtain ⟨h₁, h₂⟩ := det_top _ d hcol
  rw [hsum, htop] at *
  exact ⟨h₁, h₂⟩

/-! ### The next-to-top coefficient -/

lemma coeff_mul_subtop {p q : K[X]} {a b : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (p * q).coeff (a + b - 1) = p.coeff (a - 1) * q.coeff b + p.coeff a * q.coeff (b - 1) := by
  rw [coeff_mul, Finset.sum_eq_add (a - 1, b) (a, b - 1)]
  · intro h; simp only [Prod.mk.injEq] at h; omega
  · rintro ⟨i, j⟩ hij ⟨h1, h2⟩
    have hij' : i + j = a + b - 1 := Finset.mem_antidiagonal.mp hij
    rcases lt_or_ge a i with h | h
    · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt h), zero_mul]
    rcases lt_or_ge b j with h' | h'
    · rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt h'), mul_zero]
    exfalso
    rcases Nat.eq_or_lt_of_le h with h3 | h3
    · exact h2 (Prod.ext (by simp only; omega) (by simp only; omega))
    · exact h1 (Prod.ext (by simp only; omega) (by simp only; omega))
  · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by omega)) h
  · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by omega)) h

lemma prod_subtop {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → K[X]) (d : ι → ℕ)
    (e : ι → K) (h : ∀ i ∈ s, (f i).natDegree ≤ d i) (hd : ∀ i ∈ s, 1 ≤ d i)
    (he : ∀ i ∈ s, (f i).coeff (d i - 1) = e i * (f i).coeff (d i)) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i - 1) = (∑ i ∈ s, e i) * ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp [he a (Finset.mem_singleton_self a)]
  | cons a s ha hs ih =>
    have hs' : ∀ i ∈ s, i ∈ Finset.cons a s ha := fun i hi => Finset.mem_cons_of_mem hi
    have ha' : a ∈ Finset.cons a s ha := Finset.mem_cons_self a s
    obtain ⟨htop₁, htop₂⟩ := prod_top s f d fun i hi => h i (hs' i hi)
    have ih' := ih (fun i hi => h i (hs' i hi)) (fun i hi => hd i (hs' i hi))
      (fun i hi => he i (hs' i hi))
    have hD : 1 ≤ ∑ i ∈ s, d i := by
      obtain ⟨j, hj⟩ := hs
      exact le_trans (hd j (hs' j hj)) (Finset.single_le_sum (fun i _ => Nat.zero_le _) hj)
    rw [Finset.prod_cons, Finset.sum_cons, Finset.sum_cons, Finset.prod_cons,
      coeff_mul_subtop (h a ha') htop₁ (hd a ha') hD, htop₂, ih', he a ha']
    ring

/-- **Next-to-top coefficient of a determinant**, when in every column the next-to-top
coefficients are a fixed multiple `e j` of the top ones. -/
theorem det_subtop {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (M : Matrix n n K[X])
    (d : n → ℕ) (e : n → K) (h : ∀ i j, (M i j).natDegree ≤ d j) (hd : ∀ j, 1 ≤ d j)
    (he : ∀ i j, (M i j).coeff (d j - 1) = e j * (M i j).coeff (d j)) :
    M.det.coeff (∑ j, d j - 1) = (∑ j, e j) * (Matrix.of fun i j => (M i j).coeff (d j)).det := by
  rw [Matrix.det_apply, Matrix.det_apply, finsetSum_coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have := prod_subtop Finset.univ Finset.univ_nonempty (fun j => M (σ j) j) d e
    (fun j _ => h _ _) (fun j _ => hd j) (fun j _ => he _ _)
  rw [Units.smul_def, Units.smul_def]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] <;>
    simp [this]

/-- **Next-to-top coefficient of a resultant.** -/
theorem resultant_subtop (p q : K[X][X]) (m n d₁ d₂ : ℕ) (pt qt : K[X]) (e₁ e₂ : K)
    (hmn : 1 ≤ m + n) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (hp : ∀ k, (p.coeff k).natDegree ≤ d₁) (hq : ∀ k, (q.coeff k).natDegree ≤ d₂)
    (hpt : ∀ k, (p.coeff k).coeff d₁ = pt.coeff k) (hqt : ∀ k, (q.coeff k).coeff d₂ = qt.coeff k)
    (he₁ : ∀ k, (p.coeff k).coeff (d₁ - 1) = e₁ * (p.coeff k).coeff d₁)
    (he₂ : ∀ k, (q.coeff k).coeff (d₂ - 1) = e₂ * (q.coeff k).coeff d₂) :
    (p.resultant q m n).coeff (m * d₂ + n * d₁ - 1) = (m * e₂ + n * e₁) * pt.resultant qt m n := by
  have : Nonempty (Fin (m + n)) := ⟨⟨0, by omega⟩⟩
  let d : Fin (m + n) → ℕ := fun j => Fin.addCases (fun _ => d₂) (fun _ => d₁) j
  let e : Fin (m + n) → K := fun j => Fin.addCases (fun _ => e₂) (fun _ => e₁) j
  have hsum : ∑ j, d j = m * d₂ + n * d₁ := by rw [Fin.sum_univ_add]; simp [d]
  have hesum : ∑ j, e j = m * e₂ + n * e₁ := by rw [Fin.sum_univ_add]; simp [e]
  have hcol : ∀ i j, ((sylvester p q m n) i j).natDegree ≤ d j := by
    intro i j
    induction j using Fin.addCases with
    | left j => simp only [sylvester, Matrix.of_apply, Fin.addCases_left, d]; split_ifs <;> simp [hq]
    | right j => simp only [sylvester, Matrix.of_apply, Fin.addCases_right, d]; split_ifs <;> simp [hp]
  have hdj : ∀ j, 1 ≤ d j := by
    intro j
    induction j using Fin.addCases with
    | left j => simp [d, hd₂]
    | right j => simp [d, hd₁]
  have hej : ∀ i j, ((sylvester p q m n) i j).coeff (d j - 1) =
      e j * ((sylvester p q m n) i j).coeff (d j) := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left, d, e]; split_ifs <;> simp [he₂]
    | right j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right, d, e]; split_ifs <;> simp [he₁]
  have htop : (Matrix.of fun i j => ((sylvester p q m n) i j).coeff (d j)) = sylvester pt qt m n := by
    ext i j
    induction j using Fin.addCases with
    | left j => simp only [sylvester, Matrix.of_apply, Fin.addCases_left, d]; split_ifs <;> simp [hqt]
    | right j => simp only [sylvester, Matrix.of_apply, Fin.addCases_right, d]; split_ifs <;> simp [hpt]
  have := det_subtop _ d e hcol hdj hej
  rw [hsum, hesum, htop] at this
  exact this

end Lemniscates.ResTop
