import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic
import LeanProofs.AcuteTetra.Comb

/-!
# Acute tetrahedron: Gram-matrix bookkeeping

Every quantity in the proof is a quadratic expression in the six dot products `⟪A i, A j⟫` of
four unit vectors. We record such an expression as an integer matrix `M` and write
`gram x M = ∑ i j, M i j * x i j`. Two matrices give the same value for every Gram matrix of unit
vectors as soon as their symmetrised off-diagonal parts and their traces agree (`gramEq`); that
check is a finite computation, so all the vector identities of the proof are verified by `decide`.
-/

namespace AcuteTetra

open Finset

/-- `sgZ true = 1`, `sgZ false = -1`. -/
def sgZ (b : Bool) : ℤ := if b then 1 else -1

/-- Coefficients of the signed sum `A f₀ + s(b₁) A f₁ + s(b₂) A f₂` for the edge `(l, b₁, b₂)`. -/
def cE (e : Edge) (i : Fin 4) : ℤ :=
  if i = face e.1 0 then 1 else if i = face e.1 1 then sgZ e.2.1
  else if i = face e.1 2 then sgZ e.2.2 else 0

/-- Coefficients of `Σ σ_i A_i`. -/
def cS (σ : Sign) (i : Fin 4) : ℤ := sgZ (σ i)

def outer (c d : Fin 4 → ℤ) (i j : Fin 4) : ℤ := c i * d j

/-- The matrix whose Gram value is `x 0 0 = 1`. -/
def unitM (i j : Fin 4) : ℤ := if i = 0 ∧ j = 0 then 1 else 0

def fins : List (Fin 4) := List.finRange 4

/-- Same symmetrised off-diagonal part and same trace. -/
def gramEq (M N : Fin 4 → Fin 4 → ℤ) : Bool :=
  (fins.all fun i => fins.all fun j => i == j || M i j + M j i == N i j + N j i) &&
    (fins.map fun i => M i i).sum == (fins.map fun i => N i i).sum

def gram (x : Fin 4 → Fin 4 → ℝ) (M : Fin 4 → Fin 4 → ℤ) : ℝ := ∑ i, ∑ j, (M i j : ℝ) * x i j

lemma gram_canon (x : Fin 4 → Fin 4 → ℝ) (hs : ∀ i j, x i j = x j i) (hd : ∀ i, x i i = 1)
    (M : Fin 4 → Fin 4 → ℤ) :
    gram x M = (M 0 0 + M 1 1 + M 2 2 + M 3 3 : ℝ)
      + (M 0 1 + M 1 0 : ℝ) * x 0 1 + (M 0 2 + M 2 0 : ℝ) * x 0 2 + (M 0 3 + M 3 0 : ℝ) * x 0 3
      + (M 1 2 + M 2 1 : ℝ) * x 1 2 + (M 1 3 + M 3 1 : ℝ) * x 1 3 + (M 2 3 + M 3 2 : ℝ) * x 2 3 := by
  simp only [gram, Fin.sum_univ_four, hd]
  rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2]
  ring

lemma gram_congr (x : Fin 4 → Fin 4 → ℝ) (hs : ∀ i j, x i j = x j i) (hd : ∀ i, x i i = 1)
    {M N : Fin 4 → Fin 4 → ℤ} (h : gramEq M N = true) : gram x M = gram x N := by
  simp [gramEq, fins, List.finRange_succ] at h
  obtain ⟨⟨⟨h01, h02, h03⟩, ⟨h10, h12, h13⟩, ⟨h20, h21, h23⟩, ⟨h30, h31, h32⟩⟩, htr⟩ := h
  rw [gram_canon x hs hd M, gram_canon x hs hd N]
  have c01 : (M 0 1 + M 1 0 : ℝ) = N 0 1 + N 1 0 := by exact_mod_cast h01
  have c02 : (M 0 2 + M 2 0 : ℝ) = N 0 2 + N 2 0 := by exact_mod_cast h02
  have c03 : (M 0 3 + M 3 0 : ℝ) = N 0 3 + N 3 0 := by exact_mod_cast h03
  have c12 : (M 1 2 + M 2 1 : ℝ) = N 1 2 + N 2 1 := by exact_mod_cast h12
  have c13 : (M 1 3 + M 3 1 : ℝ) = N 1 3 + N 3 1 := by exact_mod_cast h13
  have c23 : (M 2 3 + M 3 2 : ℝ) = N 2 3 + N 3 2 := by exact_mod_cast h23
  have ctr : (M 0 0 + M 1 1 + M 2 2 + M 3 3 : ℝ) = N 0 0 + N 1 1 + N 2 2 + N 3 3 := by
    exact_mod_cast (by linarith : M 0 0 + M 1 1 + M 2 2 + M 3 3 = N 0 0 + N 1 1 + N 2 2 + N 3 3)
  rw [c01, c02, c03, c12, c13, c23, ctr]

lemma gram_add (x) (M N : Fin 4 → Fin 4 → ℤ) : gram x (M + N) = gram x M + gram x N := by
  simp [gram, add_mul, Finset.sum_add_distrib]

lemma gram_smul (x) (k : ℤ) (M : Fin 4 → Fin 4 → ℤ) : gram x (k • M) = k * gram x M := by
  simp [gram, Finset.mul_sum, mul_assoc]

end AcuteTetra
