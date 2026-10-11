import LeanProofs.AcuteTetra.Gram

/-!
# Acute tetrahedron: the finite facts, checked by `decide`

Each statement below is an identity between integer coefficient matrices (or a choice of edges),
quantified over the finitely many signs, edges, faces and corners. Combined with `gram_congr`, each
becomes an identity between dot-product expressions valid for every four unit vectors.
-/

namespace AcuteTetra

/-- Coefficients of the corner `σ_i A_i`. -/
def pc (σ : Sign) (i : Fin 4) (t : Fin 4) : ℤ := if t = i then sgZ (σ i) else 0

/-- The two sides at corner `face l k` of the face opposite `l` in the variant `σ`. -/
def sideU (σ : Sign) (l : Fin 4) (k : Fin 3) (t : Fin 4) : ℤ :=
  pc σ (face l (k + 1)) t - pc σ (face l k) t
def sideV (σ : Sign) (l : Fin 4) (k : Fin 3) (t : Fin 4) : ℤ :=
  pc σ (face l (k + 2)) t - pc σ (face l k) t

/-- Coefficients of `Σ_{i ≠ m} ε_i A_i`. -/
def cDrop (ε : Sign) (m : Fin 4) (t : Fin 4) : ℤ := if t = m then 0 else sgZ (ε t)

def adj (g e : Edge) : Bool := allSigns.any fun σ => inc g σ && inc e σ

theorem incP_inc : ∀ σ : Sign, ∀ l : Fin 4, inc (l, incP σ l) σ = true := by decide

theorem not_disjoint_self : ∀ e : Edge, disjointE e e = false := by decide

theorem inc_unique : ∀ σ : Sign, ∀ e : Edge, inc e σ = true → e.2 = incP σ e.1 := by decide

/-- Two different sums on one face differ, or add up, to twice a signed unit coordinate. -/
theorem face_pair : ∀ l : Fin 4, ∀ p p' : Bool × Bool, p ≠ p' → ∃ k : Fin 4, ∃ s : Bool,
    (∀ t, cE (l, p) t - cE (l, p') t = 2 * pc (fun _ => s) k t) ∨
    (∀ t, cE (l, p) t + cE (l, p') t = 2 * pc (fun _ => s) k t) := by decide

/-- The four edges at a vertex: `Σ ‖S - A_l‖² = 4 + 2‖S‖²`. -/
theorem star_identity : ∀ σ : Sign,
    gramEq (outer (cE (0, incP σ 0)) (cE (0, incP σ 0)) + outer (cE (1, incP σ 1)) (cE (1, incP σ 1))
      + outer (cE (2, incP σ 2)) (cE (2, incP σ 2)) + outer (cE (3, incP σ 3)) (cE (3, incP σ 3)))
      ((2 : ℤ) • outer (cS σ) (cS σ) + (4 : ℤ) • unitM) = true := by decide

/-- Two disjoint edges on different faces have two joining edges whose squared lengths add up to
theirs. -/
theorem joiners : ∀ e f : Edge, e.1 ≠ f.1 → disjointE e f = true → ∃ g h : Edge,
    adj g e = true ∧ adj g f = true ∧ adj h e = true ∧ adj h f = true ∧
    gramEq (outer (cE g) (cE g) + outer (cE h) (cE h)) (outer (cE e) (cE e) + outer (cE f) (cE f))
      = true := by decide

/-- Every angle of every variant is `(‖sum‖² - 1)/2` for a sum not incident to that variant. -/
theorem angle_edge : ∀ σ : Sign, ∀ l : Fin 4, ∀ k : Fin 3, ∃ p : Bool × Bool,
    inc (l, p) σ = false ∧
    gramEq (outer (cE (l, p)) (cE (l, p))) ((2 : ℤ) • outer (sideU σ l k) (sideV σ l k) + unitM)
      = true := by decide

/-- ... and every sum not incident to `σ` is one of those angles. -/
theorem edge_angle : ∀ σ : Sign, ∀ e : Edge, inc e σ = false → ∃ k : Fin 3,
    gramEq (outer (cE e) (cE e)) ((2 : ℤ) • outer (sideU σ e.1 k) (sideV σ e.1 k) + unitM)
      = true := by decide

/-- Dropping one term of a signed four-term sum gives (up to sign) an edge sum. -/
theorem drop_edge : ∀ ε : Sign, ∀ m : Fin 4, ∃ e : Edge,
    gramEq (outer (cE e) (cE e)) (outer (cDrop ε m) (cDrop ε m)) = true := by decide

end AcuteTetra
