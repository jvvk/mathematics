import Mathlib

/-!
# The Spectre and the 54 placements, exactly (MO 516016)

Points of `ℤ[ζ]`, `ζ = e^{πi/6}`, are integer 4-tuples in the basis `1, ζ, ζ², ζ³`, with
`ζ⁴ = ζ² - 1`. The Spectre `Tile(1,1)` has edge directions `ζ^d` for
`d = 0,10,1,3,0,2,5,7,4,6,6,8,11,9`; `verts` lists its 14 vertices and `tris` a triangulation into
12 triangles. The 54 placements `(r, x, y)` of the answer put the tile `ζ^r S + x a + y b`, with
`a = ζ² + ζ³`, `b = -2 - ζ - ζ³`, and the period lattice is `ℤ v + ℤ w`.

Everything here is computable and every check is a kernel `decide`.
-/

namespace SpectreCover

/-- An element `a₀ + a₁ζ + a₂ζ² + a₃ζ³` of `ℤ[ζ]`. -/
abbrev Zz := ℤ × ℤ × ℤ × ℤ

/-- Multiplication by `ζ`, using `ζ⁴ = ζ² - 1`. -/
def rotZ (a : Zz) : Zz := (-a.2.2.2, a.1, a.2.1 + a.2.2.2, a.2.2.1)

def rotN : ℕ → Zz → Zz
  | 0, a => a
  | n + 1, a => rotZ (rotN n a)

def dirs : List ℕ := [0, 10, 1, 3, 0, 2, 5, 7, 4, 6, 6, 8, 11, 9]

/-- The 14 vertices of the Spectre `Tile(1,1)`. -/
def verts : Fin 14 → Zz :=
  ![(0, 0, 0, 0), (1, 0, 0, 0), (2, 0, -1, 0), (2, 1, -1, 0), (2, 1, -1, 1), (3, 1, -1, 1),
    (3, 1, 0, 1), (3, 0, 0, 2), (3, -1, 0, 2), (2, -1, 1, 2), (1, -1, 1, 2), (0, -1, 1, 2),
    (0, -1, 0, 2), (0, 0, 0, 1)]

/-- Successive edges are the unit vectors `ζ^d`. -/
theorem verts_edges : ∀ i : Fin 14,
    verts (i + 1) = verts i + rotN (dirs.getD i.val 0) (1, 0, 0, 0) := by decide

/-- A triangulation of the Spectre into 12 counterclockwise triangles. -/
def tris : Fin 12 → Fin 3 → Fin 14 :=
  ![![13, 0, 1], ![1, 2, 3], ![13, 1, 3], ![13, 3, 4], ![13, 4, 5], ![13, 5, 6], ![6, 7, 8],
    ![13, 6, 8], ![13, 8, 9], ![13, 9, 10], ![13, 10, 11], ![11, 12, 13]]

def aZ : Zz := (0, 0, 1, 1)
def bZ : Zz := (-2, -1, 0, -1)
def vZ : Zz := (3, 1, 2, 3)
def wZ : Zz := (-4, -3, 3, 1)

/-- The 54 placements `(r, x, y)`: the tile `ζ^r S + x a + y b`. -/
def placements : Fin 54 → ℕ × ℤ × ℤ :=
  ![(0,-2,5),(0,-1,5),(0,2,5),(0,3,5),(1,-8,-10),(2,-2,-1),(2,-1,-1),(2,0,-1),(2,1,-1),(2,2,-1),
    (2,3,-1),(2,4,-1),(2,5,-1),(4,-5,-10),(4,-4,-10),(4,-4,-4),(4,-3,-10),(4,-3,-4),(4,-3,2),
    (4,-1,-10),(4,0,-10),(4,0,-4),(4,1,-10),(4,1,-4),(4,1,2),(5,-1,17),(5,3,17),(6,-9,-13),
    (6,-8,-7),(6,-7,-7),(6,-6,-7),(6,-5,-13),(6,-4,-7),(6,-3,-7),(6,-3,-1),(6,-2,-7),(6,1,-1),
    (7,3,8),(7,4,8),(7,8,8),(8,-10,-1),(8,-9,-1),(8,-8,-1),(8,-7,-1),(8,-6,-1),(8,-5,-1),
    (8,-4,-1),(8,-3,-1),(10,-5,2),(10,-5,8),(10,-4,8),(10,-1,2),(10,-1,8),(10,0,8)]

/-- The offset `x a + y b` of placement `j`. -/
def offset (j : Fin 54) : Zz := (placements j).2.1 • aZ + (placements j).2.2 • bZ

/-- Vertex `k` of triangle `t` of placement `j`, in `ℤ[ζ]`. -/
def vertZ (j : Fin 54) (t : Fin 12) (k : Fin 3) : Zz :=
  rotN (placements j).1 (verts (tris t k)) + offset j

/-- `K : ℤ⁴ → ℤ²`, with kernel `ℤ v + ℤ w` and `K a = (1,0)`, `K b = (0,1)`. -/
def kZ (a : Zz) : ℤ × ℤ :=
  (-2 * a.1 + 3 * a.2.1 + a.2.2.2, a.1 + 2 * a.2.1 + 5 * a.2.2.1 - 5 * a.2.2.2)

/-- All triangle edges, as `(placement, triangle, k)`. -/
def edges : List (Fin 54 × Fin 12 × Fin 3) :=
  (List.finRange 54).flatMap fun j => (List.finRange 12).flatMap fun t =>
    (List.finRange 3).map fun k => (j, t, k)

/-- An oriented edge `P → Q` up to the lattice: the class of `P` and the vector `Q - P`. -/
def key (e : Fin 54 × Fin 12 × Fin 3) : (ℤ × ℤ) × Zz :=
  (kZ (vertZ e.1 e.2.1 e.2.2), vertZ e.1 e.2.1 (e.2.2 + 1) - vertZ e.1 e.2.1 e.2.2)

/-- The reversed edge `Q → P` up to the lattice. -/
def rkey (e : Fin 54 × Fin 12 × Fin 3) : (ℤ × ℤ) × Zz :=
  (kZ (vertZ e.1 e.2.1 (e.2.2 + 1)), vertZ e.1 e.2.1 e.2.2 - vertZ e.1 e.2.1 (e.2.2 + 1))

/-- Lexicographic order on integer lists. -/
def lexLe : List ℤ → List ℤ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a = b then lexLe as bs else false

/-- Lexicographic comparison of keys, for sorting. -/
def keyLe (p q : (ℤ × ℤ) × Zz) : Bool :=
  lexLe [p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]
    [q.1.1, q.1.2, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2]

section Sorting

variable {α : Type*} (le : α → α → Bool)

/-- Merge with fuel (structural, so the kernel can evaluate it). -/
def mergeF : ℕ → List α → List α → List α
  | 0, l₁, l₂ => l₁ ++ l₂
  | _ + 1, [], l₂ => l₂
  | _ + 1, a :: as, [] => a :: as
  | n + 1, a :: as, b :: bs =>
    if le a b then a :: mergeF n as (b :: bs) else b :: mergeF n (a :: as) bs

/-- Merge sort with fuel. -/
def msort : ℕ → List α → List α
  | 0, l => l
  | n + 1, l =>
    if l.length ≤ 1 then l
    else mergeF le l.length (msort n (l.take (l.length / 2))) (msort n (l.drop (l.length / 2)))

theorem mergeF_perm : ∀ (n : ℕ) (l₁ l₂ : List α), (mergeF le n l₁ l₂).Perm (l₁ ++ l₂)
  | 0, l₁, l₂ => by simp [mergeF]
  | _ + 1, [], l₂ => by simp [mergeF]
  | _ + 1, a :: as, [] => by simp [mergeF]
  | n + 1, a :: as, b :: bs => by
    unfold mergeF
    split_ifs
    · exact (mergeF_perm n as (b :: bs)).cons a
    · refine ((mergeF_perm n (a :: as) bs).cons b).trans ?_
      exact List.perm_middle.symm

theorem msort_perm : ∀ (n : ℕ) (l : List α), (msort le n l).Perm l
  | 0, l => by simp [msort]
  | n + 1, l => by
    unfold msort
    split_ifs
    · exact List.Perm.refl l
    · refine (mergeF_perm le _ _ _).trans ?_
      refine ((msort_perm n _).append (msort_perm n _)).trans ?_
      rw [List.take_append_drop]

end Sorting

set_option maxRecDepth 1000000 in
/-- **The certificate.** Sorted, the 1944 edge keys equal the 1944 reversed keys. -/
theorem keys_sorted_eq :
    msort keyLe 12 (edges.map key) = msort keyLe 12 (edges.map rkey) := by
  decide +kernel

theorem keys_perm : (edges.map key).Perm (edges.map rkey) := by
  have h := msort_perm keyLe 12 (edges.map rkey)
  rw [← keys_sorted_eq] at h
  exact (msort_perm keyLe 12 _).symm.trans h

/-! ### Sanity checks on the data -/

/-- The 36 directed edges of the triangulation, as vertex-index pairs. -/
def triEdges : List (Fin 14 × Fin 14) :=
  (List.finRange 12).flatMap fun t => (List.finRange 3).map fun k => (tris t k, tris t (k + 1))

/-- The triangulation's boundary is the Spectre's boundary: each edge `i → i+1` of the 14-gon
occurs once and its reverse never; every other edge occurs once, together with its reverse. -/
theorem tris_boundary :
    (∀ i : Fin 14, triEdges.count (i, i + 1) = 1 ∧ triEdges.count (i + 1, i) = 0) ∧
    ∀ e ∈ triEdges, e.2 ≠ e.1 + 1 → triEdges.count e = 1 ∧ triEdges.count (e.2, e.1) = 1 := by
  decide +kernel

/-- The 54 placements are distinct. -/
theorem placements_injective : Function.Injective placements := by
  decide +kernel

/-- Codex's curved-edge record of polygon edge `i` of placement `j`: the rotated copy of the
edge curve (`label`) and its distinguished start modulo the lattice. Even edges traverse the
curve forward, odd edges backward. -/
def curvedRecord (j : Fin 54) (i : Fin 14) : List ℤ :=
  let r := (placements j).1
  let ε := i.val % 2
  let s : Fin 14 := if ε = 0 then i else i + 1
  [((r + dirs.getD i.val 0 + 6 * ε) % 12 : ℕ),
    (placements j).2.1 + (kZ (rotN r (verts s))).1,
    (placements j).2.2 + (kZ (rotN r (verts s))).2]

def curvedRecords (parity : ℕ) : List (List ℤ) :=
  (List.finRange 54).flatMap fun j =>
    ((List.finRange 14).filter fun i => i.val % 2 == parity).map fun i => curvedRecord j i

set_option maxRecDepth 100000 in
/-- **Codex's certificate for curved Spectres.** The 378 forward curve copies and the 378
backward ones agree as multisets, so whole curved edges cancel in pairs modulo the lattice. -/
theorem curved_records_cancel :
    msort lexLe 10 (curvedRecords 0) = msort lexLe 10 (curvedRecords 1) ∧
      (curvedRecords 0).length = 378 := by
  decide +kernel

end SpectreCover
