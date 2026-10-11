import Mathlib

/-!
# Incomplete open solids by hand (MO 508521): the finite counts

The note counts incomplete open tetrahedra (6), cubes (122) and octahedra (185) up to rotation.
Its route: Burnside's lemma gives the number of rotation classes of `k`-edge sets; for many edges
one subtracts the few disconnected classes, and for few edges one counts spanning trees after
deleting the unused vertices and divides by a small stabiliser. This file checks every finite
number that route uses.

* `cube_burnside`, `cube_cycle_profile`: the edge-set polynomial of the cube from its 24 rotations.
* `cube_induced`, `oct_induced`: how many edges a few vertices can span.
* `ladder_trees`, `square_leaves_trees`, `hexagon_trees`, `hub_trees`, `wheel_trees`, `k4e_trees`,
  `k4_trees`: spanning-tree counts, by the number of spokes where the note counts that way.
* `*_fixed`: the trees fixed by each element of the stabiliser.
* `cube_total`, `octahedron_total`, `tetrahedron_total`: the averages and the final sums.

Graphs are lists of edges on vertices `0, 1, …`. Cube vertices are the numbers `0, …, 7` read as
three bits, joined when they differ in one bit; octahedron vertices `2i` and `2i + 1` are `±eᵢ`,
joined unless antipodal. A set of `n - 1` edges that covers all `n` vertices of a vertex set and is
connected is a spanning tree of it. Small facts are checked with `decide +kernel` (kernel reduction,
no extra axioms): they are the hand checks of the note, on graphs with at most twelve edges.
-/

namespace OpenSolids

/-- A graph as a list of edges `(a, b)`, `a < b`. -/
abbrev Edges := List (ℕ × ℕ)

/-- All pairs `a < b` below `n` satisfying `p`. -/
def pairsWith (n : ℕ) (p : ℕ → ℕ → Bool) : Edges :=
  (List.range n).flatMap fun a => (List.range n).filterMap fun b =>
    if a < b && p a b then some (a, b) else none

/-- The cube: `0, …, 7` as bit vectors, joined when they differ in exactly one bit. -/
def cube : Edges := pairsWith 8 fun a b => a ^^^ b == 1 || a ^^^ b == 2 || a ^^^ b == 4

/-- The octahedron: `2i, 2i + 1` are `±eᵢ`; two vertices are joined unless antipodal. -/
def oct : Edges := pairsWith 6 fun a b => a / 2 != b / 2

/-- The tetrahedron: all pairs of four vertices. -/
def tet : Edges := pairsWith 4 fun _ _ => true

/-- Delete a list of vertices. -/
def delete (D : List ℕ) (es : Edges) : Edges :=
  es.filter fun e => !(D.contains e.1 || D.contains e.2)

/-- The edges among the vertices `S`. -/
def induced (S : List ℕ) (es : Edges) : ℕ :=
  (es.filter fun e => S.contains e.1 && S.contains e.2).length

/-- Vertex sets as bit masks. -/
def vmask (es : Edges) : ℕ := es.foldl (fun M e => M ||| 2 ^ e.1 ||| 2 ^ e.2) 0

/-- One round of growing a set of reached vertices along the edges. -/
def grow (es : Edges) (M : ℕ) : ℕ :=
  es.foldl (fun M e => if M.testBit e.1 || M.testBit e.2 then M ||| 2 ^ e.1 ||| 2 ^ e.2 else M) M

/-- The number of set bits below `8`. -/
def pop (M : ℕ) : ℕ := ((List.range 8).filter fun i => M.testBit i).length

/-- The least vertex of a nonempty mask. -/
def low (M : ℕ) : ℕ := ((List.range 8).find? fun i => M.testBit i).getD 0

/-- `t` is a spanning tree of the vertex set `M`: `|M| - 1` edges covering `M`, connected. -/
def IsTree (M : ℕ) (t : Edges) : Bool :=
  t.length + 1 == pop M && vmask t == M && (grow t)^[8] (2 ^ low M) == M

/-- The spanning trees of `es` (on the vertices it covers). -/
def trees (es : Edges) : List Edges := es.sublists.filter (IsTree (vmask es))

/-- How many edges of `t` meet the vertex `h`. -/
def spokes (h : ℕ) (t : Edges) : ℕ := (t.filter fun e => e.1 == h || e.2 == h).length

/-! ## Rotations -/

/-- The edge `(g a, g b)`, ordered. -/
def mapE (g : ℕ → ℕ) (e : ℕ × ℕ) : ℕ × ℕ :=
  (min (g e.1) (g e.2), max (g e.1) (g e.2))

/-- `t` is carried to itself by `g`. -/
def Fixes (g : ℕ → ℕ) (t : Edges) : Bool := t.all fun e => t.contains (mapE g e)

/-- The sign of a permutation of `0, 1, 2`. -/
def sgn3 (p : List ℕ) : Bool := p == [0, 1, 2] || p == [1, 2, 0] || p == [2, 0, 1]

/-- The cube symmetry that sets bit `i` of the image to bit `p i` of `v`, flipped when `f i`. -/
def cubeMap (p : List ℕ) (f : List Bool) (v : ℕ) : ℕ :=
  (List.range 3).foldl (fun acc i =>
    acc + if xor (v.testBit (p.getD i 0)) (f.getD i false) then 2 ^ i else 0) 0

/-- The octahedron symmetry with the same coordinate data, on `±eᵢ` (vertex `2i + s`). -/
def octMap (p : List ℕ) (f : List Bool) (v : ℕ) : ℕ :=
  let k := (p.findIdx? (· == v / 2)).getD 0
  2 * k + if xor (v % 2 == 1) (f.getD k false) then 1 else 0

/-- The 24 rotations: coordinate permutations with sign flips, of determinant `+1`. -/
def rotData : List (List ℕ × List Bool) :=
  ([[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]].flatMap fun p =>
    [false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].filterMap fun c =>
      let flips := [a, b, c].count true
      if sgn3 p == (flips % 2 == 0) then some (p, [a, b, c]) else none)

/-- The cycle length of the edge `e` under `g`: the least `j ≤ 4` with `gʲ e = e`. -/
def cycLen (g : ℕ → ℕ) (e : ℕ × ℕ) : ℕ :=
  ((List.range' 1 4).find? fun j => (mapE g)^[j] e == e).getD 0

/-- How many edges lie in cycles of length `1, 2, 3, 4`. -/
def profile (g : ℕ → ℕ) (es : Edges) : List ℕ :=
  [1, 2, 3, 4].map fun l => (es.filter fun e => cycLen g e == l).length

/-- The rotations of the cube fixing the vertex set `D`. -/
def cubeStab (D : List ℕ) : List (ℕ → ℕ) :=
  (rotData.filter fun d => D.all fun x => D.contains (cubeMap d.1 d.2 x)).map fun d =>
    cubeMap d.1 d.2

/-- For each rotation in the stabiliser of `D`, the number of trees in `ts` it fixes. -/
def cubeFixed (D : List ℕ) (ts : List Edges) : List ℕ :=
  (cubeStab D).map fun g => (ts.filter (Fixes g)).length

def octStab (D : List ℕ) : List (ℕ → ℕ) :=
  (rotData.filter fun d => D.all fun x => D.contains (octMap d.1 d.2 x)).map fun d => octMap d.1 d.2

def octFixed (D : List ℕ) (ts : List Edges) : List ℕ :=
  (octStab D).map fun g => (ts.filter (Fixes g)).length

/-! ## The solids and their symmetries -/

theorem cube_size : cube.length = 12 ∧ oct.length = 12 ∧ tet.length = 6 := by decide +kernel

theorem rot_count : rotData.length = 24 := by decide +kernel

/-- Each of the 24 maps carries edges to edges, on the cube and on the octahedron. -/
theorem rot_preserve :
    rotData.all (fun d => cube.all fun e => cube.contains (mapE (cubeMap d.1 d.2) e)) ∧
    rotData.all (fun d => oct.all fun e => oct.contains (mapE (octMap d.1 d.2) e)) := by
  decide +kernel

/-- The cycle profiles of the 24 rotations on the cube's edges: the identity, six quarter-turns
(three 4-cycles), three face half-turns (six 2-cycles), six edge half-turns (two fixed edges,
five 2-cycles) and eight third-turns (four 3-cycles). The octahedron's are the same. -/
theorem cube_cycle_profile :
    (rotData.map fun d => profile (cubeMap d.1 d.2) cube).count [12, 0, 0, 0] = 1 ∧
    (rotData.map fun d => profile (cubeMap d.1 d.2) cube).count [0, 0, 0, 12] = 6 ∧
    (rotData.map fun d => profile (cubeMap d.1 d.2) cube).count [0, 12, 0, 0] = 3 ∧
    (rotData.map fun d => profile (cubeMap d.1 d.2) cube).count [2, 10, 0, 0] = 6 ∧
    (rotData.map fun d => profile (cubeMap d.1 d.2) cube).count [0, 0, 12, 0] = 8 ∧
    rotData.map (fun d => profile (octMap d.1 d.2) oct) =
      rotData.map (fun d => profile (cubeMap d.1 d.2) cube) := by
  decide +kernel

open Polynomial in
/-- Burnside's lemma with those cycle types: the rotation classes of `k`-edge sets are the
coefficients of this polynomial (the same for the octahedron). -/
theorem cube_burnside :
    ((1 + X) ^ 12 + 3 * (1 + X ^ 2) ^ 6 + 6 * (1 + X ^ 4) ^ 3 + 6 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 5
      + 8 * (1 + X ^ 3) ^ 4 : ℤ[X]) =
    24 * (1 + X + 5 * X ^ 2 + 13 * X ^ 3 + 27 * X ^ 4 + 38 * X ^ 5 + 48 * X ^ 6 + 38 * X ^ 7
      + 27 * X ^ 8 + 13 * X ^ 9 + 5 * X ^ 10 + X ^ 11 + X ^ 12) := by
  ring

/-! ## How many edges a few vertices span -/

/-- Cube: four, five and six vertices span at most four, five and seven edges. -/
theorem cube_induced :
    ((List.range 8).sublists.filter (·.length = 4)).all (fun S => induced S cube ≤ 4) ∧
    ((List.range 8).sublists.filter (·.length = 5)).all (fun S => induced S cube ≤ 5) ∧
    ((List.range 8).sublists.filter (·.length = 6)).all (fun S => induced S cube ≤ 7) := by
  decide +kernel

/-- Octahedron: two, three and four vertices span at most one, three and five edges, and four
vertices span five exactly when they contain one antipodal pair. -/
theorem oct_induced :
    ((List.range 6).sublists.filter (·.length = 2)).all (fun S => induced S oct ≤ 1) ∧
    ((List.range 6).sublists.filter (·.length = 3)).all (fun S => induced S oct ≤ 3) ∧
    ((List.range 6).sublists.filter (·.length = 4)).all (fun S =>
      (induced S oct == 5) == (((List.range 3).filter fun i =>
        S.contains (2 * i) && S.contains (2 * i + 1)).length == 1)) := by
  decide +kernel

/-! ## Cube: trees with two unused vertices (five edges) -/

/-- Unused vertices at distance 1: a ladder of two squares, fifteen trees. -/
theorem ladder_trees : (trees (delete [0, 1] cube)).length = 15 := by decide +kernel

theorem ladder_fixed : cubeFixed [0, 1] (trees (delete [0, 1] cube)) = [15, 3] := by decide +kernel

/-- Distance 2: a square with leaves at opposite corners, four trees, none fixed by the
half-turn. -/
theorem square_leaves_trees : (trees (delete [0, 3] cube)).length = 4 := by decide +kernel

theorem square_leaves_fixed : cubeFixed [0, 3] (trees (delete [0, 3] cube)) = [4, 0] := by
  decide +kernel

/-- Distance 3: a hexagon, six trees; third-turns fix none, half-turns fix two each. -/
theorem hexagon_trees : (trees (delete [0, 7] cube)).length = 6 := by decide +kernel

theorem hexagon_fixed : (cubeFixed [0, 7] (trees (delete [0, 7] cube))).length = 6 ∧
    (cubeFixed [0, 7] (trees (delete [0, 7] cube))).count 6 = 1 ∧
    (cubeFixed [0, 7] (trees (delete [0, 7] cube))).count 2 = 3 ∧
    (cubeFixed [0, 7] (trees (delete [0, 7] cube))).count 0 = 2 := by decide +kernel

/-! ## Cube: trees with one unused vertex (six edges) -/

/-- A hexagon with a hub on alternate vertices: `3·6 + 3·(2·4) + 2³ = 50` trees by spokes. -/
theorem hub_trees :
    ((trees (delete [0] cube)).filter (spokes 7 · == 1)).length = 18 ∧
    ((trees (delete [0] cube)).filter (spokes 7 · == 2)).length = 24 ∧
    ((trees (delete [0] cube)).filter (spokes 7 · == 3)).length = 8 ∧
    (trees (delete [0] cube)).length = 50 := by decide +kernel

theorem hub_fixed : cubeFixed [0] (trees (delete [0] cube)) = [50, 2, 2] := by decide +kernel

/-! ## Octahedron -/

/-- One unused vertex (four edges, five vertices): the wheel with four spokes has `16 + 20 + 8 + 1
= 45` trees by spokes; the quarter-turns fix one each, the half-turn five. -/
theorem wheel_trees :
    ((trees (delete [5] oct)).filter (spokes 4 · == 1)).length = 16 ∧
    ((trees (delete [5] oct)).filter (spokes 4 · == 2)).length = 20 ∧
    ((trees (delete [5] oct)).filter (spokes 4 · == 3)).length = 8 ∧
    ((trees (delete [5] oct)).filter (spokes 4 · == 4)).length = 1 ∧
    (trees (delete [5] oct)).length = 45 := by decide +kernel

theorem wheel_fixed : (octFixed [5] (trees (delete [5] oct))).length = 4 ∧
    (octFixed [5] (trees (delete [5] oct))).count 45 = 1 ∧
    (octFixed [5] (trees (delete [5] oct))).count 5 = 1 ∧
    (octFixed [5] (trees (delete [5] oct))).count 1 = 2 := by decide +kernel

/-- Two unused vertices forming an edge (three edges): the other four vertices span `K₄` minus an
edge, with eight trees; its half-turn fixes two. -/
theorem k4e_trees : (trees (delete [0, 2] oct)).length = 8 := by decide +kernel

theorem k4e_fixed : octFixed [0, 2] (trees (delete [0, 2] oct)) = [8, 2] := by decide +kernel

/-- Tetrahedron: sixteen spanning trees, four of them stars. -/
theorem k4_trees : (trees tet).length = 16 ∧
    ((trees tet).filter fun t => [0, 1, 2, 3].any (spokes · t == 3)).length = 4 := by
  decide +kernel

/-! ## The sums -/

/-- The cube: the tree averages, the corrections, and `122`. -/
theorem cube_total :
    (15 + 3) / 2 = 9 ∧ (4 + 0) / 2 = 2 ∧ (6 + 3 * 2) / 6 = 2 ∧ (50 + 2 + 2) / 3 = 18 ∧
    (9 + 2 + 2) + 1 = 14 ∧ 18 + 6 = 24 ∧ 38 - 6 = 32 ∧ 27 - 2 = 25 ∧
    3 + 5 + 14 + 24 + 32 + 25 + 13 + 5 + 1 = 122 := by norm_num

/-- The octahedron: `5`, `3 + 13`, `38 - 4`, `48 - 2`, then the Burnside coefficients, `185`. -/
theorem octahedron_total :
    (8 + 2) / 2 = 5 ∧ (45 + 1 + 1 + 5) / 4 = 13 ∧ 3 + 13 = 16 ∧ 38 - 4 = 34 ∧
    48 - 2 = 46 ∧
    5 + 16 + 34 + 46 + 38 + 27 + 13 + 5 + 1 = 185 := by norm_num

/-- The tetrahedron: one star class and two path classes (orbits of six), then `2` and `1`. -/
theorem tetrahedron_total : 4 / 4 + 12 / 6 = 3 ∧ 3 + 2 + 1 = 6 := by norm_num

end OpenSolids
