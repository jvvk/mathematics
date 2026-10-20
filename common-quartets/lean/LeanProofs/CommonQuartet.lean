/-
Snir-Yuster h(3) (arXiv 2602.23096 §5): three unrooted binary phylogenetic trees on 13 leaves with no common
quartet split, so h(3) ≥ 14.

A tree is written rooted on the pendant edge of leaf 0; suppressing that degree-2 root gives the unrooted binary
tree. Every edge split of the unrooted tree is (leaf set of some subtree | rest), so the quartet ab|cd is displayed
iff some subtree's leaves meet {a,b,c,d} in exactly {a,b} or exactly {c,d}.
-/

namespace CommonQuartet

inductive Tr where
  | leaf : Nat → Tr
  | node : Tr → Tr → Tr

open Tr

def Tr.leaves : Tr → List Nat
  | leaf n => [n]
  | node l r => l.leaves ++ r.leaves

/-- Leaf sets of all subtrees (one side of every edge split). -/
def Tr.clusters : Tr → List (List Nat)
  | leaf n => [[n]]
  | node l r => (l.leaves ++ r.leaves) :: (l.clusters ++ r.clusters)

/-- `S` cuts off exactly the pair {x,y} from the quartet {x,y,u,v}. -/
def cutsPair (S : List Nat) (x y u v : Nat) : Bool :=
  (S.contains x && S.contains y && !S.contains u && !S.contains v) ||
  (!S.contains x && !S.contains y && S.contains u && S.contains v)

/-- The tree displays xy|uv. -/
def displays (t : Tr) (x y u v : Nat) : Bool :=
  t.clusters.any fun S => cutsPair S x y u v

/-- The three splits of the 4-set a<b<c<d: ab|cd, ac|bd, ad|bc. -/
def splitsOf (a b c d : Nat) : List (Nat × Nat × Nat × Nat) :=
  [(a, b, c, d), (a, c, b, d), (a, d, b, c)]

def quads (n : Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b => (List.range n).flatMap fun c =>
    (List.range n).filterMap fun d => if a < b ∧ b < c ∧ c < d then some (a, b, c, d) else none

/-- Leaf labels are exactly 0, ..., n-1, each once. -/
def onLeaves (t : Tr) (n : Nat) : Bool :=
  t.leaves.length == n && (List.range n).all fun i => t.leaves.contains i

/-- Every quartet is resolved (the tree is binary on these leaves). -/
def resolvesAll (t : Tr) (n : Nat) : Bool :=
  (quads n).all fun (a, b, c, d) => (splitsOf a b c d).any fun (x, y, u, v) => displays t x y u v

/-- No 4-set has the same split in all three trees. -/
def noCommon (t₁ t₂ t₃ : Tr) (n : Nat) : Bool :=
  (quads n).all fun (a, b, c, d) => (splitsOf a b c d).all fun (x, y, u, v) =>
    !(displays t₁ x y u v && displays t₂ x y u v && displays t₃ x y u v)

local notation "L" => Tr.leaf
local infixl:65 " ⋆ " => Tr.node

-- (0, ((((6,5),(1,(8,10))),((2,9),(12,(11,7)))),(4,3)))
def T1 : Tr := L 0 ⋆ ((((L 6 ⋆ L 5) ⋆ (L 1 ⋆ (L 8 ⋆ L 10))) ⋆ ((L 2 ⋆ L 9) ⋆ (L 12 ⋆ (L 11 ⋆ L 7)))) ⋆ (L 4 ⋆ L 3))
-- (0, ((12, (((6,9),(4,(7,10))),((2,5),(3,(1,11))))), 8))
def T2 : Tr := L 0 ⋆ ((L 12 ⋆ (((L 6 ⋆ L 9) ⋆ (L 4 ⋆ (L 7 ⋆ L 10))) ⋆ ((L 2 ⋆ L 5) ⋆ (L 3 ⋆ (L 1 ⋆ L 11))))) ⋆ L 8)
-- (0, (((5,9),((12,(1,4)),((6,2),((3,7),8)))),(10,11)))
def T3 : Tr := L 0 ⋆ (((L 5 ⋆ L 9) ⋆ ((L 12 ⋆ (L 1 ⋆ L 4)) ⋆ ((L 6 ⋆ L 2) ⋆ ((L 3 ⋆ L 7) ⋆ L 8)))) ⋆ (L 10 ⋆ L 11))

theorem quads_card : (quads 13).length = 715 := by decide +kernel

theorem witness_leaves : onLeaves T1 13 ∧ onLeaves T2 13 ∧ onLeaves T3 13 := by decide +kernel

theorem witness_binary : resolvesAll T1 13 ∧ resolvesAll T2 13 ∧ resolvesAll T3 13 := by decide +kernel

/-- Three 13-leaf binary trees with no common quartet: h(3) ≥ 14. -/
theorem no_common_quartet : noCommon T1 T2 T3 13 = true := by decide +kernel

/-- Relabel the leaves of a tree. -/
def Tr.map (f : Nat → Nat) : Tr → Tr
  | leaf n => leaf (f n)
  | node l r => node (l.map f) (r.map f)

/-- The cyclic form used in the paper: T on Z_13 with its images under x ↦ 3x and x ↦ 9x.
Newick (0, 1, (((8,11),((5,(4,6)),((3,9),(12,(7,10))))), 2)), written rooted on leaf 0's pendant edge. -/
def T : Tr := L 0 ⋆ (L 1 ⋆ ((((L 8 ⋆ L 11) ⋆ ((L 5 ⋆ (L 4 ⋆ L 6)) ⋆ ((L 3 ⋆ L 9) ⋆ (L 12 ⋆ (L 7 ⋆ L 10))))) ⋆ L 2)))

def times3 (x : Nat) : Nat := 3 * x % 13

theorem cyclic_leaves : onLeaves T 13 ∧ onLeaves (T.map times3) 13 ∧ onLeaves ((T.map times3).map times3) 13 := by
  decide +kernel

theorem cyclic_binary : resolvesAll T 13 ∧ resolvesAll (T.map times3) 13 ∧
    resolvesAll ((T.map times3).map times3) 13 := by decide +kernel

/-- Paper, Proposition 5.1: T, 3T, 9T share no quartet. -/
theorem cyclic_no_common_quartet : noCommon T (T.map times3) ((T.map times3).map times3) 13 = true := by
  decide +kernel

end CommonQuartet
