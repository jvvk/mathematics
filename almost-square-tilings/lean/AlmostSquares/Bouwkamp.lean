/-
  Bouwkamp codes. The paper names its squared squares by the codes in Moews's lists
  (https://djm.cc/21-simple-sqsq.bouwkamp.txt, https://djm.cc/22-simple-sqsq.bouwkamp.txt and
  https://djm.cc/simple-perfect-rects-to-16.txt, checked 7 October 2026). This file decodes a code
  into a layout and checks that the layouts used elsewhere (`sq112`, `sq110`, `sq139`, `moron`) are
  exactly the decoded ones, up to the order of the squares.

  The convention: each group lists, left to right, the squares whose top sides lie on the highest
  free horizontal segment, taking the leftmost such segment when several are equally high. Depths are
  measured down from the top edge; the decoded layout is returned with the origin at the lower left.
-/
import AlmostSquares.Examples

namespace AlmostSq

/-- The least entry of a nonempty list. -/
def minD (l : List ℕ) : ℕ := l.foldl min (l.headD 0)

/-- Add `k` to the entries `x, …, x+s-1`. -/
def addRange (l : List ℕ) (x s k : ℕ) : List ℕ :=
  l.mapIdx (fun i a => if x ≤ i ∧ i < x + s then a + k else a)

/-- Place the squares of one group side by side from column `x` at depth `d`; each must sit on
    a flat stretch of depth `d`. Returns the new depths and the placements `(side, x, depth)`. -/
def placeRow (d : ℕ) : List ℕ → ℕ → List ℕ → List (ℕ × ℕ × ℕ) → Option (List ℕ × List (ℕ × ℕ × ℕ))
  | dep, _, [], acc => some (dep, acc)
  | dep, x, s :: r, acc =>
    if 0 < s ∧ ((dep.drop x).take s).length = s ∧ ((dep.drop x).take s).all (· == d) then
      placeRow d (addRange dep x s s) (x + s) r ((s, x, d) :: acc)
    else none

/-- Place every group in turn, starting from all depths zero. -/
def placeAll : List ℕ → List (List ℕ) → List (ℕ × ℕ × ℕ) → Option (List ℕ × List (ℕ × ℕ × ℕ))
  | dep, [], acc => some (dep, acc)
  | dep, g :: r, acc =>
    match placeRow (minD dep) dep (dep.idxOf (minD dep)) g acc with
    | some (dep', acc') => placeAll dep' r acc'
    | none => none

/-- Decode a Bouwkamp code into `(width, height, squares)`, or `none` if it is not a valid code of a
    rectangle (some group does not fit, or the final bottom edge is not flat). -/
def decode (code : List (List ℕ)) : Option (ℕ × ℕ × List Tile) :=
  match code with
  | [] => none
  | g :: _ =>
    let W := g.sum
    match placeAll (List.replicate W 0) code [] with
    | some (dep, pl) =>
      if dep.all (· == minD dep) then
        some (W, minD dep, pl.map (fun p => sq p.1 p.2.1 ((minD dep : ℤ) - p.2.2 - p.1)))
      else none
    | none => none

/-- The decoded code is the rectangle `W × H` with exactly the squares `ts` (in any order). -/
def codeIs (code : List (List ℕ)) (W H : ℕ) (ts : List Tile) : Bool :=
  match decode code with
  | some (W', H', L) => W' == W && H' == H && L.isPerm ts
  | none => false

/-- Duijvestijn's square of order 21 and side 112. -/
def code112 : List (List ℕ) :=
  [[50, 35, 27], [8, 19], [15, 17, 11], [6, 24], [29, 25, 9, 2], [7, 18], [16], [42], [4, 37], [33]]

/-- The order-22 square of side 110 used for odd `n`. -/
def code110 : List (List ℕ) :=
  [[60, 50], [27, 23], [24, 22, 14], [4, 19], [8, 6], [3, 12, 16], [9], [2, 28], [26], [21], [1, 18],
    [17]]

/-- The order-22 square of side 139 of Proposition 6(3). -/
def code139 : List (List ℕ) :=
  [[80, 59], [21, 38], [29, 28, 17, 27], [7, 10], [18, 20], [4, 3], [32, 8], [1, 31], [30], [24, 2],
    [22]]

/-- Moroń's rectangle, order 9, 33 by 32. -/
def codeMoron : List (List ℕ) := [[18, 15], [7, 8], [14, 4], [10, 1], [9]]

theorem sq112_code : codeIs code112 112 112 sq112 = true := by decide +kernel
theorem sq110_code : codeIs code110 110 110 sq110 = true := by decide +kernel
theorem sq139_code : codeIs code139 139 139 sq139 = true := by decide +kernel
theorem moron_code : codeIs codeMoron 33 32 moron = true := by decide +kernel

end AlmostSq
