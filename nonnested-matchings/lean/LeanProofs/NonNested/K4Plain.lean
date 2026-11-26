import LeanProofs.NonNested.Defs

/-!
# The plain case `k = 4`: the local star lemmas

The proof that `f₄(n) = 3n` (version 2 of the note) rests on a short list of *local* lemmas: given a
few prescribed edges of `G` near a vertex `c`, and the long chords of one `3`-star of the
`3`-triangulation (the star on a linear boundary edge `(i, i+3)`, whose other vertices `p < q < r`
lie in cyclic order after `i + 3`), the graph `G` contains a non-nested `4`-matching. Each lemma is
the note's table: one explicit matching per case, checked by `omega`.

* `star3 i p q r` lists the six chords of that star other than `(i, i+3)`:
  `(i+1,p), (i+2,q), (i+3,r), (p,i), (q,i+1), (r,i+2)`.
* `StarPos n i p q r`: `p, q, r` are in cyclic order in the open interval after `i + 3`
  (the vertices right of `i + 3` come first).
* `StarLongIn G i p q r`: every chord of the star of linear length at least `4` lies in `G`
  (in the note this holds when no long edge of the star is missing from `G`).

Lemmas (names as in the note): `lemmaE` (window `[c-1, c+2]`, edges `(c-3,c), (c,c+2)` and a
non-nested pair beyond `c+4`), `endWindowA` (window `[c-2, c+1]`), `endWindowB` (window
`[c-1, c+2]` with `(c-2,c), (c,c+3)`), `lemmaM` (middle window), `closePair1`, `closePair2`
(two centres at distance `1` or `2`), and `exceptional` (the arrangement `a, a+4, a+8`).
The Pilaud–Santos star theorem that produces the star is not used here: these lemmas take the
star as given.
-/

set_option linter.style.longLine false

namespace NonNested

/-- The six chords of the `3`-star on the boundary edge `(i, i+3)` with outer vertices `p, q, r`,
other than the boundary edge itself. -/
def star3 (i p q r : ℕ) : List Edge :=
  [edge (i + 1) p, edge (i + 2) q, edge (i + 3) r, edge i p, edge (i + 1) q, edge (i + 2) r]

/-- `p, q, r` lie in cyclic order in the interval after `i + 3` on `[1, n]`: those right of
`i + 3` first, then those left of `i`. -/
def StarPos (n i p q r : ℕ) : Prop :=
  (i + 3 < p ∧ p < q ∧ q < r ∧ r ≤ n) ∨
  (i + 3 < p ∧ p < q ∧ q ≤ n ∧ 1 ≤ r ∧ r < i) ∨
  (i + 3 < p ∧ p ≤ n ∧ 1 ≤ q ∧ q < r ∧ r < i) ∨
  (1 ≤ p ∧ p < q ∧ q < r ∧ r < i)

/-- An edge of linear length at least `4`. -/
def Long (e : Edge) : Prop := e.1 + 4 ≤ e.2

/-- Every long chord of the star lies in `G`. -/
def StarLongIn (G : Finset Edge) (i p q r : ℕ) : Prop :=
  ∀ e ∈ star3 i p q r, Long e → e ∈ G

/-- Disjoint and not nested. -/
def OK (e f : Edge) : Prop := Disj e f ∧ ¬ Nested e f

theorem OK.symm {e f : Edge} (h : OK e f) : OK f e := by
  unfold OK Disj Nested at *; omega

/-- Four edges of `G`, pairwise disjoint and non-nested, contradict `NoNN 4 G`. -/
theorem NoNN.four {G : Finset Edge} (h : NoNN 4 G) {e f g k : Edge}
    (he : e ∈ G) (hf : f ∈ G) (hg : g ∈ G) (hk : k ∈ G)
    (hef : OK e f) (heg : OK e g) (hek : OK e k) (hfg : OK f g) (hfk : OK f k) (hgk : OK g k) :
    False := by
  have ne : ∀ {x y : Edge}, OK x y → x ≠ y := fun hxy => hxy.1.ne
  apply h {e, f, g, k}
  · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair (ne hgk)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨ne hfg, ne hfk⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨ne hef, ne heg, ne hek⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | assumption | exact OK.symm ‹_›

theorem edge_lt {x y : ℕ} (h : x < y) : edge x y = (x, y) := by
  simp [edge, Nat.min_eq_left h.le, Nat.max_eq_right h.le]

theorem edge_gt {x y : ℕ} (h : y < x) : edge x y = (y, x) := by
  simp [edge, Nat.min_eq_right h.le, Nat.max_eq_left h.le]

/-- Membership of a long star chord, in the orientation `x < y`. -/
theorem StarLongIn.mem {G : Finset Edge} {i p q r x y : ℕ} (h : StarLongIn G i p q r)
    (hmem : edge x y ∈ star3 i p q r) (hxy : x + 4 ≤ y) : (x, y) ∈ G := by
  have := h _ hmem; rw [edge_lt (by omega)] at this; exact this (by simp [Long]; omega)

/-- Same, for a chord listed as `edge y x` with `x < y`. -/
theorem StarLongIn.mem' {G : Finset Edge} {i p q r x y : ℕ} (h : StarLongIn G i p q r)
    (hmem : edge y x ∈ star3 i p q r) (hxy : x + 4 ≤ y) : (x, y) ∈ G := by
  have := h _ hmem; rw [edge_gt (by omega)] at this; exact this (by simp [Long]; omega)

theorem star3_1 (i p q r : ℕ) : edge (i + 1) p ∈ star3 i p q r := by simp [star3]
theorem star3_2 (i p q r : ℕ) : edge (i + 2) q ∈ star3 i p q r := by simp [star3]
theorem star3_3 (i p q r : ℕ) : edge (i + 3) r ∈ star3 i p q r := by simp [star3]
theorem star3_4 (i p q r : ℕ) : edge i p ∈ star3 i p q r := by simp [star3]
theorem star3_5 (i p q r : ℕ) : edge (i + 1) q ∈ star3 i p q r := by simp [star3]
theorem star3_6 (i p q r : ℕ) : edge (i + 2) r ∈ star3 i p q r := by simp [star3]

/-- Discharge `OK` between two explicit edges by linear arithmetic. -/
macro "ok" : tactic => `(tactic| (unfold OK Disj Nested; simp only; omega))

/-- **Lemma M** (middle window), with the centre written `c = z + 3` (so the window is
`[z+2, z+5] = [c-1, c+2]`). If `(c-3,c), (c,c+3) ∈ G`, an edge `a ∈ G` lies in `[1, c-4]` and an
edge `b ∈ G` in `[c+4, n]`, then no placement of the star on `(c-1, c+2)` has all its long chords
in `G`. Cases: `p, q, r` all right: `(c-1,p), (c,q), (c+1,r), a`; `q, r` left:
`(q,c+1), (r,c+2), (c,c+3), b`; `p, q` right and `r` left with `q ≥ c+5`: `(c-1,p), (c+1,q),
(c-3,c), a`; with `q = c+4` (so `p = c+3`): `(c-1,c+3), (c-3,c), a, b`. -/
theorem lemmaM {n z p q r : ℕ} {G : Finset Edge} {a b : Edge} (hG : NoNN 4 G)
    (h1 : (z, z + 3) ∈ G) (h2 : (z + 3, z + 6) ∈ G) (ha : a ∈ G) (hb : b ∈ G)
    (ha' : a.1 < a.2 ∧ a.2 < z) (hb' : z + 7 ≤ b.1 ∧ b.1 < b.2)
    (hpos : StarPos n (z + 2) p q r) (hS : StarLongIn G (z + 2) p q r) : False := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; simp only at ha' hb'
  rcases hpos with ⟨h3, h4, h5, h6⟩ | ⟨h3, h4, h5, h6, h7⟩ | ⟨h3, h4, h6, h7, h8⟩ | ⟨h3, h4, h5, h6⟩
  · have e1 := hS.mem (star3_4 _ p q r) (by omega)
    have e2 := hS.mem (star3_5 _ p q r) (by omega)
    have e3 := hS.mem (star3_6 _ p q r) (by omega)
    exact hG.four e1 e2 e3 ha (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
  · by_cases hq : z + 8 ≤ q
    · have e1 := hS.mem (star3_4 _ p q r) (by omega)
      have e2 := hS.mem (star3_2 _ p q r) (by omega)
      exact hG.four e1 e2 h1 ha (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
    · have e1 := hS.mem (star3_4 _ p q r) (by omega)
      exact hG.four e1 h1 ha hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
  all_goals
    have e1 := hS.mem' (star3_2 _ p q r) (by omega)
    have e2 := hS.mem' (star3_3 _ p q r) (by omega)
    exact hG.four e1 e2 h2 hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)

/-- **Lemma E** (end window `[c-1, c+2]`, `c = z + 3`; the note's Lemma 4.1, in the weakened form
noted in review: only `(c-3,c)` and `(c,c+2)` are needed). If `a, b ∈ G` are disjoint and
non-nested with all ends at least `c+4`, no placement of the star on `(c-1,c+2)` has all its long
chords in `G`. Cases: `p` right and left of `a, b`: `(c-1,p), (c-3,c), a, b`; `r ≤ c-3`:
`(r,c+1), (c,c+2), a, b`; `r = c-2`, `q` left: `(q,c), (c-2,c+2), a, b`; `r = c-2`, `p, q` right
beyond `a, b`: `(c-1,p), (c+1,q), (c-2,c+2), (c-3,c)`; all right beyond `a, b`:
`(c-1,p), (c+1,q), (c+2,r), (c-3,c)`. -/
theorem lemmaE {n z p q r : ℕ} {G : Finset Edge} {a b : Edge} (hG : NoNN 4 G)
    (h1 : (z, z + 3) ∈ G) (h2 : (z + 3, z + 5) ∈ G) (ha : a ∈ G) (hb : b ∈ G) (hab : OK a b)
    (ha' : z + 7 ≤ a.1 ∧ a.1 < a.2) (hb' : z + 7 ≤ b.1 ∧ b.1 < b.2)
    (hpos : StarPos n (z + 2) p q r) (hS : StarLongIn G (z + 2) p q r) : False := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; simp only at ha' hb'
  unfold OK Disj Nested at hab; simp only at hab
  by_cases hp : z + 5 < p ∧ p < a1 ∧ p < b1
  · have e1 := hS.mem (star3_4 _ p q r) (by omega)
    exact hG.four e1 h1 ha hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
  rcases hpos with ⟨h3, h4, h5, h6⟩ | ⟨h3, h4, h5, h6, h7⟩ | ⟨h3, h4, h6, h7, h8⟩ | ⟨h3, h4, h5, h6⟩
  · -- all right, p beyond a or b
    have e1 := hS.mem (star3_4 _ p q r) (by omega)
    have e2 := hS.mem (star3_2 _ p q r) (by omega)
    have e3 := hS.mem (star3_3 _ p q r) (by omega)
    exact hG.four e1 e2 e3 h1 (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
  all_goals
    by_cases hr : r + 3 ≤ z + 3
    · have e1 := hS.mem' (star3_6 _ p q r) (by omega)
      exact hG.four e1 h2 ha hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
    · have hr' : r = z + 1 := by omega
      subst hr'
      first
        | (-- q left
           have hF := hS.mem (star3_3 _ p q (z + 1)) (by omega)
           by_cases hq : q = z
           · subst hq; omega
           · have eC := hS.mem' (star3_5 _ p q (z + 1)) (by omega)
             exact hG.four eC hF ha hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok))
        | (-- p, q right beyond a or b
           have e1 := hS.mem (star3_4 _ p q (z + 1)) (by omega)
           have e2 := hS.mem (star3_2 _ p q (z + 1)) (by omega)
           have hF := hS.mem' (star3_3 _ p q (z + 1)) (by omega)
           exact hG.four e1 e2 hF h1 (by ok) (by ok) (by ok) (by ok) (by ok) (by ok))
        | (-- q left with q = z: (q, c) is (c-3, c)
           have hF := hS.mem' (star3_3 _ p q (z + 1)) (by omega)
           by_cases hq : q = z
           · subst hq; exact hG.four h1 hF ha hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
           · have eC := hS.mem' (star3_5 _ p q (z + 1)) (by omega)
             exact hG.four eC hF ha hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok))

/-- **End window `[c-2, c+1]`** (`c = z + 3`, star on `(c-2, c+1)`): with `(c-3,c), (c,c+2) ∈ G`
and `a, b ∈ G` disjoint, non-nested, all ends at least `c+3`. Cases: `r` left:
`(r,c+1), (c,c+2), a, b`; all right with `r = c+4`: `(c-3,c), (c-2,c+2), a, b`; all right with
`r ≥ c+5`: `(c-3,c), (c-2,p), (c-1,q), (c+1,r)`. -/
theorem endWindowA {n z p q r : ℕ} {G : Finset Edge} {a b : Edge} (hG : NoNN 4 G)
    (h1 : (z, z + 3) ∈ G) (h2 : (z + 3, z + 5) ∈ G) (ha : a ∈ G) (hb : b ∈ G) (hab : OK a b)
    (ha' : z + 6 ≤ a.1 ∧ a.1 < a.2) (hb' : z + 6 ≤ b.1 ∧ b.1 < b.2)
    (hpos : StarPos n (z + 1) p q r) (hS : StarLongIn G (z + 1) p q r) : False := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; simp only at ha' hb'
  unfold OK Disj Nested at hab; simp only at hab
  rcases hpos with ⟨h3, h4, h5, h6⟩ | ⟨h3, h4, h5, h6, h7⟩ | ⟨h3, h4, h6, h7, h8⟩ | ⟨h3, h4, h5, h6⟩
  · by_cases hr : r = z + 7
    · subst hr
      have e1 := hS.mem (star3_4 _ p q (z + 7)) (by omega)
      exact hG.four h1 e1 ha hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
    · have e1 := hS.mem (star3_4 _ p q r) (by omega)
      have e2 := hS.mem (star3_5 _ p q r) (by omega)
      have e3 := hS.mem (star3_3 _ p q r) (by omega)
      exact hG.four h1 e1 e2 e3 (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
  all_goals
    have e1 := hS.mem' (star3_3 _ p q r) (by omega)
    exact hG.four e1 h2 ha hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)

/-- **End window `[c-1, c+2]`, second form** (`c = z + 3`): with `(c-2,c), (c,c+3) ∈ G` and
`a, b ∈ G` disjoint, non-nested, all ends at least `c+4`. Cases: `r` left:
`(r,c+2), (c,c+3), a, b`; all right with `p = c+3`: `(c-2,c), (c-1,c+3), a, b`; all right with
`p ≥ c+4`: `(c-2,c), (c-1,p), (c+1,q), (c+2,r)`. -/
theorem endWindowB {n z p q r : ℕ} {G : Finset Edge} {a b : Edge} (hG : NoNN 4 G)
    (h1 : (z + 1, z + 3) ∈ G) (h2 : (z + 3, z + 6) ∈ G) (ha : a ∈ G) (hb : b ∈ G) (hab : OK a b)
    (ha' : z + 7 ≤ a.1 ∧ a.1 < a.2) (hb' : z + 7 ≤ b.1 ∧ b.1 < b.2)
    (hpos : StarPos n (z + 2) p q r) (hS : StarLongIn G (z + 2) p q r) : False := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; simp only at ha' hb'
  unfold OK Disj Nested at hab; simp only at hab
  rcases hpos with ⟨h3, h4, h5, h6⟩ | ⟨h3, h4, h5, h6, h7⟩ | ⟨h3, h4, h6, h7, h8⟩ | ⟨h3, h4, h5, h6⟩
  · by_cases hp : p = z + 6
    · subst hp
      have e1 := hS.mem (star3_4 _ (z + 6) q r) (by omega)
      exact hG.four h1 e1 ha hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
    · have e1 := hS.mem (star3_4 _ p q r) (by omega)
      have e2 := hS.mem (star3_2 _ p q r) (by omega)
      have e3 := hS.mem (star3_3 _ p q r) (by omega)
      exact hG.four h1 e1 e2 e3 (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
  all_goals
    have e1 := hS.mem' (star3_3 _ p q r) (by omega)
    exact hG.four e1 h2 ha hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)

/-- **Close pair at distance `1`** (centres `c = z+3` and `c+1`, window `[c-1, c+2]`): uses
`(c-2,c), (c,c+3), (c+1,c+4) ∈ G` and an edge `b ∈ G` with ends at least `c+5`. Cases: `r` left:
`(r,c+2), (c,c+3), (c+1,c+4), b`; `p = c+3`: `(c-2,c), (c-1,c+3), (c+1,c+4), b`; `p ≥ c+4`:
`(c-2,c), (c-1,p), (c+1,q), (c+2,r)`. -/
theorem closePair1 {n z p q r : ℕ} {G : Finset Edge} {b : Edge} (hG : NoNN 4 G)
    (h1 : (z + 1, z + 3) ∈ G) (h2 : (z + 3, z + 6) ∈ G) (h3 : (z + 4, z + 7) ∈ G) (hb : b ∈ G)
    (hb' : z + 8 ≤ b.1 ∧ b.1 < b.2)
    (hpos : StarPos n (z + 2) p q r) (hS : StarLongIn G (z + 2) p q r) : False := by
  obtain ⟨b1, b2⟩ := b; simp only at hb'
  rcases hpos with ⟨h4, h5, h6, h7⟩ | ⟨h4, h5, h6, h7, h8⟩ | ⟨h4, h5, h7, h8, h9⟩ | ⟨h4, h5, h6, h7⟩
  · by_cases hp : p = z + 6
    · subst hp
      have e1 := hS.mem (star3_4 _ (z + 6) q r) (by omega)
      exact hG.four h1 e1 h3 hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
    · have e1 := hS.mem (star3_4 _ p q r) (by omega)
      have e2 := hS.mem (star3_2 _ p q r) (by omega)
      have e3 := hS.mem (star3_3 _ p q r) (by omega)
      exact hG.four h1 e1 e2 e3 (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
  all_goals
    have e1 := hS.mem' (star3_3 _ p q r) (by omega)
    exact hG.four e1 h2 h3 hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)

/-- **Close pair at distance `2`** (centres `c = z+3` and `c+2`, window `[c-2, c+1]`): uses
`(c-3,c), (c,c+3), (c+2,c+4) ∈ G` and an edge `b ∈ G` with ends at least `c+6`. Cases: `r` left:
`(r,c+1), (c,c+3), (c+2,c+4), b`; all right with `r = c+4`: `(c-3,c), (c-1,c+3), (c+2,c+4), b`;
all right with `r ≥ c+5`: `(c-3,c), (c-2,p), (c-1,q), (c+1,r)`. -/
theorem closePair2 {n z p q r : ℕ} {G : Finset Edge} {b : Edge} (hG : NoNN 4 G)
    (h1 : (z, z + 3) ∈ G) (h2 : (z + 3, z + 6) ∈ G) (h3 : (z + 5, z + 7) ∈ G) (hb : b ∈ G)
    (hb' : z + 9 ≤ b.1 ∧ b.1 < b.2)
    (hpos : StarPos n (z + 1) p q r) (hS : StarLongIn G (z + 1) p q r) : False := by
  obtain ⟨b1, b2⟩ := b; simp only at hb'
  rcases hpos with ⟨h4, h5, h6, h7⟩ | ⟨h4, h5, h6, h7, h8⟩ | ⟨h4, h5, h7, h8, h9⟩ | ⟨h4, h5, h6, h7⟩
  · by_cases hr : r = z + 7
    · subst hr
      have e1 := hS.mem (star3_5 _ p q (z + 7)) (by omega)
      exact hG.four h1 e1 h3 hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
    · have e1 := hS.mem (star3_4 _ p q r) (by omega)
      have e2 := hS.mem (star3_5 _ p q r) (by omega)
      have e3 := hS.mem (star3_3 _ p q r) (by omega)
      exact hG.four h1 e1 e2 e3 (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)
  all_goals
    have e1 := hS.mem' (star3_3 _ p q r) (by omega)
    exact hG.four e1 h2 h3 hb (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)

/-- **The exceptional arrangement** (centres `a, a+4, a+8` with `a = z + 2`, missing edges
`(a-2,a+2)` and `(a+6,a+10)`). The star on `(a+2, a+5)` contains `(a-2,a+2)` as its chord `(p, i)`,
so `p = a-2`; then `q, r` lie in `[a-1, a+1]` and the chords `(a-2,a+3), (q,a+4), (r,a+5)` are
long, distinct from the missing edges, hence in `G`. They cross pairwise; with the unit edge
`(a+8, a+9)` they form a non-nested `4`-matching. -/
theorem exceptional {n z q r : ℕ} {G : Finset Edge} (hG : NoNN 4 G)
    (hu : (z + 10, z + 11) ∈ G)
    (hpos : StarPos n (z + 4) z q r)
    (hS : ∀ e ∈ star3 (z + 4) z q r, Long e → e ≠ (z, z + 4) → e ∈ G) : False := by
  have hq : z < q ∧ q < r ∧ r < z + 4 := by unfold StarPos at hpos; omega
  have m1 := hS _ (star3_1 _ z q r); rw [edge_gt (by omega)] at m1
  have m2 := hS _ (star3_2 _ z q r); rw [edge_gt (by omega)] at m2
  have m3 := hS _ (star3_3 _ z q r); rw [edge_gt (by omega)] at m3
  have e1 := m1 (by simp [Long] <;> omega) (by simp)
  have e2 := m2 (by simp [Long] <;> omega) (by simp <;> omega)
  have e3 := m3 (by simp [Long] <;> omega) (by simp <;> omega)
  exact hG.four e1 e2 e3 hu (by ok) (by ok) (by ok) (by ok) (by ok) (by ok)

/-- **The counting step.** If every star in a family `F` contains an edge of `X`, and every edge
of `X` lies in at most two members of `F`, then `|F| ≤ 2|X|`. (In the note: each good star of the
`3`-triangulation must contain a missing long edge, and every edge lies in at most two `3`-stars.) -/
theorem card_le_two_mul (F : Finset (Finset Edge)) (X : Finset Edge)
    (hmeet : ∀ s ∈ F, ∃ e ∈ X, e ∈ s) (hdeg : ∀ e ∈ X, (F.filter (fun s => e ∈ s)).card ≤ 2) :
    F.card ≤ 2 * X.card := by
  have hsub : F ⊆ X.biUnion (fun e => F.filter (fun s => e ∈ s)) := by
    intro s hs; obtain ⟨e, he, hes⟩ := hmeet s hs
    exact Finset.mem_biUnion.2 ⟨e, he, Finset.mem_filter.2 ⟨hs, hes⟩⟩
  calc F.card ≤ (X.biUnion (fun e => F.filter (fun s => e ∈ s))).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ X, (F.filter (fun s => e ∈ s)).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ X, 2 := Finset.sum_le_sum hdeg
    _ = 2 * X.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end NonNested
