/-
  Shuffle anti-squares exist of every even length ≥ 34 (explicit family U k).

  A binary word is a *shuffle square* if it is an interleaving of two copies of one word; an even
  word is a *shuffle anti-square* if none of its rotations is a shuffle square (Grytczuk, Pawlik,
  Pleszczyński, "Variations on shuffle squares", arXiv 2308.13882, Conjecture 1).

  Plain Lean 4 (core only). The combinatorial content is one reduction: a shuffle square yields a
  splitting of each run of zeros between the two copies with equal zero-run lists (`ZS`). Every
  remaining step is linear arithmetic, discharged by `omega`.
-/

/-- `Shuffle u v w`: `w` is an interleaving of `u` and `v`. -/
inductive Shuffle : List Bool → List Bool → List Bool → Prop
  | nil : Shuffle [] [] []
  | left {a : Bool} {u v w : List Bool} : Shuffle u v w → Shuffle (a :: u) v (a :: w)
  | right {a : Bool} {u v w : List Bool} : Shuffle u v w → Shuffle u (a :: v) (a :: w)

def IsShuffleSquare (w : List Bool) : Prop := ∃ u, Shuffle u u w

/-- Add one to the head of a list (the head of a zero-run list is the open run). -/
def incHead : List Nat → List Nat
  | [] => [1]
  | h :: t => (h + 1) :: t

/-- Zero-run lengths: `zruns (0^e₀ 1 0^e₁ 1 ⋯ 1 0^eₘ) = [e₀, …, eₘ]` (`false` = 0, `true` = 1). -/
def zruns : List Bool → List Nat
  | [] => [0]
  | false :: l => incHead (zruns l)
  | true :: l => 0 :: zruns l

/-- `ZS cu cv W U V`: the zero runs `W` of a word split between two copies whose zero-run lists are
    `U` and `V`; `cu`, `cv` zeros are already in the copies' currently open runs. Each constructor
    handles one run `e` of `W`: it gives `x` zeros to the first copy and `y` to the second, and the
    `1` that follows (if any) goes to the first copy (`toU`) or the second (`toV`). -/
inductive ZS : Nat → Nat → List Nat → List Nat → List Nat → Prop
  | last {cu cv e x y u v : Nat} :
      x + y = e → u = cu + x → v = cv + y → ZS cu cv [e] [u] [v]
  | toU {cu cv e x y u c : Nat} {W U V : List Nat} :
      x + y = e → u = cu + x → c = cv + y → ZS 0 c W U V → ZS cu cv (e :: W) (u :: U) V
  | toV {cu cv e x y v c : Nat} {W U V : List Nat} :
      x + y = e → v = cv + y → c = cu + x → ZS c 0 W U V → ZS cu cv (e :: W) U (v :: V)

/-- One more zero in the first copy's open run. -/
theorem ZS.bumpU {cu cv : Nat} {W U V : List Nat} (h : ZS cu cv W U V) :
    ZS (cu + 1) cv W (incHead U) V := by
  induction h with
  | last hxy hu hv => exact .last hxy (by omega) hv
  | toU hxy hu hc h' _ => exact .toU hxy (by omega) hc h'
  | toV hxy hv hc _ ih => exact .toV hxy hv (by omega) ih

theorem ZS.bumpV {cu cv : Nat} {W U V : List Nat} (h : ZS cu cv W U V) :
    ZS cu (cv + 1) W U (incHead V) := by
  induction h with
  | last hxy hu hv => exact .last hxy hu (by omega)
  | toU hxy hu hc _ ih => exact .toU hxy hu (by omega) ih
  | toV hxy hv hc h' _ => exact .toV hxy (by omega) hc h'

/-- A leading zero of the word that goes to the first copy. -/
theorem ZS.zeroU {W U V : List Nat} (h : ZS 0 0 W U V) : ZS 0 0 (incHead W) (incHead U) V := by
  cases h with
  | @last _ _ e x y u v hxy hu hv =>
    exact .last (x := x + 1) (y := y) (by omega) (by simp; omega) hv
  | @toU _ _ e x y u c W U V hxy hu hc h' =>
    exact .toU (x := x + 1) (y := y) (by omega) (by omega) hc h'
  | @toV _ _ e x y v c W U V hxy hv hc h' =>
    exact .toV (x := x + 1) (y := y) (c := c + 1) (by omega) hv (by omega) h'.bumpU

theorem ZS.zeroV {W U V : List Nat} (h : ZS 0 0 W U V) : ZS 0 0 (incHead W) U (incHead V) := by
  cases h with
  | @last _ _ e x y u v hxy hu hv =>
    exact .last (x := x) (y := y + 1) (by omega) hu (by simp; omega)
  | @toU _ _ e x y u c W U V hxy hu hc h' =>
    exact .toU (x := x) (y := y + 1) (c := c + 1) (by omega) hu (by omega) h'.bumpV
  | @toV _ _ e x y v c W U V hxy hv hc h' =>
    exact .toV (x := x) (y := y + 1) (by omega) (by omega) hc h'

/-- The reduction: an interleaving of `u` and `v` into `w` splits the zero runs of `w`. -/
theorem Shuffle.zs {u v w : List Bool} (h : Shuffle u v w) : ZS 0 0 (zruns w) (zruns u) (zruns v) := by
  induction h with
  | nil => exact .last (x := 0) (y := 0) rfl rfl rfl
  | @left a u v w _ ih =>
    cases a with
    | false => exact ih.zeroU
    | true => exact .toU (x := 0) (y := 0) rfl rfl rfl ih
  | @right a u v w _ ih =>
    cases a with
    | false => exact ih.zeroV
    | true => exact .toV (x := 0) (y := 0) rfl rfl rfl ih

theorem IsShuffleSquare.zs {w : List Bool} (h : IsShuffleSquare w) :
    ∃ R, ZS 0 0 (zruns w) R R := by
  obtain ⟨u, hu⟩ := h
  exact ⟨zruns u, hu.zs⟩

/-- `zruns` of a concatenation: the last run of `a` merges with the first run of `b`. -/
theorem zruns_append (a b : List Bool) :
    ∃ A x y B, zruns a = A ++ [x] ∧ zruns b = y :: B ∧ zruns (a ++ b) = A ++ (x + y) :: B := by
  induction a with
  | nil =>
    cases hb : zruns b with
    | nil => cases b with
      | nil => simp [zruns] at hb
      | cons c l => cases c <;> simp [zruns] at hb <;> cases h : zruns l <;> simp_all [incHead]
    | cons y B => exact ⟨[], 0, y, B, rfl, rfl, by simp [hb]⟩
  | cons c a ih =>
    obtain ⟨A, x, y, B, ha, hb, hab⟩ := ih
    cases c with
    | true => exact ⟨0 :: A, x, y, B, by simp [zruns, ha], hb, by simp [zruns, hab]⟩
    | false =>
      cases A with
      | nil => exact ⟨[], x + 1, y, B, by simp [zruns, ha, incHead], hb,
                  by simp [zruns, hab, incHead]; omega⟩
      | cons h t => exact ⟨(h + 1) :: t, x, y, B, by simp [zruns, ha, incHead], hb,
                  by simp [zruns, hab, incHead]⟩

/-! ### Words given by their zero runs -/

/-- `ofGaps [e₀, …, eₘ] = 0^e₀ 1 0^e₁ 1 ⋯ 1 0^eₘ`. -/
def ofGaps : List Nat → List Bool
  | [] => []
  | [e] => List.replicate e false
  | e :: f :: G => List.replicate e false ++ true :: ofGaps (f :: G)

theorem zruns_replicate (e : Nat) : zruns (List.replicate e false) = [e] := by
  induction e with
  | zero => rfl
  | succ e ih => simp [List.replicate_succ, zruns, ih, incHead]

theorem zruns_replicate_cons (e : Nat) (l : List Bool) :
    zruns (List.replicate e false ++ true :: l) = e :: zruns l := by
  induction e with
  | zero => rfl
  | succ e ih => simp [List.replicate_succ, zruns, ih, incHead]

theorem zruns_ofGaps : ∀ (e : Nat) (G : List Nat), zruns (ofGaps (e :: G)) = e :: G
  | e, [] => zruns_replicate e
  | e, f :: G => by rw [ofGaps, zruns_replicate_cons, zruns_ofGaps f G]

/-! ### Rotations -/

/-- Join two zero-run lists: the last run of the first merges with the first run of the second. -/
def glue : List Nat → List Nat → List Nat
  | [], B => B
  | [a], [] => [a]
  | [a], b :: B => (a + b) :: B
  | a :: a' :: A, B => a :: glue (a' :: A) B

theorem zruns_ne_nil : ∀ w : List Bool, zruns w ≠ []
  | [] => by simp [zruns]
  | true :: _ => by simp [zruns]
  | false :: l => by
    have := zruns_ne_nil l
    cases h : zruns l with
    | nil => exact absurd h this
    | cons _ _ => simp [zruns, h, incHead]

theorem glue_incHead : ∀ (A B : List Nat), A ≠ [] → glue (incHead A) B = incHead (glue A B)
  | [a], [] => by simp [glue, incHead]
  | [a], b :: B => by simp [glue, incHead]; omega
  | a :: a' :: A, B => by simp [glue, incHead]
  | [], _ => by simp

theorem zruns_append_glue (a b : List Bool) : zruns (a ++ b) = glue (zruns a) (zruns b) := by
  induction a with
  | nil =>
    have := zruns_ne_nil b
    cases h : zruns b with
    | nil => exact absurd h this
    | cons c B => simp [zruns, glue, h]
  | cons c a ih =>
    cases c with
    | false => rw [List.cons_append, zruns, zruns, ih, glue_incHead _ _ (zruns_ne_nil a)]
    | true =>
      have := zruns_ne_nil a
      cases h : zruns a with
      | nil => exact absurd h this
      | cons d A => simp only [List.cons_append, zruns, ih, h, glue]
