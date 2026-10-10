import Mathlib

/-!
# Wandering over the divisors of a power of ten: the game and its basic strategies

Board `{0, …, n}²`; the square `(x, y)` stands for the divisor `2^x 5^y` of `10^n`. The moves are
`E = (1, 0)`, `N = (0, 1)` and `D = (-1, -1)`. A square may not be named twice; the player to move with no
legal move loses. Alice moves first, Bob second.

`BobWins n V p` says: Alice is to move with the piece at `p`, the named squares are `V`, and Bob has a
winning strategy. It is an inductive predicate, so it records a finite strategy tree: for every legal move
of Alice, Bob has a legal reply after which Bob still wins. If Alice has no legal move the condition holds
vacuously, which is the rule "the player who cannot move loses".
-/

namespace DivisorWalk

abbrev Sq := ℕ × ℕ

/-- `q` is reached from `p` by one move that stays on the board `{0, …, n}²`. -/
def Move (n : ℕ) (p q : Sq) : Prop :=
  q.1 ≤ n ∧ q.2 ≤ n ∧
    (q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1) ∨ (1 ≤ p.1 ∧ 1 ≤ p.2 ∧ q = (p.1 - 1, p.2 - 1)))

/-- Alice to move at `p` with named squares `V`: Bob has a winning strategy. The constructor names Bob's
reply `f q` to each legal move `q` of Alice. -/
inductive BobWins (n : ℕ) : Finset Sq → Sq → Prop
  | mk {V : Finset Sq} {p : Sq} (f : Sq → Sq)
      (hmove : ∀ q, Move n p q → q ∉ V → Move n q (f q))
      (hfree : ∀ q, Move n p q → q ∉ V → f q ∉ insert q V)
      (hwin : ∀ q, Move n p q → q ∉ V → BobWins n (insert (f q) (insert q V)) (f q)) :
      BobWins n V p

/-- The same condition with an existential reply. -/
theorem BobWins.of {n : ℕ} {V : Finset Sq} {p : Sq}
    (h : ∀ q, Move n p q → q ∉ V →
      ∃ r, Move n q r ∧ r ∉ insert q V ∧ BobWins n (insert r (insert q V)) r) :
    BobWins n V p := by
  classical
  let f : Sq → Sq := fun q => if hq : Move n p q ∧ q ∉ V then Classical.choose (h q hq.1 hq.2) else q
  have hf : ∀ q (hm : Move n p q) (hq : q ∉ V), f q = Classical.choose (h q hm hq) := by
    intro q hm hq; simp [f, hm, hq]
  refine BobWins.mk f ?_ ?_ ?_
  · intro q hm hq; rw [hf q hm hq]; exact (Classical.choose_spec (h q hm hq)).1
  · intro q hm hq; rw [hf q hm hq]; exact (Classical.choose_spec (h q hm hq)).2.1
  · intro q hm hq; rw [hf q hm hq]; exact (Classical.choose_spec (h q hm hq)).2.2

/-- Unfolding: every legal move of Alice has a winning reply. -/
theorem BobWins.reply {n : ℕ} {V : Finset Sq} {p : Sq} (h : BobWins n V p) :
    ∀ q, Move n p q → q ∉ V →
      ∃ r, Move n q r ∧ r ∉ insert q V ∧ BobWins n (insert r (insert q V)) r := by
  cases h with
  | mk f hm hf hw => exact fun q h1 h2 => ⟨f q, hm q h1 h2, hf q h1 h2, hw q h1 h2⟩

/-- Bob, to move at `q` with named squares `V`, has a reply that wins. -/
def BobAnswers (n : ℕ) (V : Finset Sq) (q : Sq) : Prop :=
  ∃ r, Move n q r ∧ r ∉ V ∧ BobWins n (insert r V) r

/-! ## Reflection in the diagonal -/

/-- The reflection `(x, y) ↦ (y, x)`; it swaps `E` and `N` and fixes `D`. -/
def sw (p : Sq) : Sq := (p.2, p.1)

@[simp] lemma sw_sw (p : Sq) : sw (sw p) = p := rfl

lemma sw_injective : Function.Injective sw := fun a b h => by
  simpa using congrArg sw h

lemma move_sw {n : ℕ} {p q : Sq} (h : Move n p q) : Move n (sw p) (sw q) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h2, h1, ?_⟩
  rcases h3 with h | h | ⟨a, b, h⟩
  · right; left; simp [h, sw]
  · left; simp [h, sw]
  · right; right; exact ⟨b, a, by simp [h, sw]⟩

lemma mem_image_sw {V : Finset Sq} {q : Sq} : q ∈ V.image sw ↔ sw q ∈ V := by
  constructor
  · rintro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    simpa using ha
  · intro h
    exact Finset.mem_image.mpr ⟨sw q, h, by simp⟩

/-- Reflecting a won position gives a won position. -/
theorem reflect {n : ℕ} {V : Finset Sq} {p : Sq} (h : BobWins n V p) :
    BobWins n (V.image sw) (sw p) := by
  induction h with
  | @mk V p f hmv hfr _ ih =>
    refine BobWins.of ?_
    intro q hm hq
    have hm' : Move n p (sw q) := by simpa using move_sw hm
    have hq' : sw q ∉ V := fun h => hq (mem_image_sw.mpr (by simpa using h))
    refine ⟨sw (f (sw q)), by simpa using move_sw (hmv _ hm' hq'), ?_, ?_⟩
    · intro hmem
      apply hfr _ hm' hq'
      rcases Finset.mem_insert.mp hmem with h | h
      · exact Finset.mem_insert.mpr (Or.inl (by simpa using congrArg sw h))
      · exact Finset.mem_insert.mpr (Or.inr (by simpa using mem_image_sw.mp h))
    · have : (insert (f (sw q)) (insert (sw q) V)).image sw
          = insert (sw (f (sw q))) (insert q (V.image sw)) := by
        simp [Finset.image_insert]
      simpa [this] using ih _ hm' hq'

/-! ## Lemma 2: sweeping the right-hand edge -/

/-- Lemma 2 of the note. Alice to move at `(n, y)`; `(n, y + 1)` is named or `y = n`; the squares
`(n, m), …, (n, y - 1)` are free; and `m = 0` or `(n - 1, m - 1)` is named. Then Bob wins. -/
theorem sweep (n : ℕ) :
    ∀ (k y m : ℕ) (V : Finset Sq), y - m ≤ k → m ≤ y → y ≤ n → (n, y) ∈ V →
      (y = n ∨ (n, y + 1) ∈ V) → (∀ j, m ≤ j → j < y → (n, j) ∉ V) →
      (m = 0 ∨ (n - 1, m - 1) ∈ V) → BobWins n V (n, y) := by
  intro k
  induction k with
  | zero =>
    intro y m V hk hmy hyn hp htop hfree hm
    have hym : y = m := by omega
    subst hym
    refine BobWins.of ?_
    intro q hmv hq
    obtain ⟨hq1, hq2, h | h | ⟨_, hy1, h⟩⟩ := hmv
    · simp [h] at hq1
    · rcases htop with ht | ht
      · simp [h] at hq2; omega
      · exact absurd (by simpa [h] using ht) hq
    · rcases hm with hm | hm
      · omega
      · exact absurd (by simpa [h] using hm) hq
  | succ k ih =>
    intro y m V hk hmy hyn hp htop hfree hm
    by_cases hym : y = m
    · exact ih y m V (by omega) hmy hyn hp htop hfree hm
    refine BobWins.of ?_
    intro q hmv hq
    obtain ⟨hq1, hq2, h | h | ⟨hn1, hy1, h⟩⟩ := hmv
    · simp [h] at hq1
    · rcases htop with ht | ht
      · simp [h] at hq2; omega
      · exact absurd (by simpa [h] using ht) hq
    · -- Alice stepped D to (n - 1, y - 1); Bob steps E to (n, y - 1).
      simp only at hn1 hy1
      subst h
      refine ⟨(n, y - 1), ⟨le_refl _, by omega, Or.inl (by simp; omega)⟩, ?_, ?_⟩
      · intro hmem
        rcases Finset.mem_insert.mp hmem with h' | h'
        · simp [Prod.ext_iff] at h'; omega
        · exact hfree (y - 1) (by omega) (by omega) h'
      · refine ih (y - 1) m _ (by omega) (by omega) (by omega) (Finset.mem_insert_self _ _) ?_ ?_ ?_
        · right
          have : y - 1 + 1 = y := by omega
          rw [this]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp)
        · intro j hj1 hj2 hmem
          rcases Finset.mem_insert.mp hmem with h' | h'
          · simp [Prod.ext_iff] at h'; omega
          rcases Finset.mem_insert.mp h' with h'' | h''
          · simp [Prod.ext_iff] at h''; omega
          · exact hfree j hj1 (by omega) h''
        · rcases hm with hm | hm
          · exact Or.inl hm
          · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))

/-- Lemma 2 for the top row, by reflection. -/
theorem sweep_top (n : ℕ) (x m : ℕ) (V : Finset Sq) (hmx : m ≤ x) (hxn : x ≤ n) (hp : (x, n) ∈ V)
    (hright : x = n ∨ (x + 1, n) ∈ V) (hfree : ∀ j, m ≤ j → j < x → (j, n) ∉ V)
    (hm : m = 0 ∨ (m - 1, n - 1) ∈ V) : BobWins n V (x, n) := by
  have h := sweep n (x - m) x m (V.image sw) le_rfl hmx hxn (mem_image_sw.mpr (by simpa [sw] using hp))
    (by rcases hright with h | h
        · exact Or.inl h
        · exact Or.inr (mem_image_sw.mpr (by simpa [sw] using h)))
    (fun j h1 h2 hmem => hfree j h1 h2 (by simpa [sw] using mem_image_sw.mp hmem))
    (by rcases hm with h | h
        · exact Or.inl h
        · exact Or.inr (mem_image_sw.mpr (by simpa [sw] using h)))
  have h2 := reflect h
  have hV : (V.image sw).image sw = V := by
    rw [Finset.image_image]; simp [Function.comp_def]
  simpa [hV, sw] using h2

/-! ## The diagonal climb -/

/-- Bob answers `E` with `N` and `N` with `E`. `F` is a fixed set of named squares that never lies just
above or to the right of the piece; every other named square lies in the box below and to the left of the
piece; and the square diagonally below is named (or off the board). `P` carries any further facts, which
only need to survive new names. The climb reaches the edge, where `hEnd` takes over. -/
theorem climb (n : ℕ) (F : Sq → Prop) (P : Finset Sq → Prop) (hP : ∀ V a, P V → P (insert a V))
    (Q : ℕ → ℕ → Prop) (hQ : ∀ x y, Q x y → Q (x + 1) (y + 1))
    (hEnd : ∀ (V : Finset Sq) (x y : ℕ), (x = n ∨ y = n) → x ≤ n → y ≤ n → Q x y → P V → (x, y) ∈ V →
      (∀ v ∈ V, F v ∨ (v.1 ≤ x ∧ v.2 ≤ y)) → (x = 0 ∨ y = 0 ∨ (x - 1, y - 1) ∈ V) →
      BobWins n V (x, y)) :
    ∀ (k x y : ℕ) (V : Finset Sq), 2 * n - x - y ≤ k → x ≤ n → y ≤ n → Q x y → P V → (x, y) ∈ V →
      (∀ u w, x ≤ u → y ≤ w → ¬ F (u + 1, w) ∧ ¬ F (u, w + 1) ∧ ¬ F (u + 1, w + 1)) →
      (∀ v ∈ V, F v ∨ (v.1 ≤ x ∧ v.2 ≤ y)) → (x = 0 ∨ y = 0 ∨ (x - 1, y - 1) ∈ V) →
      BobWins n V (x, y) := by
  intro k
  induction k with
  | zero =>
    intro x y V hk hx hy hQxy hPV hp hF hV hD
    exact hEnd V x y (by omega) hx hy hQxy hPV hp hV hD
  | succ k ih =>
    intro x y V hk hx hy hQxy hPV hp hF hV hD
    by_cases he : x = n ∨ y = n
    · exact hEnd V x y he hx hy hQxy hPV hp hV hD
    have hxn : x < n := by omega
    have hyn : y < n := by omega
    refine BobWins.of ?_
    intro q hmv hq
    obtain ⟨_, _, hstep⟩ := hmv
    -- the reply square and the facts about it
    have hrV : (x + 1, y + 1) ∉ V := by
      intro hmem
      rcases hV _ hmem with h | h
      · exact (hF x y le_rfl le_rfl).2.2 h
      · simp at h
    have hnext : ∀ q : Sq, (q = (x + 1, y) ∨ q = (x, y + 1)) → q ∉ V →
        ∃ r, Move n q r ∧ r ∉ insert q V ∧ BobWins n (insert r (insert q V)) r := by
      intro q hq' hqV
      refine ⟨(x + 1, y + 1), ?_, ?_, ?_⟩
      · rcases hq' with rfl | rfl
        · exact ⟨by simp; omega, by simp; omega, Or.inr (Or.inl rfl)⟩
        · exact ⟨by simp; omega, by simp; omega, Or.inl rfl⟩
      · intro hmem
        rcases Finset.mem_insert.mp hmem with h | h
        · rcases hq' with rfl | rfl <;> simp [Prod.ext_iff] at h
        · exact hrV h
      · refine ih (x + 1) (y + 1) _ (by omega) (by omega) (by omega) (hQ x y hQxy)
          (hP _ _ (hP _ _ hPV)) (Finset.mem_insert_self _ _) ?_ ?_ ?_
        · intro u w hu hw
          exact hF u w (by omega) (by omega)
        · intro v hv
          rcases Finset.mem_insert.mp hv with h | h
          · right; simp [h]
          rcases Finset.mem_insert.mp h with h' | h'
          · right; rcases hq' with rfl | rfl <;> simp [h'] <;> omega
          · rcases hV v h' with h'' | h''
            · left; exact h''
            · right; omega
        · right; right
          have e : (x + 1 - 1, y + 1 - 1) = (x, y) := by simp
          rw [e]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp)
    rcases hstep with h | h | ⟨h1, h2, h⟩
    · exact hnext q (Or.inl h) hq
    · exact hnext q (Or.inr h) hq
    · exfalso
      rcases hD with hD | hD | hD
      · simp at h1; omega
      · simp at h2; omega
      · exact hq (by simpa [h] using hD)

end DivisorWalk
