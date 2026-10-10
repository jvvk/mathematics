import Mathlib

/-!
# Labelling binary trees by powers of two: definitions and transport lemmas

A rooted tree in which every vertex has at most two children (children unordered) is labelled by a set `S`
of natural numbers, bijectively, with the root labelled `r` and every child labelled its parent's label plus
a power of two. `Fits t S r` records such a labelling. The question of MathOverflow 304266 is whether every
tree with `n` vertices fits `{0, …, n - 1}` with root `0`.
-/

namespace PowTwoTrees

/-- Rooted trees with at most two children per vertex. `two a b` and `two b a` are the same tree; the
lemma `fits_two_comm` makes the order irrelevant. -/
inductive BT
  | leaf : BT
  | one : BT → BT
  | two : BT → BT → BT
  deriving DecidableEq

/-- Number of vertices. -/
def BT.size : BT → ℕ
  | .leaf => 1
  | .one c => c.size + 1
  | .two a b => a.size + b.size + 1

lemma BT.size_pos (t : BT) : 0 < t.size := by
  cases t <;> simp [BT.size]

/-- `Fits t S r`: the tree `t` is labelled bijectively by `S`, its root by `r`, and every child by its
parent's label plus a power of two. -/
inductive Fits : BT → Finset ℕ → ℕ → Prop
  | leaf (r : ℕ) : Fits .leaf {r} r
  | one {c : BT} {S : Finset ℕ} {r : ℕ} (k : ℕ) :
      Fits c S (r + 2 ^ k) → r ∉ S → Fits (.one c) (insert r S) r
  | two {a b : BT} {A B : Finset ℕ} {r : ℕ} (i j : ℕ) :
      Fits a A (r + 2 ^ i) → Fits b B (r + 2 ^ j) → Disjoint A B → r ∉ A → r ∉ B →
      Fits (.two a b) (insert r (A ∪ B)) r

/-- A labelling in the sense of the question. -/
def Labelled (t : BT) : Prop := Fits t (Finset.range t.size) 0

/-! ## Basic facts -/

/-- The root label is in the set, every label is at least the root label, and the set has as many
elements as the tree has vertices. -/
theorem Fits.basic {t : BT} {S : Finset ℕ} {r : ℕ} (h : Fits t S r) :
    r ∈ S ∧ (∀ x ∈ S, r ≤ x) ∧ S.card = t.size := by
  induction h with
  | leaf r => simp [BT.size]
  | @one c S r k _ hr ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨Finset.mem_insert_self _ _, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · have := h2 x hx; have := Nat.two_pow_pos k; omega
    · rw [Finset.card_insert_of_notMem hr, h3]; rfl
  | @two a b A B r i j _ _ hd hrA hrB iha ihb =>
    obtain ⟨a1, a2, a3⟩ := iha
    obtain ⟨b1, b2, b3⟩ := ihb
    refine ⟨Finset.mem_insert_self _ _, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      rcases Finset.mem_union.mp hx with hx | hx
      · have := a2 x hx; have := Nat.two_pow_pos i; omega
      · have := b2 x hx; have := Nat.two_pow_pos j; omega
    · have hr : r ∉ A ∪ B := by simp [hrA, hrB]
      rw [Finset.card_insert_of_notMem hr, Finset.card_union_of_disjoint hd, a3, b3]; rfl

/-- The order of the two children does not matter. -/
theorem fits_two_comm {a b : BT} {S : Finset ℕ} {r : ℕ} (h : Fits (.two a b) S r) :
    Fits (.two b a) S r := by
  cases h with
  | two i j ha hb hd hrA hrB =>
    have := Fits.two j i hb ha hd.symm hrB hrA
    rwa [Finset.union_comm] at this

/-! ## Transport: affine maps `x ↦ 2^m x + c` -/

/-- Adding `d` to every label. -/
theorem Fits.shift {t : BT} {S : Finset ℕ} {r : ℕ} (h : Fits t S r) (d : ℕ) :
    Fits t (S.image (· + d)) (r + d) := by
  induction h with
  | leaf r => simpa using Fits.leaf (r + d)
  | @one c S r k _ hr ih =>
    have e : r + 2 ^ k + d = r + d + 2 ^ k := by ring
    rw [e] at ih
    have := Fits.one k ih (by simpa using hr)
    simpa [Finset.image_insert] using this
  | @two a b A B r i j _ _ hd hrA hrB iha ihb =>
    have ea : r + 2 ^ i + d = r + d + 2 ^ i := by ring
    have eb : r + 2 ^ j + d = r + d + 2 ^ j := by ring
    rw [ea] at iha
    rw [eb] at ihb
    have hinj : Function.Injective (· + d : ℕ → ℕ) := fun x y h => by simpa using h
    have := Fits.two i j iha ihb ((Finset.disjoint_image hinj).mpr hd) (by simpa using hrA)
      (by simpa using hrB)
    simpa [Finset.image_insert, Finset.image_union] using this

/-- Doubling every label. -/
theorem Fits.double {t : BT} {S : Finset ℕ} {r : ℕ} (h : Fits t S r) :
    Fits t (S.image (2 * ·)) (2 * r) := by
  induction h with
  | leaf r => simpa using Fits.leaf (2 * r)
  | @one c S r k _ hr ih =>
    have e : 2 * (r + 2 ^ k) = 2 * r + 2 ^ (k + 1) := by ring
    rw [e] at ih
    have := Fits.one (k + 1) ih (by simpa using hr)
    simpa [Finset.image_insert] using this
  | @two a b A B r i j _ _ hd hrA hrB iha ihb =>
    have ea : 2 * (r + 2 ^ i) = 2 * r + 2 ^ (i + 1) := by ring
    have eb : 2 * (r + 2 ^ j) = 2 * r + 2 ^ (j + 1) := by ring
    rw [ea] at iha
    rw [eb] at ihb
    have hinj : Function.Injective (2 * · : ℕ → ℕ) := fun x y h => by simpa using h
    have := Fits.two (i + 1) (j + 1) iha ihb ((Finset.disjoint_image hinj).mpr hd)
      (by simpa using hrA) (by simpa using hrB)
    simpa [Finset.image_insert, Finset.image_union] using this

/-- Subtracting `d` from every label, when every label is at least `d`. -/
theorem Fits.unshift {t : BT} {S : Finset ℕ} {r : ℕ} (h : Fits t S r) (d : ℕ) (hd : ∀ x ∈ S, d ≤ x) :
    Fits t (S.image (· - d)) (r - d) := by
  induction h with
  | leaf r => simpa using Fits.leaf (r - d)
  | @one c S r k hc hr ih =>
    have hS : ∀ x ∈ S, d ≤ x := fun x hx => hd x (Finset.mem_insert_of_mem hx)
    have hrd : d ≤ r := hd r (Finset.mem_insert_self _ _)
    have e : r + 2 ^ k - d = r - d + 2 ^ k := by have := Nat.two_pow_pos k; omega
    have ih' := ih hS
    rw [e] at ih'
    have hr' : r - d ∉ S.image (· - d) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro x hx hxe
      have := hS x hx
      exact hr (by have : x = r := by omega
                   simpa [this] using hx)
    have := Fits.one k ih' hr'
    simpa [Finset.image_insert] using this
  | @two a b A B r i j ha hb hdAB hrA hrB iha ihb =>
    have hA : ∀ x ∈ A, d ≤ x := fun x hx =>
      hd x (Finset.mem_insert_of_mem (Finset.mem_union_left _ hx))
    have hB : ∀ x ∈ B, d ≤ x := fun x hx =>
      hd x (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
    have hrd : d ≤ r := hd r (Finset.mem_insert_self _ _)
    have ea : r + 2 ^ i - d = r - d + 2 ^ i := by have := Nat.two_pow_pos i; omega
    have eb : r + 2 ^ j - d = r - d + 2 ^ j := by have := Nat.two_pow_pos j; omega
    have iha' := iha hA
    have ihb' := ihb hB
    rw [ea] at iha'
    rw [eb] at ihb'
    have hdis : Disjoint (A.image (· - d)) (B.image (· - d)) := by
      rw [Finset.disjoint_left]
      intro y hyA hyB
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyA
      obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hyB
      have h1 := hA x hx
      have h2 := hB z hz
      have : z = x := by omega
      subst this
      exact Finset.disjoint_left.mp hdAB hx hz
    have hra : r - d ∉ A.image (· - d) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro x hx hxe
      have := hA x hx
      exact hrA (by have : x = r := by omega
                    simpa [this] using hx)
    have hrb : r - d ∉ B.image (· - d) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro x hx hxe
      have := hB x hx
      exact hrB (by have : x = r := by omega
                    simpa [this] using hx)
    have := Fits.two i j iha' ihb' hdis hra hrb
    simpa [Finset.image_insert, Finset.image_union] using this

end PowTwoTrees
