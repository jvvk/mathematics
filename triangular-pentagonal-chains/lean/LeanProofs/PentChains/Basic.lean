import Mathlib

/-!
# Pentagonal chains: definitions and the inflation lemma

Berlekamp and Guy (Crux Math. 46(8), 2020, pp. 344-345) conjecture that `1, …, n` can be ordered so that
adjacent sums are generalized pentagonal numbers `k(3k-1)/2` (`k ∈ ℤ`) for all `n ≥ 4`, and cyclically for
all `n ≥ 9`.

* `IsTri s` (here: `s` is generalized pentagonal, `2s = k(3k-1)` for some `k : ℤ`); `OddTri s`: odd such `s`.
  (Names kept from the triangular development so the step file transfers verbatim.)
* `tri_inflate` (the key identity): `2s = k(3k-1)` implies `2(49s + 2) = (7k-1)(3(7k-1)-1)`,
  i.e. `49 P_k + 2 = P_{7k-1}`.
* `f c v = 49 v + (c if v odd, 2 - c if v even)`; `oddTri_f`: odd pentagonal sums are preserved.
* `Good N l`: `l` lists `1, …, N` without repetition, adjacent sums are odd generalized pentagonal, `l` starts
  at `3` and ends at `bEnd N` (`2` for even `N`, `19` for odd `N`).
-/

namespace PentChains

/-- `s` is a generalized pentagonal number `k(3k-1)/2`, `k ∈ ℤ`. -/
def IsTri (s : ℤ) : Prop := ∃ k : ℤ, 2 * s = k * (3 * k - 1)

/-- `s` is an odd triangular number. -/
def OddTri (s : ℤ) : Prop := IsTri s ∧ s % 2 = 1

/-- The key identity `49 P_k + 2 = P_{7k-1}`. -/
theorem tri_inflate {s : ℤ} (h : IsTri s) : IsTri (49 * s + 2) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨7 * k - 1, by nlinarith [hk]⟩

theorem oddTri_inflate {s : ℤ} (h : OddTri s) : OddTri (49 * s + 2) :=
  ⟨tri_inflate h.1, by have := h.2; omega⟩

/-- The block map: `f c v = 49 v + c` for odd `v`, `49 v + 2 - c` for even `v`. -/
def f (c v : ℤ) : ℤ := 49 * v + if v % 2 = 1 then c else 2 - c

theorem oddTri_f (c : ℤ) {a b : ℤ} (h : OddTri (a + b)) : OddTri (f c a + f c b) := by
  have hp := h.2
  have : f c a + f c b = 49 * (a + b) + 2 := by
    unfold f
    rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
      rcases Int.emod_two_eq_zero_or_one b with hb | hb <;> simp [ha, hb] <;> omega
  rw [this]; exact oddTri_inflate h

/-- Adjacent sums odd triangular. -/
abbrev OT (a b : ℤ) : Prop := OddTri (a + b)

theorem chain_map_f (c : ℤ) {x : List ℤ} (h : x.IsChain OT) : (x.map (f c)).IsChain OT :=
  List.isChain_map_of_isChain (f c) (fun _ _ hab => oddTri_f c hab) h

theorem chain_reverse {x : List ℤ} (h : x.IsChain OT) : x.reverse.IsChain OT := by
  rw [List.isChain_reverse]
  exact h.imp fun a b hab => by simpa [OT, flip, add_comm] using hab

/-- `f c` is injective, and two values of `f` with offsets in `[-23, 25]` determine `v` and the offset. -/
theorem f_window {c₁ c₂ v₁ v₂ : ℤ} (h1 : -23 ≤ c₁ ∧ c₁ ≤ 25) (h2 : -23 ≤ c₂ ∧ c₂ ≤ 25)
    (h : f c₁ v₁ = f c₂ v₂) : v₁ = v₂ ∧ c₁ = c₂ := by
  unfold f at h
  split_ifs at h <;> omega

/-- The prescribed last entry: `2` for even length, `19` for odd length. -/
def bEnd (N : ℕ) : ℤ := if N % 2 = 0 then 2 else 19

/-- The inductive statement for one length `N`. -/
structure Good (N : ℕ) (l : List ℤ) : Prop where
  nodup : l.Nodup
  len : l.length = N
  range : ∀ x ∈ l, 1 ≤ x ∧ x ≤ N
  chain : l.IsChain OT
  head : l.head? = some 3
  last : l.getLast? = some (bEnd N)

/-! ### Decidable test (bisection square root with fuel, so the kernel can evaluate it) -/

/-- Largest `r ≤ hi` with `r * r ≤ m`, by bisection, assuming `lo * lo ≤ m`. -/
def bs : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, lo, _ => lo
  | fuel + 1, m, lo, hi =>
      let mid := (lo + hi) / 2
      if mid * mid ≤ m then bs fuel m mid hi else bs fuel m lo mid

/-- Candidate index: from `r = ⌊√(24s+1)⌋`, try `k = (r+1)/6` and `k = (1-r)/6`, and test `2s = k(3k-1)`. -/
def triB (s : ℤ) : Bool :=
  let r : ℤ := (bs 48 (24 * s.toNat + 1) 0 (24 * s.toNat + 2) : ℕ)
  let k₁ := (r + 1) / 6
  let k₂ := (1 - r) / 6
  (2 * s == k₁ * (3 * k₁ - 1)) || (2 * s == k₂ * (3 * k₂ - 1))

theorem isTri_of_triB {s : ℤ} (h : triB s = true) : IsTri s := by
  unfold triB at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

/-- Boolean odd-triangularity test. -/
def otB (s : ℤ) : Bool := triB s && s % 2 == 1

theorem oddTri_of_otB {s : ℤ} (h : otB s = true) : OddTri s := by
  unfold otB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨isTri_of_triB h.1, h.2⟩

end PentChains
