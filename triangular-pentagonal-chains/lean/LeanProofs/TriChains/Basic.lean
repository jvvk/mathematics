import Mathlib

/-!
# Triangular chains: definitions and the inflation lemma

Berlekamp and Guy (Crux Math. 46(8), 2020, p. 343) ask for proofs that `1, …, n` can be ordered so that
adjacent sums are triangular for `n = 2` and all `n ≥ 9`, and cyclically for `n ≥ 12`, `n ≠ 14`.

* `IsTri s`: `s` is a triangular number (`2s = k(k+1)`); `OddTri s`: an odd triangular number.
* `tri_inflate` (the key identity): `2s = k(k+1)` implies `2(49s + 6) = (7k+3)(7k+4)`,
  i.e. `49 T_k + 6 = T_{7k+3}`.
* `f c v = 49 v + (c if v odd, 6 - c if v even)`; `oddTri_f`: if `a + b` is odd triangular then so is
  `f c a + f c b`, so `f c` maps a chain with odd triangular sums to another (`chain_map_f`).
* `Good N l`: `l` lists `1, …, N` without repetition, adjacent sums are odd triangular, `l` starts at `1`
  and ends at `bEnd N` (`2` for even `N`, `9` for odd `N`).
-/

namespace TriChains

/-- `s` is a triangular number `k(k+1)/2`. -/
def IsTri (s : ℤ) : Prop := ∃ k : ℕ, 2 * s = (k : ℤ) * (k + 1)

/-- `s` is an odd triangular number. -/
def OddTri (s : ℤ) : Prop := IsTri s ∧ s % 2 = 1

/-- The key identity `49 T_k + 6 = T_{7k+3}`. -/
theorem tri_inflate {s : ℤ} (h : IsTri s) : IsTri (49 * s + 6) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨7 * k + 3, by push_cast; nlinarith [hk]⟩

theorem oddTri_inflate {s : ℤ} (h : OddTri s) : OddTri (49 * s + 6) :=
  ⟨tri_inflate h.1, by have := h.2; omega⟩

/-- The block map: `f c v = 49 v + c` for odd `v`, `49 v + 6 - c` for even `v`. -/
def f (c v : ℤ) : ℤ := 49 * v + if v % 2 = 1 then c else 6 - c

theorem oddTri_f (c : ℤ) {a b : ℤ} (h : OddTri (a + b)) : OddTri (f c a + f c b) := by
  have hp := h.2
  have : f c a + f c b = 49 * (a + b) + 6 := by
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

/-- `f c` is injective, and two values of `f` with offsets in `[-21, 27]` determine `v` and the offset. -/
theorem f_window {c₁ c₂ v₁ v₂ : ℤ} (h1 : -21 ≤ c₁ ∧ c₁ ≤ 27) (h2 : -21 ≤ c₂ ∧ c₂ ≤ 27)
    (h : f c₁ v₁ = f c₂ v₂) : v₁ = v₂ ∧ c₁ = c₂ := by
  unfold f at h
  split_ifs at h <;> omega

/-- The prescribed last entry: `2` for even length, `9` for odd length. -/
def bEnd (N : ℕ) : ℤ := if N % 2 = 0 then 2 else 9

/-- The inductive statement for one length `N`. -/
structure Good (N : ℕ) (l : List ℤ) : Prop where
  nodup : l.Nodup
  len : l.length = N
  range : ∀ x ∈ l, 1 ≤ x ∧ x ≤ N
  chain : l.IsChain OT
  head : l.head? = some 1
  last : l.getLast? = some (bEnd N)

/-! ### Decidable triangularity (binary search with fuel, so the kernel can evaluate it) -/

/-- Largest `k ≤ hi` with `k(k+1) ≤ m` found by bisection, assuming `lo(lo+1) ≤ m`. -/
def bs : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, lo, _ => lo
  | fuel + 1, m, lo, hi =>
      let mid := (lo + hi) / 2
      if mid * (mid + 1) ≤ m then bs fuel m mid hi else bs fuel m lo mid

/-- Boolean triangularity test for integers. -/
def triB (s : ℤ) : Bool :=
  decide (0 ≤ s) && (let k := bs 40 (2 * s.toNat) 0 (2 * s.toNat + 1); k * (k + 1) == 2 * s.toNat)

theorem isTri_of_triB {s : ℤ} (h : triB s = true) : IsTri s := by
  unfold triB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨h0, hk⟩ := h
  refine ⟨bs 40 (2 * s.toNat) 0 (2 * s.toNat + 1), ?_⟩
  have : ((bs 40 (2 * s.toNat) 0 (2 * s.toNat + 1) * (bs 40 (2 * s.toNat) 0 (2 * s.toNat + 1) + 1) : ℕ) : ℤ)
      = ((2 * s.toNat : ℕ) : ℤ) := by rw [hk]
  push_cast at this
  rw [Int.toNat_of_nonneg h0] at this
  linarith

/-- Boolean odd-triangularity test. -/
def otB (s : ℤ) : Bool := triB s && s % 2 == 1

theorem oddTri_of_otB {s : ℤ} (h : otB s = true) : OddTri s := by
  unfold otB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨isTri_of_triB h.1, h.2⟩

end TriChains
