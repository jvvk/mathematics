import Mathlib.Tactic

/-!
  Guy, Unsolved Problems in Number Theory, E27: is every mex sequence ultimately periodic?

  A mex sequence continues a finite starting word by
  `a (n+1) = mex {a i + a (n - i) : i ≤ n}`, the least natural number not of that form.
  We show that the mex sequence starting `1,1,1,0,1,0,1,1` is unbounded, so the answer is no.
-/

namespace MexE27

/-- Every finite set of naturals misses some natural. -/
theorem exists_notMem (S : Finset ℕ) : ∃ v, v ∉ S :=
  ⟨S.sup id + 1, fun h => by
    have := Finset.le_sup (f := id) h
    simp only [id] at this
    omega⟩

/-- The least natural number not in `S`. -/
noncomputable def mex (S : Finset ℕ) : ℕ := Nat.find (exists_notMem S)

theorem mex_eq_iff (S : Finset ℕ) (v : ℕ) :
    mex S = v ↔ v ∉ S ∧ ∀ u < v, u ∈ S := by
  unfold mex
  rw [Nat.find_eq_iff]
  simp only [not_not]

/-- The sums `a i + a (n - i)` for `i ≤ n`. -/
def sums (a : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).image (fun i => a i + a (n - i))

theorem mem_sums (a : ℕ → ℕ) (n u : ℕ) :
    u ∈ sums a n ↔ ∃ i, i < n + 1 ∧ a i + a (n - i) = u := by
  simp [sums, Finset.mem_image, Finset.mem_range]

/-- `a` is the mex sequence started from `1,1,1,0,1,0,1,1`. -/
def IsMex (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 0 ∧ a 4 = 1 ∧ a 5 = 0 ∧ a 6 = 1 ∧ a 7 = 1 ∧
    ∀ n, 7 ≤ n → a (n + 1) = mex (sums a n)

/-- The values at positions `5b+1` and `5b+2`. -/
def y (b : ℕ) : ℕ :=
  if b = 0 then 1 else if b = 1 then 1 else if b = 2 then 3 else
    (if (b - 3) % 3 = 0 then 2 else if (b - 3) % 3 = 1 then 5 else 4) + 4 * ((b - 3) / 3)

/-- The values at positions `5b+4`. -/
def w (b : ℕ) : ℕ := if b = 0 then 1 else if b ≤ 2 then 3 else 2

/-- The closed form of the sequence. -/
def F (n : ℕ) : ℕ :=
  if n = 0 then 1 else if n % 5 = 0 ∨ n % 5 = 3 then 0
  else if n % 5 = 4 then w (n / 5) else y (n / 5)

/-- Decidable form of "the mex of the sums of `F` at `n` is `v`", for the finite checks. -/
def StepOK (n : ℕ) : Prop :=
  (∀ i, i < n + 1 → F i + F (n - i) ≠ F (n + 1)) ∧
    ∀ u, u < F (n + 1) → ∃ i, i < n + 1 ∧ F i + F (n - i) = u

instance (n : ℕ) : Decidable (StepOK n) := by unfold StepOK; infer_instance

theorem step_of_ok (n : ℕ) (h : StepOK n) : mex (sums F n) = F (n + 1) := by
  rw [mex_eq_iff]
  refine ⟨fun hm => ?_, fun u hu => (mem_sums F n u).2 (h.2 u hu)⟩
  obtain ⟨i, hi, he⟩ := (mem_sums F n _).1 hm
  exact h.1 i hi he

theorem small_steps : ∀ n, 7 ≤ n → n < 60 → StepOK n := by decide

end MexE27
