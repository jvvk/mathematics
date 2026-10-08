"""Emit LeanProofs/ShuffleBlocks.lean: rotation dispatch, main theorem, cutting corollary, witnesses."""
import pathlib
from emit import RUNS, LET, layout

HEAD = r'''import LeanProofs.ShuffleU
''' + "".join(f"import LeanProofs.ShuffleBlocks.Cut{r:02d}\n" for r in range(10)) + r'''
/-!
  Blow-ups of `U k` (paper, Theorem 4) and the cutting-distance corollary (paper, Corollary 5).

  `V K λ μ` reads, around a circle, `0^(Kλ) 1^μ 0^(5λ) 1^(2μ) 0^(Kλ) 1^μ 0^(2λ) 1^μ 0^λ 1^(3μ)`.
  If `K ≥ 9`, `λ ≥ 1` and `μ` is odd, no rotation of `V K λ μ` is a shuffle square. The ten files
  `ShuffleBlocks/CutNN.lean` treat a cut inside each of the ten runs; each is a case analysis over the
  facts of `Blocks.pair_fact`, closed by linear arithmetic, with `K λ` and `μ` symbolic throughout.
-/

set_option linter.style.longLine false

namespace Blocks

/-- A rotation of a run word: either the trivial one, or a cut inside run `r` after `k` letters. -/
theorem rot_general : ∀ (l : List (Bool × Nat)) (p s : List Bool), p ++ s = rw l →
    (s = [] ∧ p = rw l) ∨
    ∃ r c n k, l[r]? = some (c, n) ∧ k ≤ n ∧ p = rw (l.take r) ++ List.replicate k c ∧
      s = List.replicate (n - k) c ++ rw (l.drop (r + 1))
  | [], p, s, h => by
    simp only [rw, List.append_eq_nil_iff] at h
    exact Or.inl ⟨h.2, h.1⟩
  | (c, n) :: l, p, s, h => by
    rcases rot_cons h with ⟨k, hk, rfl, rfl⟩ | ⟨p', rfl, h'⟩
    · exact Or.inr ⟨0, c, n, k, rfl, hk, by simp [rw], by simp [rw]⟩
    · rcases rot_general l p' s h' with ⟨rfl, rfl⟩ | ⟨r, c', n', k, hr, hk, rfl, rfl⟩
      · exact Or.inl ⟨rfl, by simp [rw]⟩
      · exact Or.inr ⟨r + 1, c', n', k, by simpa using hr, hk, by simp [rw], by simp [rw]⟩

/-- The runs of `V` read from the start of `G`, with `L = Kλ`. -/
def Vr (L l m : Nat) : List (Bool × Nat) :=
  [(false, L), (true, m), (false, 5 * l), (true, 2 * m), (false, L), (true, m), (false, 2 * l),
    (true, m), (false, l), (true, 3 * m)]

/-- `V K λ μ`, the blow-up of `U`. -/
def V (K l m : Nat) : List Bool := rw (Vr (K * l) l m)

set_option maxHeartbeats 0 in
theorem Vr_rotation_not_square (L l m v : Nat) (hl : 1 ≤ l) (hm : m = 2 * v + 1) (hL : 9 * l ≤ L)
    (p s : List Bool) (h : p ++ s = rw (Vr L l m)) : ¬ IsShuffleSquare (s ++ p) := by
  rintro ⟨u, hu⟩
  rcases rot_general _ p s h with ⟨hs, hp⟩ | ⟨r, c, n, k, hr, hk, hp, hs⟩
'''


def lin_text(r: int) -> list[tuple[str, str]]:
    c, n, lin, *_ = layout(r)
    return [(LET[ci], ni) for ci, ni in lin]


def dispatch(r: int, k: str, pre: str) -> str:
    import re
    lin = [(c, re.sub(r"\bk\b", k, n)) for c, n in lin_text(r)]
    lst = ", ".join(f"({c}, {n})" for c, n in lin)
    N = len(lin)
    out = []
    w = out.append
    w(f"{pre}have hw : s ++ p = rw [{lst}] := by")
    w(f"{pre}  rw [hs, hp]; simp [Vr, rw, List.append_assoc]")
    w(f"{pre}rw [hw] at hu")
    w(f"{pre}obtain ⟨la, lb, hsp, hua, hub⟩ := shuffle_split hu")
    for i in range(N):
        w(f"{pre}obtain ⟨a{i}, b{i}, la, lb, rfl, rfl, e{i}, hsp⟩ := split_cons_inv hsp")
    w(f"{pre}obtain ⟨rfl, rfl⟩ := split_nil_inv hsp")
    args = " ".join(f"a{i} b{i}" for i in range(N))
    es = " ".join(f"e{i}" for i in range(N))
    w(f"{pre}exact V_cut{r:02d} L l m v {k} {args} hl hm hL (by omega) {es} (hua.symm.trans hub)")
    return "\n".join(out)


def main_body() -> str:
    out = []
    w = out.append
    # trivial rotation: s = [], p = whole word = cut in run 0 with k = 0
    w("  · -- the trivial rotation is the cut after 0 letters of run 0")
    w(dispatch(0, "0", "    ").replace("rw [hw] at hu", "rw [hw] at hu"))
    w("  · have hr10 : r < 10 := by")
    w("      have := (List.getElem?_eq_some_iff.mp hr).1; simpa [Vr] using this")
    w("    interval_cases r")
    for r in range(10):
        c, n = RUNS[r]
        w(f"    · -- cut inside run {r}")
        w(f"      obtain ⟨rfl, rfl⟩ : c = {LET[c]} ∧ {n} = n := by simp [Vr] at hr; exact ⟨hr.1, hr.2⟩")
        w(dispatch(r, "k", "      "))
    return "\n".join(out)


TAIL = r'''

theorem V_count_true (K l m : Nat) : (V K l m).count true = 8 * m := by
  simp [V, Vr, count_rw]; omega

theorem V_count_false (K l m : Nat) : (V K l m).count false = 2 * (K * l) + 8 * l := by
  simp [V, Vr, count_rw]; omega

/-- **Theorem 4.** If `K ≥ 9`, `λ ≥ 1` and `μ` is odd, then `V K λ μ` is a shuffle anti-square. -/
theorem V_isAntiSquare (K l m : Nat) (hK : 9 ≤ K) (hl : 1 ≤ l) (hm : m % 2 = 1) :
    IsAntiSquare (V K l m) := by
  refine ⟨by rw [V_count_true]; omega, by rw [V_count_false]; omega, fun p s h => ?_⟩
  exact Vr_rotation_not_square (K * l) l m (m / 2) hl (by omega) (Nat.mul_le_mul_right l hK) p s h

/-- `U k` is the case `λ = μ = 1`, `K = k + 9`. -/
theorem U_eq_V (k : Nat) : U k = V (k + 9) 1 1 := by
  simp [U, V, Vr, rw, ofGaps, List.replicate_succ]

/-! ### Explicit witnesses -/

/-- The letters of `w` whose mask entry is `b`. -/
def pick : List Bool → List Bool → Bool → List Bool
  | [], _, _ => []
  | _ :: _, [], _ => []
  | x :: w, t :: mask, b => if t = b then x :: pick w mask b else pick w mask b

theorem shuffle_pick : ∀ (w mask : List Bool), mask.length = w.length →
    Shuffle (pick w mask true) (pick w mask false) w
  | [], [], _ => .nil
  | x :: w, t :: mask, h => by
    have ih := shuffle_pick w mask (by simpa using h)
    cases t
    · simpa [pick] using Shuffle.right ih
    · simpa [pick] using Shuffle.left ih

/-- A mask whose two colour classes spell the same word witnesses a shuffle square. -/
theorem isShuffleSquare_of_mask (w mask : List Bool) (h : mask.length = w.length)
    (he : pick w mask true = pick w mask false) : IsShuffleSquare w :=
  ⟨pick w mask true, by have := shuffle_pick w mask h; rwa [← he] at this⟩

/-- `true` = copy A, `false` = copy B. -/
def maskOf (s : String) : List Bool := s.toList.map (· = 'A')

def wordOf (s : String) : List Bool := s.toList.map (· = '1')

theorem not_antiSquare_of_square {w : List Bool} (h : IsShuffleSquare w) : ¬ IsAntiSquare w :=
  fun ha => ha.2.2 [] w (by simp) (by simpa using h)

'''


def witnesses() -> str:
    data = [
        ((8, 1, 1), "ABABABABAAAAAABABBBBBAAABBBABBAB"),
        ((8, 1, 3), "ABABABABAAAAAAAABBBAAABBBBBAAABBBBBAAABBBBABABAB"),
        ((9, 1, 2), "ABABAAAAAAABBBBBBBABABABABABAAABABBBABABAB"),
        ((9, 1, 4), "ABABAAAAAAAAABBBBBBBBBABABABABABABAAAAABABBBBBABABABABABAB"),
    ]
    out = ["/-- Tightness of Theorem 4: `K = 8`, or `μ` even, can fail. -/"]
    for (K, l, m), mask in data:
        name = f"V_{K}_{l}_{m}_not_anti"
        out.append(f"theorem {name} : ¬ IsAntiSquare (V {K} {l} {m}) :=")
        out.append(f"  not_antiSquare_of_square (isShuffleSquare_of_mask _ (maskOf \"{mask}\") (by decide) (by decide))")
        out.append("")
    out.append("/-- Section 5: `W 0 = 0 | 0^4 1 | 0^2 1^4 0^4 1^3 0 1^4`, rearranged as `Y X Z`, is a shuffle square. -/")
    out.append("theorem W0_two_cut_example :")
    out.append("    W 0 = wordOf \"0\" ++ wordOf \"00001\" ++ wordOf \"001111000011101111\" ∧")
    out.append("    IsShuffleSquare (wordOf \"00001\" ++ wordOf \"0\" ++ wordOf \"001111000011101111\") :=")
    out.append("  ⟨by decide, isShuffleSquare_of_mask _ (maskOf \"ABABAAAABAAABBBABBBBABAB\") (by decide) (by decide)⟩")
    return "\n".join(out)


CUT = r'''

/-! ### Cutting distance (paper, Section 5) -/

/-- `w'` is obtained from `w` by cutting it into at most `c + 1` pieces and rearranging them. -/
def CutsTo (c : Nat) (w w' : List Bool) : Prop :=
  ∃ pieces pieces' : List (List Bool), pieces.length ≤ c + 1 ∧ pieces.flatten = w ∧
    pieces'.Perm pieces ∧ pieces'.flatten = w'

/-- One cut can only rotate. -/
theorem cutsTo_one {w w' : List Bool} (h : CutsTo 1 w w') : ∃ p s, p ++ s = w ∧ w' = s ++ p := by
  obtain ⟨ps, ps', hlen, rfl, hperm, rfl⟩ := h
  have hl := hperm.length_eq
  rcases ps with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · rcases ps' with _ | ⟨a, t⟩
    · exact ⟨[], [], rfl, rfl⟩
    · simp at hl
  · rcases ps' with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp at hl
    have := List.perm_singleton.mp hperm
    simp at this; subst this
    exact ⟨[], a, by simp, by simp⟩
  · rcases ps' with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl
    have ha : a ∈ [x, y] := hperm.subset (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · have hb := List.perm_singleton.mp ((List.perm_cons a).mp hperm)
      simp at hb; subst hb
      exact ⟨[], a ++ b, by simp, by simp⟩
    · have h2 : [a, b].Perm [a, x] := hperm.trans (List.Perm.swap a x [])
      have hb := List.perm_singleton.mp ((List.perm_cons a).mp h2)
      simp at hb; subst hb
      exact ⟨b, a, by simp, by simp⟩
  · simp at hlen

/-- **Corollary 5.** An anti-square cannot be made a shuffle square with at most one cut. -/
theorem antiSquare_needs_two_cuts {w : List Bool} (hw : IsAntiSquare w) (w' : List Bool)
    (h : CutsTo 1 w w') : ¬ IsShuffleSquare w' := by
  obtain ⟨p, s, hps, rfl⟩ := cutsTo_one h
  exact hw.2.2 p s hps

/-- **Corollary 6.** For every `n ≥ 12` some even binary word of length `2n` needs at least two cuts
    (`s(2, 2n) ≥ 2`). Grytczuk, Pawlik and Ruciński (arXiv:2503.22043, Section 6.3) found such a word of
    length 24; the anti-squares of `exists_antiSquare` give one of every even length from 24. -/
theorem two_cuts_needed (n : Nat) (hn : 12 ≤ n) :
    ∃ w : List Bool, w.length = 2 * n ∧ w.count true % 2 = 0 ∧ w.count false % 2 = 0 ∧
      ∀ w', CutsTo 1 w w' → ¬ IsShuffleSquare w' := by
  obtain ⟨w, hl, hw⟩ := exists_antiSquare n hn
  exact ⟨w, hl, hw.1, hw.2.1, antiSquare_needs_two_cuts hw⟩

end Blocks

#print axioms Blocks.V_isAntiSquare
#print axioms Blocks.two_cuts_needed
#print axioms Blocks.U_eq_V
#print axioms Blocks.W0_two_cut_example
#print axioms Blocks.V_8_1_1_not_anti
'''

if __name__ == "__main__":
    text = HEAD + main_body() + TAIL + witnesses() + CUT
    p = pathlib.Path(__file__).resolve().parents[2] / "lean/LeanProofs/ShuffleBlocks.lean"
    p.write_text(text)
    print("wrote", p, len(text.splitlines()), "lines")
