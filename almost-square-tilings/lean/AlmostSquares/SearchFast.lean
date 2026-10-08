/-
  The exhaustive search for small `n`, in a form the kernel evaluates quickly, with its soundness.

  The staircase is packed into one natural number `s`, base 32, one digit per column; the used sizes
  are the bits of `u`. Every state is then a numeral and every step is `Nat` arithmetic, which the
  kernel evaluates with GMP.

  The rule: the lowest, then leftmost, empty cell `(a, m)` is the lower-left corner of the tile
  covering it, since the cells to its left and below are filled. So trying every unused size, in
  both orientations, with its corner there is exhaustive. A tile of width `w` there covers columns
  `a, …, a+w-1`, which must all have height `m`, so `w` is at most the run `wd` of such columns.
-/
import AlmostSquares.Basic

namespace AlmostSq

/-- Height of column `x` in the packed state `s`. -/
def col (s x : ℕ) : ℕ := s / 32 ^ x % 32

/-- The least height among columns `x, …, x+k-1` (`n` if `k = 0`). -/
def minFrom (n s : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => n
  | k + 1, x => min (col s x) (minFrom n s k (x + 1))

/-- The first column among `x, …, x+k-1` of height `m`. -/
def firstFrom (s m : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => if col s x = m then x else firstFrom s m k (x + 1)

/-- The number of consecutive columns from `x` (at most `k`) of height `m`. -/
def runFrom (s m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, x => if col s x = m then runFrom s m k (x + 1) + 1 else 0

/-- One unit in each of the digits `a, …, a+w-1`. -/
def mask (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | w + 1 => mask a w + 32 ^ (a + w)

/-- The branch for size `j`: already used, or both orientations fail. -/
def branch (n : ℕ) (rec : ℕ → ℕ → Bool) (s u m a wd j : ℕ) : Bool :=
  u.testBit j ||
    ((!(decide (j ≤ wd) && decide (m + (j + 1) ≤ n)) ||
        rec (s + (j + 1) * mask a j) (u ||| 2 ^ j)) &&
     (!(decide (j + 1 ≤ wd) && decide (m + j ≤ n)) ||
        rec (s + j * mask a (j + 1)) (u ||| 2 ^ j)))

/-- All sizes `1, …, K` fail. -/
def tryK (n : ℕ) (rec : ℕ → ℕ → Bool) (s u m a wd : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => branch n rec s u m a wd (k + 1) && tryK n rec s u m a wd k

/-- `true` iff the staircase `s` (width `W`) has no completion with sizes outside `u`
    (within `f` placements; out of fuel answers `false`). -/
def searchF (n W : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, s, u =>
    if minFrom n s W 0 = n then false else
    tryK n (searchF n W f) s u (minFrom n s W 0) (firstFrom s (minFrom n s W 0) W 0)
      (runFrom s (minFrom n s W 0) (W - firstFrom s (minFrom n s W 0) W 0)
        (firstFrom s (minFrom n s W 0) W 0))
      (min (n - 1) (runFrom s (minFrom n s W 0) (W - firstFrom s (minFrom n s W 0) W 0)
        (firstFrom s (minFrom n s W 0) W 0)))

/-- The search from the empty rectangle `R_n`. -/
def noTilingF (n : ℕ) : Bool := searchF n (n + 1) n 0 0

/-! ### Lemmas on the helpers -/

theorem minFrom_le_n (n s : ℕ) : ∀ k x, minFrom n s k x ≤ n
  | 0, _ => le_rfl
  | k + 1, x => le_trans (min_le_right _ _) (minFrom_le_n n s k (x + 1))

theorem minFrom_le (n s : ℕ) : ∀ k x y, x ≤ y → y < x + k → minFrom n s k x ≤ col s y
  | 0, _, _, h1, h2 => by omega
  | k + 1, x, y, h1, h2 => by
    simp only [minFrom]
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (minFrom_le n s k (x + 1) y h (by omega))

theorem minFrom_mem (n s : ℕ) : ∀ k x, minFrom n s k x ≠ n →
    ∃ y, x ≤ y ∧ y < x + k ∧ col s y = minFrom n s k x
  | 0, _, h => absurd rfl h
  | k + 1, x, h => by
    simp only [minFrom] at h ⊢
    rcases le_total (col s x) (minFrom n s k (x + 1)) with hx | hx
    · exact ⟨x, le_rfl, by omega, (min_eq_left hx).symm⟩
    · rw [min_eq_right hx] at h ⊢
      obtain ⟨y, h1, h2, h3⟩ := minFrom_mem n s k (x + 1) h
      exact ⟨y, by omega, by omega, h3⟩

theorem firstFrom_spec (s m : ℕ) : ∀ k x, (∃ y, x ≤ y ∧ y < x + k ∧ col s y = m) →
    x ≤ firstFrom s m k x ∧ firstFrom s m k x < x + k ∧ col s (firstFrom s m k x) = m ∧
      ∀ y, x ≤ y → y < firstFrom s m k x → col s y ≠ m
  | 0, _, ⟨_, h1, h2, _⟩ => by omega
  | k + 1, x, ⟨y, h1, h2, h3⟩ => by
    simp only [firstFrom]
    by_cases hx : col s x = m
    · rw [if_pos hx]
      exact ⟨le_rfl, by omega, hx, fun z hz1 hz2 => by omega⟩
    · rw [if_neg hx]
      have hy : x + 1 ≤ y := by
        rcases Nat.eq_or_lt_of_le h1 with rfl | h
        · exact absurd h3 hx
        · exact h
      obtain ⟨a1, a2, a3, a4⟩ := firstFrom_spec s m k (x + 1) ⟨y, hy, by omega, h3⟩
      refine ⟨by omega, by omega, a3, fun z hz1 hz2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hz1 with rfl | h
      · exact hx
      · exact a4 z (by omega) hz2

theorem runFrom_ge (s m : ℕ) : ∀ k x w, w ≤ k → (∀ y, x ≤ y → y < x + w → col s y = m) →
    w ≤ runFrom s m k x
  | _, _, 0, _, _ => Nat.zero_le _
  | 0, _, _ + 1, h, _ => by omega
  | k + 1, x, w + 1, h, hc => by
    simp only [runFrom, hc x le_rfl (by omega), if_true]
    have := runFrom_ge s m k (x + 1) w (by omega) (fun y h1 h2 => hc y (by omega) (by omega))
    omega

/-- Adding `h` to one digit that stays below 32 changes only that digit. -/
theorem col_add (t y0 h y : ℕ) (hc : col t y0 + h < 32) :
    col (t + h * 32 ^ y0) y = col t y + if y = y0 then h else 0 := by
  unfold col at *
  rcases lt_trichotomy y y0 with hy | rfl | hy
  · rw [if_neg (by omega)]
    have e : h * 32 ^ y0 = 32 * (h * 32 ^ (y0 - y - 1)) * 32 ^ y := by
      rw [show y0 = y0 - y - 1 + 1 + y by omega, pow_add, pow_succ]
      rw [show y0 - y - 1 + 1 + y - y - 1 = y0 - y - 1 by omega]
      ring
    rw [e, Nat.add_mul_div_right _ _ (by positivity)]
    omega
  · rw [if_pos rfl, Nat.add_mul_div_right _ _ (by positivity)]
    omega
  · rw [if_neg (by omega), add_zero]
    obtain ⟨e, rfl⟩ : ∃ e, y = y0 + (e + 1) := ⟨y - y0 - 1, by omega⟩
    rw [pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_right _ _ (by positivity)]
    generalize t / 32 ^ y0 = X at *
    have hE : 32 ^ (e + 1) = 32 * 32 ^ e := by rw [pow_succ]; ring
    rw [hE]
    have hq : (X + h) / (32 * 32 ^ e) = X / (32 * 32 ^ e) := by
      have hP : 0 < 32 ^ e := by positivity
      have h1 := Nat.div_add_mod X (32 * 32 ^ e)
      have h2 := Nat.mod_lt X (show 0 < 32 * 32 ^ e by positivity)
      have h3 : X % (32 * 32 ^ e) % 32 = X % 32 := Nat.mod_mod_of_dvd X (Dvd.intro _ rfl)
      have h4 := Nat.div_add_mod (X % (32 * 32 ^ e)) 32
      generalize 32 ^ e = P at *
      generalize X / (32 * P) = q at *
      generalize X % (32 * P) = R at *
      have hR : R + h < 32 * P := by omega
      apply Nat.div_eq_of_lt_le
      · nlinarith
      · nlinarith
    rw [hq]

theorem col_add_mask (s a h : ℕ) : ∀ w, (∀ y, a ≤ y → y < a + w → col s y + h < 32) →
    ∀ y, col (s + h * mask a w) y = col s y + if a ≤ y ∧ y < a + w then h else 0
  | 0, _, y => by simp [mask]
  | w + 1, hc, y => by
    have ih := col_add_mask s a h w (fun z h1 h2 => hc z h1 (by omega))
    have e : s + h * mask a (w + 1) = s + h * mask a w + h * 32 ^ (a + w) := by
      simp only [mask]; ring
    have hc0 : col (s + h * mask a w) (a + w) + h < 32 := by
      rw [ih (a + w), if_neg (by omega), add_zero]; exact hc _ (by omega) (by omega)
    rw [e, col_add _ _ _ _ hc0, ih y]
    split_ifs <;> omega

theorem tryK_false {n : ℕ} {rec : ℕ → ℕ → Bool} {s u m a wd : ℕ} :
    ∀ K j, 1 ≤ j → j ≤ K → branch n rec s u m a wd j = false → tryK n rec s u m a wd K = false
  | 0, j, h1, h2, _ => by omega
  | K + 1, j, h1, h2, hb => by
    simp only [tryK, Bool.and_eq_false_iff]
    rcases Nat.eq_or_lt_of_le h2 with rfl | h
    · exact Or.inl hb
    · exact Or.inr (tryK_false K j h1 (by omega) hb)

/-! ### Soundness -/

/-- Cell `p` lies under the staircase `s` of width `W`. -/
def InRegF (W s : ℕ) (p : ℤ × ℤ) : Prop :=
  ∃ x : ℕ, p.1 = x ∧ x < W ∧ 0 ≤ p.2 ∧ p.2 < (col s x : ℤ)

/-- In an admissible tiling, a cell lies in at most one tile. -/
theorem Admissible.unique' {n : ℕ} {ts : List Tile} (hA : Admissible n ts) {U V : Tile}
    (hU : U ∈ ts) (hV : V ∈ ts) {p : ℤ × ℤ} (hpU : p ∈ U.cells) (hpV : p ∈ V.cells) : U = V := by
  have hl := hA.cover p (hA.inside U hU hpU)
  have mU : U ∈ ts.filter (fun T => p ∈ T.cells) := by simp [hU, hpU]
  have mV : V ∈ ts.filter (fun T => p ∈ T.cells) := by simp [hV, hpV]
  generalize ts.filter (fun T => p ∈ T.cells) = l at hl mU mV
  match l, hl with
  | [x], _ => simp only [List.mem_singleton] at mU mV; rw [mU, mV]

/-- The invariant: if an admissible tiling extends the staircase, the search does not answer
    `true`. -/
theorem searchF_false {n : ℕ} (hn : n < 32) {ts : List Tile} (hA : Admissible n ts) :
    ∀ (f s u : ℕ) (P : List Tile), (∀ T ∈ P, T ∈ ts) →
      (∀ p, (∃ T ∈ P, p ∈ T.cells) ↔ InRegF (n + 1) s p) →
      (∀ k : ℕ, u.testBit k = true → ∃ V ∈ P, V.size = k) →
      searchF n (n + 1) f s u = false := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _ _; rfl
  | succ f ih =>
  intro s u P hPts hreg hused
  unfold searchF
  by_cases hfull : minFrom n s (n + 1) 0 = n
  · simp [hfull]
  rw [if_neg hfull]
  generalize hm : minFrom n s (n + 1) 0 = m at hfull ⊢
  -- every column has height at most `n`
  have hcol : ∀ x < n + 1, col s x ≤ n := by
    intro x hx
    by_contra hc
    obtain ⟨T, hT, hpT⟩ := (hreg ((x : ℤ), (n : ℤ))).mpr ⟨x, rfl, hx, by positivity, by omega⟩
    have := hA.inside T (hPts T hT) hpT
    simp only [rect, Finset.mem_product, Finset.mem_Ico] at this
    omega
  have hmin : ∀ x < n + 1, m ≤ col s x := fun x hx => hm ▸ minFrom_le n s _ 0 x (Nat.zero_le _)
    (by omega)
  obtain ⟨y0, -, hy0, hcy0⟩ := minFrom_mem n s (n + 1) 0 (hm ▸ hfull)
  rw [hm] at hcy0
  obtain ⟨-, ha, hma, hbefore⟩ := firstFrom_spec s m (n + 1) 0 ⟨y0, Nat.zero_le _, hy0, hcy0⟩
  generalize hadef : firstFrom s m (n + 1) 0 = a at ha hma hbefore ⊢
  rw [Nat.zero_add] at ha
  have hmn : m < n := by have := minFrom_le_n n s (n + 1) 0; omega
  -- the tile `U` covering the cell `(a, m)`
  have hc : ((a : ℤ), (m : ℤ)) ∈ rect n := by
    simp only [rect, Finset.mem_product, Finset.mem_Ico]; omega
  have hlen1 := hA.cover _ hc
  obtain ⟨U, hUf⟩ : ∃ U, U ∈ ts.filter (fun T => ((a : ℤ), (m : ℤ)) ∈ T.cells) := by
    rcases h : ts.filter (fun T => ((a : ℤ), (m : ℤ)) ∈ T.cells) with _ | ⟨U, _⟩
    · rw [h] at hlen1; simp at hlen1
    · exact ⟨U, by rw [h]; exact List.mem_cons_self ..⟩
  simp only [List.mem_filter, decide_eq_true_eq] at hUf
  obtain ⟨hU, hcU⟩ := hUf
  have hcU' := hcU
  simp only [Tile.cells, Finset.mem_product, Finset.mem_Ico] at hcU'
  have notU : ∀ p, InRegF (n + 1) s p → p ∉ U.cells := by
    intro p hp hpU
    obtain ⟨V, hV, hpV⟩ := (hreg p).mpr hp
    have := hA.unique' hU (hPts V hV) hpU hpV
    subst this
    obtain ⟨x, hx1, hx2, hx3, hx4⟩ := (hreg _).mp ⟨U, hV, hcU⟩
    simp only at hx1
    have : x = a := by omega
    subst this
    omega
  have hUP : U ∉ P := fun h => notU _ ((hreg _).mp ⟨U, h, hcU⟩) hcU
  have halm := hA.almost U hU
  have hs1 := hA.size_pos U hU
  have hsn := hA.size_lt U hU
  have hin := hA.inside U hU
  have hUin : 0 ≤ U.x ∧ 0 ≤ U.y ∧ U.x + U.w ≤ (n : ℤ) + 1 ∧ U.y + U.h ≤ n := by
    have hwh : 1 ≤ U.w ∧ 1 ≤ U.h := by simp only [Tile.size] at hs1; omega
    have h0 := hin (show (U.x, U.y) ∈ U.cells by
      simp only [Tile.cells, Finset.mem_product, Finset.mem_Ico]; omega)
    have h1 := hin (show (U.x + U.w - 1, U.y + U.h - 1) ∈ U.cells by
      simp only [Tile.cells, Finset.mem_product, Finset.mem_Ico]; omega)
    simp only [rect, Finset.mem_product, Finset.mem_Ico] at h0 h1; omega
  -- `U` has its lower-left corner at `(a, m)`
  have hUy : U.y = m := by
    by_contra hne
    apply notU ((a : ℤ), (m : ℤ) - 1) ⟨a, rfl, ha, by omega, by simp only; omega⟩
    simp only [Tile.cells, Finset.mem_product, Finset.mem_Ico]; omega
  have hUx : U.x = a := by
    by_contra hne
    have hb := hbefore (a - 1) (Nat.zero_le _) (by omega)
    have hle := hmin (a - 1) (by omega)
    apply notU ((a : ℤ) - 1, (m : ℤ)) ⟨a - 1, by simp only; omega, by omega, by omega, ?_⟩
    · simp only [Tile.cells, Finset.mem_product, Finset.mem_Ico]; omega
    · simp only; omega
  -- its size is unused
  obtain ⟨k, hk⟩ : ∃ k : ℕ, U.size = k := ⟨U.size.toNat, by omega⟩
  have hku : u.testBit k = false := by
    rw [Bool.eq_false_iff]
    intro hb
    obtain ⟨V, hV, hVs⟩ := hused k hb
    have := List.inj_on_of_nodup_map hA.distinct (hPts V hV) hU (by rw [hVs, hk])
    exact hUP (this ▸ hV)
  -- the columns under `U` are at height `m`
  have hcols : ∀ (w : ℕ), U.w = w → ∀ i, a ≤ i → i < a + w → col s i = m := by
    intro w hw i hi1 hi2
    have hle := hmin i (by omega)
    by_contra hne
    apply notU ((i : ℤ), (m : ℤ)) ⟨i, rfl, by omega, by omega, by simp only; omega⟩
    simp only [Tile.cells, Finset.mem_product, Finset.mem_Ico]; omega
  have hwd : ∀ (w : ℕ), U.w = w → w ≤ runFrom s m (n + 1 - a) a := fun w hw =>
    runFrom_ge s m _ a w (by omega) (hcols w hw)
  -- placing `U` keeps the invariant
  have step : ∀ (w h : ℕ), U.w = w → U.h = h →
      searchF n (n + 1) f (s + h * mask a w) (u ||| 2 ^ k) = false := by
    intro w h hw hh
    have hcm := col_add_mask s a h w (fun y h1 h2 => by rw [hcols w hw y h1 h2]; omega)
    apply ih _ _ (U :: P)
    · intro T hT
      rcases List.mem_cons.mp hT with rfl | hT
      · exact hU
      · exact hPts T hT
    · intro p
      constructor
      · rintro ⟨T, hT, hpT⟩
        rcases List.mem_cons.mp hT with rfl | hT
        · simp only [Tile.cells, Finset.mem_product, Finset.mem_Ico] at hpT
          refine ⟨p.1.toNat, by omega, by omega, by omega, ?_⟩
          rw [hcm, if_pos (by omega), hcols w hw _ (by omega) (by omega)]
          push_cast; omega
        · obtain ⟨x, hx1, hx2, hx3, hx4⟩ := (hreg p).mp ⟨T, hT, hpT⟩
          refine ⟨x, hx1, hx2, hx3, ?_⟩
          rw [hcm]; push_cast; split_ifs <;> omega
      · rintro ⟨x, hx1, hx2, hx3, hx4⟩
        rw [hcm] at hx4
        split_ifs at hx4 with hx
        · by_cases hy : p.2 < m
          · have := hcols w hw x hx.1 hx.2
            obtain ⟨T, hT, hpT⟩ := (hreg p).mpr ⟨x, hx1, hx2, hx3, by omega⟩
            exact ⟨T, List.mem_cons_of_mem _ hT, hpT⟩
          · have := hcols w hw x hx.1 hx.2
            exact ⟨U, List.mem_cons_self .., by
              simp only [Tile.cells, Finset.mem_product, Finset.mem_Ico]; push_cast at hx4; omega⟩
        · obtain ⟨T, hT, hpT⟩ := (hreg p).mpr ⟨x, hx1, hx2, hx3, by simpa using hx4⟩
          exact ⟨T, List.mem_cons_of_mem _ hT, hpT⟩
    · intro j hj
      rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at hj
      rcases hj with hj | hj
      · obtain ⟨V, hV, hVs⟩ := hused j hj
        exact ⟨V, List.mem_cons_of_mem _ hV, hVs⟩
      · have : k = j := of_decide_eq_true hj
        subst this
        exact ⟨U, List.mem_cons_self .., hk⟩
  -- the branch for `k` fails, so `tryK` answers `false`
  have hk1 : 1 ≤ k := by simp only [Tile.size] at hk hs1; omega
  have hkn : k < n := by simp only [Tile.size] at hk hsn; omega
  simp only [Tile.size] at hk
  apply tryK_false _ k hk1
  · rcases halm with hw | hw
    · have := hwd (k + 1) (by push_cast; omega); omega
    · have := hwd k (by omega); omega
  · simp only [branch, hku, Bool.false_or, Bool.and_eq_false_iff]
    rcases halm with hw | hw
    · -- `U` is `(k+1) × k`
      right
      have hw' : U.w = (k + 1 : ℕ) := by push_cast; omega
      have hh : U.h = k := by omega
      rw [decide_eq_true (hwd (k + 1) hw'), decide_eq_true (by omega : m + k ≤ n),
        step (k + 1) k hw' hh]
      rfl
    · -- `U` is `k × (k+1)`
      left
      have hw' : U.w = k := by omega
      have hh : U.h = (k + 1 : ℕ) := by push_cast; omega
      rw [decide_eq_true (hwd k hw'), decide_eq_true (by omega : m + (k + 1) ≤ n),
        step k (k + 1) hw' hh]
      rfl

/-- **Soundness of the search**: if `noTilingF n` evaluates to `true` (and `n < 32`), then `R_n`
    has no admissible tiling. -/
theorem noTilingF_sound {n : ℕ} (hn : n < 32) (h : noTilingF n = true) (ts : List Tile) :
    ¬ Admissible n ts := by
  intro hA
  have := searchF_false hn hA n 0 0 [] (by simp)
    (fun p => by
      simp only [List.not_mem_nil, false_and, exists_false, false_iff, InRegF]
      rintro ⟨x, -, -, h0, hy⟩
      simp [col] at hy
      omega)
    (fun k hk => by simp at hk)
  unfold noTilingF at h
  rw [h] at this
  exact Bool.noConfusion this

end AlmostSq
