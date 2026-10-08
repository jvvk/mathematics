#!/bin/zsh
# Mutation tests for AlmostSquares (Inflation, Parity, Real, Examples):
# each wrong variant must FAIL to check; each unmutated copy (baseline) must pass. Run after `lake build`.
cd "${0:A:h}" || exit 1
D=AlmostSquares
M=$D/Mut.lean
mk() { sed -e "s/^namespace AlmostSq\$/namespace AlmostSqMut\nopen AlmostSq/; s/^end AlmostSq\$/end AlmostSqMut/" "$D/$1" > "$M"; }
run_mut() {
  name="$1"; file="$2"; expr="$3"
  mk "$file"; base=$(cat "$M")
  sed -i '' "$expr" "$M"
  if [[ "$(cat $M)" == "$base" ]]; then echo "MUTATION DID NOT APPLY: $name"; return; fi
  if nice -n 15 timeout 300 lake env lean --threads=1 "$M" >/dev/null 2>&1; then echo "MUTANT SURVIVED: $name"; else echo "rejected: $name"; fi
}
for file in Inflation.lean Parity.lean Real.lean Examples.lean Scales.lean Classes.lean Inflations.lean Main.lean Bouwkamp.lean Counts.lean Reach.lean; do   # unmutated renamed copies must pass
  mk "$file"
  if nice -n 15 timeout 300 lake env lean --threads=1 "$M" >/dev/null 2>&1; then echo "baseline ok: $file"; else echo "BASELINE FAILS: $file"; fi
done
run_mut "balance: right side (f W - f 0) -> f W"        Inflation.lean 's/      (f W - f 0) \* (g H - g 0) := by/      f W * (g H - g 0) := by/'
run_mut "inflation: strict -> monotone"                 Inflation.lean 's/    (hX : StrictMonoOn X (CutX W ts)) (hY : StrictMonoOn Y (CutY H ts)) :/    (hX : MonotoneOn X (CutX W ts)) (hY : StrictMonoOn Y (CutY H ts)) :/'
run_mut "inflation: size min -> max"                    Inflation.lean 's/        T.\(.size = t \* T.w + \)min /        T.\1max /'
run_mut "signed identity: S (uS - vS) -> S (uS + vS)"   Inflation.lean 's/      S \* (u S - v S) := by/      S * (u S + v S) := by/'
run_mut "parity: |T| -> |T| + 1"                        Parity.lean 's/    ((T.map (coordSum u v)).sum - T.length) % 2 = 0$/    ((T.map (coordSum u v)).sum - T.length - 1) % 2 = 0/'
run_mut "prop 112: even -> odd"                         Parity.lean 's/IsInflation 112 sq112 u v) : Even (v 112)/IsInflation 112 sq112 u v) : Odd (v 112)/'
run_mut "prop 110: odd -> even"                         Parity.lean 's/IsInflation 110 sq110 u v) : Odd (v 110)/IsInflation 110 sq110 u v) : Even (v 110)/'
run_mut "stack T112 loses the 6-square"                 Parity.lean 's/sq 18 70 42, sq 6 82 60, sq 11 82 66/sq 18 70 42, sq 11 82 66/'
run_mut "sq139: one square moved"                       Parity.lean 's/^  sq 1 29 30,$/  sq 1 30 30,/'
run_mut "integer corners: x -> x/2"                     Real.lean 's/    ∀ T ∈ ts, IsInt T.x ∧ IsInt T.y := fun T hT =>/    ∀ T ∈ ts, IsInt (T.x \/ 2) ∧ IsInt T.y := fun T hT =>/'
run_mut "real theorem: drop 18 from the list"           Real.lean 's/(∃ ts : List RTile, RAdmissible n ts) ↔ n ∈ \[4, 10, 12, 14, 15, 18\] ∨ 20 ≤ n/(∃ ts : List RTile, RAdmissible n ts) ↔ n ∈ [4, 10, 12, 14, 15] ∨ 20 ≤ n/'
run_mut "Moron: v(10) = 1 -> 2"                         Examples.lean 's/def moronV (b : ℤ) : ℤ := if b = 10 then 1 else 0/def moronV (b : ℤ) : ℤ := if b = 10 then 2 else 0/'
run_mut "Moron: 43 -> 44"                               Examples.lean 's/T = 1)).map Tile.w).sum = 43/T = 1)).map Tile.w).sum = 44/'
run_mut "112 example: signed sum 112 -> 111"            Examples.lean 's/T \* T.w)).sum = 112 ∧/T * T.w)).sum = 111 ∧/'
run_mut "112 example: t = 2 -> t = 1"                   Examples.lean 's/Admissible 224 (sq112.map (img (scaleShift 2 u112) (scaleShift 2 v112)))/Admissible 112 (sq112.map (img (scaleShift 1 u112) (scaleShift 1 v112)))/'
run_mut "Lemma 4: drop the collision hypothesis"        Scales.lean 's/    (hcol : ∀ T ∈ ts, ∀ U ∈ ts, T.w ≠ U.w →/    (hcol : True) (hcol2 : ∀ T ∈ ts, ∀ U ∈ ts, T.w ≠ U.w →/'
run_mut "collision check: < t0 -> <= t0"                Classes.lean 's/    decide ((cmin u v U - cmin u v T) \/ (T.w - U.w) < t0)/    decide ((cmin u v U - cmin u v T) \/ (T.w - U.w) ≤ t0)/'
run_mut "class data: one shift value changed"           Inflations.lean 's/(29, -32), (33, -35)/(29, -31), (33, -35)/'
run_mut "coverage: even residues -> odd"                Main.lean 's/theorem resid112 : ∀ r : ℕ, r < 112 → r % 2 = 0 →/theorem resid112 : ∀ r : ℕ, r < 112 → r % 2 = 1 →/'
run_mut "Bouwkamp 112: last group 33 -> 34"             Bouwkamp.lean 's/\[4, 37\], \[33\]\]/[4, 37], [34]]/'
run_mut "Bouwkamp: 139 code checked against 110 layout" Bouwkamp.lean 's/codeIs code139 139 139 sq139/codeIs code139 139 139 sq110/'
run_mut "Table 2: last entry 56 -> 55"                   Counts.lean 's/30, 27, 42, 56\]/30, 27, 42, 55]/'
run_mut "cnt: empty case counts every t"                 Counts.lean 's/  | 0, t => if t = 0 then 1 else 0/  | 0, t => 1/'
run_mut "uncovered: 151 -> 150"                          Counts.lean 's/uncovered.length = 151/uncovered.length = 150/'
run_mut "thresholds: t0 <= 3 -> t0 <= 2"                 Counts.lean 's/(I.V - (r : ℤ)) % 112 = 0 ∧ I.t0 ≤ 3/(I.V - (r : ℤ)) % 112 = 0 ∧ I.t0 ≤ 2/'
run_mut "pieces: 22 -> 21"                               Counts.lean 's/(base 110).length = 22/(base 110).length = 21/'
run_mut "57x55: 67 -> 68"                                Reach.lean 's/dedup.length = 67/dedup.length = 68/'
run_mut "Moron: n = 60 -> 61"                            Reach.lean 's/(tab \[(9, -1), (10, -2), (14, -1), (17, -2), (32, -4)\]) 60 = true/(tab [(9, -1), (10, -2), (14, -1), (17, -2), (32, -4)]) 61 = true/'
rm -f "$M"
