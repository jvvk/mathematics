#!/bin/zsh
# Mutation tests for SixCircles/Note.lean: each wrong variant of a step must FAIL to check.
cd "${0:A:h}" || exit 1
SRC=SixCircles/Note.lean; M=SixCircles/NoteMut.lean
base() { sed -e 's/namespace SixCircles/namespace SixNoteMut/; s/end SixCircles/end SixNoteMut/' $SRC; }
run_mut() {
  name="$1"; expr="$2"
  base > "$M"; sed -i '' "$expr" "$M"
  if cmp -s "$M" <(base); then echo "MUTATION DID NOT APPLY: $name"; return; fi
  if nice -n 15 timeout 600 lake env lean "$M" >/dev/null 2>&1; then echo "MUTANT SURVIVED: $name"; else echo "rejected: $name"; fi
}
run_mut "theorem: conclusion off by one"     's/= (2 \* h) ^ 2 := by/= (2 * h) ^ 2 + 1 := by/'
run_mut "theorem: C-A tangency wrong"        "s/(hCA' : (a - c) ^ 2 + (2 \* h - a - c) ^ 2 = (a + c) ^ 2)/(hCA' : (a - c) ^ 2 + (2 * h - a - c) ^ 2 = (2 * a + c) ^ 2)/"
run_mut "tangent length: rho sigma, not 2"   's/(h : sep ^ 2 + (ρ ^ 2 - σ ^ 2) ^ 2 = (ρ ^ 2 + σ ^ 2) ^ 2) : sep = 2 \* ρ \* σ/(h : sep ^ 2 + (ρ ^ 2 - σ ^ 2) ^ 2 = (ρ ^ 2 + σ ^ 2) ^ 2) : sep = ρ * σ/'
run_mut "AtCt: not twice OB_t"               's/    2 \* β \* (α + γ) = 2 \* d := by/    2 * β * (α + γ) = d := by/'
run_mut "bisector: wrong ratio"              's/    m \* d = (x - m) \* h := by/    m * d = (x + m) * h := by/'
run_mut "bisects: wrong angle condition"     's/(hratio : m \* d = (x - m) \* h) : h \* d = m \* x + h ^ 2/(hratio : m * d = (x - m) * h) : h * d = m * x + 2 * h ^ 2/'
run_mut "homothety: wrong ratio"             's/    a \* (C1 - T1) = c \* (T1 - A1) ∧/    a * (C1 - T1) = 2 * c * (T1 - A1) ∧/'
run_mut "T on circle: radius 2a"             's/    (T1 - A1) ^ 2 + (T2 - A2) ^ 2 = a ^ 2 := by/    (T1 - A1) ^ 2 + (T2 - A2) ^ 2 = 4 * a ^ 2 := by/'
run_mut "double angle: 3 not 2"              's/    x \* (h ^ 2 - m ^ 2) = 2 \* m \* h ^ 2 := by/    x * (h ^ 2 - m ^ 2) = 3 * m * h ^ 2 := by/'
run_mut "radius: not parallel to OB_t"       's/    (T1 - A1) \* h - (T2 - A2) \* x = 0 := by/    (T1 - A1) * h + (T2 - A2) * x = 0 := by/'
run_mut "line of centres: not parallel"      's/: (C1 - A1) \* h - (C2 - A2) \* x = 0 := by/: (C1 - A1) * h + (C2 - A2) * x = 0 := by/'
run_mut "tangents: MK = 2 MU"                's/    (h \/ d \* x - m) ^ 2 + (h \/ d \* h - h) ^ 2 = m ^ 2 := by/    (h \/ d * x - m) ^ 2 + (h \/ d * h - h) ^ 2 = 4 * m ^ 2 := by/'
run_mut "angle at M: d + h"                  's/    (d - h) \* h = m \* x := by/    (d + h) * h = m * x := by/'
run_mut "congruence: S0X = d + h"            's/    m \/ h \* x = d - h := by/    m \/ h * x = d + h := by/'
run_mut "Step 4: angle at E' wrong"          's/  have hOEA : ∠ O E A = π \/ 2 - ψ := by/  have hOEA : ∠ O E A = π \/ 3 - ψ := by/'
run_mut "Step 4: angle at O wrong"           's/  have hUOB : ∠ U O B = 2 \* ψ := by/  have hUOB : ∠ U O B = 3 * ψ := by/'
run_mut "Step 4: OA = 2h"                    's/    p ^ 2 + s ^ 2 = h ^ 2 := by/    p ^ 2 + s ^ 2 = 4 * h ^ 2 := by/'
rm -f "$M"
