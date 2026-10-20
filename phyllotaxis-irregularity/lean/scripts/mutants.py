"""Mutation tests for the Lean files: each mutant plants one wrong constant, sign, hypothesis or statement and
must make its file fail to compile. Run from lean/ after `lake build LeanProofs`."""
import subprocess, sys

MUTANTS = [
    ('LeanProofs/Phyllotaxis/Tilings.lean', 'threshold law sign flipped', '    m * sin β + n * sin (β + π / 3) = 0 ↔ tan β = -(√3 * n) / (2 * m + n) := by', '    m * sin β + n * sin (β + π / 3) = 0 ↔ tan β = (√3 * n) / (2 * m + n) := by'),
    ('LeanProofs/Phyllotaxis/Tilings.lean', '(1,2) threshold tan -sqrt3/3', '    1 * sin β + 2 * sin (β + π / 3) = 0 ↔ tan β = -(√3 / 2) := by', '    1 * sin β + 2 * sin (β + π / 3) = 0 ↔ tan β = -(√3 / 3) := by'),
    ('LeanProofs/Phyllotaxis/Tilings.lean', 'K0 threshold tan -sqrt3/2', '    3 * sin β + 2 * sin (β + π / 3) = 0 ↔ tan β = -(√3 / 4) := by', '    3 * sin β + 2 * sin (β + π / 3) = 0 ↔ tan β = -(√3 / 2) := by'),
    ('LeanProofs/Phyllotaxis/Tilings.lean', 'rotation by 60 with wrong sign', 'def rot60 (p : ℚ × ℚ) : ℚ × ℚ := ((p.1 - 3 * p.2) / 2, (p.1 + p.2) / 2)', 'def rot60 (p : ℚ × ℚ) : ℚ × ℚ := ((p.1 + 3 * p.2) / 2, (p.1 + p.2) / 2)'),
    ('LeanProofs/Phyllotaxis/Tilings.lean', 'pentagon apex moved', 'def Q : ℚ × ℚ := (11, 2)', 'def Q : ℚ × ℚ := (11, 5 / 2)'),
    ('LeanProofs/Phyllotaxis/Tilings.lean', 'Q tangent to P1 (distance 1 instead of sqrt3)', 'theorem Q_P1 : nsq (Q - z4) = 3 * 19 := by', 'theorem Q_P1 : nsq (Q - z4) = 19 := by'),
    ('LeanProofs/Phyllotaxis/Tilings.lean', 'T-Q distance 2 instead of sqrt3', 'theorem sqrt3_distances : nsq (T - Q) = 3 * 19 ∧ nsq (Q - z1) = 3 * 19 := by', 'theorem sqrt3_distances : nsq (T - Q) = 4 * 19 ∧ nsq (Q - z1) = 3 * 19 := by'),
    ('LeanProofs/Phyllotaxis/Tilings.lean', 'K0 height gap sqrt(3/19)', '    (emb 19 T).2 - (emb 19 Q).2 = √(3 / 76) ∧ (emb 19 Q).2 - (emb 19 z1).2 = √(3 / 76) := by', '    (emb 19 T).2 - (emb 19 Q).2 = √(3 / 19) ∧ (emb 19 Q).2 - (emb 19 z1).2 = √(3 / 76) := by'),
    ('LeanProofs/Phyllotaxis/Tilings.lean', 'alternation margin sqrt(3/7)', 'theorem alternation_margin : (emb 7 Rnext).2 - (emb 7 Tlow).2 = √(3 / 28) := by', 'theorem alternation_margin : (emb 7 Rnext).2 - (emb 7 Tlow).2 = √(3 / 7) := by'),
    ('LeanProofs/Phyllotaxis/Tilings.lean', 'K0 period 18', 'theorem period : z7 = (19, 0) := by', 'theorem period : z7 = (18, 0) := by'),
    ('LeanProofs/Phyllotaxis/Static.lean', 'pentagon margin: rate coefficient 5 sqrt3 -> 3 sqrt3', '  √3 / 2 * (ε - σ) + k * (3 * Wi + 5 * √3 * Wr) / 8', '  √3 / 2 * (ε - σ) + k * (3 * Wi + 3 * √3 * Wr) / 8'),
    ('LeanProofs/Phyllotaxis/Static.lean', 'channel margin: 2 sigma -> sigma', '  √3 / 2 * (2 * σ + α - ε) - k * (3 * Wi + √3 * Wr) / 2', '  √3 / 2 * (σ + α - ε) - k * (3 * Wi + √3 * Wr) / 2'),
    ('LeanProofs/Phyllotaxis/Static.lean', 'window upper bound: /4 -> /2', '        σ < ε - |k| * (√3 * Real.sin u + 5 * Real.cos u) / 4) := by', '        σ < ε - |k| * (√3 * Real.sin u + 5 * Real.cos u) / 2) := by'),
    ('LeanProofs/Phyllotaxis/Static.lean', 'window lower bound: alpha sign', '      ((ε - α) / 2 - |k| * (√3 * Real.sin u + Real.cos u) / 2 < σ ∧', '      ((ε + α) / 2 - |k| * (√3 * Real.sin u + Real.cos u) / 2 < σ ∧'),
    ('LeanProofs/Phyllotaxis/Static.lean', 'notch-60 law: m -> n in numerator', '    m * Real.sin (u - 2 * π / 3) + n * Real.sin u = 0 ↔ Real.tan u = √3 * m / (2 * n - m) := by', '    m * Real.sin (u - 2 * π / 3) + n * Real.sin u = 0 ↔ Real.tan u = √3 * n / (2 * n - m) := by'),
    ('LeanProofs/Phyllotaxis/Static.lean', 'B at distance 2 from Q0 instead of sqrt3', '    d2 Z Q = 1 ∧ d2 A Q = 1 ∧ d2 C Q = 1 ∧ d2 E Q = 1 ∧ d2 B Q = 3 ∧ d2 Z E = 4 ∧', '    d2 Z Q = 1 ∧ d2 A Q = 1 ∧ d2 C Q = 1 ∧ d2 E Q = 1 ∧ d2 B Q = 4 ∧ d2 Z E = 4 ∧'),
    ('LeanProofs/Phyllotaxis/Static.lean', 'ZA height gap halved', "    √3 * (Wi * (V.x' - Q.x') + Wr * (V.y' - Q.y')) = 2 * Rm α σ ε k Wr Wi * Wr := by", "    √3 * (Wi * (V.x' - Q.x') + Wr * (V.y' - Q.y')) = Rm α σ ε k Wr Wi * Wr := by"),
    ('LeanProofs/Phyllotaxis/Static.lean', 'ZC overlap rate -(P+R) -> -P', '    HasDerivAt (clr (k * Wi) (k * Wr) F.A Q) (2 * -(Pm α σ ε k Wr Wi + Rm α σ ε k Wr Wi)) 0 := by', '    HasDerivAt (clr (k * Wi) (k * Wr) F.A Q) (2 * -(Pm α σ ε k Wr Wi)) 0 := by'),
    ('LeanProofs/Phyllotaxis/Static.lean', 'notch hinge normalised by omega instead of -omega', '  hσ : HasDerivAt (fun t => arg ((B.pos t - A.pos t) / (-ω * (C.pos t - B.pos t)))) σ 0', '  hσ : HasDerivAt (fun t => arg ((B.pos t - A.pos t) / (ω * (C.pos t - B.pos t)))) σ 0'),
    ('LeanProofs/Phyllotaxis/Static.lean', 'pentagon_first with non-strict channel margin', '    (hPm : 0 < Pm α σ ε k Wr Wi) (hRm : 0 < Rm α σ ε k Wr Wi)', '    (hPm : 0 < Pm α σ ε k Wr Wi) (hRm : 0 ≤ Rm α σ ε k Wr Wi)'),
    ('LeanProofs/Phyllotaxis/StaticExists.lean', 'existence: notch turning at 2 sigma', '  set θA : ℝ → ℝ := fun t => π / 3 + σ * t', '  set θA : ℝ → ℝ := fun t => π / 3 + 2 * σ * t'),
    ('LeanProofs/Phyllotaxis/StaticExists.lean', 'existence: height functional with Wr, Wi swapped', 'def hgt (z : ℂ) : ℝ := Wi * z.re + Wr * z.im', 'def hgt (z : ℂ) : ℝ := Wr * z.re + Wi * z.im'),
    ('LeanProofs/Phyllotaxis/Static.lean', 'notch clearance rate term /8 -> /4', '      (2 * (√3 / 2 * σ - k * (√3 * Wr + 3 * Wi) / 8)) 0 := by', '      (2 * (√3 / 2 * σ - k * (√3 * Wr + 3 * Wi) / 4)) 0 := by'),
    ('LeanProofs/Phyllotaxis/Static.lean', 'channel opens for growing disks too (k >= 0)', 'theorem channel_of_valid {α σ ε k Wr Wi : ℝ} (hk : k ≤ 0) (hW : 0 ≤ 3 * Wi + √3 * Wr)', 'theorem channel_of_valid {α σ ε k Wr Wi : ℝ} (hk : 0 ≤ k) (hW : 0 ≤ 3 * Wi + √3 * Wr)'),
    ('LeanProofs/Phyllotaxis/FirstOrder.lean', 'Lemma 1 coefficient halved', '    (Q.vel - A.vel) - (C.vel - B.vel) = I * (C.pos 0 - B.pos 0) * (B.pos 0 - A.pos 0) / b0 := by', '    (Q.vel - A.vel) - (C.vel - B.vel) = I * (C.pos 0 - B.pos 0) * (B.pos 0 - A.pos 0) / (2 * b0) := by'),
    ('LeanProofs/Phyllotaxis/FirstOrder.lean', 'Lemma 1 sign flipped', '    (Q.vel - A.vel) - (C.vel - B.vel) = I * (C.pos 0 - B.pos 0) * (B.pos 0 - A.pos 0) / b0 := by', '    (Q.vel - A.vel) - (C.vel - B.vel) = -I * (C.pos 0 - B.pos 0) * (B.pos 0 - A.pos 0) / b0 := by'),
    ('LeanProofs/Phyllotaxis/FirstOrder.lean', 'Lemma 3 missing factor 1/2', '    (Q.vel - B.vel) - ω * (C.vel - B.vel) = I * (C.pos 0 - B.pos 0) ^ 2 / (2 * b0) := by', '    (Q.vel - B.vel) - ω * (C.vel - B.vel) = I * (C.pos 0 - B.pos 0) ^ 2 / b0 := by'),
    ('LeanProofs/Phyllotaxis/FirstOrder.lean', 'Lemma 3 phase of the new up instead of U', '    (Q.vel - B.vel) - ω * (C.vel - B.vel) = I * (C.pos 0 - B.pos 0) ^ 2 / (2 * b0) := by', '    (Q.vel - B.vel) - ω * (C.vel - B.vel) = I * (C.pos 0 - B.pos 0) * (Q.pos 0 - B.pos 0) / (2 * b0) := by'),
    ('LeanProofs/Phyllotaxis/FirstOrder.lean', 'tangency derivative without the 1/2', '      b0 * (hs * (P.x 0 + Q.x 0) + hc * (P.y 0 + Q.y 0)) / 2 := by', '      b0 * (hs * (P.x 0 + Q.x 0) + hc * (P.y 0 + Q.y 0)) := by'),
    ('LeanProofs/Phyllotaxis/FirstOrder.lean', 'cushion phase beta + 60', '      (Real.cos (β - π / 3) / 2) 0 := by', '      (Real.cos (β + π / 3) / 2) 0 := by'),
    ('LeanProofs/Phyllotaxis/FirstOrder.lean', 'split rate cos beta (no 1/2)', '      (Real.cos β / 2) 0 := by\n  have hξ := triangle_step hb B C Q hBC hBQ hQC hQ0\n  have hF := (Q', '      (Real.cos β) 0 := by\n  have hξ := triangle_step hb B C Q hBC hBQ hQC hQ0\n  have hF := (Q'),
    ('LeanProofs/Phyllotaxis/FirstOrder.lean', 'pass rate safe sign flipped', '    HasDerivAt (fun c => arg ((C.pos c - Q.pos c) / (B.pos c - A.pos c))) (-Real.cos β) 0 := by', '    HasDerivAt (fun c => arg ((C.pos c - Q.pos c) / (B.pos c - A.pos c))) (Real.cos β) 0 := by'),
    ('LeanProofs/Phyllotaxis/FirstOrder.lean', 'up rotation sin instead of cos', '    HasDerivAt (fun c => arg ((Q.pos c - A.pos c) / (C.pos c - B.pos c))) (Real.cos β) 0 := by', '    HasDerivAt (fun c => arg ((Q.pos c - A.pos c) / (C.pos c - B.pos c))) (Real.sin β) 0 := by'),
    ('LeanProofs/Phyllotaxis/FirstOrder.lean', 'N=1 margin 1/2 instead of 3/2', '      3 / 2 * |c| * Real.cos β := by', '      1 / 2 * |c| * Real.cos β := by'),
    ('LeanProofs/Phyllotaxis/FirstOrder.lean', 'cos split sums to 2 cos', 'theorem cos_split (β : ℝ) : Real.cos (β - π / 3) + Real.cos (β + π / 3) = Real.cos β := by', 'theorem cos_split (β : ℝ) : Real.cos (β - π / 3) + Real.cos (β + π / 3) = 2 * Real.cos β := by'),
    ('LeanProofs/Phyllotaxis/Apex.lean', 'IFT without transversality', '    (hT : (q0.1 - ax 0) * (q0.2 - cy 0) - (q0.2 - ay 0) * (q0.1 - cx 0) ≠ 0) :\n    ∃ ψ', '    :\n    ∃ ψ'),
    ('LeanProofs/Phyllotaxis/Apex.lean', 'triangle family with |U|^2 = b0^2 + 1', 'theorem triangle_family_exists {b0 ux uy : ℝ} (hb : 0 < b0) (hU : ux ^ 2 + uy ^ 2 = b0 ^ 2) :', 'theorem triangle_family_exists {b0 ux uy : ℝ} (hb : 0 < b0) (hU : ux ^ 2 + uy ^ 2 = b0 ^ 2 + 1) :'),
    ('LeanProofs/Phyllotaxis/Apex.lean', 'rhombic family with parallel U, D allowed', '    (hD : dx ^ 2 + dy ^ 2 = b0 ^ 2) (hnd : ux * dy - uy * dx ≠ 0) :', '    (hD : dx ^ 2 + dy ^ 2 = b0 ^ 2) :'),
    ('LeanProofs/Phyllotaxis/Lemma4.lean', 'dG/dc with +s', '      ((5 * (s / 2 + √3 / 2 * k) - s) / 2) 0 := by\n  have h3', '      ((5 * (s / 2 + √3 / 2 * k) + s) / 2) 0 := by\n  have h3'),
    ('LeanProofs/Phyllotaxis/Lemma4.lean', 'dG/dtheta = 1', '    HasDerivAt (fun θ => (Q.x θ - P2.x θ) ^ 2 + (Q.y θ - P2.y θ) ^ 2 - 1) √3 0 := by', '    HasDerivAt (fun θ => (Q.x θ - P2.x θ) ^ 2 + (Q.y θ - P2.y θ) ^ 2 - 1) 1 0 := by'),
    ('LeanProofs/Phyllotaxis/Lemma4.lean', 'kappa2 with 3 instead of 3 sqrt3', '      -(Real.cos β + 3 * √3 * Real.sin β) / 4 := by', '      -(Real.cos β + 3 * Real.sin β) / 4 := by'),
    ('LeanProofs/Phyllotaxis/Lemma4.lean', 'kappa2 at K0 = 13/(2 sqrt19)', '    -(cβ + 3 * √3 * sβ) / 4 = 11 / (2 * √19) := by', '    -(cβ + 3 * √3 * sβ) / 4 = 13 / (2 * √19) := by'),
    ('LeanProofs/Phyllotaxis/Lemma4.lean', 'N=1 exclusion kappa2 11/(4 sqrt7)', '    -(cβ + 3 * √3 * sβ) / 4 = 13 / (4 * √7) ∧ 3 / 2 * cU = 15 / (4 * √7) ∧', '    -(cβ + 3 * √3 * sβ) / 4 = 11 / (4 * √7) ∧ 3 / 2 * cU = 15 / (4 * √7) ∧'),
    ('LeanProofs/Phyllotaxis/Lemma4.lean', 'boundary slope sign flipped', "    (hzero : ∀ᶠ c in 𝓝 0, G (θs c, c) = 0) : θ' = -b / a := by", "    (hzero : ∀ᶠ c in 𝓝 0, G (θs c, c) = 0) : θ' = b / a := by"),
    ('LeanProofs/Phyllotaxis/Lemma4.lean', 'binding constraint |Q - P1| = 1', 'theorem binding_constraint : (3 / 2 - 0 : ℝ) ^ 2 + (√3 / 2 - 0) ^ 2 = 3 := by', 'theorem binding_constraint : (3 / 2 - 0 : ℝ) ^ 2 + (√3 / 2 - 0) ^ 2 = 1 := by'),
    ('LeanProofs/Phyllotaxis/Lemma4Exists.lean', 'pentagon apex at the wrong base point', '      (P0.x 0 = 1 / 2 ∧ P0.y 0 = √3 / 2) ∧ (Q.x 0 = 3 / 2 ∧ Q.y 0 = √3 / 2) ∧', '      (P0.x 0 = 1 / 2 ∧ P0.y 0 = √3 / 2) ∧ (Q.x 0 = 3 / 2 ∧ Q.y 0 = √3) ∧'),
    ('LeanProofs/Phyllotaxis/Lemma4Exists.lean', "D' direction not kept (slope 1 instead of sqrt3)", "      P2.y' = 0 ∧ P3.y' = 0 ∧ P0.y' = √3 * P0.x' := by", "      P2.y' = 0 ∧ P3.y' = 0 ∧ P0.y' = P0.x' := by"),
    ('LeanProofs/Phyllotaxis/Lemma4Exists.lean', 'P3 not turning (velocity 0)', "      (P3.x 0 = 2 ∧ P3.y 0 = 0) ∧ (P3.x' = 0 ∧ P3.y' = 1) ∧", "      (P3.x 0 = 2 ∧ P3.y 0 = 0) ∧ (P3.x' = 0 ∧ P3.y' = 0) ∧"),
    ('LeanProofs/Phyllotaxis/Prop2.lean', 'matched sums with 2m leftover', '    ‖∑ k ∈ range Ku, a k - ∑ k ∈ range Kv, b k‖ ≤ Ku * η + 3 * m := by', '    ‖∑ k ∈ range Ku, a k - ∑ k ∈ range Kv, b k‖ ≤ Ku * η + 2 * m := by'),
    ('LeanProofs/Phyllotaxis/Prop2.lean', 'matched sums without the pairing error', '    ‖∑ k ∈ range Ku, a k - ∑ k ∈ range Kv, b k‖ ≤ Ku * η + 3 * m := by', '    ‖∑ k ∈ range Ku, a k - ∑ k ∈ range Kv, b k‖ ≤ 3 * m := by'),
    ('LeanProofs/Phyllotaxis/Prop2.lean', 'phase matching 2nm eps', '    ‖f (du k) (tu k) - f (dv (k + δ)) (tv (k + δ))‖ ≤ 3 * n * m * ε := by', '    ‖f (du k) (tu k) - f (dv (k + δ)) (tv (k + δ))‖ ≤ 2 * n * m * ε := by'),
    ('LeanProofs/Phyllotaxis/Prop2.lean', 'sweep offset off by one', '    du k = dv (k + ((αv - αu) % m).toNat) := by', '    du k = dv (k + ((αv - αu) % m).toNat + 1) := by'),
    ('LeanProofs/Phyllotaxis/Prop2.lean', 'log factor without the remainder term', '    ‖log (1 + (I * c * a + r)) - I * c * a‖ ≤ (|c| + R * c ^ 2) ^ 2 + R * c ^ 2 := by', '    ‖log (1 + (I * c * a + r)) - I * c * a‖ ≤ (|c| + R * c ^ 2) ^ 2 := by'),
    ('LeanProofs/Phyllotaxis/Prop2.lean', 'Prop 2 with m leftover', '      |c| * (Ku * (3 * n * m * ε) + 3 * m) + (Ku + Kv) * ((|c| + R * c ^ 2) ^ 2 + R * c ^ 2) := by', '      |c| * (Ku * (3 * n * m * ε) + m) + (Ku + Kv) * ((|c| + R * c ^ 2) ^ 2 + R * c ^ 2) := by'),
    ('LeanProofs/Phyllotaxis/Prop2.lean', 'Prop 2 for |c| + R c^2 <= 1', '    (hc : |c| + R * c ^ 2 ≤ 1 / 2)\n    (f : ℕ → ℕ → ℂ)', '    (hc : |c| + R * c ^ 2 ≤ 1)\n    (f : ℕ → ℕ → ℂ)'),
    ('LeanProofs/Phyllotaxis/Sweep.lean', 'labels increase with passes', '    labels r0 s i = r0 i - (s.count i : ZMod m) := by', '    labels r0 s i = r0 i + (s.count i : ZMod m) := by'),
    ('LeanProofs/Phyllotaxis/Sweep.lean', 'sweep off by one', '    labels r0 (s.take j) s[j] - 1 = r0 s[j] - (((s.take (j + 1)).count s[j] : ℕ) : ZMod m) := by', '    labels r0 (s.take j) s[j] - 1 = r0 s[j] + 1 - (((s.take (j + 1)).count s[j] : ℕ) : ZMod m) := by'),
    ('LeanProofs/Phyllotaxis/Sweep.lean', 'alternation gap parity shifted', '    gaps g0 (alt a (a + 1) j) a = g0 a + (j % 2 : ℕ) := by', '    gaps g0 (alt a (a + 1) j) a = g0 a + ((j + 1) % 2 : ℕ) := by'),
    ('LeanProofs/Phyllotaxis/PassBalance.lean', 'balance bound m - 1 instead of m', '    |(s.count j : ℤ) - s.count k| ≤ ∑ i, g0 i := by', '    |(s.count j : ℤ) - s.count k| ≤ ∑ i, g0 i - 1 := by'),
    ('LeanProofs/Phyllotaxis/PassBalance.lean', 'balance without nonnegative final gaps', '    (h0 : ∀ i, 0 ≤ g0 i) (hs : ∀ i, 0 ≤ gaps g0 s i) (j k : Fin n) :', '    (h0 : ∀ i, 0 ≤ g0 i) (j k : Fin n) :'),
    ('LeanProofs/Phyllotaxis/PassBalance.lean', 'lag bound without the factor n', '    |(n : ℤ) * s.count u - s.length| ≤ (n : ℤ) * ∑ i, g0 i := by', '    |(n : ℤ) * s.count u - s.length| ≤ ∑ i, g0 i := by'),
    ('LeanProofs/Phyllotaxis/PassBalance.lean', 'gap formula with the pass direction reversed', '    gaps g0 s i = g0 i + (s.count i : ℤ) - (s.count (i + 1) : ℤ) := by', '    gaps g0 s i = g0 i + (s.count i : ℤ) - (s.count (i - 1) : ℤ) := by'),
    ('LeanProofs/Phyllotaxis/PassBalance.lean', 'total downs not conserved (+1)', '    ∑ i, gaps g0 s i = ∑ i, g0 i := by', '    ∑ i, gaps g0 s i = ∑ i, g0 i + 1 := by'),
]

killed = 0
for src, name, old, new in MUTANTS:
    text = open(src).read()
    assert text.count(old) == 1, f"{name}: anchor not unique in {src}"
    open(src, "w").write(text.replace(old, new))
    try:
        r = subprocess.run(["lake", "env", "lean", src], capture_output=True, text=True, timeout=1200)
        dead = r.returncode != 0 or "error" in r.stdout + r.stderr
    finally:
        open(src, "w").write(text)
    killed += dead
    print(("killed   " if dead else "SURVIVED ") + f"{src}: {name}", flush=True)
print(f"{killed}/{len(MUTANTS)} mutants killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
