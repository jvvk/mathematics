import LeanProofs.RandPascal.Cert.Cases39
import LeanProofs.RandPascal.Cert.Cases40
import LeanProofs.RandPascal.Cert.Cases41
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace RandPascal.Cert

theorem chunk49 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : (c + -d) < 0)
  (h1 : (b + -2 * c + -d) < 0)
  (h2 : (b + -2 * c + d) < 0)
  (h3 : (b + -c) < 0)
  (h4 : (b + -d) < 0)
  (h5 : 0 ≤ (b + d))
  (h6 : 0 ≤ (b + 2 * c + -d))
  (h7 : (a + -3 * b + -3 * c + d) < 0)
  (h8 : (a + -3 * b + -c + -d) < 0)
  (h9 : 0 ≤ (a + -3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  by_cases h10 : 0 ≤ (a + -3 * b + c + -d)
  ·
    have h11 : 0 ≤ (a + -3 * b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    have h12 : 0 ≤ (a + -3 * b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    have h13 : 0 ≤ (a + -3 * b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
    by_cases h14 : 0 ≤ (a + -2 * b + -c)
    ·
      have h15 : 0 ≤ (a + -2 * b + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
      by_cases h16 : 0 ≤ (a + -b + -3 * c + d)
      ·
        by_cases h17 : 0 ≤ (a + -b + -c + -d)
        ·
          have h18 : 0 ≤ (a + -b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
          have h19 : 0 ≤ (a + -b) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
          have h20 : 0 ≤ (a + -b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
          have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
          have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
          have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
          have h24 : 0 ≤ (a + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
          have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
          by_cases h26 : 0 ≤ (a + b + -3 * c + -d)
          ·
            have h27 : 0 ≤ (a + b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
            have h28 : 0 ≤ (a + b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
            have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
            have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
            have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
            have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
            have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
            have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
            have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
            exact region630 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h26 : (a + b + -3 * c + -d) < 0 := lt_of_not_ge h26
            have h27 : 0 ≤ (a + b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
            have h28 : 0 ≤ (a + b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
            have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
            have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
            have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
            have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
            have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
            have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
            have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
            exact region631 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
        ·
          have h17 : (a + -b + -c + -d) < 0 := lt_of_not_ge h17
          have h18 : 0 ≤ (a + -b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
          have h19 : 0 ≤ (a + -b) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
          have h20 : 0 ≤ (a + -b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
          have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
          have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
          have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
          have h24 : 0 ≤ (a + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
          have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
          have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
          have h27 : 0 ≤ (a + b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
          by_cases h28 : 0 ≤ (a + b + -c + -d)
          ·
            have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
            have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
            have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
            have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
            have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
            have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
            have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
            exact region632 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h28 : (a + b + -c + -d) < 0 := lt_of_not_ge h28
            have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
            have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
            have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
            have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
            have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
            have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            by_cases h35 : 0 ≤ (a + 3 * b + -c + -d)
            ·
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region633 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h35 : (a + 3 * b + -c + -d) < 0 := lt_of_not_ge h35
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region634 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
      ·
        have h16 : (a + -b + -3 * c + d) < 0 := lt_of_not_ge h16
        have h17 : (a + -b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
        have h18 : 0 ≤ (a + -b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
        have h19 : 0 ≤ (a + -b) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
        have h20 : 0 ≤ (a + -b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
        have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
        have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
        have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
        have h24 : 0 ≤ (a + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
        have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
        have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
        by_cases h27 : 0 ≤ (a + b + -3 * c + d)
        ·
          by_cases h28 : 0 ≤ (a + b + -c + -d)
          ·
            have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
            have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
            have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
            have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
            have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
            have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
            have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
            exact region635 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h28 : (a + b + -c + -d) < 0 := lt_of_not_ge h28
            have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
            have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
            have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
            have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
            have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
            have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            by_cases h35 : 0 ≤ (a + 3 * b + -c + -d)
            ·
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region636 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h35 : (a + 3 * b + -c + -d) < 0 := lt_of_not_ge h35
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region637 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
        ·
          have h27 : (a + b + -3 * c + d) < 0 := lt_of_not_ge h27
          have h28 : (a + b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
          have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
          have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
          have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
          have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
          have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
          by_cases h34 : 0 ≤ (a + 3 * b + -3 * c + d)
          ·
            by_cases h35 : 0 ≤ (a + 3 * b + -c + -d)
            ·
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region638 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h35 : (a + 3 * b + -c + -d) < 0 := lt_of_not_ge h35
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region639 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h34 : (a + 3 * b + -3 * c + d) < 0 := lt_of_not_ge h34
            have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
            have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
            exact region640 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
    ·
      have h14 : (a + -2 * b + -c) < 0 := lt_of_not_ge h14
      have h15 : 0 ≤ (a + -2 * b + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
      have h16 : (a + -b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
      have h17 : (a + -b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
      have h18 : 0 ≤ (a + -b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
      have h19 : 0 ≤ (a + -b) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
      have h20 : 0 ≤ (a + -b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
      have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
      have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
      have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
      by_cases h24 : 0 ≤ (a + -c)
      ·
        have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
        have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
        by_cases h27 : 0 ≤ (a + b + -3 * c + d)
        ·
          by_cases h28 : 0 ≤ (a + b + -c + -d)
          ·
            have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
            have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
            have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
            have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
            have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
            have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
            have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
            exact region641 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h28 : (a + b + -c + -d) < 0 := lt_of_not_ge h28
            have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
            have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
            have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
            have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
            have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
            have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            by_cases h35 : 0 ≤ (a + 3 * b + -c + -d)
            ·
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region642 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h35 : (a + 3 * b + -c + -d) < 0 := lt_of_not_ge h35
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region643 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
        ·
          have h27 : (a + b + -3 * c + d) < 0 := lt_of_not_ge h27
          have h28 : (a + b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
          have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
          have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
          have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
          have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
          have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
          by_cases h34 : 0 ≤ (a + 3 * b + -3 * c + d)
          ·
            by_cases h35 : 0 ≤ (a + 3 * b + -c + -d)
            ·
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region644 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h35 : (a + 3 * b + -c + -d) < 0 := lt_of_not_ge h35
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region645 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h34 : (a + 3 * b + -3 * c + d) < 0 := lt_of_not_ge h34
            have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
            have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
            exact region646 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
      ·
        have h24 : (a + -c) < 0 := lt_of_not_ge h24
        have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
        have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
        have h27 : (a + b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
        have h28 : (a + b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
        have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
        have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
        have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
        have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
        by_cases h33 : 0 ≤ (a + 2 * b + -c)
        ·
          have h34 : (a + 3 * b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
          have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
          have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
          exact region647 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
        ·
          have h33 : (a + 2 * b + -c) < 0 := lt_of_not_ge h33
          have h34 : (a + 3 * b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
          have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
          have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
          exact region648 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
  ·
    have h10 : (a + -3 * b + c + -d) < 0 := lt_of_not_ge h10
    have h11 : 0 ≤ (a + -3 * b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    have h12 : 0 ≤ (a + -3 * b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    have h13 : 0 ≤ (a + -3 * b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
    have h14 : (a + -2 * b + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
    have h15 : 0 ≤ (a + -2 * b + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
    have h16 : (a + -b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
    have h17 : (a + -b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
    have h18 : 0 ≤ (a + -b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
    by_cases h19 : 0 ≤ (a + -b)
    ·
      by_cases h20 : 0 ≤ (a + -b + c + -d)
      ·
        have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
        have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
        have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
        by_cases h24 : 0 ≤ (a + -c)
        ·
          have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
          have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
          by_cases h27 : 0 ≤ (a + b + -3 * c + d)
          ·
            by_cases h28 : 0 ≤ (a + b + -c + -d)
            ·
              have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
              have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
              have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
              have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
              have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
              have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
              have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region649 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h28 : (a + b + -c + -d) < 0 := lt_of_not_ge h28
              have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
              have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
              have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
              have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
              have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
              have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
              by_cases h35 : 0 ≤ (a + 3 * b + -c + -d)
              ·
                have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                exact region650 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
              ·
                have h35 : (a + 3 * b + -c + -d) < 0 := lt_of_not_ge h35
                have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                exact region651 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h27 : (a + b + -3 * c + d) < 0 := lt_of_not_ge h27
            have h28 : (a + b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
            have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
            have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
            have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
            have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
            have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
            have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            by_cases h35 : 0 ≤ (a + 3 * b + -c + -d)
            ·
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region652 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h35 : (a + 3 * b + -c + -d) < 0 := lt_of_not_ge h35
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region653 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
        ·
          have h24 : (a + -c) < 0 := lt_of_not_ge h24
          have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
          have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
          have h27 : (a + b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
          have h28 : (a + b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
          have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
          have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
          have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
          have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
          by_cases h33 : 0 ≤ (a + 2 * b + -c)
          ·
            by_cases h34 : 0 ≤ (a + 3 * b + -3 * c + d)
            ·
              have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region654 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h34 : (a + 3 * b + -3 * c + d) < 0 := lt_of_not_ge h34
              have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region655 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h33 : (a + 2 * b + -c) < 0 := lt_of_not_ge h33
            have h34 : (a + 3 * b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
            have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
            exact region656 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
      ·
        have h20 : (a + -b + c + -d) < 0 := lt_of_not_ge h20
        have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
        have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
        have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
        have h24 : (a + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
        have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
        have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
        have h27 : (a + b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
        have h28 : (a + b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
        have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
        by_cases h30 : 0 ≤ (a + b + c + -d)
        ·
          have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
          have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
          by_cases h33 : 0 ≤ (a + 2 * b + -c)
          ·
            by_cases h34 : 0 ≤ (a + 3 * b + -3 * c + d)
            ·
              have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region657 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h34 : (a + 3 * b + -3 * c + d) < 0 := lt_of_not_ge h34
              have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region658 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h33 : (a + 2 * b + -c) < 0 := lt_of_not_ge h33
            have h34 : (a + 3 * b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
            have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
            exact region659 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
        ·
          have h30 : (a + b + c + -d) < 0 := lt_of_not_ge h30
          have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
          have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
          have h33 : (a + 2 * b + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
          have h34 : (a + 3 * b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
          have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
          have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
          exact region660 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
    ·
      have h19 : (a + -b) < 0 := lt_of_not_ge h19
      have h20 : (a + -b + c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
      have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
      have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
      have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
      have h24 : (a + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
      have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
      have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
      have h27 : (a + b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
      have h28 : (a + b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
      have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
      have h30 : (a + b + c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
      have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
      have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
      have h33 : (a + 2 * b + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
      have h34 : (a + 3 * b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
      have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
      have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
      exact region661 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
end RandPascal.Cert
