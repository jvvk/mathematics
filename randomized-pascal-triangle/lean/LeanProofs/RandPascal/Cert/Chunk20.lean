import LeanProofs.RandPascal.Cert.Cases12
import LeanProofs.RandPascal.Cert.Cases13
import LeanProofs.RandPascal.Cert.Cases14
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace RandPascal.Cert

theorem chunk20 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : (b + -2 * c + -d) < 0)
  (h2 : (b + -2 * c + d) < 0)
  (h3 : (b + -c) < 0)
  (h4 : (b + -d) < 0)
  (h5 : 0 ≤ (b + d))
  (h6 : 0 ≤ (b + 2 * c + -d))
  (h7 : (a + -3 * b + -3 * c + d) < 0)
  (h8 : (a + -3 * b + -c + -d) < 0)
  (h9 : (a + -3 * b + -c + d) < 0)
  (h10 : (a + -3 * b + c + -d) < 0)
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  by_cases h11 : 0 ≤ (a + -3 * b + c + d)
  ·
    have h12 : 0 ≤ (a + -3 * b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    have h13 : 0 ≤ (a + -3 * b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
    have h14 : (a + -2 * b + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
    by_cases h15 : 0 ≤ (a + -2 * b + c)
    ·
      have h16 : (a + -b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
      have h17 : (a + -b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
      by_cases h18 : 0 ≤ (a + -b + -c + d)
      ·
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
            have h28 : 0 ≤ (a + b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
            have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
            have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
            have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
            have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
            have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
            have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
            have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
            exact region206 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h27 : (a + b + -3 * c + d) < 0 := lt_of_not_ge h27
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
              exact region207 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h28 : (a + b + -c + -d) < 0 := lt_of_not_ge h28
              have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
              have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
              have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
              have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
              have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
              have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
              have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region208 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
              have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region209 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h34 : (a + 3 * b + -3 * c + d) < 0 := lt_of_not_ge h34
              by_cases h35 : 0 ≤ (a + 3 * b + -c + -d)
              ·
                have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                exact region210 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
              ·
                have h35 : (a + 3 * b + -c + -d) < 0 := lt_of_not_ge h35
                have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                exact region211 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h33 : (a + 2 * b + -c) < 0 := lt_of_not_ge h33
            have h34 : (a + 3 * b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
            have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
            exact region212 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
      ·
        have h18 : (a + -b + -c + d) < 0 := lt_of_not_ge h18
        by_cases h19 : 0 ≤ (a + -b)
        ·
          have h20 : 0 ≤ (a + -b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
          have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
          have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
          have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
          have h24 : (a + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
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
              have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region213 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h34 : (a + 3 * b + -3 * c + d) < 0 := lt_of_not_ge h34
              by_cases h35 : 0 ≤ (a + 3 * b + -c + -d)
              ·
                have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                exact region214 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
              ·
                have h35 : (a + 3 * b + -c + -d) < 0 := lt_of_not_ge h35
                have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                exact region215 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h33 : (a + 2 * b + -c) < 0 := lt_of_not_ge h33
            have h34 : (a + 3 * b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
            have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
            have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
            exact region216 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
        ·
          have h19 : (a + -b) < 0 := lt_of_not_ge h19
          by_cases h20 : 0 ≤ (a + -b + c + -d)
          ·
            have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
            have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
            have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
            have h24 : (a + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
            have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
            have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
            have h27 : (a + b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
            have h28 : (a + b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
            by_cases h29 : 0 ≤ (a + b + -c + d)
            ·
              have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
              have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
              have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
              by_cases h33 : 0 ≤ (a + 2 * b + -c)
              ·
                by_cases h34 : 0 ≤ (a + 3 * b + -3 * c + d)
                ·
                  have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
                  have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                  exact region217 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                ·
                  have h34 : (a + 3 * b + -3 * c + d) < 0 := lt_of_not_ge h34
                  by_cases h35 : 0 ≤ (a + 3 * b + -c + -d)
                  ·
                    have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                    exact region218 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                  ·
                    have h35 : (a + 3 * b + -c + -d) < 0 := lt_of_not_ge h35
                    have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                    exact region219 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
              ·
                have h33 : (a + 2 * b + -c) < 0 := lt_of_not_ge h33
                have h34 : (a + 3 * b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
                have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
                have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                exact region220 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h29 : (a + b + -c + d) < 0 := lt_of_not_ge h29
              have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
              have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
              have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
              have h33 : (a + 2 * b + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
              have h34 : (a + 3 * b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
              have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region221 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
            have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
            have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
            have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
            by_cases h33 : 0 ≤ (a + 2 * b + -c)
            ·
              by_cases h34 : 0 ≤ (a + 3 * b + -3 * c + d)
              ·
                have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
                have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                exact region222 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
              ·
                have h34 : (a + 3 * b + -3 * c + d) < 0 := lt_of_not_ge h34
                by_cases h35 : 0 ≤ (a + 3 * b + -c + -d)
                ·
                  have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                  exact region223 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                ·
                  have h35 : (a + 3 * b + -c + -d) < 0 := lt_of_not_ge h35
                  have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                  exact region224 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h33 : (a + 2 * b + -c) < 0 := lt_of_not_ge h33
              have h34 : (a + 3 * b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
              have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
              have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
              exact region225 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
    ·
      have h15 : (a + -2 * b + c) < 0 := lt_of_not_ge h15
      have h16 : (a + -b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
      have h17 : (a + -b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
      have h18 : (a + -b + -c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
      have h19 : (a + -b) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
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
      have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
      have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
      have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
      have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
      by_cases h34 : 0 ≤ (a + 3 * b + -3 * c + d)
      ·
        have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
        have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
        exact region226 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
      ·
        have h34 : (a + 3 * b + -3 * c + d) < 0 := lt_of_not_ge h34
        by_cases h35 : 0 ≤ (a + 3 * b + -c + -d)
        ·
          have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
          exact region227 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
        ·
          have h35 : (a + 3 * b + -c + -d) < 0 := lt_of_not_ge h35
          have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
          exact region228 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
  ·
    have h11 : (a + -3 * b + c + d) < 0 := lt_of_not_ge h11
    by_cases h12 : 0 ≤ (a + -3 * b + 3 * c + -d)
    ·
      have h13 : 0 ≤ (a + -3 * b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
      have h14 : (a + -2 * b + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
      have h15 : (a + -2 * b + c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
      have h16 : (a + -b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
      have h17 : (a + -b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
      have h18 : (a + -b + -c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
      have h19 : (a + -b) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
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
      have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
      have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
      have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
      have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
      by_cases h34 : 0 ≤ (a + 3 * b + -3 * c + d)
      ·
        have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
        have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
        exact region229 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
      ·
        have h34 : (a + 3 * b + -3 * c + d) < 0 := lt_of_not_ge h34
        have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
        have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
        exact region230 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
    ·
      have h12 : (a + -3 * b + 3 * c + -d) < 0 := lt_of_not_ge h12
      have h13 : 0 ≤ (a + -3 * b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
      have h14 : (a + -2 * b + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
      have h15 : (a + -2 * b + c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
      have h16 : (a + -b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
      have h17 : (a + -b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
      have h18 : (a + -b + -c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
      have h19 : (a + -b) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
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
      have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
      have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
      have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
      have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
      have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
      have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
      have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
      exact region231 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
end RandPascal.Cert
