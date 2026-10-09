import LeanProofs.RandPascal.Cert.Cases2
import LeanProofs.RandPascal.Cert.Cases3
import LeanProofs.RandPascal.Cert.Cases4
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace RandPascal.Cert

theorem chunk6 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : (b + -2 * c + -d) < 0)
  (h2 : 0 ≤ (b + -2 * c + d))
  (h3 : 0 ≤ (b + -c))
  (h4 : 0 ≤ (b + -d))
  (h5 : 0 ≤ (b + d))
  (h6 : 0 ≤ (b + 2 * c + -d))
  (h7 : (a + -3 * b + -3 * c + d) < 0)
  (h8 : (a + -3 * b + -c + -d) < 0)
  (h9 : (a + -3 * b + -c + d) < 0)
  (h10 : (a + -3 * b + c + -d) < 0)
  (h11 : (a + -3 * b + c + d) < 0)
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  by_cases h12 : 0 ≤ (a + -3 * b + 3 * c + -d)
  ·
    have h13 : 0 ≤ (a + -3 * b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
    have h14 : (a + -2 * b + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
    have h15 : 0 ≤ (a + -2 * b + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
    by_cases h16 : 0 ≤ (a + -b + -3 * c + d)
    ·
      have h17 : 0 ≤ (a + -b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
      have h18 : 0 ≤ (a + -b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
      have h19 : 0 ≤ (a + -b) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
      have h20 : 0 ≤ (a + -b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
      have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
      have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
      have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
      have h24 : 0 ≤ (a + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
      have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
      have h26 : 0 ≤ (a + b + -3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
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
      exact region38 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
    ·
      have h16 : (a + -b + -3 * c + d) < 0 := lt_of_not_ge h16
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
        have h26 : 0 ≤ (a + b + -3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
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
        exact region39 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
          exact region40 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
          exact region41 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
  ·
    have h12 : (a + -3 * b + 3 * c + -d) < 0 := lt_of_not_ge h12
    by_cases h13 : 0 ≤ (a + -3 * b + 3 * c + d)
    ·
      have h14 : (a + -2 * b + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
      by_cases h15 : 0 ≤ (a + -2 * b + c)
      ·
        by_cases h16 : 0 ≤ (a + -b + -3 * c + d)
        ·
          have h17 : 0 ≤ (a + -b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
          have h18 : 0 ≤ (a + -b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
          have h19 : 0 ≤ (a + -b) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
          have h20 : 0 ≤ (a + -b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
          have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
          have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
          have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
          have h24 : 0 ≤ (a + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
          have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
          have h26 : 0 ≤ (a + b + -3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
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
          exact region42 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
        ·
          have h16 : (a + -b + -3 * c + d) < 0 := lt_of_not_ge h16
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
            have h26 : 0 ≤ (a + b + -3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
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
            exact region43 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
              exact region44 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
              exact region45 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
      ·
        have h15 : (a + -2 * b + c) < 0 := lt_of_not_ge h15
        have h16 : (a + -b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
        have h17 : (a + -b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
        by_cases h18 : 0 ≤ (a + -b + -c + d)
        ·
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
            exact region46 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
            exact region47 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
        ·
          have h18 : (a + -b + -c + d) < 0 := lt_of_not_ge h18
          by_cases h19 : 0 ≤ (a + -b)
          ·
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
              exact region48 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
              exact region49 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h19 : (a + -b) < 0 := lt_of_not_ge h19
            by_cases h20 : 0 ≤ (a + -b + c + -d)
            ·
              have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
              have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
              have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
              have h24 : 0 ≤ (a + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
              have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
              have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
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
              exact region50 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h20 : (a + -b + c + -d) < 0 := lt_of_not_ge h20
              have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
              have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
              have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
              by_cases h24 : 0 ≤ (a + -c)
              ·
                have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
                have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
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
                exact region51 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
              ·
                have h24 : (a + -c) < 0 := lt_of_not_ge h24
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
                  exact region52 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
                    exact region53 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
                    exact region54 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
    ·
      have h13 : (a + -3 * b + 3 * c + d) < 0 := lt_of_not_ge h13
      have h14 : (a + -2 * b + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
      have h15 : (a + -2 * b + c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
      have h16 : (a + -b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
      have h17 : (a + -b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
      by_cases h18 : 0 ≤ (a + -b + -c + d)
      ·
        have h19 : 0 ≤ (a + -b) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
        have h20 : 0 ≤ (a + -b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
        have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
        have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
        have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
        have h24 : 0 ≤ (a + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
        have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
        have h26 : 0 ≤ (a + b + -3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
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
        exact region55 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
      ·
        have h18 : (a + -b + -c + d) < 0 := lt_of_not_ge h18
        by_cases h19 : 0 ≤ (a + -b)
        ·
          have h20 : 0 ≤ (a + -b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
          have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
          have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
          have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
          have h24 : 0 ≤ (a + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
          have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
          have h26 : 0 ≤ (a + b + -3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
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
          exact region56 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
        ·
          have h19 : (a + -b) < 0 := lt_of_not_ge h19
          by_cases h20 : 0 ≤ (a + -b + c + -d)
          ·
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
              exact region57 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
              exact region58 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
          ·
            have h20 : (a + -b + c + -d) < 0 := lt_of_not_ge h20
            by_cases h21 : 0 ≤ (a + -b + c + d)
            ·
              have h22 : 0 ≤ (a + -b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
              have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
              by_cases h24 : 0 ≤ (a + -c)
              ·
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
                  exact region59 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
                  exact region60 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
              ·
                have h24 : (a + -c) < 0 := lt_of_not_ge h24
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
                  exact region61 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
                    exact region62 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
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
                    exact region63 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
            ·
              have h21 : (a + -b + c + d) < 0 := lt_of_not_ge h21
              by_cases h22 : 0 ≤ (a + -b + 3 * c + -d)
              ·
                have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
                have h24 : (a + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
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
                  exact region64 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                ·
                  have h27 : (a + b + -3 * c + d) < 0 := lt_of_not_ge h27
                  have h28 : 0 ≤ (a + b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
                  have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
                  have h30 : 0 ≤ (a + b + c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
                  have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
                  have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
                  have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
                  have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
                  have h35 : 0 ≤ (a + 3 * b + -c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
                  have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                  exact region65 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
              ·
                have h22 : (a + -b + 3 * c + -d) < 0 := lt_of_not_ge h22
                have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
                have h24 : (a + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
                have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
                have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
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
                exact region66 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
end RandPascal.Cert
