import LeanProofs.RandPascal.Cert.Cases38
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace RandPascal.Cert

theorem chunk47 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : (c + -d) < 0)
  (h1 : (b + -2 * c + -d) < 0)
  (h2 : 0 ≤ (b + -2 * c + d))
  (h3 : (b + -c) < 0)
  (h4 : (b + -d) < 0)
  (h5 : 0 ≤ (b + d))
  (h6 : (b + 2 * c + -d) < 0)
  (h7 : (a + -3 * b + -3 * c + d) < 0)
  (h8 : (a + -3 * b + -c + -d) < 0)
  (h9 : (a + -3 * b + -c + d) < 0)
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have h10 : (a + -3 * b + c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  have h11 : 0 ≤ (a + -3 * b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  have h12 : (a + -3 * b + 3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have h13 : 0 ≤ (a + -3 * b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  have h14 : (a + -2 * b + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  have h15 : (a + -2 * b + c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  have h16 : (a + -b + -3 * c + d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  have h17 : (a + -b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  have h18 : 0 ≤ (a + -b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
  have h19 : (a + -b) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
  have h20 : (a + -b + c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
  have h21 : 0 ≤ (a + -b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
  have h22 : (a + -b + 3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
  have h23 : 0 ≤ (a + -b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
  have h24 : (a + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
  have h25 : 0 ≤ (a + c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
  have h26 : (a + b + -3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
  have h27 : 0 ≤ (a + b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
  have h28 : (a + b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  have h29 : 0 ≤ (a + b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
  have h30 : (a + b + c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
  have h31 : 0 ≤ (a + b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
  have h32 : 0 ≤ (a + b + 3 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
  have h33 : 0 ≤ (a + 2 * b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
  have h34 : 0 ≤ (a + 3 * b + -3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
  have h35 : (a + 3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
  have h36 : 0 ≤ (a + 3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
  exact region622 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
end RandPascal.Cert
