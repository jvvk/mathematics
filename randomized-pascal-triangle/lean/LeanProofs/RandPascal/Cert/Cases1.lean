import LeanProofs.RandPascal.Cert.LocalDefs
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace RandPascal.Cert

theorem region16 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : 0 ≤ (a + -b + -c + d))
  (h19 : 0 ≤ (a + -b))
  (h20 : 0 ≤ (a + -b + c + -d))
  (h21 : 0 ≤ (a + -b + c + d))
  (h22 : 0 ≤ (a + -b + 3 * c + -d))
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : 0 ≤ (a + -c))
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = (a-b) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = (a-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs ((a-b) - (b-c)) = -((a-b) - (b-c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs ((a-b) - (c-d)) = ((a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs (-((a-b) - (b-c)) - ((b-c) - (c-d))) = -(-((a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs ((a-b) - (c+d)) = -((a-b) - (c+d)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs (-((a-b) - (b-c)) - ((b-c) - (c+d))) = (-((a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs ((a-b) - (b+c)) = -((a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-((a-b) - (b+c)) - ((b+c) - (c-d))) = -(-((a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-((a-b) - (b+c)) - ((b+c) - (c+d))) = (-((a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = (((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = (((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = ((a+b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (((a+b) - (b+c)) - ((b+c) - (c-d))) = -(((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (((a+b) - (b+c)) - ((b+c) - (c+d))) = (((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region17 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : (a + -b + -c + d) < 0)
  (h19 : 0 ≤ (a + -b))
  (h20 : 0 ≤ (a + -b + c + -d))
  (h21 : 0 ≤ (a + -b + c + d))
  (h22 : 0 ≤ (a + -b + 3 * c + -d))
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : 0 ≤ (a + -c))
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = (a-b) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = (a-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs ((a-b) - (b-c)) = -((a-b) - (b-c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs ((a-b) - (c-d)) = -((a-b) - (c-d)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs (-((a-b) - (b-c)) - ((b-c) - (c-d))) = (-((a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs ((a-b) - (c+d)) = -((a-b) - (c+d)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs (-((a-b) - (b-c)) - ((b-c) - (c+d))) = (-((a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs ((a-b) - (b+c)) = -((a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-((a-b) - (b+c)) - ((b+c) - (c-d))) = (-((a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-((a-b) - (b+c)) - ((b+c) - (c+d))) = (-((a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = (((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = (((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = ((a+b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (((a+b) - (b+c)) - ((b+c) - (c-d))) = -(((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (((a+b) - (b+c)) - ((b+c) - (c+d))) = -(((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region18 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : (a + -b + -c + d) < 0)
  (h19 : (a + -b) < 0)
  (h20 : 0 ≤ (a + -b + c + -d))
  (h21 : 0 ≤ (a + -b + c + d))
  (h22 : 0 ≤ (a + -b + 3 * c + -d))
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : 0 ≤ (a + -c))
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = -(a-b) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = (a-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs (-(a-b) - (b-c)) = -(-(a-b) - (b-c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs (-(a-b) - (c-d)) = -(-(a-b) - (c-d)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs (-(-(a-b) - (b-c)) - ((b-c) - (c-d))) = (-(-(a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs (-(a-b) - (c+d)) = -(-(a-b) - (c+d)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs (-(-(a-b) - (b-c)) - ((b-c) - (c+d))) = (-(-(a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs (-(a-b) - (b+c)) = -(-(a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c-d))) = (-(-(a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) = (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = (((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = (((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = ((a+b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (((a+b) - (b+c)) - ((b+c) - (c-d))) = -(((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (((a+b) - (b+c)) - ((b+c) - (c+d))) = -(((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region19 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : (a + -b + -c + d) < 0)
  (h19 : (a + -b) < 0)
  (h20 : (a + -b + c + -d) < 0)
  (h21 : 0 ≤ (a + -b + c + d))
  (h22 : 0 ≤ (a + -b + 3 * c + -d))
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : 0 ≤ (a + -c))
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = -(a-b) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = (a-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs (-(a-b) - (b-c)) = -(-(a-b) - (b-c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs (-(a-b) - (c-d)) = (-(a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs (-(-(a-b) - (b-c)) - ((b-c) - (c-d))) = -(-(-(a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs (-(a-b) - (c+d)) = -(-(a-b) - (c+d)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs (-(-(a-b) - (b-c)) - ((b-c) - (c+d))) = (-(-(a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs (-(a-b) - (b+c)) = -(-(a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c-d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) = (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = (((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = (((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = ((a+b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (((a+b) - (b+c)) - ((b+c) - (c-d))) = -(((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (((a+b) - (b+c)) - ((b+c) - (c+d))) = -(((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region20 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : (a + -b + -c + d) < 0)
  (h19 : (a + -b) < 0)
  (h20 : (a + -b + c + -d) < 0)
  (h21 : (a + -b + c + d) < 0)
  (h22 : 0 ≤ (a + -b + 3 * c + -d))
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : 0 ≤ (a + -c))
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = -(a-b) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = (a-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs (-(a-b) - (b-c)) = -(-(a-b) - (b-c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs (-(a-b) - (c-d)) = (-(a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs (-(-(a-b) - (b-c)) - ((b-c) - (c-d))) = -(-(-(a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs (-(a-b) - (c+d)) = (-(a-b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs (-(-(a-b) - (b-c)) - ((b-c) - (c+d))) = -(-(-(a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs (-(a-b) - (b+c)) = -(-(a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c-d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = (((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = (((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = ((a+b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (((a+b) - (b+c)) - ((b+c) - (c-d))) = -(((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (((a+b) - (b+c)) - ((b+c) - (c+d))) = -(((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region21 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : (a + -b + -c + d) < 0)
  (h19 : (a + -b) < 0)
  (h20 : (a + -b + c + -d) < 0)
  (h21 : (a + -b + c + d) < 0)
  (h22 : 0 ≤ (a + -b + 3 * c + -d))
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : (a + -c) < 0)
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = -(a-b) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = -(a-c) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs (-(a-b) - (b-c)) = (-(a-b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs (-(a-b) - (c-d)) = (-(a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs ((-(a-b) - (b-c)) - ((b-c) - (c-d))) = -((-(a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs (-(a-b) - (c+d)) = (-(a-b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs ((-(a-b) - (b-c)) - ((b-c) - (c+d))) = -((-(a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs (-(a-b) - (b+c)) = -(-(a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c-d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = (((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = (((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = -((a+b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (-((a+b) - (b+c)) - ((b+c) - (c-d))) = -(-((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (-((a+b) - (b+c)) - ((b+c) - (c+d))) = -(-((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region22 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : (a + -b + -c + d) < 0)
  (h19 : (a + -b) < 0)
  (h20 : (a + -b + c + -d) < 0)
  (h21 : (a + -b + c + d) < 0)
  (h22 : 0 ≤ (a + -b + 3 * c + -d))
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : (a + -c) < 0)
  (h25 : 0 ≤ (a + c))
  (h26 : (a + b + -3 * c + -d) < 0)
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = -(a-b) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = -(a-c) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs (-(a-b) - (b-c)) = (-(a-b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs (-(a-b) - (c-d)) = (-(a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs ((-(a-b) - (b-c)) - ((b-c) - (c-d))) = -((-(a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs (-(a-b) - (c+d)) = (-(a-b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs ((-(a-b) - (b-c)) - ((b-c) - (c+d))) = ((-(a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs (-(a-b) - (b+c)) = -(-(a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c-d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = (((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = (((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = -((a+b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (-((a+b) - (b+c)) - ((b+c) - (c-d))) = -(-((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (-((a+b) - (b+c)) - ((b+c) - (c+d))) = -(-((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region23 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : (a + -b + -c + d) < 0)
  (h19 : (a + -b) < 0)
  (h20 : (a + -b + c + -d) < 0)
  (h21 : (a + -b + c + d) < 0)
  (h22 : 0 ≤ (a + -b + 3 * c + -d))
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : (a + -c) < 0)
  (h25 : 0 ≤ (a + c))
  (h26 : (a + b + -3 * c + -d) < 0)
  (h27 : (a + b + -3 * c + d) < 0)
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = -(a-b) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = -(a-c) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs (-(a-b) - (b-c)) = (-(a-b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs (-(a-b) - (c-d)) = (-(a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs ((-(a-b) - (b-c)) - ((b-c) - (c-d))) = ((-(a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs (-(a-b) - (c+d)) = (-(a-b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs ((-(a-b) - (b-c)) - ((b-c) - (c+d))) = ((-(a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs (-(a-b) - (b+c)) = -(-(a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c-d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = (((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = (((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = -((a+b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (-((a+b) - (b+c)) - ((b+c) - (c-d))) = -(-((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (-((a+b) - (b+c)) - ((b+c) - (c+d))) = -(-((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region24 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : (a + -b + -c + d) < 0)
  (h19 : (a + -b) < 0)
  (h20 : (a + -b + c + -d) < 0)
  (h21 : (a + -b + c + d) < 0)
  (h22 : (a + -b + 3 * c + -d) < 0)
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : 0 ≤ (a + -c))
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = -(a-b) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = (a-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs (-(a-b) - (b-c)) = -(-(a-b) - (b-c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs (-(a-b) - (c-d)) = (-(a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs (-(-(a-b) - (b-c)) - ((b-c) - (c-d))) = -(-(-(a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs (-(a-b) - (c+d)) = (-(a-b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs (-(-(a-b) - (b-c)) - ((b-c) - (c+d))) = -(-(-(a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs (-(a-b) - (b+c)) = -(-(a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c-d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = -(((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = (((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = ((a+b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (((a+b) - (b+c)) - ((b+c) - (c-d))) = -(((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (((a+b) - (b+c)) - ((b+c) - (c+d))) = -(((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region25 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : (a + -b + -c + d) < 0)
  (h19 : (a + -b) < 0)
  (h20 : (a + -b + c + -d) < 0)
  (h21 : (a + -b + c + d) < 0)
  (h22 : (a + -b + 3 * c + -d) < 0)
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : (a + -c) < 0)
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = -(a-b) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = -(a-c) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs (-(a-b) - (b-c)) = (-(a-b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs (-(a-b) - (c-d)) = (-(a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs ((-(a-b) - (b-c)) - ((b-c) - (c-d))) = -((-(a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs (-(a-b) - (c+d)) = (-(a-b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs ((-(a-b) - (b-c)) - ((b-c) - (c+d))) = -((-(a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs (-(a-b) - (b+c)) = -(-(a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c-d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = -(((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = (((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = -((a+b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (-((a+b) - (b+c)) - ((b+c) - (c-d))) = -(-((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (-((a+b) - (b+c)) - ((b+c) - (c+d))) = -(-((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region26 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : (a + -b + -c + d) < 0)
  (h19 : (a + -b) < 0)
  (h20 : (a + -b + c + -d) < 0)
  (h21 : (a + -b + c + d) < 0)
  (h22 : (a + -b + 3 * c + -d) < 0)
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : (a + -c) < 0)
  (h25 : 0 ≤ (a + c))
  (h26 : (a + b + -3 * c + -d) < 0)
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = -(a-b) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = -(a-c) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs (-(a-b) - (b-c)) = (-(a-b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs (-(a-b) - (c-d)) = (-(a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs ((-(a-b) - (b-c)) - ((b-c) - (c-d))) = -((-(a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs (-(a-b) - (c+d)) = (-(a-b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs ((-(a-b) - (b-c)) - ((b-c) - (c+d))) = ((-(a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs (-(a-b) - (b+c)) = -(-(a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c-d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = -(((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = (((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = -((a+b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (-((a+b) - (b+c)) - ((b+c) - (c-d))) = -(-((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (-((a+b) - (b+c)) - ((b+c) - (c+d))) = -(-((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region27 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : (a + -b + -c + d) < 0)
  (h19 : (a + -b) < 0)
  (h20 : (a + -b + c + -d) < 0)
  (h21 : (a + -b + c + d) < 0)
  (h22 : (a + -b + 3 * c + -d) < 0)
  (h23 : (a + -b + 3 * c + d) < 0)
  (h24 : 0 ≤ (a + -c))
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = -(a-b) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = (a-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs (-(a-b) - (b-c)) = -(-(a-b) - (b-c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs (-(a-b) - (c-d)) = (-(a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs (-(-(a-b) - (b-c)) - ((b-c) - (c-d))) = -(-(-(a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs (-(a-b) - (c+d)) = (-(a-b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs (-(-(a-b) - (b-c)) - ((b-c) - (c+d))) = -(-(-(a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs (-(a-b) - (b+c)) = -(-(a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c-d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = -(((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = -(((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = ((a+b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (((a+b) - (b+c)) - ((b+c) - (c-d))) = -(((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (((a+b) - (b+c)) - ((b+c) - (c+d))) = -(((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region28 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : 0 ≤ (b + -2 * c + -d))
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
  (h12 : (a + -3 * b + 3 * c + -d) < 0)
  (h13 : (a + -3 * b + 3 * c + d) < 0)
  (h14 : (a + -2 * b + -c) < 0)
  (h15 : (a + -2 * b + c) < 0)
  (h16 : (a + -b + -3 * c + d) < 0)
  (h17 : (a + -b + -c + -d) < 0)
  (h18 : (a + -b + -c + d) < 0)
  (h19 : (a + -b) < 0)
  (h20 : (a + -b + c + -d) < 0)
  (h21 : (a + -b + c + d) < 0)
  (h22 : (a + -b + 3 * c + -d) < 0)
  (h23 : (a + -b + 3 * c + d) < 0)
  (h24 : (a + -c) < 0)
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = -(a-b) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = -(a-c) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs (-(a-b) - (b-c)) = (-(a-b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs (-(a-b) - (c-d)) = (-(a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs ((-(a-b) - (b-c)) - ((b-c) - (c-d))) = -((-(a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = ((b-c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs (-(a-b) - (c+d)) = (-(a-b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs ((-(a-b) - (b-c)) - ((b-c) - (c+d))) = -((-(a-b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs (-(a-b) - (b+c)) = -(-(a-b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c-d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (-(-(a-b) - (b+c)) - ((b+c) - (c+d))) = -(-(-(a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = -(((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - ((b-c) - (c+d))) = -(((a+b) - (b-c)) - ((b-c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = -((a+b) - (b+c)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (-((a+b) - (b+c)) - ((b+c) - (c-d))) = -(-((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (-((a+b) - (b+c)) - ((b+c) - (c+d))) = -(-((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region29 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : (b + -2 * c + -d) < 0)
  (h2 : 0 ≤ (b + -2 * c + d))
  (h3 : 0 ≤ (b + -c))
  (h4 : 0 ≤ (b + -d))
  (h5 : 0 ≤ (b + d))
  (h6 : 0 ≤ (b + 2 * c + -d))
  (h7 : 0 ≤ (a + -3 * b + -3 * c + d))
  (h8 : 0 ≤ (a + -3 * b + -c + -d))
  (h9 : 0 ≤ (a + -3 * b + -c + d))
  (h10 : 0 ≤ (a + -3 * b + c + -d))
  (h11 : 0 ≤ (a + -3 * b + c + d))
  (h12 : 0 ≤ (a + -3 * b + 3 * c + -d))
  (h13 : 0 ≤ (a + -3 * b + 3 * c + d))
  (h14 : 0 ≤ (a + -2 * b + -c))
  (h15 : 0 ≤ (a + -2 * b + c))
  (h16 : 0 ≤ (a + -b + -3 * c + d))
  (h17 : 0 ≤ (a + -b + -c + -d))
  (h18 : 0 ≤ (a + -b + -c + d))
  (h19 : 0 ≤ (a + -b))
  (h20 : 0 ≤ (a + -b + c + -d))
  (h21 : 0 ≤ (a + -b + c + d))
  (h22 : 0 ≤ (a + -b + 3 * c + -d))
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : 0 ≤ (a + -c))
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = (a-b) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = (a-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs ((a-b) - (b-c)) = ((a-b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs ((a-b) - (c-d)) = ((a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs (((a-b) - (b-c)) - ((b-c) - (c-d))) = (((a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = -((b-c) - (c+d)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs ((a-b) - (c+d)) = ((a-b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs (((a-b) - (b-c)) - -((b-c) - (c+d))) = (((a-b) - (b-c)) - -((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs ((a-b) - (b+c)) = ((a-b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (((a-b) - (b+c)) - ((b+c) - (c-d))) = (((a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (((a-b) - (b+c)) - ((b+c) - (c+d))) = (((a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = (((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - -((b-c) - (c+d))) = (((a+b) - (b-c)) - -((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = ((a+b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (((a+b) - (b+c)) - ((b+c) - (c-d))) = (((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (((a+b) - (b+c)) - ((b+c) - (c+d))) = (((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region30 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : (b + -2 * c + -d) < 0)
  (h2 : 0 ≤ (b + -2 * c + d))
  (h3 : 0 ≤ (b + -c))
  (h4 : 0 ≤ (b + -d))
  (h5 : 0 ≤ (b + d))
  (h6 : 0 ≤ (b + 2 * c + -d))
  (h7 : (a + -3 * b + -3 * c + d) < 0)
  (h8 : 0 ≤ (a + -3 * b + -c + -d))
  (h9 : 0 ≤ (a + -3 * b + -c + d))
  (h10 : 0 ≤ (a + -3 * b + c + -d))
  (h11 : 0 ≤ (a + -3 * b + c + d))
  (h12 : 0 ≤ (a + -3 * b + 3 * c + -d))
  (h13 : 0 ≤ (a + -3 * b + 3 * c + d))
  (h14 : 0 ≤ (a + -2 * b + -c))
  (h15 : 0 ≤ (a + -2 * b + c))
  (h16 : 0 ≤ (a + -b + -3 * c + d))
  (h17 : 0 ≤ (a + -b + -c + -d))
  (h18 : 0 ≤ (a + -b + -c + d))
  (h19 : 0 ≤ (a + -b))
  (h20 : 0 ≤ (a + -b + c + -d))
  (h21 : 0 ≤ (a + -b + c + d))
  (h22 : 0 ≤ (a + -b + 3 * c + -d))
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : 0 ≤ (a + -c))
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = (a-b) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = (a-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs ((a-b) - (b-c)) = ((a-b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs ((a-b) - (c-d)) = ((a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs (((a-b) - (b-c)) - ((b-c) - (c-d))) = (((a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = -((b-c) - (c+d)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs ((a-b) - (c+d)) = ((a-b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs (((a-b) - (b-c)) - -((b-c) - (c+d))) = (((a-b) - (b-c)) - -((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs ((a-b) - (b+c)) = ((a-b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (((a-b) - (b+c)) - ((b+c) - (c-d))) = (((a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (((a-b) - (b+c)) - ((b+c) - (c+d))) = (((a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = (((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - -((b-c) - (c+d))) = (((a+b) - (b-c)) - -((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = ((a+b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (((a+b) - (b+c)) - ((b+c) - (c-d))) = (((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (((a+b) - (b+c)) - ((b+c) - (c+d))) = (((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

theorem region31 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h0 : 0 ≤ (c + -d))
  (h1 : (b + -2 * c + -d) < 0)
  (h2 : 0 ≤ (b + -2 * c + d))
  (h3 : 0 ≤ (b + -c))
  (h4 : 0 ≤ (b + -d))
  (h5 : 0 ≤ (b + d))
  (h6 : 0 ≤ (b + 2 * c + -d))
  (h7 : (a + -3 * b + -3 * c + d) < 0)
  (h8 : (a + -3 * b + -c + -d) < 0)
  (h9 : 0 ≤ (a + -3 * b + -c + d))
  (h10 : 0 ≤ (a + -3 * b + c + -d))
  (h11 : 0 ≤ (a + -3 * b + c + d))
  (h12 : 0 ≤ (a + -3 * b + 3 * c + -d))
  (h13 : 0 ≤ (a + -3 * b + 3 * c + d))
  (h14 : 0 ≤ (a + -2 * b + -c))
  (h15 : 0 ≤ (a + -2 * b + c))
  (h16 : 0 ≤ (a + -b + -3 * c + d))
  (h17 : 0 ≤ (a + -b + -c + -d))
  (h18 : 0 ≤ (a + -b + -c + d))
  (h19 : 0 ≤ (a + -b))
  (h20 : 0 ≤ (a + -b + c + -d))
  (h21 : 0 ≤ (a + -b + c + d))
  (h22 : 0 ≤ (a + -b + 3 * c + -d))
  (h23 : 0 ≤ (a + -b + 3 * c + d))
  (h24 : 0 ≤ (a + -c))
  (h25 : 0 ≤ (a + c))
  (h26 : 0 ≤ (a + b + -3 * c + -d))
  (h27 : 0 ≤ (a + b + -3 * c + d))
  (h28 : 0 ≤ (a + b + -c + -d))
  (h29 : 0 ≤ (a + b + -c + d))
  (h30 : 0 ≤ (a + b + c + -d))
  (h31 : 0 ≤ (a + b + c + d))
  (h32 : 0 ≤ (a + b + 3 * c + -d))
  (h33 : 0 ≤ (a + 2 * b + -c))
  (h34 : 0 ≤ (a + 3 * b + -3 * c + d))
  (h35 : 0 ≤ (a + 3 * b + -c + -d))
  (h36 : 0 ≤ (a + 3 * b + -c + d))
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  have e0 : abs (a-b) = (a-b) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e1 : abs (b-c) = (b-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e2 : abs (c-d) = (c-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e3 : abs (a-c) = (a-c) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e4 : abs (b-d) = (b-d) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e5 : abs ((a-b) - (b-c)) = ((a-b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e6 : abs ((b-c) - (c-d)) = ((b-c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e7 : abs ((a-b) - (c-d)) = ((a-b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e8 : abs (((a-b) - (b-c)) - ((b-c) - (c-d))) = (((a-b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e9 : abs ((b-c) - (c+d)) = -((b-c) - (c+d)) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e10 : abs ((a-b) - (c+d)) = ((a-b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e11 : abs (((a-b) - (b-c)) - -((b-c) - (c+d))) = (((a-b) - (b-c)) - -((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e12 : abs ((a-b) - (b+c)) = ((a-b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e13 : abs ((b+c) - (c-d)) = ((b+c) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e14 : abs (((a-b) - (b+c)) - ((b+c) - (c-d))) = -(((a-b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonpos (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e15 : abs ((b+c) - (c+d)) = ((b+c) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e16 : abs (((a-b) - (b+c)) - ((b+c) - (c+d))) = (((a-b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e17 : abs ((a+b) - (b-c)) = ((a+b) - (b-c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e18 : abs ((a+b) - (c-d)) = ((a+b) - (c-d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e19 : abs (((a+b) - (b-c)) - ((b-c) - (c-d))) = (((a+b) - (b-c)) - ((b-c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e20 : abs ((a+b) - (c+d)) = ((a+b) - (c+d)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e21 : abs (((a+b) - (b-c)) - -((b-c) - (c+d))) = (((a+b) - (b-c)) - -((b-c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e22 : abs ((a+b) - (b+c)) = ((a+b) - (b+c)) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e23 : abs (((a+b) - (b+c)) - ((b+c) - (c-d))) = (((a+b) - (b+c)) - ((b+c) - (c-d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  have e24 : abs (((a+b) - (b+c)) - ((b+c) - (c+d))) = (((a+b) - (b+c)) - ((b+c) - (c+d))) := by
    exact abs_of_nonneg (by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36])
  simp only [b0, b1, b2, b3, base, inputCost, outputCost, upd, out000, out001, out010, out011, out100, out101, out110, out111, Bool.false_eq_true, ite_false, ite_true, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor
  · linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
  constructor <;> linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

end RandPascal.Cert
