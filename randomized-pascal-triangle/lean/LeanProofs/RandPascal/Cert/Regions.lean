import LeanProofs.RandPascal.Cert.Chunk0
import LeanProofs.RandPascal.Cert.Chunk1
import LeanProofs.RandPascal.Cert.Chunk2
import LeanProofs.RandPascal.Cert.Chunk3
import LeanProofs.RandPascal.Cert.Chunk4
import LeanProofs.RandPascal.Cert.Chunk5
import LeanProofs.RandPascal.Cert.Chunk6
import LeanProofs.RandPascal.Cert.Chunk7
import LeanProofs.RandPascal.Cert.Chunk8
import LeanProofs.RandPascal.Cert.Chunk9
import LeanProofs.RandPascal.Cert.Chunk10
import LeanProofs.RandPascal.Cert.Chunk11
import LeanProofs.RandPascal.Cert.Chunk12
import LeanProofs.RandPascal.Cert.Chunk13
import LeanProofs.RandPascal.Cert.Chunk14
import LeanProofs.RandPascal.Cert.Chunk15
import LeanProofs.RandPascal.Cert.Chunk16
import LeanProofs.RandPascal.Cert.Chunk17
import LeanProofs.RandPascal.Cert.Chunk18
import LeanProofs.RandPascal.Cert.Chunk19
import LeanProofs.RandPascal.Cert.Chunk20
import LeanProofs.RandPascal.Cert.Chunk21
import LeanProofs.RandPascal.Cert.Chunk22
import LeanProofs.RandPascal.Cert.Chunk23
import LeanProofs.RandPascal.Cert.Chunk24
import LeanProofs.RandPascal.Cert.Chunk25
import LeanProofs.RandPascal.Cert.Chunk26
import LeanProofs.RandPascal.Cert.Chunk27
import LeanProofs.RandPascal.Cert.Chunk28
import LeanProofs.RandPascal.Cert.Chunk29
import LeanProofs.RandPascal.Cert.Chunk30
import LeanProofs.RandPascal.Cert.Chunk31
import LeanProofs.RandPascal.Cert.Chunk32
import LeanProofs.RandPascal.Cert.Chunk33
import LeanProofs.RandPascal.Cert.Chunk34
import LeanProofs.RandPascal.Cert.Chunk35
import LeanProofs.RandPascal.Cert.Chunk36
import LeanProofs.RandPascal.Cert.Chunk37
import LeanProofs.RandPascal.Cert.Chunk38
import LeanProofs.RandPascal.Cert.Chunk39
import LeanProofs.RandPascal.Cert.Chunk40
import LeanProofs.RandPascal.Cert.Chunk41
import LeanProofs.RandPascal.Cert.Chunk42
import LeanProofs.RandPascal.Cert.Chunk43
import LeanProofs.RandPascal.Cert.Chunk44
import LeanProofs.RandPascal.Cert.Chunk45
import LeanProofs.RandPascal.Cert.Chunk46
import LeanProofs.RandPascal.Cert.Chunk47
import LeanProofs.RandPascal.Cert.Chunk48
import LeanProofs.RandPascal.Cert.Chunk49
import LeanProofs.RandPascal.Cert.Chunk50
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace RandPascal.Cert

theorem bernstein_nonneg (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  : 0 ≤ b0 a b c d ∧ 0 ≤ b1 a b c d ∧ 0 ≤ b2 a b c d ∧ 0 ≤ b3 a b c d := by
  by_cases h0 : 0 ≤ (c + -d)
  ·
    by_cases h1 : 0 ≤ (b + -2 * c + -d)
    ·
      exact chunk0 a b c d ha hb hc hd h0 h1
    ·
      have h1 : (b + -2 * c + -d) < 0 := lt_of_not_ge h1
      by_cases h2 : 0 ≤ (b + -2 * c + d)
      ·
        have h3 : 0 ≤ (b + -c) := by linarith only [ha, hb, hc, hd, h0, h1, h2]
        have h4 : 0 ≤ (b + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3]
        have h5 : 0 ≤ (b + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4]
        have h6 : 0 ≤ (b + 2 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5]
        by_cases h7 : 0 ≤ (a + -3 * b + -3 * c + d)
        ·
          exact chunk1 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7
        ·
          have h7 : (a + -3 * b + -3 * c + d) < 0 := lt_of_not_ge h7
          by_cases h8 : 0 ≤ (a + -3 * b + -c + -d)
          ·
            exact chunk2 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8
          ·
            have h8 : (a + -3 * b + -c + -d) < 0 := lt_of_not_ge h8
            by_cases h9 : 0 ≤ (a + -3 * b + -c + d)
            ·
              exact chunk3 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
            ·
              have h9 : (a + -3 * b + -c + d) < 0 := lt_of_not_ge h9
              by_cases h10 : 0 ≤ (a + -3 * b + c + -d)
              ·
                exact chunk4 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
              ·
                have h10 : (a + -3 * b + c + -d) < 0 := lt_of_not_ge h10
                by_cases h11 : 0 ≤ (a + -3 * b + c + d)
                ·
                  exact chunk5 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
                ·
                  have h11 : (a + -3 * b + c + d) < 0 := lt_of_not_ge h11
                  exact chunk6 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      ·
        have h2 : (b + -2 * c + d) < 0 := lt_of_not_ge h2
        by_cases h3 : 0 ≤ (b + -c)
        ·
          have h4 : 0 ≤ (b + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3]
          have h5 : 0 ≤ (b + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4]
          have h6 : 0 ≤ (b + 2 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5]
          by_cases h7 : 0 ≤ (a + -3 * b + -3 * c + d)
          ·
            exact chunk7 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7
          ·
            have h7 : (a + -3 * b + -3 * c + d) < 0 := lt_of_not_ge h7
            by_cases h8 : 0 ≤ (a + -3 * b + -c + -d)
            ·
              exact chunk8 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8
            ·
              have h8 : (a + -3 * b + -c + -d) < 0 := lt_of_not_ge h8
              by_cases h9 : 0 ≤ (a + -3 * b + -c + d)
              ·
                exact chunk9 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
              ·
                have h9 : (a + -3 * b + -c + d) < 0 := lt_of_not_ge h9
                exact chunk10 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
        ·
          have h3 : (b + -c) < 0 := lt_of_not_ge h3
          by_cases h4 : 0 ≤ (b + -d)
          ·
            have h5 : 0 ≤ (b + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4]
            have h6 : 0 ≤ (b + 2 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5]
            by_cases h7 : 0 ≤ (a + -3 * b + -3 * c + d)
            ·
              exact chunk11 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7
            ·
              have h7 : (a + -3 * b + -3 * c + d) < 0 := lt_of_not_ge h7
              by_cases h8 : 0 ≤ (a + -3 * b + -c + -d)
              ·
                exact chunk12 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8
              ·
                have h8 : (a + -3 * b + -c + -d) < 0 := lt_of_not_ge h8
                by_cases h9 : 0 ≤ (a + -3 * b + -c + d)
                ·
                  exact chunk13 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
                ·
                  have h9 : (a + -3 * b + -c + d) < 0 := lt_of_not_ge h9
                  by_cases h10 : 0 ≤ (a + -3 * b + c + -d)
                  ·
                    exact chunk14 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
                  ·
                    have h10 : (a + -3 * b + c + -d) < 0 := lt_of_not_ge h10
                    exact chunk15 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
          ·
            have h4 : (b + -d) < 0 := lt_of_not_ge h4
            have h5 : 0 ≤ (b + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4]
            have h6 : 0 ≤ (b + 2 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5]
            by_cases h7 : 0 ≤ (a + -3 * b + -3 * c + d)
            ·
              exact chunk16 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7
            ·
              have h7 : (a + -3 * b + -3 * c + d) < 0 := lt_of_not_ge h7
              by_cases h8 : 0 ≤ (a + -3 * b + -c + -d)
              ·
                exact chunk17 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8
              ·
                have h8 : (a + -3 * b + -c + -d) < 0 := lt_of_not_ge h8
                by_cases h9 : 0 ≤ (a + -3 * b + -c + d)
                ·
                  exact chunk18 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
                ·
                  have h9 : (a + -3 * b + -c + d) < 0 := lt_of_not_ge h9
                  by_cases h10 : 0 ≤ (a + -3 * b + c + -d)
                  ·
                    exact chunk19 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
                  ·
                    have h10 : (a + -3 * b + c + -d) < 0 := lt_of_not_ge h10
                    exact chunk20 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  ·
    have h0 : (c + -d) < 0 := lt_of_not_ge h0
    by_cases h1 : 0 ≤ (b + -2 * c + -d)
    ·
      exact chunk21 a b c d ha hb hc hd h0 h1
    ·
      have h1 : (b + -2 * c + -d) < 0 := lt_of_not_ge h1
      by_cases h2 : 0 ≤ (b + -2 * c + d)
      ·
        by_cases h3 : 0 ≤ (b + -c)
        ·
          by_cases h4 : 0 ≤ (b + -d)
          ·
            have h5 : 0 ≤ (b + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4]
            have h6 : 0 ≤ (b + 2 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5]
            by_cases h7 : 0 ≤ (a + -3 * b + -3 * c + d)
            ·
              exact chunk22 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7
            ·
              have h7 : (a + -3 * b + -3 * c + d) < 0 := lt_of_not_ge h7
              have h8 : (a + -3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7]
              by_cases h9 : 0 ≤ (a + -3 * b + -c + d)
              ·
                exact chunk23 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
              ·
                have h9 : (a + -3 * b + -c + d) < 0 := lt_of_not_ge h9
                have h10 : (a + -3 * b + c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
                by_cases h11 : 0 ≤ (a + -3 * b + c + d)
                ·
                  exact chunk24 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
                ·
                  have h11 : (a + -3 * b + c + d) < 0 := lt_of_not_ge h11
                  have h12 : (a + -3 * b + 3 * c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
                  by_cases h13 : 0 ≤ (a + -3 * b + 3 * c + d)
                  ·
                    exact chunk25 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
                  ·
                    have h13 : (a + -3 * b + 3 * c + d) < 0 := lt_of_not_ge h13
                    exact chunk26 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
          ·
            have h4 : (b + -d) < 0 := lt_of_not_ge h4
            have h5 : 0 ≤ (b + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4]
            by_cases h6 : 0 ≤ (b + 2 * c + -d)
            ·
              by_cases h7 : 0 ≤ (a + -3 * b + -3 * c + d)
              ·
                exact chunk27 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7
              ·
                have h7 : (a + -3 * b + -3 * c + d) < 0 := lt_of_not_ge h7
                have h8 : (a + -3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7]
                by_cases h9 : 0 ≤ (a + -3 * b + -c + d)
                ·
                  exact chunk28 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
                ·
                  have h9 : (a + -3 * b + -c + d) < 0 := lt_of_not_ge h9
                  have h10 : (a + -3 * b + c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
                  by_cases h11 : 0 ≤ (a + -3 * b + c + d)
                  ·
                    exact chunk29 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
                  ·
                    have h11 : (a + -3 * b + c + d) < 0 := lt_of_not_ge h11
                    exact chunk30 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
            ·
              have h6 : (b + 2 * c + -d) < 0 := lt_of_not_ge h6
              by_cases h7 : 0 ≤ (a + -3 * b + -3 * c + d)
              ·
                by_cases h8 : 0 ≤ (a + -3 * b + -c + -d)
                ·
                  exact chunk31 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8
                ·
                  have h8 : (a + -3 * b + -c + -d) < 0 := lt_of_not_ge h8
                  have h9 : 0 ≤ (a + -3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8]
                  by_cases h10 : 0 ≤ (a + -3 * b + c + -d)
                  ·
                    exact chunk32 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
                  ·
                    have h10 : (a + -3 * b + c + -d) < 0 := lt_of_not_ge h10
                    have h11 : 0 ≤ (a + -3 * b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
                    by_cases h12 : 0 ≤ (a + -3 * b + 3 * c + -d)
                    ·
                      exact chunk33 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
                    ·
                      have h12 : (a + -3 * b + 3 * c + -d) < 0 := lt_of_not_ge h12
                      have h13 : 0 ≤ (a + -3 * b + 3 * c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
                      by_cases h14 : 0 ≤ (a + -2 * b + -c)
                      ·
                        exact chunk34 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
                      ·
                        have h14 : (a + -2 * b + -c) < 0 := lt_of_not_ge h14
                        exact chunk35 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
              ·
                have h7 : (a + -3 * b + -3 * c + d) < 0 := lt_of_not_ge h7
                have h8 : (a + -3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7]
                by_cases h9 : 0 ≤ (a + -3 * b + -c + d)
                ·
                  exact chunk36 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
                ·
                  have h9 : (a + -3 * b + -c + d) < 0 := lt_of_not_ge h9
                  exact chunk37 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
        ·
          have h3 : (b + -c) < 0 := lt_of_not_ge h3
          have h4 : (b + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3]
          have h5 : 0 ≤ (b + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4]
          by_cases h6 : 0 ≤ (b + 2 * c + -d)
          ·
            by_cases h7 : 0 ≤ (a + -3 * b + -3 * c + d)
            ·
              exact chunk38 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7
            ·
              have h7 : (a + -3 * b + -3 * c + d) < 0 := lt_of_not_ge h7
              have h8 : (a + -3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7]
              by_cases h9 : 0 ≤ (a + -3 * b + -c + d)
              ·
                by_cases h10 : 0 ≤ (a + -3 * b + c + -d)
                ·
                  exact chunk39 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
                ·
                  have h10 : (a + -3 * b + c + -d) < 0 := lt_of_not_ge h10
                  exact chunk40 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
              ·
                have h9 : (a + -3 * b + -c + d) < 0 := lt_of_not_ge h9
                exact chunk41 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
          ·
            have h6 : (b + 2 * c + -d) < 0 := lt_of_not_ge h6
            by_cases h7 : 0 ≤ (a + -3 * b + -3 * c + d)
            ·
              by_cases h8 : 0 ≤ (a + -3 * b + -c + -d)
              ·
                exact chunk42 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8
              ·
                have h8 : (a + -3 * b + -c + -d) < 0 := lt_of_not_ge h8
                have h9 : 0 ≤ (a + -3 * b + -c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8]
                by_cases h10 : 0 ≤ (a + -3 * b + c + -d)
                ·
                  exact chunk43 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
                ·
                  have h10 : (a + -3 * b + c + -d) < 0 := lt_of_not_ge h10
                  exact chunk44 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
            ·
              have h7 : (a + -3 * b + -3 * c + d) < 0 := lt_of_not_ge h7
              have h8 : (a + -3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7]
              by_cases h9 : 0 ≤ (a + -3 * b + -c + d)
              ·
                have h10 : (a + -3 * b + c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
                have h11 : 0 ≤ (a + -3 * b + c + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
                by_cases h12 : 0 ≤ (a + -3 * b + 3 * c + -d)
                ·
                  exact chunk45 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
                ·
                  have h12 : (a + -3 * b + 3 * c + -d) < 0 := lt_of_not_ge h12
                  exact chunk46 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
              ·
                have h9 : (a + -3 * b + -c + d) < 0 := lt_of_not_ge h9
                exact chunk47 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      ·
        have h2 : (b + -2 * c + d) < 0 := lt_of_not_ge h2
        have h3 : (b + -c) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2]
        have h4 : (b + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3]
        have h5 : 0 ≤ (b + d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4]
        have h6 : 0 ≤ (b + 2 * c + -d) := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5]
        by_cases h7 : 0 ≤ (a + -3 * b + -3 * c + d)
        ·
          exact chunk48 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7
        ·
          have h7 : (a + -3 * b + -3 * c + d) < 0 := lt_of_not_ge h7
          have h8 : (a + -3 * b + -c + -d) < 0 := by linarith only [ha, hb, hc, hd, h0, h1, h2, h3, h4, h5, h6, h7]
          by_cases h9 : 0 ≤ (a + -3 * b + -c + d)
          ·
            exact chunk49 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
          ·
            have h9 : (a + -3 * b + -c + d) < 0 := lt_of_not_ge h9
            exact chunk50 a b c d ha hb hc hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
end RandPascal.Cert
