import LeanProofs.ShuffleBlocks.Basic

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Blocks

set_option maxHeartbeats 0 in
/-- Cut inside run 0 of `V`: no splitting of this rotation gives two equal copies. -/
theorem V_cut00 (L l m v k a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9 a10 b10 : Nat)
    (hl : 1 ≤ l) (hm : m = 2 * v + 1) (hL : 9 * l ≤ L) (hk : k ≤ L)
    (e0 : a0 + b0 = (L - k))
    (e1 : a1 + b1 = m)
    (e2 : a2 + b2 = 5 * l)
    (e3 : a3 + b3 = 2 * m)
    (e4 : a4 + b4 = L)
    (e5 : a5 + b5 = m)
    (e6 : a6 + b6 = 2 * l)
    (e7 : a7 + b7 = m)
    (e8 : a8 + b8 = l)
    (e9 : a9 + b9 = 3 * m)
    (e10 : a10 + b10 = k)
    (E : rw [(false, a0), (true, a1), (false, a2), (true, a3), (false, a4), (true, a5), (false, a6), (true, a7), (false, a8), (true, a9), (false, a10)] = rw [(false, b0), (true, b1), (false, b2), (true, b3), (false, b4), (true, b5), (false, b6), (true, b7), (false, b8), (true, b9), (false, b10)]) : False := by
  have ho := congrArg (List.count true) E
  have hz := congrArg (List.count false) E
  simp only [count_rw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    Bool.true_eq_false, Bool.false_eq_true] at ho hz
  by_cases c1 : 0 < a1
  swap
  · -- branch
    by_cases c2 : 0 < a1
    swap
    · -- branch
      by_cases c3 : 0 < a1
      swap
      · -- branch
        by_cases c4 : 0 < a1
        swap
        · -- branch
          by_cases c5 : 0 < a1
          swap
          · -- branch
            by_cases c6 : 0 < a3
            swap
            · -- branch
              by_cases c7 : 0 < a3
              swap
              · -- branch
                by_cases c8 : 0 < a3
                swap
                · -- branch
                  by_cases c9 : 0 < a3
                  swap
                  · -- branch
                    by_cases c10 : 0 < a3
                    swap
                    · -- branch
                      by_cases c11 : 0 < a5
                      swap
                      · -- branch
                        by_cases c12 : 0 < a7
                        swap
                        · omega
                        by_cases c13 : 0 < b1
                        swap
                        · omega
                        by_cases c14 : a1 + a3 + a5 < 0 + b1
                        swap
                        · omega
                        by_cases c15 : 0 < a1 + a3 + a5 + a7
                        swap
                        · omega
                        have f16 := pair_fact E (i := 7) (j := 1) rfl rfl c12 c13
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f16
                        omega
                      by_cases c17 : 0 < b1
                      swap
                      · omega
                      by_cases c18 : a1 + a3 < 0 + b1
                      swap
                      · omega
                      by_cases c19 : 0 < a1 + a3 + a5
                      swap
                      · omega
                      have f20 := pair_fact E (i := 5) (j := 1) rfl rfl c11 c17
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f20
                      omega
                    by_cases c21 : 0 < b9
                    swap
                    · omega
                    by_cases c22 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c23 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · omega
                    have f24 := pair_fact E (i := 3) (j := 9) rfl rfl c10 c21
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f24
                    omega
                  by_cases c25 : 0 < b7
                  swap
                  · omega
                  by_cases c26 : a1 < b1 + b3 + b5 + b7
                  swap
                  · omega
                  by_cases c27 : b1 + b3 + b5 < a1 + a3
                  swap
                  · omega
                  have f28 := pair_fact E (i := 3) (j := 7) rfl rfl c9 c25
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f28
                  omega
                by_cases c29 : 0 < b5
                swap
                · omega
                by_cases c30 : a1 < b1 + b3 + b5
                swap
                · omega
                by_cases c31 : b1 + b3 < a1 + a3
                swap
                · omega
                have f32 := pair_fact E (i := 3) (j := 5) rfl rfl c8 c29
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f32
                omega
              by_cases c33 : 0 < b3
              swap
              · omega
              by_cases c34 : a1 < b1 + b3
              swap
              · omega
              by_cases c35 : b1 < a1 + a3
              swap
              · omega
              have f36 := pair_fact E (i := 3) (j := 3) rfl rfl c7 c33
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f36
              omega
            by_cases c37 : 0 < b1
            swap
            · omega
            by_cases c38 : a1 < 0 + b1
            swap
            · omega
            by_cases c39 : 0 < a1 + a3
            swap
            · omega
            have f40 := pair_fact E (i := 3) (j := 1) rfl rfl c6 c37
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f40
            by_cases c41 : 0 < a3
            swap
            · omega
            by_cases c42 : 0 < b5
            swap
            · -- branch
              by_cases c43 : 0 < a3
              swap
              · omega
              by_cases c44 : 0 < b9
              swap
              · omega
              by_cases c45 : a1 < b1 + b3 + b5 + b7 + b9
              swap
              · omega
              by_cases c46 : b1 + b3 + b5 + b7 < a1 + a3
              swap
              · -- branch
                by_cases c47 : 0 < a5
                swap
                · omega
                by_cases c48 : 0 < b1
                swap
                · omega
                by_cases c49 : a1 + a3 < 0 + b1
                swap
                · -- branch
                  by_cases c50 : 0 < a5
                  swap
                  · omega
                  by_cases c51 : 0 < b5
                  swap
                  · -- branch
                    by_cases c52 : 0 < a9
                    swap
                    · omega
                    by_cases c53 : 0 < b1
                    swap
                    · omega
                    by_cases c54 : a1 + a3 + a5 + a7 < 0 + b1
                    swap
                    · -- branch
                      by_cases c55 : 0 < a9
                      swap
                      · omega
                      by_cases c56 : 0 < b5
                      swap
                      · -- branch
                        by_cases c57 : 0 < a9
                        swap
                        · omega
                        by_cases c58 : 0 < b9
                        swap
                        · omega
                        by_cases c59 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                        swap
                        · omega
                        by_cases c60 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                        swap
                        · omega
                        have f61 := pair_fact E (i := 9) (j := 9) rfl rfl c57 c58
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f61
                        by_cases c62 : 0 < a3
                        swap
                        · omega
                        by_cases c63 : 0 < b7
                        swap
                        · -- branch
                          by_cases c64 : 0 < a5
                          swap
                          · omega
                          by_cases c65 : 0 < b3
                          swap
                          · omega
                          by_cases c66 : a1 + a3 < b1 + b3
                          swap
                          · omega
                          by_cases c67 : b1 < a1 + a3 + a5
                          swap
                          · omega
                          have f68 := pair_fact E (i := 5) (j := 3) rfl rfl c64 c65
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f68
                          omega
                        by_cases c69 : a1 < b1 + b3 + b5 + b7
                        swap
                        · omega
                        by_cases c70 : b1 + b3 + b5 < a1 + a3
                        swap
                        · -- branch
                          by_cases c71 : 0 < a5
                          swap
                          · omega
                          by_cases c72 : 0 < b3
                          swap
                          · omega
                          by_cases c73 : a1 + a3 < b1 + b3
                          swap
                          · omega
                          by_cases c74 : b1 < a1 + a3 + a5
                          swap
                          · omega
                          have f75 := pair_fact E (i := 5) (j := 3) rfl rfl c71 c72
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f75
                          omega
                        have f76 := pair_fact E (i := 3) (j := 7) rfl rfl c62 c63
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f76
                        omega
                      by_cases c77 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                      swap
                      · omega
                      by_cases c78 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                      swap
                      · omega
                      have f79 := pair_fact E (i := 9) (j := 5) rfl rfl c55 c56
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f79
                      omega
                    by_cases c80 : 0 < a1 + a3 + a5 + a7 + a9
                    swap
                    · omega
                    have f81 := pair_fact E (i := 9) (j := 1) rfl rfl c52 c53
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f81
                    omega
                  by_cases c82 : a1 + a3 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c83 : b1 + b3 < a1 + a3 + a5
                  swap
                  · omega
                  have f84 := pair_fact E (i := 5) (j := 5) rfl rfl c50 c51
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f84
                  omega
                by_cases c85 : 0 < a1 + a3 + a5
                swap
                · omega
                have f86 := pair_fact E (i := 5) (j := 1) rfl rfl c47 c48
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f86
                omega
              have f87 := pair_fact E (i := 3) (j := 9) rfl rfl c43 c44
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f87
              omega
            by_cases c88 : a1 < b1 + b3 + b5
            swap
            · omega
            by_cases c89 : b1 + b3 < a1 + a3
            swap
            · -- branch
              by_cases c90 : 0 < a9
              swap
              · omega
              by_cases c91 : 0 < b1
              swap
              · omega
              by_cases c92 : a1 + a3 + a5 + a7 < 0 + b1
              swap
              · -- branch
                by_cases c93 : 0 < a3
                swap
                · omega
                by_cases c94 : 0 < b3
                swap
                · omega
                by_cases c95 : a1 < b1 + b3
                swap
                · omega
                by_cases c96 : b1 < a1 + a3
                swap
                · -- branch
                  by_cases c97 : 0 < a3
                  swap
                  · omega
                  by_cases c98 : 0 < b7
                  swap
                  · -- branch
                    by_cases c99 : 0 < a3
                    swap
                    · omega
                    by_cases c100 : 0 < b9
                    swap
                    · omega
                    by_cases c101 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c102 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · -- branch
                      by_cases c103 : 0 < a7
                      swap
                      · omega
                      by_cases c104 : 0 < b1
                      swap
                      · omega
                      by_cases c105 : a1 + a3 + a5 < 0 + b1
                      swap
                      · -- branch
                        by_cases c106 : 0 < a7
                        swap
                        · omega
                        by_cases c107 : 0 < b3
                        swap
                        · omega
                        by_cases c108 : a1 + a3 + a5 < b1 + b3
                        swap
                        · omega
                        by_cases c109 : b1 < a1 + a3 + a5 + a7
                        swap
                        · omega
                        have f110 := pair_fact E (i := 7) (j := 3) rfl rfl c106 c107
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f110
                        by_cases c111 : 0 < a9
                        swap
                        · omega
                        by_cases c112 : 0 < b9
                        swap
                        · omega
                        by_cases c113 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                        swap
                        · omega
                        by_cases c114 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                        swap
                        · omega
                        have f115 := pair_fact E (i := 9) (j := 9) rfl rfl c111 c112
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f115
                        omega
                      by_cases c116 : 0 < a1 + a3 + a5 + a7
                      swap
                      · omega
                      have f117 := pair_fact E (i := 7) (j := 1) rfl rfl c103 c104
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f117
                      omega
                    have f118 := pair_fact E (i := 3) (j := 9) rfl rfl c99 c100
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f118
                    omega
                  by_cases c119 : a1 < b1 + b3 + b5 + b7
                  swap
                  · omega
                  by_cases c120 : b1 + b3 + b5 < a1 + a3
                  swap
                  · -- branch
                    by_cases c121 : 0 < a3
                    swap
                    · omega
                    by_cases c122 : 0 < b9
                    swap
                    · -- branch
                      by_cases c123 : 0 < a5
                      swap
                      · -- branch
                        by_cases c124 : 0 < a5
                        swap
                        · -- branch
                          by_cases c125 : 0 < a5
                          swap
                          · -- branch
                            by_cases c126 : 0 < a5
                            swap
                            · -- branch
                              by_cases c127 : 0 < a5
                              swap
                              · -- branch
                                by_cases c128 : 0 < a7
                                swap
                                · -- branch
                                  by_cases c129 : 0 < a7
                                  swap
                                  · -- branch
                                    by_cases c130 : 0 < a7
                                    swap
                                    · -- branch
                                      by_cases c131 : 0 < a7
                                      swap
                                      · -- branch
                                        by_cases c132 : 0 < a7
                                        swap
                                        · -- branch
                                          by_cases c133 : 0 < a9
                                          swap
                                          · omega
                                          by_cases c134 : 0 < b3
                                          swap
                                          · omega
                                          by_cases c135 : a1 + a3 + a5 + a7 < b1 + b3
                                          swap
                                          · omega
                                          by_cases c136 : b1 < a1 + a3 + a5 + a7 + a9
                                          swap
                                          · omega
                                          have f137 := pair_fact E (i := 9) (j := 3) rfl rfl c133 c134
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f137
                                          by_cases c138 : 0 < a9
                                          swap
                                          · omega
                                          by_cases c139 : 0 < b5
                                          swap
                                          · omega
                                          by_cases c140 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                                          swap
                                          · omega
                                          by_cases c141 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                                          swap
                                          · omega
                                          have f142 := pair_fact E (i := 9) (j := 5) rfl rfl c138 c139
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f142
                                          omega
                                        by_cases c143 : 0 < b9
                                        swap
                                        · omega
                                        by_cases c144 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
                                        swap
                                        · omega
                                        by_cases c145 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
                                        swap
                                        · omega
                                        have f146 := pair_fact E (i := 7) (j := 9) rfl rfl c132 c143
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f146
                                        omega
                                      by_cases c147 : 0 < b7
                                      swap
                                      · omega
                                      by_cases c148 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                                      swap
                                      · omega
                                      by_cases c149 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                                      swap
                                      · omega
                                      have f150 := pair_fact E (i := 7) (j := 7) rfl rfl c131 c147
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f150
                                      omega
                                    by_cases c151 : 0 < b5
                                    swap
                                    · omega
                                    by_cases c152 : a1 + a3 + a5 < b1 + b3 + b5
                                    swap
                                    · omega
                                    by_cases c153 : b1 + b3 < a1 + a3 + a5 + a7
                                    swap
                                    · omega
                                    have f154 := pair_fact E (i := 7) (j := 5) rfl rfl c130 c151
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f154
                                    omega
                                  by_cases c155 : 0 < b3
                                  swap
                                  · omega
                                  by_cases c156 : a1 + a3 + a5 < b1 + b3
                                  swap
                                  · omega
                                  by_cases c157 : b1 < a1 + a3 + a5 + a7
                                  swap
                                  · omega
                                  have f158 := pair_fact E (i := 7) (j := 3) rfl rfl c129 c155
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f158
                                  omega
                                by_cases c159 : 0 < b1
                                swap
                                · omega
                                by_cases c160 : a1 + a3 + a5 < 0 + b1
                                swap
                                · omega
                                by_cases c161 : 0 < a1 + a3 + a5 + a7
                                swap
                                · omega
                                have f162 := pair_fact E (i := 7) (j := 1) rfl rfl c128 c159
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f162
                                omega
                              by_cases c163 : 0 < b9
                              swap
                              · omega
                              by_cases c164 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                              swap
                              · omega
                              by_cases c165 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                              swap
                              · omega
                              have f166 := pair_fact E (i := 5) (j := 9) rfl rfl c127 c163
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f166
                              omega
                            by_cases c167 : 0 < b7
                            swap
                            · omega
                            by_cases c168 : a1 + a3 < b1 + b3 + b5 + b7
                            swap
                            · omega
                            by_cases c169 : b1 + b3 + b5 < a1 + a3 + a5
                            swap
                            · omega
                            have f170 := pair_fact E (i := 5) (j := 7) rfl rfl c126 c167
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f170
                            omega
                          by_cases c171 : 0 < b5
                          swap
                          · omega
                          by_cases c172 : a1 + a3 < b1 + b3 + b5
                          swap
                          · omega
                          by_cases c173 : b1 + b3 < a1 + a3 + a5
                          swap
                          · omega
                          have f174 := pair_fact E (i := 5) (j := 5) rfl rfl c125 c171
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f174
                          omega
                        by_cases c175 : 0 < b3
                        swap
                        · omega
                        by_cases c176 : a1 + a3 < b1 + b3
                        swap
                        · omega
                        by_cases c177 : b1 < a1 + a3 + a5
                        swap
                        · omega
                        have f178 := pair_fact E (i := 5) (j := 3) rfl rfl c124 c175
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f178
                        omega
                      by_cases c179 : 0 < b1
                      swap
                      · omega
                      by_cases c180 : a1 + a3 < 0 + b1
                      swap
                      · omega
                      by_cases c181 : 0 < a1 + a3 + a5
                      swap
                      · omega
                      have f182 := pair_fact E (i := 5) (j := 1) rfl rfl c123 c179
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f182
                      omega
                    by_cases c183 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c184 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · -- branch
                      by_cases c185 : 0 < a9
                      swap
                      · omega
                      by_cases c186 : 0 < b9
                      swap
                      · omega
                      by_cases c187 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                      swap
                      · omega
                      by_cases c188 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                      swap
                      · omega
                      have f189 := pair_fact E (i := 9) (j := 9) rfl rfl c185 c186
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f189
                      by_cases c190 : 0 < a7
                      swap
                      · -- branch
                        by_cases c191 : 0 < a5
                        swap
                        · omega
                        by_cases c192 : 0 < b3
                        swap
                        · omega
                        by_cases c193 : a1 + a3 < b1 + b3
                        swap
                        · omega
                        by_cases c194 : b1 < a1 + a3 + a5
                        swap
                        · omega
                        have f195 := pair_fact E (i := 5) (j := 3) rfl rfl c191 c192
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f195
                        omega
                      by_cases c196 : 0 < b3
                      swap
                      · omega
                      by_cases c197 : a1 + a3 + a5 < b1 + b3
                      swap
                      · omega
                      by_cases c198 : b1 < a1 + a3 + a5 + a7
                      swap
                      · omega
                      have f199 := pair_fact E (i := 7) (j := 3) rfl rfl c190 c196
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f199
                      omega
                    have f200 := pair_fact E (i := 3) (j := 9) rfl rfl c121 c122
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f200
                    omega
                  have f201 := pair_fact E (i := 3) (j := 7) rfl rfl c97 c98
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f201
                  omega
                have f202 := pair_fact E (i := 3) (j := 3) rfl rfl c93 c94
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f202
                by_cases c203 : 0 < a3
                swap
                · omega
                by_cases c204 : 0 < b9
                swap
                · omega
                by_cases c205 : a1 < b1 + b3 + b5 + b7 + b9
                swap
                · omega
                by_cases c206 : b1 + b3 + b5 + b7 < a1 + a3
                swap
                · -- branch
                  by_cases c207 : 0 < a5
                  swap
                  · -- branch
                    by_cases c208 : 0 < a5
                    swap
                    · -- branch
                      by_cases c209 : 0 < a5
                      swap
                      · -- branch
                        by_cases c210 : 0 < a5
                        swap
                        · -- branch
                          by_cases c211 : 0 < a5
                          swap
                          · -- branch
                            by_cases c212 : 0 < a7
                            swap
                            · -- branch
                              by_cases c213 : 0 < a9
                              swap
                              · omega
                              by_cases c214 : 0 < b3
                              swap
                              · omega
                              by_cases c215 : a1 + a3 + a5 + a7 < b1 + b3
                              swap
                              · omega
                              by_cases c216 : b1 < a1 + a3 + a5 + a7 + a9
                              swap
                              · omega
                              have f217 := pair_fact E (i := 9) (j := 3) rfl rfl c213 c214
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f217
                              omega
                            by_cases c218 : 0 < b3
                            swap
                            · omega
                            by_cases c219 : a1 + a3 + a5 < b1 + b3
                            swap
                            · omega
                            by_cases c220 : b1 < a1 + a3 + a5 + a7
                            swap
                            · omega
                            have f221 := pair_fact E (i := 7) (j := 3) rfl rfl c212 c218
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f221
                            omega
                          by_cases c222 : 0 < b9
                          swap
                          · omega
                          by_cases c223 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                          swap
                          · omega
                          by_cases c224 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                          swap
                          · omega
                          have f225 := pair_fact E (i := 5) (j := 9) rfl rfl c211 c222
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f225
                          omega
                        by_cases c226 : 0 < b7
                        swap
                        · omega
                        by_cases c227 : a1 + a3 < b1 + b3 + b5 + b7
                        swap
                        · omega
                        by_cases c228 : b1 + b3 + b5 < a1 + a3 + a5
                        swap
                        · omega
                        have f229 := pair_fact E (i := 5) (j := 7) rfl rfl c210 c226
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f229
                        omega
                      by_cases c230 : 0 < b5
                      swap
                      · omega
                      by_cases c231 : a1 + a3 < b1 + b3 + b5
                      swap
                      · omega
                      by_cases c232 : b1 + b3 < a1 + a3 + a5
                      swap
                      · omega
                      have f233 := pair_fact E (i := 5) (j := 5) rfl rfl c209 c230
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f233
                      omega
                    by_cases c234 : 0 < b1
                    swap
                    · omega
                    by_cases c235 : a1 + a3 < 0 + b1
                    swap
                    · omega
                    by_cases c236 : 0 < a1 + a3 + a5
                    swap
                    · omega
                    have f237 := pair_fact E (i := 5) (j := 1) rfl rfl c208 c234
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f237
                    omega
                  by_cases c238 : 0 < b3
                  swap
                  · omega
                  by_cases c239 : a1 + a3 < b1 + b3
                  swap
                  · omega
                  by_cases c240 : b1 < a1 + a3 + a5
                  swap
                  · omega
                  have f241 := pair_fact E (i := 5) (j := 3) rfl rfl c207 c238
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f241
                  omega
                have f242 := pair_fact E (i := 3) (j := 9) rfl rfl c203 c204
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f242
                omega
              by_cases c243 : 0 < a1 + a3 + a5 + a7 + a9
              swap
              · omega
              have f244 := pair_fact E (i := 9) (j := 1) rfl rfl c90 c91
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f244
              omega
            have f245 := pair_fact E (i := 3) (j := 5) rfl rfl c41 c42
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f245
            omega
          by_cases c246 : 0 < b9
          swap
          · omega
          by_cases c247 : 0 < b1 + b3 + b5 + b7 + b9
          swap
          · omega
          by_cases c248 : b1 + b3 + b5 + b7 < 0 + a1
          swap
          · omega
          have f249 := pair_fact E (i := 1) (j := 9) rfl rfl c5 c246
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f249
          omega
        by_cases c250 : 0 < b7
        swap
        · omega
        by_cases c251 : 0 < b1 + b3 + b5 + b7
        swap
        · omega
        by_cases c252 : b1 + b3 + b5 < 0 + a1
        swap
        · omega
        have f253 := pair_fact E (i := 1) (j := 7) rfl rfl c4 c250
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f253
        omega
      by_cases c254 : 0 < b5
      swap
      · omega
      by_cases c255 : 0 < b1 + b3 + b5
      swap
      · omega
      by_cases c256 : b1 + b3 < 0 + a1
      swap
      · omega
      have f257 := pair_fact E (i := 1) (j := 5) rfl rfl c3 c254
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f257
      omega
    by_cases c258 : 0 < b3
    swap
    · omega
    by_cases c259 : 0 < b1 + b3
    swap
    · omega
    by_cases c260 : b1 < 0 + a1
    swap
    · omega
    have f261 := pair_fact E (i := 1) (j := 3) rfl rfl c2 c258
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f261
    omega
  by_cases c262 : 0 < b1
  swap
  · -- branch
    by_cases c263 : 0 < a1
    swap
    · omega
    by_cases c264 : 0 < b3
    swap
    · -- branch
      by_cases c265 : 0 < a1
      swap
      · omega
      by_cases c266 : 0 < b5
      swap
      · -- branch
        by_cases c267 : 0 < a1
        swap
        · omega
        by_cases c268 : 0 < b7
        swap
        · omega
        by_cases c269 : 0 < b1 + b3 + b5 + b7
        swap
        · omega
        by_cases c270 : b1 + b3 + b5 < 0 + a1
        swap
        · omega
        have f271 := pair_fact E (i := 1) (j := 7) rfl rfl c267 c268
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f271
        omega
      by_cases c272 : 0 < b1 + b3 + b5
      swap
      · omega
      by_cases c273 : b1 + b3 < 0 + a1
      swap
      · omega
      have f274 := pair_fact E (i := 1) (j := 5) rfl rfl c265 c266
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f274
      omega
    by_cases c275 : 0 < b1 + b3
    swap
    · omega
    by_cases c276 : b1 < 0 + a1
    swap
    · omega
    have f277 := pair_fact E (i := 1) (j := 3) rfl rfl c263 c264
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f277
    by_cases c278 : 0 < a1
    swap
    · omega
    by_cases c279 : 0 < b5
    swap
    · -- branch
      by_cases c280 : 0 < a1
      swap
      · omega
      by_cases c281 : 0 < b9
      swap
      · omega
      by_cases c282 : 0 < b1 + b3 + b5 + b7 + b9
      swap
      · omega
      by_cases c283 : b1 + b3 + b5 + b7 < 0 + a1
      swap
      · -- branch
        by_cases c284 : 0 < a5
        swap
        · omega
        by_cases c285 : 0 < b1
        swap
        · -- branch
          by_cases c286 : 0 < a5
          swap
          · omega
          by_cases c287 : 0 < b3
          swap
          · omega
          by_cases c288 : a1 + a3 < b1 + b3
          swap
          · -- branch
            by_cases c289 : 0 < a3
            swap
            · omega
            by_cases c290 : 0 < b1
            swap
            · -- branch
              by_cases c291 : 0 < a3
              swap
              · omega
              by_cases c292 : 0 < b5
              swap
              · -- branch
                by_cases c293 : 0 < a5
                swap
                · omega
                by_cases c294 : 0 < b5
                swap
                · -- branch
                  by_cases c295 : 0 < a5
                  swap
                  · omega
                  by_cases c296 : 0 < b9
                  swap
                  · omega
                  by_cases c297 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                  swap
                  · omega
                  by_cases c298 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                  swap
                  · omega
                  have f299 := pair_fact E (i := 5) (j := 9) rfl rfl c295 c296
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f299
                  by_cases c300 : 0 < a3
                  swap
                  · omega
                  by_cases c301 : 0 < b9
                  swap
                  · omega
                  by_cases c302 : a1 < b1 + b3 + b5 + b7 + b9
                  swap
                  · omega
                  by_cases c303 : b1 + b3 + b5 + b7 < a1 + a3
                  swap
                  · -- branch
                    by_cases c304 : 0 < a3
                    swap
                    · omega
                    by_cases c305 : 0 < b7
                    swap
                    · omega
                    by_cases c306 : a1 < b1 + b3 + b5 + b7
                    swap
                    · omega
                    by_cases c307 : b1 + b3 + b5 < a1 + a3
                    swap
                    · omega
                    have f308 := pair_fact E (i := 3) (j := 7) rfl rfl c304 c305
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f308
                    omega
                  have f309 := pair_fact E (i := 3) (j := 9) rfl rfl c300 c301
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f309
                  omega
                by_cases c310 : a1 + a3 < b1 + b3 + b5
                swap
                · omega
                by_cases c311 : b1 + b3 < a1 + a3 + a5
                swap
                · omega
                have f312 := pair_fact E (i := 5) (j := 5) rfl rfl c293 c294
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f312
                omega
              by_cases c313 : a1 < b1 + b3 + b5
              swap
              · omega
              by_cases c314 : b1 + b3 < a1 + a3
              swap
              · omega
              have f315 := pair_fact E (i := 3) (j := 5) rfl rfl c291 c292
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f315
              omega
            by_cases c316 : a1 < 0 + b1
            swap
            · omega
            by_cases c317 : 0 < a1 + a3
            swap
            · omega
            have f318 := pair_fact E (i := 3) (j := 1) rfl rfl c289 c290
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f318
            omega
          by_cases c319 : b1 < a1 + a3 + a5
          swap
          · omega
          have f320 := pair_fact E (i := 5) (j := 3) rfl rfl c286 c287
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f320
          omega
        by_cases c321 : a1 + a3 < 0 + b1
        swap
        · omega
        by_cases c322 : 0 < a1 + a3 + a5
        swap
        · omega
        have f323 := pair_fact E (i := 5) (j := 1) rfl rfl c284 c285
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f323
        omega
      have f324 := pair_fact E (i := 1) (j := 9) rfl rfl c280 c281
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f324
      omega
    by_cases c325 : 0 < b1 + b3 + b5
    swap
    · omega
    by_cases c326 : b1 + b3 < 0 + a1
    swap
    · -- branch
      by_cases c327 : 0 < a9
      swap
      · omega
      by_cases c328 : 0 < b1
      swap
      · -- branch
        by_cases c329 : 0 < a9
        swap
        · omega
        by_cases c330 : 0 < b3
        swap
        · omega
        by_cases c331 : a1 + a3 + a5 + a7 < b1 + b3
        swap
        · -- branch
          by_cases c332 : 0 < a1
          swap
          · omega
          by_cases c333 : 0 < b9
          swap
          · omega
          by_cases c334 : 0 < b1 + b3 + b5 + b7 + b9
          swap
          · omega
          by_cases c335 : b1 + b3 + b5 + b7 < 0 + a1
          swap
          · -- branch
            by_cases c336 : 0 < a9
            swap
            · omega
            by_cases c337 : 0 < b9
            swap
            · omega
            by_cases c338 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
            swap
            · omega
            by_cases c339 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
            swap
            · omega
            have f340 := pair_fact E (i := 9) (j := 9) rfl rfl c336 c337
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f340
            by_cases c341 : 0 < a1
            swap
            · omega
            by_cases c342 : 0 < b7
            swap
            · -- branch
              by_cases c343 : 0 < a7
              swap
              · omega
              by_cases c344 : 0 < b1
              swap
              · -- branch
                by_cases c345 : 0 < a7
                swap
                · omega
                by_cases c346 : 0 < b3
                swap
                · omega
                by_cases c347 : a1 + a3 + a5 < b1 + b3
                swap
                · -- branch
                  by_cases c348 : 0 < a3
                  swap
                  · omega
                  by_cases c349 : 0 < b1
                  swap
                  · -- branch
                    by_cases c350 : 0 < a3
                    swap
                    · omega
                    by_cases c351 : 0 < b5
                    swap
                    · omega
                    by_cases c352 : a1 < b1 + b3 + b5
                    swap
                    · omega
                    by_cases c353 : b1 + b3 < a1 + a3
                    swap
                    · -- branch
                      by_cases c354 : 0 < a5
                      swap
                      · omega
                      by_cases c355 : 0 < b3
                      swap
                      · omega
                      by_cases c356 : a1 + a3 < b1 + b3
                      swap
                      · omega
                      by_cases c357 : b1 < a1 + a3 + a5
                      swap
                      · omega
                      have f358 := pair_fact E (i := 5) (j := 3) rfl rfl c354 c355
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f358
                      omega
                    have f359 := pair_fact E (i := 3) (j := 5) rfl rfl c350 c351
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f359
                    omega
                  by_cases c360 : a1 < 0 + b1
                  swap
                  · omega
                  by_cases c361 : 0 < a1 + a3
                  swap
                  · omega
                  have f362 := pair_fact E (i := 3) (j := 1) rfl rfl c348 c349
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f362
                  omega
                by_cases c363 : b1 < a1 + a3 + a5 + a7
                swap
                · omega
                have f364 := pair_fact E (i := 7) (j := 3) rfl rfl c345 c346
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f364
                omega
              by_cases c365 : a1 + a3 + a5 < 0 + b1
              swap
              · omega
              by_cases c366 : 0 < a1 + a3 + a5 + a7
              swap
              · omega
              have f367 := pair_fact E (i := 7) (j := 1) rfl rfl c343 c344
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f367
              omega
            by_cases c368 : 0 < b1 + b3 + b5 + b7
            swap
            · omega
            by_cases c369 : b1 + b3 + b5 < 0 + a1
            swap
            · -- branch
              by_cases c370 : 0 < a3
              swap
              · -- branch
                by_cases c371 : 0 < a5
                swap
                · omega
                by_cases c372 : 0 < b3
                swap
                · omega
                by_cases c373 : a1 + a3 < b1 + b3
                swap
                · omega
                by_cases c374 : b1 < a1 + a3 + a5
                swap
                · omega
                have f375 := pair_fact E (i := 5) (j := 3) rfl rfl c371 c372
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f375
                omega
              by_cases c376 : 0 < b1
              swap
              · -- branch
                by_cases c377 : 0 < a3
                swap
                · omega
                by_cases c378 : 0 < b5
                swap
                · omega
                by_cases c379 : a1 < b1 + b3 + b5
                swap
                · omega
                by_cases c380 : b1 + b3 < a1 + a3
                swap
                · -- branch
                  by_cases c381 : 0 < a3
                  swap
                  · omega
                  by_cases c382 : 0 < b3
                  swap
                  · omega
                  by_cases c383 : a1 < b1 + b3
                  swap
                  · omega
                  by_cases c384 : b1 < a1 + a3
                  swap
                  · omega
                  have f385 := pair_fact E (i := 3) (j := 3) rfl rfl c381 c382
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f385
                  by_cases c386 : 0 < a3
                  swap
                  · omega
                  by_cases c387 : 0 < b7
                  swap
                  · omega
                  by_cases c388 : a1 < b1 + b3 + b5 + b7
                  swap
                  · omega
                  by_cases c389 : b1 + b3 + b5 < a1 + a3
                  swap
                  · -- branch
                    by_cases c390 : 0 < a3
                    swap
                    · omega
                    by_cases c391 : 0 < b9
                    swap
                    · omega
                    by_cases c392 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c393 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · -- branch
                      by_cases c394 : 0 < a5
                      swap
                      · -- branch
                        by_cases c395 : 0 < a7
                        swap
                        · omega
                        by_cases c396 : 0 < b3
                        swap
                        · omega
                        by_cases c397 : a1 + a3 + a5 < b1 + b3
                        swap
                        · omega
                        by_cases c398 : b1 < a1 + a3 + a5 + a7
                        swap
                        · omega
                        have f399 := pair_fact E (i := 7) (j := 3) rfl rfl c395 c396
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f399
                        omega
                      by_cases c400 : 0 < b3
                      swap
                      · omega
                      by_cases c401 : a1 + a3 < b1 + b3
                      swap
                      · omega
                      by_cases c402 : b1 < a1 + a3 + a5
                      swap
                      · omega
                      have f403 := pair_fact E (i := 5) (j := 3) rfl rfl c394 c400
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f403
                      omega
                    have f404 := pair_fact E (i := 3) (j := 9) rfl rfl c390 c391
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f404
                    omega
                  have f405 := pair_fact E (i := 3) (j := 7) rfl rfl c386 c387
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f405
                  omega
                have f406 := pair_fact E (i := 3) (j := 5) rfl rfl c377 c378
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f406
                omega
              by_cases c407 : a1 < 0 + b1
              swap
              · omega
              by_cases c408 : 0 < a1 + a3
              swap
              · omega
              have f409 := pair_fact E (i := 3) (j := 1) rfl rfl c370 c376
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f409
              omega
            have f410 := pair_fact E (i := 1) (j := 7) rfl rfl c341 c342
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f410
            omega
          have f411 := pair_fact E (i := 1) (j := 9) rfl rfl c332 c333
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f411
          omega
        by_cases c412 : b1 < a1 + a3 + a5 + a7 + a9
        swap
        · omega
        have f413 := pair_fact E (i := 9) (j := 3) rfl rfl c329 c330
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f413
        omega
      by_cases c414 : a1 + a3 + a5 + a7 < 0 + b1
      swap
      · omega
      by_cases c415 : 0 < a1 + a3 + a5 + a7 + a9
      swap
      · omega
      have f416 := pair_fact E (i := 9) (j := 1) rfl rfl c327 c328
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f416
      omega
    have f417 := pair_fact E (i := 1) (j := 5) rfl rfl c278 c279
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f417
    omega
  by_cases c418 : 0 < 0 + b1
  swap
  · omega
  by_cases c419 : 0 < 0 + a1
  swap
  · omega
  have f420 := pair_fact E (i := 1) (j := 1) rfl rfl c1 c262
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f420
  by_cases c421 : 0 < a1
  swap
  · omega
  by_cases c422 : 0 < b5
  swap
  · -- branch
    by_cases c423 : 0 < a1
    swap
    · omega
    by_cases c424 : 0 < b9
    swap
    · omega
    by_cases c425 : 0 < b1 + b3 + b5 + b7 + b9
    swap
    · omega
    by_cases c426 : b1 + b3 + b5 + b7 < 0 + a1
    swap
    · -- branch
      by_cases c427 : 0 < a5
      swap
      · omega
      by_cases c428 : 0 < b1
      swap
      · omega
      by_cases c429 : a1 + a3 < 0 + b1
      swap
      · -- branch
        by_cases c430 : 0 < a5
        swap
        · omega
        by_cases c431 : 0 < b5
        swap
        · -- branch
          by_cases c432 : 0 < a1
          swap
          · omega
          by_cases c433 : 0 < b7
          swap
          · -- branch
            by_cases c434 : 0 < a5
            swap
            · omega
            by_cases c435 : 0 < b7
            swap
            · -- branch
              by_cases c436 : 0 < a7
              swap
              · omega
              by_cases c437 : 0 < b1
              swap
              · omega
              by_cases c438 : a1 + a3 + a5 < 0 + b1
              swap
              · -- branch
                by_cases c439 : 0 < a7
                swap
                · omega
                by_cases c440 : 0 < b5
                swap
                · -- branch
                  by_cases c441 : 0 < a7
                  swap
                  · omega
                  by_cases c442 : 0 < b7
                  swap
                  · -- branch
                    by_cases c443 : 0 < a7
                    swap
                    · omega
                    by_cases c444 : 0 < b9
                    swap
                    · omega
                    by_cases c445 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c446 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
                    swap
                    · omega
                    have f447 := pair_fact E (i := 7) (j := 9) rfl rfl c443 c444
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f447
                    by_cases c448 : 0 < a5
                    swap
                    · omega
                    by_cases c449 : 0 < b3
                    swap
                    · omega
                    by_cases c450 : a1 + a3 < b1 + b3
                    swap
                    · -- branch
                      by_cases c451 : 0 < a3
                      swap
                      · omega
                      by_cases c452 : 0 < b9
                      swap
                      · omega
                      by_cases c453 : a1 < b1 + b3 + b5 + b7 + b9
                      swap
                      · omega
                      by_cases c454 : b1 + b3 + b5 + b7 < a1 + a3
                      swap
                      · omega
                      have f455 := pair_fact E (i := 3) (j := 9) rfl rfl c451 c452
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f455
                      omega
                    by_cases c456 : b1 < a1 + a3 + a5
                    swap
                    · omega
                    have f457 := pair_fact E (i := 5) (j := 3) rfl rfl c448 c449
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f457
                    omega
                  by_cases c458 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                  swap
                  · omega
                  by_cases c459 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                  swap
                  · omega
                  have f460 := pair_fact E (i := 7) (j := 7) rfl rfl c441 c442
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f460
                  omega
                by_cases c461 : a1 + a3 + a5 < b1 + b3 + b5
                swap
                · omega
                by_cases c462 : b1 + b3 < a1 + a3 + a5 + a7
                swap
                · omega
                have f463 := pair_fact E (i := 7) (j := 5) rfl rfl c439 c440
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f463
                omega
              by_cases c464 : 0 < a1 + a3 + a5 + a7
              swap
              · omega
              have f465 := pair_fact E (i := 7) (j := 1) rfl rfl c436 c437
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f465
              omega
            by_cases c466 : a1 + a3 < b1 + b3 + b5 + b7
            swap
            · omega
            by_cases c467 : b1 + b3 + b5 < a1 + a3 + a5
            swap
            · omega
            have f468 := pair_fact E (i := 5) (j := 7) rfl rfl c434 c435
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f468
            omega
          by_cases c469 : 0 < b1 + b3 + b5 + b7
          swap
          · omega
          by_cases c470 : b1 + b3 + b5 < 0 + a1
          swap
          · -- branch
            by_cases c471 : 0 < a3
            swap
            · -- branch
              by_cases c472 : 0 < a1
              swap
              · omega
              by_cases c473 : 0 < b3
              swap
              · omega
              by_cases c474 : 0 < b1 + b3
              swap
              · omega
              by_cases c475 : b1 < 0 + a1
              swap
              · omega
              have f476 := pair_fact E (i := 1) (j := 3) rfl rfl c472 c473
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f476
              by_cases c477 : 0 < a5
              swap
              · omega
              by_cases c478 : 0 < b3
              swap
              · omega
              by_cases c479 : a1 + a3 < b1 + b3
              swap
              · omega
              by_cases c480 : b1 < a1 + a3 + a5
              swap
              · omega
              have f481 := pair_fact E (i := 5) (j := 3) rfl rfl c477 c478
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f481
              omega
            by_cases c482 : 0 < b5
            swap
            · -- branch
              by_cases c483 : 0 < a3
              swap
              · omega
              by_cases c484 : 0 < b1
              swap
              · omega
              by_cases c485 : a1 < 0 + b1
              swap
              · -- branch
                by_cases c486 : 0 < a1
                swap
                · omega
                by_cases c487 : 0 < b3
                swap
                · omega
                by_cases c488 : 0 < b1 + b3
                swap
                · omega
                by_cases c489 : b1 < 0 + a1
                swap
                · omega
                have f490 := pair_fact E (i := 1) (j := 3) rfl rfl c486 c487
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f490
                by_cases c491 : 0 < a3
                swap
                · omega
                by_cases c492 : 0 < b3
                swap
                · omega
                by_cases c493 : a1 < b1 + b3
                swap
                · -- branch
                  by_cases c494 : 0 < a3
                  swap
                  · omega
                  by_cases c495 : 0 < b7
                  swap
                  · omega
                  by_cases c496 : a1 < b1 + b3 + b5 + b7
                  swap
                  · omega
                  by_cases c497 : b1 + b3 + b5 < a1 + a3
                  swap
                  · omega
                  have f498 := pair_fact E (i := 3) (j := 7) rfl rfl c494 c495
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f498
                  by_cases c499 : 0 < a5
                  swap
                  · omega
                  by_cases c500 : 0 < b9
                  swap
                  · omega
                  by_cases c501 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                  swap
                  · omega
                  by_cases c502 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                  swap
                  · omega
                  have f503 := pair_fact E (i := 5) (j := 9) rfl rfl c499 c500
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f503
                  omega
                by_cases c504 : b1 < a1 + a3
                swap
                · omega
                have f505 := pair_fact E (i := 3) (j := 3) rfl rfl c491 c492
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f505
                omega
              by_cases c506 : 0 < a1 + a3
              swap
              · omega
              have f507 := pair_fact E (i := 3) (j := 1) rfl rfl c483 c484
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f507
              by_cases c508 : 0 < a3
              swap
              · omega
              by_cases c509 : 0 < b7
              swap
              · omega
              by_cases c510 : a1 < b1 + b3 + b5 + b7
              swap
              · omega
              by_cases c511 : b1 + b3 + b5 < a1 + a3
              swap
              · -- branch
                by_cases c512 : 0 < a1
                swap
                · omega
                by_cases c513 : 0 < b3
                swap
                · omega
                by_cases c514 : 0 < b1 + b3
                swap
                · omega
                by_cases c515 : b1 < 0 + a1
                swap
                · -- branch
                  by_cases c516 : 0 < a3
                  swap
                  · omega
                  by_cases c517 : 0 < b3
                  swap
                  · omega
                  by_cases c518 : a1 < b1 + b3
                  swap
                  · omega
                  by_cases c519 : b1 < a1 + a3
                  swap
                  · -- branch
                    by_cases c520 : 0 < a3
                    swap
                    · omega
                    by_cases c521 : 0 < b9
                    swap
                    · omega
                    by_cases c522 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c523 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · -- branch
                      by_cases c524 : 0 < a5
                      swap
                      · omega
                      by_cases c525 : 0 < b3
                      swap
                      · omega
                      by_cases c526 : a1 + a3 < b1 + b3
                      swap
                      · omega
                      by_cases c527 : b1 < a1 + a3 + a5
                      swap
                      · omega
                      have f528 := pair_fact E (i := 5) (j := 3) rfl rfl c524 c525
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f528
                      by_cases c529 : 0 < a9
                      swap
                      · omega
                      by_cases c530 : 0 < b9
                      swap
                      · omega
                      by_cases c531 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                      swap
                      · omega
                      by_cases c532 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                      swap
                      · omega
                      have f533 := pair_fact E (i := 9) (j := 9) rfl rfl c529 c530
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f533
                      omega
                    have f534 := pair_fact E (i := 3) (j := 9) rfl rfl c520 c521
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f534
                    omega
                  have f535 := pair_fact E (i := 3) (j := 3) rfl rfl c516 c517
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f535
                  omega
                have f536 := pair_fact E (i := 1) (j := 3) rfl rfl c512 c513
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f536
                omega
              have f537 := pair_fact E (i := 3) (j := 7) rfl rfl c508 c509
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f537
              omega
            by_cases c538 : a1 < b1 + b3 + b5
            swap
            · omega
            by_cases c539 : b1 + b3 < a1 + a3
            swap
            · omega
            have f540 := pair_fact E (i := 3) (j := 5) rfl rfl c471 c482
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f540
            omega
          have f541 := pair_fact E (i := 1) (j := 7) rfl rfl c432 c433
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f541
          omega
        by_cases c542 : a1 + a3 < b1 + b3 + b5
        swap
        · omega
        by_cases c543 : b1 + b3 < a1 + a3 + a5
        swap
        · omega
        have f544 := pair_fact E (i := 5) (j := 5) rfl rfl c430 c431
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f544
        omega
      by_cases c545 : 0 < a1 + a3 + a5
      swap
      · omega
      have f546 := pair_fact E (i := 5) (j := 1) rfl rfl c427 c428
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f546
      omega
    have f547 := pair_fact E (i := 1) (j := 9) rfl rfl c423 c424
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f547
    omega
  by_cases c548 : 0 < b1 + b3 + b5
  swap
  · omega
  by_cases c549 : b1 + b3 < 0 + a1
  swap
  · -- branch
    by_cases c550 : 0 < a1
    swap
    · omega
    by_cases c551 : 0 < b7
    swap
    · -- branch
      by_cases c552 : 0 < a1
      swap
      · omega
      by_cases c553 : 0 < b9
      swap
      · omega
      by_cases c554 : 0 < b1 + b3 + b5 + b7 + b9
      swap
      · omega
      by_cases c555 : b1 + b3 + b5 + b7 < 0 + a1
      swap
      · -- branch
        by_cases c556 : 0 < a7
        swap
        · omega
        by_cases c557 : 0 < b1
        swap
        · omega
        by_cases c558 : a1 + a3 + a5 < 0 + b1
        swap
        · -- branch
          by_cases c559 : 0 < a7
          swap
          · omega
          by_cases c560 : 0 < b7
          swap
          · -- branch
            by_cases c561 : 0 < a3
            swap
            · -- branch
              by_cases c562 : 0 < a3
              swap
              · -- branch
                by_cases c563 : 0 < a3
                swap
                · -- branch
                  by_cases c564 : 0 < a3
                  swap
                  · -- branch
                    by_cases c565 : 0 < a3
                    swap
                    · -- branch
                      by_cases c566 : 0 < a7
                      swap
                      · omega
                      by_cases c567 : 0 < b3
                      swap
                      · omega
                      by_cases c568 : a1 + a3 + a5 < b1 + b3
                      swap
                      · omega
                      by_cases c569 : b1 < a1 + a3 + a5 + a7
                      swap
                      · omega
                      have f570 := pair_fact E (i := 7) (j := 3) rfl rfl c566 c567
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f570
                      by_cases c571 : 0 < a9
                      swap
                      · omega
                      by_cases c572 : 0 < b9
                      swap
                      · omega
                      by_cases c573 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                      swap
                      · omega
                      by_cases c574 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                      swap
                      · omega
                      have f575 := pair_fact E (i := 9) (j := 9) rfl rfl c571 c572
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f575
                      omega
                    by_cases c576 : 0 < b9
                    swap
                    · omega
                    by_cases c577 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c578 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · omega
                    have f579 := pair_fact E (i := 3) (j := 9) rfl rfl c565 c576
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f579
                    omega
                  by_cases c580 : 0 < b5
                  swap
                  · omega
                  by_cases c581 : a1 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c582 : b1 + b3 < a1 + a3
                  swap
                  · omega
                  have f583 := pair_fact E (i := 3) (j := 5) rfl rfl c564 c580
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f583
                  omega
                by_cases c584 : 0 < b3
                swap
                · omega
                by_cases c585 : a1 < b1 + b3
                swap
                · omega
                by_cases c586 : b1 < a1 + a3
                swap
                · omega
                have f587 := pair_fact E (i := 3) (j := 3) rfl rfl c563 c584
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f587
                omega
              by_cases c588 : 0 < b1
              swap
              · omega
              by_cases c589 : a1 < 0 + b1
              swap
              · omega
              by_cases c590 : 0 < a1 + a3
              swap
              · omega
              have f591 := pair_fact E (i := 3) (j := 1) rfl rfl c562 c588
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f591
              omega
            by_cases c592 : 0 < b7
            swap
            · -- branch
              by_cases c593 : 0 < a3
              swap
              · omega
              by_cases c594 : 0 < b1
              swap
              · omega
              by_cases c595 : a1 < 0 + b1
              swap
              · -- branch
                by_cases c596 : 0 < a1
                swap
                · omega
                by_cases c597 : 0 < b3
                swap
                · omega
                by_cases c598 : 0 < b1 + b3
                swap
                · omega
                by_cases c599 : b1 < 0 + a1
                swap
                · omega
                have f600 := pair_fact E (i := 1) (j := 3) rfl rfl c596 c597
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f600
                by_cases c601 : 0 < a3
                swap
                · omega
                by_cases c602 : 0 < b3
                swap
                · omega
                by_cases c603 : a1 < b1 + b3
                swap
                · -- branch
                  by_cases c604 : 0 < a3
                  swap
                  · omega
                  by_cases c605 : 0 < b5
                  swap
                  · omega
                  by_cases c606 : a1 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c607 : b1 + b3 < a1 + a3
                  swap
                  · omega
                  have f608 := pair_fact E (i := 3) (j := 5) rfl rfl c604 c605
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f608
                  by_cases c609 : 0 < a7
                  swap
                  · omega
                  by_cases c610 : 0 < b9
                  swap
                  · omega
                  by_cases c611 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
                  swap
                  · omega
                  by_cases c612 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
                  swap
                  · omega
                  have f613 := pair_fact E (i := 7) (j := 9) rfl rfl c609 c610
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f613
                  omega
                by_cases c614 : b1 < a1 + a3
                swap
                · omega
                have f615 := pair_fact E (i := 3) (j := 3) rfl rfl c601 c602
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f615
                omega
              by_cases c616 : 0 < a1 + a3
              swap
              · omega
              have f617 := pair_fact E (i := 3) (j := 1) rfl rfl c593 c594
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f617
              by_cases c618 : 0 < a3
              swap
              · omega
              by_cases c619 : 0 < b5
              swap
              · omega
              by_cases c620 : a1 < b1 + b3 + b5
              swap
              · omega
              by_cases c621 : b1 + b3 < a1 + a3
              swap
              · -- branch
                by_cases c622 : 0 < a1
                swap
                · omega
                by_cases c623 : 0 < b3
                swap
                · omega
                by_cases c624 : 0 < b1 + b3
                swap
                · omega
                by_cases c625 : b1 < 0 + a1
                swap
                · -- branch
                  by_cases c626 : 0 < a3
                  swap
                  · omega
                  by_cases c627 : 0 < b3
                  swap
                  · omega
                  by_cases c628 : a1 < b1 + b3
                  swap
                  · omega
                  by_cases c629 : b1 < a1 + a3
                  swap
                  · -- branch
                    by_cases c630 : 0 < a3
                    swap
                    · omega
                    by_cases c631 : 0 < b9
                    swap
                    · omega
                    by_cases c632 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c633 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · -- branch
                      by_cases c634 : 0 < a7
                      swap
                      · omega
                      by_cases c635 : 0 < b3
                      swap
                      · omega
                      by_cases c636 : a1 + a3 + a5 < b1 + b3
                      swap
                      · omega
                      by_cases c637 : b1 < a1 + a3 + a5 + a7
                      swap
                      · omega
                      have f638 := pair_fact E (i := 7) (j := 3) rfl rfl c634 c635
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f638
                      by_cases c639 : 0 < a9
                      swap
                      · omega
                      by_cases c640 : 0 < b9
                      swap
                      · omega
                      by_cases c641 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                      swap
                      · omega
                      by_cases c642 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                      swap
                      · omega
                      have f643 := pair_fact E (i := 9) (j := 9) rfl rfl c639 c640
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f643
                      omega
                    have f644 := pair_fact E (i := 3) (j := 9) rfl rfl c630 c631
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f644
                    omega
                  have f645 := pair_fact E (i := 3) (j := 3) rfl rfl c626 c627
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f645
                  omega
                have f646 := pair_fact E (i := 1) (j := 3) rfl rfl c622 c623
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f646
                omega
              have f647 := pair_fact E (i := 3) (j := 5) rfl rfl c618 c619
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f647
              omega
            by_cases c648 : a1 < b1 + b3 + b5 + b7
            swap
            · omega
            by_cases c649 : b1 + b3 + b5 < a1 + a3
            swap
            · omega
            have f650 := pair_fact E (i := 3) (j := 7) rfl rfl c561 c592
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f650
            omega
          by_cases c651 : a1 + a3 + a5 < b1 + b3 + b5 + b7
          swap
          · omega
          by_cases c652 : b1 + b3 + b5 < a1 + a3 + a5 + a7
          swap
          · omega
          have f653 := pair_fact E (i := 7) (j := 7) rfl rfl c559 c560
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f653
          omega
        by_cases c654 : 0 < a1 + a3 + a5 + a7
        swap
        · omega
        have f655 := pair_fact E (i := 7) (j := 1) rfl rfl c556 c557
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f655
        omega
      have f656 := pair_fact E (i := 1) (j := 9) rfl rfl c552 c553
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f656
      omega
    by_cases c657 : 0 < b1 + b3 + b5 + b7
    swap
    · omega
    by_cases c658 : b1 + b3 + b5 < 0 + a1
    swap
    · -- branch
      by_cases c659 : 0 < a1
      swap
      · omega
      by_cases c660 : 0 < b9
      swap
      · -- branch
        by_cases c661 : 0 < a9
        swap
        · omega
        by_cases c662 : 0 < b1
        swap
        · omega
        by_cases c663 : a1 + a3 + a5 + a7 < 0 + b1
        swap
        · -- branch
          by_cases c664 : 0 < a9
          swap
          · omega
          by_cases c665 : 0 < b3
          swap
          · omega
          by_cases c666 : a1 + a3 + a5 + a7 < b1 + b3
          swap
          · omega
          by_cases c667 : b1 < a1 + a3 + a5 + a7 + a9
          swap
          · omega
          have f668 := pair_fact E (i := 9) (j := 3) rfl rfl c664 c665
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f668
          by_cases c669 : 0 < a9
          swap
          · omega
          by_cases c670 : 0 < b5
          swap
          · omega
          by_cases c671 : a1 + a3 + a5 + a7 < b1 + b3 + b5
          swap
          · omega
          by_cases c672 : b1 + b3 < a1 + a3 + a5 + a7 + a9
          swap
          · omega
          have f673 := pair_fact E (i := 9) (j := 5) rfl rfl c669 c670
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f673
          omega
        by_cases c674 : 0 < a1 + a3 + a5 + a7 + a9
        swap
        · omega
        have f675 := pair_fact E (i := 9) (j := 1) rfl rfl c661 c662
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f675
        omega
      by_cases c676 : 0 < b1 + b3 + b5 + b7 + b9
      swap
      · omega
      by_cases c677 : b1 + b3 + b5 + b7 < 0 + a1
      swap
      · -- branch
        by_cases c678 : 0 < a5
        swap
        · -- branch
          by_cases c679 : 0 < a5
          swap
          · -- branch
            by_cases c680 : 0 < a5
            swap
            · -- branch
              by_cases c681 : 0 < a5
              swap
              · -- branch
                by_cases c682 : 0 < a5
                swap
                · -- branch
                  by_cases c683 : 0 < a9
                  swap
                  · omega
                  by_cases c684 : 0 < b1
                  swap
                  · omega
                  by_cases c685 : a1 + a3 + a5 + a7 < 0 + b1
                  swap
                  · -- branch
                    by_cases c686 : 0 < a9
                    swap
                    · omega
                    by_cases c687 : 0 < b9
                    swap
                    · omega
                    by_cases c688 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c689 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                    swap
                    · omega
                    have f690 := pair_fact E (i := 9) (j := 9) rfl rfl c686 c687
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f690
                    by_cases c691 : 0 < a3
                    swap
                    · -- branch
                      by_cases c692 : 0 < a7
                      swap
                      · omega
                      by_cases c693 : 0 < b3
                      swap
                      · omega
                      by_cases c694 : a1 + a3 + a5 < b1 + b3
                      swap
                      · omega
                      by_cases c695 : b1 < a1 + a3 + a5 + a7
                      swap
                      · omega
                      have f696 := pair_fact E (i := 7) (j := 3) rfl rfl c692 c693
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f696
                      omega
                    by_cases c697 : 0 < b5
                    swap
                    · omega
                    by_cases c698 : a1 < b1 + b3 + b5
                    swap
                    · omega
                    by_cases c699 : b1 + b3 < a1 + a3
                    swap
                    · -- branch
                      by_cases c700 : 0 < a3
                      swap
                      · omega
                      by_cases c701 : 0 < b7
                      swap
                      · omega
                      by_cases c702 : a1 < b1 + b3 + b5 + b7
                      swap
                      · omega
                      by_cases c703 : b1 + b3 + b5 < a1 + a3
                      swap
                      · -- branch
                        by_cases c704 : 0 < a3
                        swap
                        · omega
                        by_cases c705 : 0 < b9
                        swap
                        · omega
                        by_cases c706 : a1 < b1 + b3 + b5 + b7 + b9
                        swap
                        · omega
                        by_cases c707 : b1 + b3 + b5 + b7 < a1 + a3
                        swap
                        · -- branch
                          by_cases c708 : 0 < a7
                          swap
                          · -- branch
                            by_cases c709 : 0 < a9
                            swap
                            · omega
                            by_cases c710 : 0 < b3
                            swap
                            · omega
                            by_cases c711 : a1 + a3 + a5 + a7 < b1 + b3
                            swap
                            · omega
                            by_cases c712 : b1 < a1 + a3 + a5 + a7 + a9
                            swap
                            · omega
                            have f713 := pair_fact E (i := 9) (j := 3) rfl rfl c709 c710
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f713
                            omega
                          by_cases c714 : 0 < b3
                          swap
                          · omega
                          by_cases c715 : a1 + a3 + a5 < b1 + b3
                          swap
                          · omega
                          by_cases c716 : b1 < a1 + a3 + a5 + a7
                          swap
                          · omega
                          have f717 := pair_fact E (i := 7) (j := 3) rfl rfl c708 c714
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f717
                          omega
                        have f718 := pair_fact E (i := 3) (j := 9) rfl rfl c704 c705
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f718
                        omega
                      have f719 := pair_fact E (i := 3) (j := 7) rfl rfl c700 c701
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f719
                      omega
                    have f720 := pair_fact E (i := 3) (j := 5) rfl rfl c691 c697
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f720
                    omega
                  by_cases c721 : 0 < a1 + a3 + a5 + a7 + a9
                  swap
                  · omega
                  have f722 := pair_fact E (i := 9) (j := 1) rfl rfl c683 c684
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f722
                  omega
                by_cases c723 : 0 < b9
                swap
                · omega
                by_cases c724 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                swap
                · omega
                by_cases c725 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                swap
                · omega
                have f726 := pair_fact E (i := 5) (j := 9) rfl rfl c682 c723
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f726
                omega
              by_cases c727 : 0 < b7
              swap
              · omega
              by_cases c728 : a1 + a3 < b1 + b3 + b5 + b7
              swap
              · omega
              by_cases c729 : b1 + b3 + b5 < a1 + a3 + a5
              swap
              · omega
              have f730 := pair_fact E (i := 5) (j := 7) rfl rfl c681 c727
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f730
              omega
            by_cases c731 : 0 < b5
            swap
            · omega
            by_cases c732 : a1 + a3 < b1 + b3 + b5
            swap
            · omega
            by_cases c733 : b1 + b3 < a1 + a3 + a5
            swap
            · omega
            have f734 := pair_fact E (i := 5) (j := 5) rfl rfl c680 c731
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f734
            omega
          by_cases c735 : 0 < b3
          swap
          · omega
          by_cases c736 : a1 + a3 < b1 + b3
          swap
          · omega
          by_cases c737 : b1 < a1 + a3 + a5
          swap
          · omega
          have f738 := pair_fact E (i := 5) (j := 3) rfl rfl c679 c735
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f738
          omega
        by_cases c739 : 0 < b1
        swap
        · omega
        by_cases c740 : a1 + a3 < 0 + b1
        swap
        · -- branch
          by_cases c741 : 0 < a5
          swap
          · omega
          by_cases c742 : 0 < b9
          swap
          · omega
          by_cases c743 : a1 + a3 < b1 + b3 + b5 + b7 + b9
          swap
          · omega
          by_cases c744 : b1 + b3 + b5 + b7 < a1 + a3 + a5
          swap
          · -- branch
            by_cases c745 : 0 < a9
            swap
            · omega
            by_cases c746 : 0 < b1
            swap
            · omega
            by_cases c747 : a1 + a3 + a5 + a7 < 0 + b1
            swap
            · -- branch
              by_cases c748 : 0 < a9
              swap
              · omega
              by_cases c749 : 0 < b9
              swap
              · omega
              by_cases c750 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
              swap
              · omega
              by_cases c751 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
              swap
              · omega
              have f752 := pair_fact E (i := 9) (j := 9) rfl rfl c748 c749
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f752
              by_cases c753 : 0 < a3
              swap
              · -- branch
                by_cases c754 : 0 < a5
                swap
                · omega
                by_cases c755 : 0 < b3
                swap
                · omega
                by_cases c756 : a1 + a3 < b1 + b3
                swap
                · omega
                by_cases c757 : b1 < a1 + a3 + a5
                swap
                · omega
                have f758 := pair_fact E (i := 5) (j := 3) rfl rfl c754 c755
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f758
                omega
              by_cases c759 : 0 < b5
              swap
              · omega
              by_cases c760 : a1 < b1 + b3 + b5
              swap
              · omega
              by_cases c761 : b1 + b3 < a1 + a3
              swap
              · -- branch
                by_cases c762 : 0 < a5
                swap
                · omega
                by_cases c763 : 0 < b3
                swap
                · omega
                by_cases c764 : a1 + a3 < b1 + b3
                swap
                · omega
                by_cases c765 : b1 < a1 + a3 + a5
                swap
                · omega
                have f766 := pair_fact E (i := 5) (j := 3) rfl rfl c762 c763
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f766
                omega
              have f767 := pair_fact E (i := 3) (j := 5) rfl rfl c753 c759
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f767
              omega
            by_cases c768 : 0 < a1 + a3 + a5 + a7 + a9
            swap
            · omega
            have f769 := pair_fact E (i := 9) (j := 1) rfl rfl c745 c746
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f769
            omega
          have f770 := pair_fact E (i := 5) (j := 9) rfl rfl c741 c742
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f770
          by_cases c771 : 0 < a3
          swap
          · omega
          by_cases c772 : 0 < b5
          swap
          · omega
          by_cases c773 : a1 < b1 + b3 + b5
          swap
          · omega
          by_cases c774 : b1 + b3 < a1 + a3
          swap
          · -- branch
            by_cases c775 : 0 < a5
            swap
            · omega
            by_cases c776 : 0 < b3
            swap
            · omega
            by_cases c777 : a1 + a3 < b1 + b3
            swap
            · omega
            by_cases c778 : b1 < a1 + a3 + a5
            swap
            · omega
            have f779 := pair_fact E (i := 5) (j := 3) rfl rfl c775 c776
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f779
            omega
          have f780 := pair_fact E (i := 3) (j := 5) rfl rfl c771 c772
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f780
          omega
        by_cases c781 : 0 < a1 + a3 + a5
        swap
        · omega
        have f782 := pair_fact E (i := 5) (j := 1) rfl rfl c678 c739
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f782
        omega
      have f783 := pair_fact E (i := 1) (j := 9) rfl rfl c659 c660
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f783
      omega
    have f784 := pair_fact E (i := 1) (j := 7) rfl rfl c550 c551
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f784
    omega
  have f785 := pair_fact E (i := 1) (j := 5) rfl rfl c421 c422
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f785
  omega

end Blocks
