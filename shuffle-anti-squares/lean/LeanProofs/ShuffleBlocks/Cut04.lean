import LeanProofs.ShuffleBlocks.Basic

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Blocks

set_option maxHeartbeats 0 in
/-- Cut inside run 4 of `V`: no splitting of this rotation gives two equal copies. -/
theorem V_cut04 (L l m v k a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9 a10 b10 : Nat)
    (hl : 1 ≤ l) (hm : m = 2 * v + 1) (hL : 9 * l ≤ L) (hk : k ≤ L)
    (e0 : a0 + b0 = (L - k))
    (e1 : a1 + b1 = m)
    (e2 : a2 + b2 = 2 * l)
    (e3 : a3 + b3 = m)
    (e4 : a4 + b4 = l)
    (e5 : a5 + b5 = 3 * m)
    (e6 : a6 + b6 = L)
    (e7 : a7 + b7 = m)
    (e8 : a8 + b8 = 5 * l)
    (e9 : a9 + b9 = 2 * m)
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
                      · omega
                      by_cases c12 : 0 < b1
                      swap
                      · omega
                      by_cases c13 : a1 + a3 < 0 + b1
                      swap
                      · omega
                      by_cases c14 : 0 < a1 + a3 + a5
                      swap
                      · omega
                      have f15 := pair_fact E (i := 5) (j := 1) rfl rfl c11 c12
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f15
                      by_cases c16 : 0 < a5
                      swap
                      · omega
                      by_cases c17 : 0 < b3
                      swap
                      · omega
                      by_cases c18 : a1 + a3 < b1 + b3
                      swap
                      · omega
                      by_cases c19 : b1 < a1 + a3 + a5
                      swap
                      · -- branch
                        by_cases c20 : 0 < a9
                        swap
                        · omega
                        by_cases c21 : 0 < b5
                        swap
                        · omega
                        by_cases c22 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                        swap
                        · omega
                        by_cases c23 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                        swap
                        · omega
                        have f24 := pair_fact E (i := 9) (j := 5) rfl rfl c20 c21
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f24
                        omega
                      have f25 := pair_fact E (i := 5) (j := 3) rfl rfl c16 c17
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f25
                      by_cases c26 : 0 < a5
                      swap
                      · omega
                      by_cases c27 : 0 < b9
                      swap
                      · -- branch
                        by_cases c28 : 0 < a9
                        swap
                        · omega
                        by_cases c29 : 0 < b5
                        swap
                        · omega
                        by_cases c30 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                        swap
                        · omega
                        by_cases c31 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                        swap
                        · omega
                        have f32 := pair_fact E (i := 9) (j := 5) rfl rfl c28 c29
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f32
                        omega
                      by_cases c33 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                      swap
                      · omega
                      by_cases c34 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                      swap
                      · -- branch
                        by_cases c35 : 0 < a9
                        swap
                        · omega
                        by_cases c36 : 0 < b1
                        swap
                        · omega
                        by_cases c37 : a1 + a3 + a5 + a7 < 0 + b1
                        swap
                        · -- branch
                          by_cases c38 : 0 < a9
                          swap
                          · omega
                          by_cases c39 : 0 < b3
                          swap
                          · omega
                          by_cases c40 : a1 + a3 + a5 + a7 < b1 + b3
                          swap
                          · -- branch
                            by_cases c41 : 0 < a9
                            swap
                            · omega
                            by_cases c42 : 0 < b9
                            swap
                            · omega
                            by_cases c43 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                            swap
                            · omega
                            by_cases c44 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                            swap
                            · omega
                            have f45 := pair_fact E (i := 9) (j := 9) rfl rfl c41 c42
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f45
                            by_cases c46 : 0 < a5
                            swap
                            · omega
                            by_cases c47 : 0 < b7
                            swap
                            · -- branch
                              by_cases c48 : 0 < a7
                              swap
                              · omega
                              by_cases c49 : 0 < b5
                              swap
                              · omega
                              by_cases c50 : a1 + a3 + a5 < b1 + b3 + b5
                              swap
                              · omega
                              by_cases c51 : b1 + b3 < a1 + a3 + a5 + a7
                              swap
                              · omega
                              have f52 := pair_fact E (i := 7) (j := 5) rfl rfl c48 c49
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f52
                              omega
                            by_cases c53 : a1 + a3 < b1 + b3 + b5 + b7
                            swap
                            · omega
                            by_cases c54 : b1 + b3 + b5 < a1 + a3 + a5
                            swap
                            · -- branch
                              by_cases c55 : 0 < a7
                              swap
                              · -- branch
                                by_cases c56 : 0 < a9
                                swap
                                · omega
                                by_cases c57 : 0 < b5
                                swap
                                · omega
                                by_cases c58 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                                swap
                                · omega
                                by_cases c59 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                                swap
                                · omega
                                have f60 := pair_fact E (i := 9) (j := 5) rfl rfl c56 c57
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f60
                                omega
                              by_cases c61 : 0 < b5
                              swap
                              · omega
                              by_cases c62 : a1 + a3 + a5 < b1 + b3 + b5
                              swap
                              · omega
                              by_cases c63 : b1 + b3 < a1 + a3 + a5 + a7
                              swap
                              · omega
                              have f64 := pair_fact E (i := 7) (j := 5) rfl rfl c55 c61
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f64
                              omega
                            have f65 := pair_fact E (i := 5) (j := 7) rfl rfl c46 c47
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f65
                            omega
                          by_cases c66 : b1 < a1 + a3 + a5 + a7 + a9
                          swap
                          · omega
                          have f67 := pair_fact E (i := 9) (j := 3) rfl rfl c38 c39
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f67
                          omega
                        by_cases c68 : 0 < a1 + a3 + a5 + a7 + a9
                        swap
                        · omega
                        have f69 := pair_fact E (i := 9) (j := 1) rfl rfl c35 c36
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f69
                        omega
                      have f70 := pair_fact E (i := 5) (j := 9) rfl rfl c26 c27
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f70
                      omega
                    by_cases c71 : 0 < b9
                    swap
                    · omega
                    by_cases c72 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c73 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · omega
                    have f74 := pair_fact E (i := 3) (j := 9) rfl rfl c10 c71
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f74
                    omega
                  by_cases c75 : 0 < b7
                  swap
                  · omega
                  by_cases c76 : a1 < b1 + b3 + b5 + b7
                  swap
                  · omega
                  by_cases c77 : b1 + b3 + b5 < a1 + a3
                  swap
                  · omega
                  have f78 := pair_fact E (i := 3) (j := 7) rfl rfl c9 c75
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f78
                  omega
                by_cases c79 : 0 < b5
                swap
                · omega
                by_cases c80 : a1 < b1 + b3 + b5
                swap
                · omega
                by_cases c81 : b1 + b3 < a1 + a3
                swap
                · omega
                have f82 := pair_fact E (i := 3) (j := 5) rfl rfl c8 c79
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f82
                omega
              by_cases c83 : 0 < b3
              swap
              · omega
              by_cases c84 : a1 < b1 + b3
              swap
              · omega
              by_cases c85 : b1 < a1 + a3
              swap
              · omega
              have f86 := pair_fact E (i := 3) (j := 3) rfl rfl c7 c83
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f86
              omega
            by_cases c87 : 0 < b1
            swap
            · omega
            by_cases c88 : a1 < 0 + b1
            swap
            · omega
            by_cases c89 : 0 < a1 + a3
            swap
            · omega
            have f90 := pair_fact E (i := 3) (j := 1) rfl rfl c6 c87
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f90
            by_cases c91 : 0 < a3
            swap
            · omega
            by_cases c92 : 0 < b3
            swap
            · -- branch
              by_cases c93 : 0 < a3
              swap
              · omega
              by_cases c94 : 0 < b5
              swap
              · -- branch
                by_cases c95 : 0 < a5
                swap
                · omega
                by_cases c96 : 0 < b9
                swap
                · omega
                by_cases c97 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                swap
                · omega
                by_cases c98 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                swap
                · omega
                have f99 := pair_fact E (i := 5) (j := 9) rfl rfl c95 c96
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f99
                omega
              by_cases c100 : a1 < b1 + b3 + b5
              swap
              · omega
              by_cases c101 : b1 + b3 < a1 + a3
              swap
              · -- branch
                by_cases c102 : 0 < a3
                swap
                · omega
                by_cases c103 : 0 < b7
                swap
                · -- branch
                  by_cases c104 : 0 < a7
                  swap
                  · omega
                  by_cases c105 : 0 < b1
                  swap
                  · omega
                  by_cases c106 : a1 + a3 + a5 < 0 + b1
                  swap
                  · -- branch
                    by_cases c107 : 0 < a7
                    swap
                    · omega
                    by_cases c108 : 0 < b3
                    swap
                    · -- branch
                      by_cases c109 : 0 < a7
                      swap
                      · omega
                      by_cases c110 : 0 < b7
                      swap
                      · -- branch
                        by_cases c111 : 0 < a3
                        swap
                        · omega
                        by_cases c112 : 0 < b9
                        swap
                        · -- branch
                          by_cases c113 : 0 < a9
                          swap
                          · omega
                          by_cases c114 : 0 < b5
                          swap
                          · omega
                          by_cases c115 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                          swap
                          · omega
                          by_cases c116 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                          swap
                          · omega
                          have f117 := pair_fact E (i := 9) (j := 5) rfl rfl c113 c114
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f117
                          omega
                        by_cases c118 : a1 < b1 + b3 + b5 + b7 + b9
                        swap
                        · omega
                        by_cases c119 : b1 + b3 + b5 + b7 < a1 + a3
                        swap
                        · -- branch
                          by_cases c120 : 0 < a5
                          swap
                          · omega
                          by_cases c121 : 0 < b1
                          swap
                          · omega
                          by_cases c122 : a1 + a3 < 0 + b1
                          swap
                          · -- branch
                            by_cases c123 : 0 < a5
                            swap
                            · omega
                            by_cases c124 : 0 < b3
                            swap
                            · -- branch
                              by_cases c125 : 0 < a5
                              swap
                              · omega
                              by_cases c126 : 0 < b5
                              swap
                              · omega
                              by_cases c127 : a1 + a3 < b1 + b3 + b5
                              swap
                              · omega
                              by_cases c128 : b1 + b3 < a1 + a3 + a5
                              swap
                              · omega
                              have f129 := pair_fact E (i := 5) (j := 5) rfl rfl c125 c126
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f129
                              by_cases c130 : 0 < a5
                              swap
                              · omega
                              by_cases c131 : 0 < b7
                              swap
                              · -- branch
                                by_cases c132 : 0 < a5
                                swap
                                · omega
                                by_cases c133 : 0 < b9
                                swap
                                · omega
                                by_cases c134 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                                swap
                                · omega
                                by_cases c135 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                                swap
                                · -- branch
                                  by_cases c136 : 0 < a7
                                  swap
                                  · omega
                                  by_cases c137 : 0 < b5
                                  swap
                                  · omega
                                  by_cases c138 : a1 + a3 + a5 < b1 + b3 + b5
                                  swap
                                  · omega
                                  by_cases c139 : b1 + b3 < a1 + a3 + a5 + a7
                                  swap
                                  · omega
                                  have f140 := pair_fact E (i := 7) (j := 5) rfl rfl c136 c137
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f140
                                  by_cases c141 : 0 < a9
                                  swap
                                  · omega
                                  by_cases c142 : 0 < b9
                                  swap
                                  · omega
                                  by_cases c143 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                                  swap
                                  · omega
                                  by_cases c144 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                                  swap
                                  · omega
                                  have f145 := pair_fact E (i := 9) (j := 9) rfl rfl c141 c142
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f145
                                  omega
                                have f146 := pair_fact E (i := 5) (j := 9) rfl rfl c132 c133
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f146
                                omega
                              by_cases c147 : a1 + a3 < b1 + b3 + b5 + b7
                              swap
                              · omega
                              by_cases c148 : b1 + b3 + b5 < a1 + a3 + a5
                              swap
                              · omega
                              have f149 := pair_fact E (i := 5) (j := 7) rfl rfl c130 c131
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f149
                              omega
                            by_cases c150 : a1 + a3 < b1 + b3
                            swap
                            · omega
                            by_cases c151 : b1 < a1 + a3 + a5
                            swap
                            · omega
                            have f152 := pair_fact E (i := 5) (j := 3) rfl rfl c123 c124
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f152
                            omega
                          by_cases c153 : 0 < a1 + a3 + a5
                          swap
                          · omega
                          have f154 := pair_fact E (i := 5) (j := 1) rfl rfl c120 c121
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f154
                          omega
                        have f155 := pair_fact E (i := 3) (j := 9) rfl rfl c111 c112
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f155
                        omega
                      by_cases c156 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                      swap
                      · omega
                      by_cases c157 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                      swap
                      · omega
                      have f158 := pair_fact E (i := 7) (j := 7) rfl rfl c109 c110
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f158
                      omega
                    by_cases c159 : a1 + a3 + a5 < b1 + b3
                    swap
                    · omega
                    by_cases c160 : b1 < a1 + a3 + a5 + a7
                    swap
                    · omega
                    have f161 := pair_fact E (i := 7) (j := 3) rfl rfl c107 c108
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f161
                    omega
                  by_cases c162 : 0 < a1 + a3 + a5 + a7
                  swap
                  · omega
                  have f163 := pair_fact E (i := 7) (j := 1) rfl rfl c104 c105
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f163
                  omega
                by_cases c164 : a1 < b1 + b3 + b5 + b7
                swap
                · omega
                by_cases c165 : b1 + b3 + b5 < a1 + a3
                swap
                · -- branch
                  by_cases c166 : 0 < a5
                  swap
                  · omega
                  by_cases c167 : 0 < b1
                  swap
                  · omega
                  by_cases c168 : a1 + a3 < 0 + b1
                  swap
                  · -- branch
                    by_cases c169 : 0 < a5
                    swap
                    · omega
                    by_cases c170 : 0 < b3
                    swap
                    · -- branch
                      by_cases c171 : 0 < a5
                      swap
                      · omega
                      by_cases c172 : 0 < b5
                      swap
                      · omega
                      by_cases c173 : a1 + a3 < b1 + b3 + b5
                      swap
                      · omega
                      by_cases c174 : b1 + b3 < a1 + a3 + a5
                      swap
                      · omega
                      have f175 := pair_fact E (i := 5) (j := 5) rfl rfl c171 c172
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f175
                      by_cases c176 : 0 < a3
                      swap
                      · omega
                      by_cases c177 : 0 < b9
                      swap
                      · -- branch
                        by_cases c178 : 0 < a9
                        swap
                        · omega
                        by_cases c179 : 0 < b5
                        swap
                        · omega
                        by_cases c180 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                        swap
                        · omega
                        by_cases c181 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                        swap
                        · omega
                        have f182 := pair_fact E (i := 9) (j := 5) rfl rfl c178 c179
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
                        by_cases c185 : 0 < a5
                        swap
                        · omega
                        by_cases c186 : 0 < b9
                        swap
                        · omega
                        by_cases c187 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                        swap
                        · omega
                        by_cases c188 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                        swap
                        · -- branch
                          by_cases c189 : 0 < a9
                          swap
                          · omega
                          by_cases c190 : 0 < b1
                          swap
                          · omega
                          by_cases c191 : a1 + a3 + a5 + a7 < 0 + b1
                          swap
                          · -- branch
                            by_cases c192 : 0 < a9
                            swap
                            · omega
                            by_cases c193 : 0 < b3
                            swap
                            · -- branch
                              by_cases c194 : 0 < a9
                              swap
                              · omega
                              by_cases c195 : 0 < b5
                              swap
                              · omega
                              by_cases c196 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                              swap
                              · -- branch
                                by_cases c197 : 0 < a9
                                swap
                                · omega
                                by_cases c198 : 0 < b9
                                swap
                                · omega
                                by_cases c199 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                                swap
                                · omega
                                by_cases c200 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                                swap
                                · omega
                                have f201 := pair_fact E (i := 9) (j := 9) rfl rfl c197 c198
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f201
                                by_cases c202 : 0 < a5
                                swap
                                · omega
                                by_cases c203 : 0 < b7
                                swap
                                · omega
                                by_cases c204 : a1 + a3 < b1 + b3 + b5 + b7
                                swap
                                · omega
                                by_cases c205 : b1 + b3 + b5 < a1 + a3 + a5
                                swap
                                · -- branch
                                  by_cases c206 : 0 < a7
                                  swap
                                  · omega
                                  by_cases c207 : 0 < b5
                                  swap
                                  · omega
                                  by_cases c208 : a1 + a3 + a5 < b1 + b3 + b5
                                  swap
                                  · omega
                                  by_cases c209 : b1 + b3 < a1 + a3 + a5 + a7
                                  swap
                                  · omega
                                  have f210 := pair_fact E (i := 7) (j := 5) rfl rfl c206 c207
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f210
                                  omega
                                have f211 := pair_fact E (i := 5) (j := 7) rfl rfl c202 c203
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f211
                                omega
                              by_cases c212 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                              swap
                              · omega
                              have f213 := pair_fact E (i := 9) (j := 5) rfl rfl c194 c195
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f213
                              omega
                            by_cases c214 : a1 + a3 + a5 + a7 < b1 + b3
                            swap
                            · omega
                            by_cases c215 : b1 < a1 + a3 + a5 + a7 + a9
                            swap
                            · omega
                            have f216 := pair_fact E (i := 9) (j := 3) rfl rfl c192 c193
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f216
                            omega
                          by_cases c217 : 0 < a1 + a3 + a5 + a7 + a9
                          swap
                          · omega
                          have f218 := pair_fact E (i := 9) (j := 1) rfl rfl c189 c190
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f218
                          omega
                        have f219 := pair_fact E (i := 5) (j := 9) rfl rfl c185 c186
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f219
                        omega
                      have f220 := pair_fact E (i := 3) (j := 9) rfl rfl c176 c177
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f220
                      omega
                    by_cases c221 : a1 + a3 < b1 + b3
                    swap
                    · omega
                    by_cases c222 : b1 < a1 + a3 + a5
                    swap
                    · omega
                    have f223 := pair_fact E (i := 5) (j := 3) rfl rfl c169 c170
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f223
                    omega
                  by_cases c224 : 0 < a1 + a3 + a5
                  swap
                  · omega
                  have f225 := pair_fact E (i := 5) (j := 1) rfl rfl c166 c167
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f225
                  omega
                have f226 := pair_fact E (i := 3) (j := 7) rfl rfl c102 c103
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f226
                omega
              have f227 := pair_fact E (i := 3) (j := 5) rfl rfl c93 c94
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f227
              omega
            by_cases c228 : a1 < b1 + b3
            swap
            · omega
            by_cases c229 : b1 < a1 + a3
            swap
            · -- branch
              by_cases c230 : 0 < a5
              swap
              · omega
              by_cases c231 : 0 < b1
              swap
              · omega
              by_cases c232 : a1 + a3 < 0 + b1
              swap
              · omega
              by_cases c233 : 0 < a1 + a3 + a5
              swap
              · omega
              have f234 := pair_fact E (i := 5) (j := 1) rfl rfl c230 c231
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f234
              by_cases c235 : 0 < a3
              swap
              · omega
              by_cases c236 : 0 < b5
              swap
              · -- branch
                by_cases c237 : 0 < a5
                swap
                · omega
                by_cases c238 : 0 < b7
                swap
                · omega
                by_cases c239 : a1 + a3 < b1 + b3 + b5 + b7
                swap
                · omega
                by_cases c240 : b1 + b3 + b5 < a1 + a3 + a5
                swap
                · omega
                have f241 := pair_fact E (i := 5) (j := 7) rfl rfl c237 c238
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f241
                omega
              by_cases c242 : a1 < b1 + b3 + b5
              swap
              · omega
              by_cases c243 : b1 + b3 < a1 + a3
              swap
              · -- branch
                by_cases c244 : 0 < a5
                swap
                · omega
                by_cases c245 : 0 < b5
                swap
                · omega
                by_cases c246 : a1 + a3 < b1 + b3 + b5
                swap
                · omega
                by_cases c247 : b1 + b3 < a1 + a3 + a5
                swap
                · -- branch
                  by_cases c248 : 0 < a9
                  swap
                  · omega
                  by_cases c249 : 0 < b5
                  swap
                  · omega
                  by_cases c250 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c251 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                  swap
                  · omega
                  have f252 := pair_fact E (i := 9) (j := 5) rfl rfl c248 c249
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f252
                  omega
                have f253 := pair_fact E (i := 5) (j := 5) rfl rfl c244 c245
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f253
                omega
              have f254 := pair_fact E (i := 3) (j := 5) rfl rfl c235 c236
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f254
              omega
            have f255 := pair_fact E (i := 3) (j := 3) rfl rfl c91 c92
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f255
            omega
          by_cases c256 : 0 < b9
          swap
          · omega
          by_cases c257 : 0 < b1 + b3 + b5 + b7 + b9
          swap
          · omega
          by_cases c258 : b1 + b3 + b5 + b7 < 0 + a1
          swap
          · omega
          have f259 := pair_fact E (i := 1) (j := 9) rfl rfl c5 c256
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f259
          omega
        by_cases c260 : 0 < b7
        swap
        · omega
        by_cases c261 : 0 < b1 + b3 + b5 + b7
        swap
        · omega
        by_cases c262 : b1 + b3 + b5 < 0 + a1
        swap
        · omega
        have f263 := pair_fact E (i := 1) (j := 7) rfl rfl c4 c260
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f263
        omega
      by_cases c264 : 0 < b5
      swap
      · omega
      by_cases c265 : 0 < b1 + b3 + b5
      swap
      · omega
      by_cases c266 : b1 + b3 < 0 + a1
      swap
      · omega
      have f267 := pair_fact E (i := 1) (j := 5) rfl rfl c3 c264
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f267
      omega
    by_cases c268 : 0 < b3
    swap
    · omega
    by_cases c269 : 0 < b1 + b3
    swap
    · omega
    by_cases c270 : b1 < 0 + a1
    swap
    · omega
    have f271 := pair_fact E (i := 1) (j := 3) rfl rfl c2 c268
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f271
    omega
  by_cases c272 : 0 < b1
  swap
  · -- branch
    by_cases c273 : 0 < a1
    swap
    · omega
    by_cases c274 : 0 < b3
    swap
    · -- branch
      by_cases c275 : 0 < a1
      swap
      · omega
      by_cases c276 : 0 < b5
      swap
      · omega
      by_cases c277 : 0 < b1 + b3 + b5
      swap
      · omega
      by_cases c278 : b1 + b3 < 0 + a1
      swap
      · omega
      have f279 := pair_fact E (i := 1) (j := 5) rfl rfl c275 c276
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f279
      by_cases c280 : 0 < a3
      swap
      · omega
      by_cases c281 : 0 < b1
      swap
      · -- branch
        by_cases c282 : 0 < a3
        swap
        · omega
        by_cases c283 : 0 < b3
        swap
        · -- branch
          by_cases c284 : 0 < a1
          swap
          · omega
          by_cases c285 : 0 < b7
          swap
          · -- branch
            by_cases c286 : 0 < a1
            swap
            · omega
            by_cases c287 : 0 < b9
            swap
            · omega
            by_cases c288 : 0 < b1 + b3 + b5 + b7 + b9
            swap
            · omega
            by_cases c289 : b1 + b3 + b5 + b7 < 0 + a1
            swap
            · -- branch
              by_cases c290 : 0 < a3
              swap
              · omega
              by_cases c291 : 0 < b5
              swap
              · omega
              by_cases c292 : a1 < b1 + b3 + b5
              swap
              · omega
              by_cases c293 : b1 + b3 < a1 + a3
              swap
              · omega
              have f294 := pair_fact E (i := 3) (j := 5) rfl rfl c290 c291
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f294
              by_cases c295 : 0 < a3
              swap
              · omega
              by_cases c296 : 0 < b7
              swap
              · -- branch
                by_cases c297 : 0 < a3
                swap
                · omega
                by_cases c298 : 0 < b9
                swap
                · omega
                by_cases c299 : a1 < b1 + b3 + b5 + b7 + b9
                swap
                · omega
                by_cases c300 : b1 + b3 + b5 + b7 < a1 + a3
                swap
                · -- branch
                  by_cases c301 : 0 < a7
                  swap
                  · omega
                  by_cases c302 : 0 < b1
                  swap
                  · -- branch
                    by_cases c303 : 0 < a7
                    swap
                    · omega
                    by_cases c304 : 0 < b3
                    swap
                    · -- branch
                      by_cases c305 : 0 < a7
                      swap
                      · omega
                      by_cases c306 : 0 < b7
                      swap
                      · -- branch
                        by_cases c307 : 0 < a5
                        swap
                        · -- branch
                          by_cases c308 : 0 < a5
                          swap
                          · -- branch
                            by_cases c309 : 0 < a5
                            swap
                            · -- branch
                              by_cases c310 : 0 < a5
                              swap
                              · -- branch
                                by_cases c311 : 0 < a5
                                swap
                                · -- branch
                                  by_cases c312 : 0 < a7
                                  swap
                                  · omega
                                  by_cases c313 : 0 < b5
                                  swap
                                  · omega
                                  by_cases c314 : a1 + a3 + a5 < b1 + b3 + b5
                                  swap
                                  · omega
                                  by_cases c315 : b1 + b3 < a1 + a3 + a5 + a7
                                  swap
                                  · omega
                                  have f316 := pair_fact E (i := 7) (j := 5) rfl rfl c312 c313
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f316
                                  by_cases c317 : 0 < a9
                                  swap
                                  · omega
                                  by_cases c318 : 0 < b9
                                  swap
                                  · omega
                                  by_cases c319 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                                  swap
                                  · omega
                                  by_cases c320 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                                  swap
                                  · omega
                                  have f321 := pair_fact E (i := 9) (j := 9) rfl rfl c317 c318
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f321
                                  omega
                                by_cases c322 : 0 < b9
                                swap
                                · omega
                                by_cases c323 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                                swap
                                · omega
                                by_cases c324 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                                swap
                                · omega
                                have f325 := pair_fact E (i := 5) (j := 9) rfl rfl c311 c322
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f325
                                omega
                              by_cases c326 : 0 < b7
                              swap
                              · omega
                              by_cases c327 : a1 + a3 < b1 + b3 + b5 + b7
                              swap
                              · omega
                              by_cases c328 : b1 + b3 + b5 < a1 + a3 + a5
                              swap
                              · omega
                              have f329 := pair_fact E (i := 5) (j := 7) rfl rfl c310 c326
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f329
                              omega
                            by_cases c330 : 0 < b5
                            swap
                            · omega
                            by_cases c331 : a1 + a3 < b1 + b3 + b5
                            swap
                            · omega
                            by_cases c332 : b1 + b3 < a1 + a3 + a5
                            swap
                            · omega
                            have f333 := pair_fact E (i := 5) (j := 5) rfl rfl c309 c330
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f333
                            omega
                          by_cases c334 : 0 < b3
                          swap
                          · omega
                          by_cases c335 : a1 + a3 < b1 + b3
                          swap
                          · omega
                          by_cases c336 : b1 < a1 + a3 + a5
                          swap
                          · omega
                          have f337 := pair_fact E (i := 5) (j := 3) rfl rfl c308 c334
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f337
                          omega
                        by_cases c338 : 0 < b1
                        swap
                        · -- branch
                          by_cases c339 : 0 < a5
                          swap
                          · omega
                          by_cases c340 : 0 < b3
                          swap
                          · -- branch
                            by_cases c341 : 0 < a5
                            swap
                            · omega
                            by_cases c342 : 0 < b7
                            swap
                            · -- branch
                              by_cases c343 : 0 < a5
                              swap
                              · omega
                              by_cases c344 : 0 < b9
                              swap
                              · omega
                              by_cases c345 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                              swap
                              · omega
                              by_cases c346 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                              swap
                              · -- branch
                                by_cases c347 : 0 < a5
                                swap
                                · omega
                                by_cases c348 : 0 < b5
                                swap
                                · omega
                                by_cases c349 : a1 + a3 < b1 + b3 + b5
                                swap
                                · omega
                                by_cases c350 : b1 + b3 < a1 + a3 + a5
                                swap
                                · omega
                                have f351 := pair_fact E (i := 5) (j := 5) rfl rfl c347 c348
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f351
                                by_cases c352 : 0 < a7
                                swap
                                · omega
                                by_cases c353 : 0 < b5
                                swap
                                · omega
                                by_cases c354 : a1 + a3 + a5 < b1 + b3 + b5
                                swap
                                · omega
                                by_cases c355 : b1 + b3 < a1 + a3 + a5 + a7
                                swap
                                · omega
                                have f356 := pair_fact E (i := 7) (j := 5) rfl rfl c352 c353
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f356
                                by_cases c357 : 0 < a7
                                swap
                                · omega
                                by_cases c358 : 0 < b9
                                swap
                                · omega
                                by_cases c359 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
                                swap
                                · omega
                                by_cases c360 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
                                swap
                                · omega
                                have f361 := pair_fact E (i := 7) (j := 9) rfl rfl c357 c358
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f361
                                omega
                              have f362 := pair_fact E (i := 5) (j := 9) rfl rfl c343 c344
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f362
                              omega
                            by_cases c363 : a1 + a3 < b1 + b3 + b5 + b7
                            swap
                            · omega
                            by_cases c364 : b1 + b3 + b5 < a1 + a3 + a5
                            swap
                            · omega
                            have f365 := pair_fact E (i := 5) (j := 7) rfl rfl c341 c342
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f365
                            omega
                          by_cases c366 : a1 + a3 < b1 + b3
                          swap
                          · omega
                          by_cases c367 : b1 < a1 + a3 + a5
                          swap
                          · omega
                          have f368 := pair_fact E (i := 5) (j := 3) rfl rfl c339 c340
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f368
                          omega
                        by_cases c369 : a1 + a3 < 0 + b1
                        swap
                        · omega
                        by_cases c370 : 0 < a1 + a3 + a5
                        swap
                        · omega
                        have f371 := pair_fact E (i := 5) (j := 1) rfl rfl c307 c338
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f371
                        omega
                      by_cases c372 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                      swap
                      · omega
                      by_cases c373 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                      swap
                      · omega
                      have f374 := pair_fact E (i := 7) (j := 7) rfl rfl c305 c306
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f374
                      omega
                    by_cases c375 : a1 + a3 + a5 < b1 + b3
                    swap
                    · omega
                    by_cases c376 : b1 < a1 + a3 + a5 + a7
                    swap
                    · omega
                    have f377 := pair_fact E (i := 7) (j := 3) rfl rfl c303 c304
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f377
                    omega
                  by_cases c378 : a1 + a3 + a5 < 0 + b1
                  swap
                  · omega
                  by_cases c379 : 0 < a1 + a3 + a5 + a7
                  swap
                  · omega
                  have f380 := pair_fact E (i := 7) (j := 1) rfl rfl c301 c302
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f380
                  omega
                have f381 := pair_fact E (i := 3) (j := 9) rfl rfl c297 c298
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f381
                omega
              by_cases c382 : a1 < b1 + b3 + b5 + b7
              swap
              · omega
              by_cases c383 : b1 + b3 + b5 < a1 + a3
              swap
              · omega
              have f384 := pair_fact E (i := 3) (j := 7) rfl rfl c295 c296
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f384
              omega
            have f385 := pair_fact E (i := 1) (j := 9) rfl rfl c286 c287
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f385
            omega
          by_cases c386 : 0 < b1 + b3 + b5 + b7
          swap
          · omega
          by_cases c387 : b1 + b3 + b5 < 0 + a1
          swap
          · -- branch
            by_cases c388 : 0 < a1
            swap
            · omega
            by_cases c389 : 0 < b9
            swap
            · -- branch
              by_cases c390 : 0 < a9
              swap
              · omega
              by_cases c391 : 0 < b5
              swap
              · omega
              by_cases c392 : a1 + a3 + a5 + a7 < b1 + b3 + b5
              swap
              · omega
              by_cases c393 : b1 + b3 < a1 + a3 + a5 + a7 + a9
              swap
              · omega
              have f394 := pair_fact E (i := 9) (j := 5) rfl rfl c390 c391
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f394
              omega
            by_cases c395 : 0 < b1 + b3 + b5 + b7 + b9
            swap
            · omega
            by_cases c396 : b1 + b3 + b5 + b7 < 0 + a1
            swap
            · -- branch
              by_cases c397 : 0 < a3
              swap
              · omega
              by_cases c398 : 0 < b9
              swap
              · omega
              by_cases c399 : a1 < b1 + b3 + b5 + b7 + b9
              swap
              · omega
              by_cases c400 : b1 + b3 + b5 + b7 < a1 + a3
              swap
              · -- branch
                by_cases c401 : 0 < a3
                swap
                · omega
                by_cases c402 : 0 < b5
                swap
                · omega
                by_cases c403 : a1 < b1 + b3 + b5
                swap
                · -- branch
                  by_cases c404 : 0 < a5
                  swap
                  · omega
                  by_cases c405 : 0 < b9
                  swap
                  · omega
                  by_cases c406 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                  swap
                  · omega
                  by_cases c407 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                  swap
                  · omega
                  have f408 := pair_fact E (i := 5) (j := 9) rfl rfl c404 c405
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f408
                  omega
                by_cases c409 : b1 + b3 < a1 + a3
                swap
                · omega
                have f410 := pair_fact E (i := 3) (j := 5) rfl rfl c401 c402
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f410
                by_cases c411 : 0 < a3
                swap
                · omega
                by_cases c412 : 0 < b7
                swap
                · omega
                by_cases c413 : a1 < b1 + b3 + b5 + b7
                swap
                · omega
                by_cases c414 : b1 + b3 + b5 < a1 + a3
                swap
                · -- branch
                  by_cases c415 : 0 < a9
                  swap
                  · omega
                  by_cases c416 : 0 < b1
                  swap
                  · -- branch
                    by_cases c417 : 0 < a9
                    swap
                    · omega
                    by_cases c418 : 0 < b3
                    swap
                    · -- branch
                      by_cases c419 : 0 < a9
                      swap
                      · omega
                      by_cases c420 : 0 < b5
                      swap
                      · omega
                      by_cases c421 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                      swap
                      · -- branch
                        by_cases c422 : 0 < a5
                        swap
                        · omega
                        by_cases c423 : 0 < b1
                        swap
                        · -- branch
                          by_cases c424 : 0 < a5
                          swap
                          · omega
                          by_cases c425 : 0 < b3
                          swap
                          · -- branch
                            by_cases c426 : 0 < a5
                            swap
                            · omega
                            by_cases c427 : 0 < b9
                            swap
                            · omega
                            by_cases c428 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                            swap
                            · omega
                            by_cases c429 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                            swap
                            · -- branch
                              by_cases c430 : 0 < a9
                              swap
                              · omega
                              by_cases c431 : 0 < b9
                              swap
                              · omega
                              by_cases c432 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                              swap
                              · omega
                              by_cases c433 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                              swap
                              · omega
                              have f434 := pair_fact E (i := 9) (j := 9) rfl rfl c430 c431
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f434
                              by_cases c435 : 0 < a5
                              swap
                              · omega
                              by_cases c436 : 0 < b7
                              swap
                              · omega
                              by_cases c437 : a1 + a3 < b1 + b3 + b5 + b7
                              swap
                              · omega
                              by_cases c438 : b1 + b3 + b5 < a1 + a3 + a5
                              swap
                              · -- branch
                                by_cases c439 : 0 < a7
                                swap
                                · omega
                                by_cases c440 : 0 < b5
                                swap
                                · omega
                                by_cases c441 : a1 + a3 + a5 < b1 + b3 + b5
                                swap
                                · omega
                                by_cases c442 : b1 + b3 < a1 + a3 + a5 + a7
                                swap
                                · omega
                                have f443 := pair_fact E (i := 7) (j := 5) rfl rfl c439 c440
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f443
                                omega
                              have f444 := pair_fact E (i := 5) (j := 7) rfl rfl c435 c436
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f444
                              omega
                            have f445 := pair_fact E (i := 5) (j := 9) rfl rfl c426 c427
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f445
                            omega
                          by_cases c446 : a1 + a3 < b1 + b3
                          swap
                          · omega
                          by_cases c447 : b1 < a1 + a3 + a5
                          swap
                          · omega
                          have f448 := pair_fact E (i := 5) (j := 3) rfl rfl c424 c425
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f448
                          omega
                        by_cases c449 : a1 + a3 < 0 + b1
                        swap
                        · omega
                        by_cases c450 : 0 < a1 + a3 + a5
                        swap
                        · omega
                        have f451 := pair_fact E (i := 5) (j := 1) rfl rfl c422 c423
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f451
                        omega
                      by_cases c452 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                      swap
                      · omega
                      have f453 := pair_fact E (i := 9) (j := 5) rfl rfl c419 c420
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f453
                      omega
                    by_cases c454 : a1 + a3 + a5 + a7 < b1 + b3
                    swap
                    · omega
                    by_cases c455 : b1 < a1 + a3 + a5 + a7 + a9
                    swap
                    · omega
                    have f456 := pair_fact E (i := 9) (j := 3) rfl rfl c417 c418
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f456
                    omega
                  by_cases c457 : a1 + a3 + a5 + a7 < 0 + b1
                  swap
                  · omega
                  by_cases c458 : 0 < a1 + a3 + a5 + a7 + a9
                  swap
                  · omega
                  have f459 := pair_fact E (i := 9) (j := 1) rfl rfl c415 c416
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f459
                  omega
                have f460 := pair_fact E (i := 3) (j := 7) rfl rfl c411 c412
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f460
                by_cases c461 : 0 < a5
                swap
                · omega
                by_cases c462 : 0 < b9
                swap
                · omega
                by_cases c463 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                swap
                · omega
                by_cases c464 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                swap
                · omega
                have f465 := pair_fact E (i := 5) (j := 9) rfl rfl c461 c462
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f465
                omega
              have f466 := pair_fact E (i := 3) (j := 9) rfl rfl c397 c398
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f466
              omega
            have f467 := pair_fact E (i := 1) (j := 9) rfl rfl c388 c389
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f467
            omega
          have f468 := pair_fact E (i := 1) (j := 7) rfl rfl c284 c285
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f468
          omega
        by_cases c469 : a1 < b1 + b3
        swap
        · omega
        by_cases c470 : b1 < a1 + a3
        swap
        · omega
        have f471 := pair_fact E (i := 3) (j := 3) rfl rfl c282 c283
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f471
        omega
      by_cases c472 : a1 < 0 + b1
      swap
      · omega
      by_cases c473 : 0 < a1 + a3
      swap
      · omega
      have f474 := pair_fact E (i := 3) (j := 1) rfl rfl c280 c281
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f474
      omega
    by_cases c475 : 0 < b1 + b3
    swap
    · omega
    by_cases c476 : b1 < 0 + a1
    swap
    · omega
    have f477 := pair_fact E (i := 1) (j := 3) rfl rfl c273 c274
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f477
    by_cases c478 : 0 < a1
    swap
    · omega
    by_cases c479 : 0 < b7
    swap
    · -- branch
      by_cases c480 : 0 < a7
      swap
      · omega
      by_cases c481 : 0 < b1
      swap
      · -- branch
        by_cases c482 : 0 < a7
        swap
        · omega
        by_cases c483 : 0 < b3
        swap
        · omega
        by_cases c484 : a1 + a3 + a5 < b1 + b3
        swap
        · -- branch
          by_cases c485 : 0 < a7
          swap
          · omega
          by_cases c486 : 0 < b7
          swap
          · -- branch
            by_cases c487 : 0 < a1
            swap
            · omega
            by_cases c488 : 0 < b5
            swap
            · omega
            by_cases c489 : 0 < b1 + b3 + b5
            swap
            · omega
            by_cases c490 : b1 + b3 < 0 + a1
            swap
            · -- branch
              by_cases c491 : 0 < a3
              swap
              · -- branch
                by_cases c492 : 0 < a3
                swap
                · -- branch
                  by_cases c493 : 0 < a3
                  swap
                  · -- branch
                    by_cases c494 : 0 < a3
                    swap
                    · -- branch
                      by_cases c495 : 0 < a3
                      swap
                      · -- branch
                        by_cases c496 : 0 < a1
                        swap
                        · omega
                        by_cases c497 : 0 < b9
                        swap
                        · -- branch
                          by_cases c498 : 0 < a9
                          swap
                          · omega
                          by_cases c499 : 0 < b5
                          swap
                          · omega
                          by_cases c500 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                          swap
                          · omega
                          by_cases c501 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                          swap
                          · omega
                          have f502 := pair_fact E (i := 9) (j := 5) rfl rfl c498 c499
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f502
                          omega
                        by_cases c503 : 0 < b1 + b3 + b5 + b7 + b9
                        swap
                        · omega
                        by_cases c504 : b1 + b3 + b5 + b7 < 0 + a1
                        swap
                        · -- branch
                          by_cases c505 : 0 < a5
                          swap
                          · omega
                          by_cases c506 : 0 < b1
                          swap
                          · -- branch
                            by_cases c507 : 0 < a5
                            swap
                            · omega
                            by_cases c508 : 0 < b3
                            swap
                            · omega
                            by_cases c509 : a1 + a3 < b1 + b3
                            swap
                            · -- branch
                              by_cases c510 : 0 < a5
                              swap
                              · omega
                              by_cases c511 : 0 < b5
                              swap
                              · omega
                              by_cases c512 : a1 + a3 < b1 + b3 + b5
                              swap
                              · omega
                              by_cases c513 : b1 + b3 < a1 + a3 + a5
                              swap
                              · omega
                              have f514 := pair_fact E (i := 5) (j := 5) rfl rfl c510 c511
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f514
                              by_cases c515 : 0 < a5
                              swap
                              · omega
                              by_cases c516 : 0 < b7
                              swap
                              · -- branch
                                by_cases c517 : 0 < a5
                                swap
                                · omega
                                by_cases c518 : 0 < b9
                                swap
                                · omega
                                by_cases c519 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                                swap
                                · omega
                                by_cases c520 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                                swap
                                · -- branch
                                  by_cases c521 : 0 < a7
                                  swap
                                  · omega
                                  by_cases c522 : 0 < b5
                                  swap
                                  · omega
                                  by_cases c523 : a1 + a3 + a5 < b1 + b3 + b5
                                  swap
                                  · omega
                                  by_cases c524 : b1 + b3 < a1 + a3 + a5 + a7
                                  swap
                                  · omega
                                  have f525 := pair_fact E (i := 7) (j := 5) rfl rfl c521 c522
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f525
                                  by_cases c526 : 0 < a9
                                  swap
                                  · omega
                                  by_cases c527 : 0 < b9
                                  swap
                                  · omega
                                  by_cases c528 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                                  swap
                                  · omega
                                  by_cases c529 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                                  swap
                                  · omega
                                  have f530 := pair_fact E (i := 9) (j := 9) rfl rfl c526 c527
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f530
                                  omega
                                have f531 := pair_fact E (i := 5) (j := 9) rfl rfl c517 c518
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f531
                                omega
                              by_cases c532 : a1 + a3 < b1 + b3 + b5 + b7
                              swap
                              · omega
                              by_cases c533 : b1 + b3 + b5 < a1 + a3 + a5
                              swap
                              · omega
                              have f534 := pair_fact E (i := 5) (j := 7) rfl rfl c515 c516
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f534
                              omega
                            by_cases c535 : b1 < a1 + a3 + a5
                            swap
                            · omega
                            have f536 := pair_fact E (i := 5) (j := 3) rfl rfl c507 c508
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f536
                            omega
                          by_cases c537 : a1 + a3 < 0 + b1
                          swap
                          · omega
                          by_cases c538 : 0 < a1 + a3 + a5
                          swap
                          · omega
                          have f539 := pair_fact E (i := 5) (j := 1) rfl rfl c505 c506
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f539
                          omega
                        have f540 := pair_fact E (i := 1) (j := 9) rfl rfl c496 c497
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f540
                        omega
                      by_cases c541 : 0 < b9
                      swap
                      · omega
                      by_cases c542 : a1 < b1 + b3 + b5 + b7 + b9
                      swap
                      · omega
                      by_cases c543 : b1 + b3 + b5 + b7 < a1 + a3
                      swap
                      · omega
                      have f544 := pair_fact E (i := 3) (j := 9) rfl rfl c495 c541
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f544
                      omega
                    by_cases c545 : 0 < b7
                    swap
                    · omega
                    by_cases c546 : a1 < b1 + b3 + b5 + b7
                    swap
                    · omega
                    by_cases c547 : b1 + b3 + b5 < a1 + a3
                    swap
                    · omega
                    have f548 := pair_fact E (i := 3) (j := 7) rfl rfl c494 c545
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f548
                    omega
                  by_cases c549 : 0 < b5
                  swap
                  · omega
                  by_cases c550 : a1 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c551 : b1 + b3 < a1 + a3
                  swap
                  · omega
                  have f552 := pair_fact E (i := 3) (j := 5) rfl rfl c493 c549
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f552
                  omega
                by_cases c553 : 0 < b3
                swap
                · omega
                by_cases c554 : a1 < b1 + b3
                swap
                · omega
                by_cases c555 : b1 < a1 + a3
                swap
                · omega
                have f556 := pair_fact E (i := 3) (j := 3) rfl rfl c492 c553
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f556
                omega
              by_cases c557 : 0 < b1
              swap
              · omega
              by_cases c558 : a1 < 0 + b1
              swap
              · omega
              by_cases c559 : 0 < a1 + a3
              swap
              · omega
              have f560 := pair_fact E (i := 3) (j := 1) rfl rfl c491 c557
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f560
              omega
            have f561 := pair_fact E (i := 1) (j := 5) rfl rfl c487 c488
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f561
            by_cases c562 : 0 < a1
            swap
            · omega
            by_cases c563 : 0 < b9
            swap
            · omega
            by_cases c564 : 0 < b1 + b3 + b5 + b7 + b9
            swap
            · omega
            by_cases c565 : b1 + b3 + b5 + b7 < 0 + a1
            swap
            · -- branch
              by_cases c566 : 0 < a3
              swap
              · omega
              by_cases c567 : 0 < b1
              swap
              · -- branch
                by_cases c568 : 0 < a3
                swap
                · omega
                by_cases c569 : 0 < b3
                swap
                · omega
                by_cases c570 : a1 < b1 + b3
                swap
                · -- branch
                  by_cases c571 : 0 < a3
                  swap
                  · omega
                  by_cases c572 : 0 < b5
                  swap
                  · omega
                  by_cases c573 : a1 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c574 : b1 + b3 < a1 + a3
                  swap
                  · omega
                  have f575 := pair_fact E (i := 3) (j := 5) rfl rfl c571 c572
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f575
                  by_cases c576 : 0 < a3
                  swap
                  · omega
                  by_cases c577 : 0 < b7
                  swap
                  · -- branch
                    by_cases c578 : 0 < a3
                    swap
                    · omega
                    by_cases c579 : 0 < b9
                    swap
                    · omega
                    by_cases c580 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c581 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · -- branch
                      by_cases c582 : 0 < a5
                      swap
                      · -- branch
                        by_cases c583 : 0 < a7
                        swap
                        · omega
                        by_cases c584 : 0 < b5
                        swap
                        · omega
                        by_cases c585 : a1 + a3 + a5 < b1 + b3 + b5
                        swap
                        · omega
                        by_cases c586 : b1 + b3 < a1 + a3 + a5 + a7
                        swap
                        · omega
                        have f587 := pair_fact E (i := 7) (j := 5) rfl rfl c583 c584
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f587
                        omega
                      by_cases c588 : 0 < b5
                      swap
                      · omega
                      by_cases c589 : a1 + a3 < b1 + b3 + b5
                      swap
                      · omega
                      by_cases c590 : b1 + b3 < a1 + a3 + a5
                      swap
                      · omega
                      have f591 := pair_fact E (i := 5) (j := 5) rfl rfl c582 c588
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f591
                      omega
                    have f592 := pair_fact E (i := 3) (j := 9) rfl rfl c578 c579
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f592
                    omega
                  by_cases c593 : a1 < b1 + b3 + b5 + b7
                  swap
                  · omega
                  by_cases c594 : b1 + b3 + b5 < a1 + a3
                  swap
                  · omega
                  have f595 := pair_fact E (i := 3) (j := 7) rfl rfl c576 c577
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f595
                  omega
                by_cases c596 : b1 < a1 + a3
                swap
                · omega
                have f597 := pair_fact E (i := 3) (j := 3) rfl rfl c568 c569
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f597
                omega
              by_cases c598 : a1 < 0 + b1
              swap
              · omega
              by_cases c599 : 0 < a1 + a3
              swap
              · omega
              have f600 := pair_fact E (i := 3) (j := 1) rfl rfl c566 c567
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f600
              omega
            have f601 := pair_fact E (i := 1) (j := 9) rfl rfl c562 c563
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f601
            omega
          by_cases c602 : a1 + a3 + a5 < b1 + b3 + b5 + b7
          swap
          · omega
          by_cases c603 : b1 + b3 + b5 < a1 + a3 + a5 + a7
          swap
          · omega
          have f604 := pair_fact E (i := 7) (j := 7) rfl rfl c485 c486
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f604
          omega
        by_cases c605 : b1 < a1 + a3 + a5 + a7
        swap
        · omega
        have f606 := pair_fact E (i := 7) (j := 3) rfl rfl c482 c483
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f606
        omega
      by_cases c607 : a1 + a3 + a5 < 0 + b1
      swap
      · omega
      by_cases c608 : 0 < a1 + a3 + a5 + a7
      swap
      · omega
      have f609 := pair_fact E (i := 7) (j := 1) rfl rfl c480 c481
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f609
      omega
    by_cases c610 : 0 < b1 + b3 + b5 + b7
    swap
    · omega
    by_cases c611 : b1 + b3 + b5 < 0 + a1
    swap
    · -- branch
      by_cases c612 : 0 < a1
      swap
      · omega
      by_cases c613 : 0 < b9
      swap
      · -- branch
        by_cases c614 : 0 < a9
        swap
        · omega
        by_cases c615 : 0 < b5
        swap
        · omega
        by_cases c616 : a1 + a3 + a5 + a7 < b1 + b3 + b5
        swap
        · omega
        by_cases c617 : b1 + b3 < a1 + a3 + a5 + a7 + a9
        swap
        · omega
        have f618 := pair_fact E (i := 9) (j := 5) rfl rfl c614 c615
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f618
        omega
      by_cases c619 : 0 < b1 + b3 + b5 + b7 + b9
      swap
      · omega
      by_cases c620 : b1 + b3 + b5 + b7 < 0 + a1
      swap
      · -- branch
        by_cases c621 : 0 < a3
        swap
        · -- branch
          by_cases c622 : 0 < a3
          swap
          · -- branch
            by_cases c623 : 0 < a3
            swap
            · -- branch
              by_cases c624 : 0 < a3
              swap
              · -- branch
                by_cases c625 : 0 < a3
                swap
                · -- branch
                  by_cases c626 : 0 < a5
                  swap
                  · omega
                  by_cases c627 : 0 < b1
                  swap
                  · -- branch
                    by_cases c628 : 0 < a5
                    swap
                    · omega
                    by_cases c629 : 0 < b3
                    swap
                    · omega
                    by_cases c630 : a1 + a3 < b1 + b3
                    swap
                    · -- branch
                      by_cases c631 : 0 < a5
                      swap
                      · omega
                      by_cases c632 : 0 < b9
                      swap
                      · omega
                      by_cases c633 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                      swap
                      · omega
                      by_cases c634 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                      swap
                      · -- branch
                        by_cases c635 : 0 < a1
                        swap
                        · omega
                        by_cases c636 : 0 < b5
                        swap
                        · omega
                        by_cases c637 : 0 < b1 + b3 + b5
                        swap
                        · omega
                        by_cases c638 : b1 + b3 < 0 + a1
                        swap
                        · -- branch
                          by_cases c639 : 0 < a5
                          swap
                          · omega
                          by_cases c640 : 0 < b5
                          swap
                          · omega
                          by_cases c641 : a1 + a3 < b1 + b3 + b5
                          swap
                          · omega
                          by_cases c642 : b1 + b3 < a1 + a3 + a5
                          swap
                          · omega
                          have f643 := pair_fact E (i := 5) (j := 5) rfl rfl c639 c640
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f643
                          by_cases c644 : 0 < a9
                          swap
                          · omega
                          by_cases c645 : 0 < b1
                          swap
                          · -- branch
                            by_cases c646 : 0 < a9
                            swap
                            · omega
                            by_cases c647 : 0 < b3
                            swap
                            · omega
                            by_cases c648 : a1 + a3 + a5 + a7 < b1 + b3
                            swap
                            · -- branch
                              by_cases c649 : 0 < a9
                              swap
                              · omega
                              by_cases c650 : 0 < b5
                              swap
                              · omega
                              by_cases c651 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                              swap
                              · -- branch
                                by_cases c652 : 0 < a9
                                swap
                                · omega
                                by_cases c653 : 0 < b9
                                swap
                                · omega
                                by_cases c654 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                                swap
                                · omega
                                by_cases c655 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                                swap
                                · omega
                                have f656 := pair_fact E (i := 9) (j := 9) rfl rfl c652 c653
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f656
                                by_cases c657 : 0 < a5
                                swap
                                · omega
                                by_cases c658 : 0 < b7
                                swap
                                · omega
                                by_cases c659 : a1 + a3 < b1 + b3 + b5 + b7
                                swap
                                · omega
                                by_cases c660 : b1 + b3 + b5 < a1 + a3 + a5
                                swap
                                · -- branch
                                  by_cases c661 : 0 < a7
                                  swap
                                  · omega
                                  by_cases c662 : 0 < b5
                                  swap
                                  · omega
                                  by_cases c663 : a1 + a3 + a5 < b1 + b3 + b5
                                  swap
                                  · omega
                                  by_cases c664 : b1 + b3 < a1 + a3 + a5 + a7
                                  swap
                                  · omega
                                  have f665 := pair_fact E (i := 7) (j := 5) rfl rfl c661 c662
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f665
                                  omega
                                have f666 := pair_fact E (i := 5) (j := 7) rfl rfl c657 c658
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f666
                                omega
                              by_cases c667 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                              swap
                              · omega
                              have f668 := pair_fact E (i := 9) (j := 5) rfl rfl c649 c650
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f668
                              omega
                            by_cases c669 : b1 < a1 + a3 + a5 + a7 + a9
                            swap
                            · omega
                            have f670 := pair_fact E (i := 9) (j := 3) rfl rfl c646 c647
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f670
                            omega
                          by_cases c671 : a1 + a3 + a5 + a7 < 0 + b1
                          swap
                          · omega
                          by_cases c672 : 0 < a1 + a3 + a5 + a7 + a9
                          swap
                          · omega
                          have f673 := pair_fact E (i := 9) (j := 1) rfl rfl c644 c645
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f673
                          omega
                        have f674 := pair_fact E (i := 1) (j := 5) rfl rfl c635 c636
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f674
                        omega
                      have f675 := pair_fact E (i := 5) (j := 9) rfl rfl c631 c632
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f675
                      omega
                    by_cases c676 : b1 < a1 + a3 + a5
                    swap
                    · omega
                    have f677 := pair_fact E (i := 5) (j := 3) rfl rfl c628 c629
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f677
                    omega
                  by_cases c678 : a1 + a3 < 0 + b1
                  swap
                  · omega
                  by_cases c679 : 0 < a1 + a3 + a5
                  swap
                  · omega
                  have f680 := pair_fact E (i := 5) (j := 1) rfl rfl c626 c627
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f680
                  omega
                by_cases c681 : 0 < b9
                swap
                · omega
                by_cases c682 : a1 < b1 + b3 + b5 + b7 + b9
                swap
                · omega
                by_cases c683 : b1 + b3 + b5 + b7 < a1 + a3
                swap
                · omega
                have f684 := pair_fact E (i := 3) (j := 9) rfl rfl c625 c681
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f684
                omega
              by_cases c685 : 0 < b7
              swap
              · omega
              by_cases c686 : a1 < b1 + b3 + b5 + b7
              swap
              · omega
              by_cases c687 : b1 + b3 + b5 < a1 + a3
              swap
              · omega
              have f688 := pair_fact E (i := 3) (j := 7) rfl rfl c624 c685
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f688
              omega
            by_cases c689 : 0 < b5
            swap
            · omega
            by_cases c690 : a1 < b1 + b3 + b5
            swap
            · omega
            by_cases c691 : b1 + b3 < a1 + a3
            swap
            · omega
            have f692 := pair_fact E (i := 3) (j := 5) rfl rfl c623 c689
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f692
            omega
          by_cases c693 : 0 < b3
          swap
          · omega
          by_cases c694 : a1 < b1 + b3
          swap
          · omega
          by_cases c695 : b1 < a1 + a3
          swap
          · omega
          have f696 := pair_fact E (i := 3) (j := 3) rfl rfl c622 c693
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f696
          omega
        by_cases c697 : 0 < b1
        swap
        · -- branch
          by_cases c698 : 0 < a1
          swap
          · omega
          by_cases c699 : 0 < b5
          swap
          · omega
          by_cases c700 : 0 < b1 + b3 + b5
          swap
          · omega
          by_cases c701 : b1 + b3 < 0 + a1
          swap
          · omega
          have f702 := pair_fact E (i := 1) (j := 5) rfl rfl c698 c699
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f702
          by_cases c703 : 0 < a3
          swap
          · omega
          by_cases c704 : 0 < b3
          swap
          · omega
          by_cases c705 : a1 < b1 + b3
          swap
          · -- branch
            by_cases c706 : 0 < a3
            swap
            · omega
            by_cases c707 : 0 < b9
            swap
            · omega
            by_cases c708 : a1 < b1 + b3 + b5 + b7 + b9
            swap
            · omega
            by_cases c709 : b1 + b3 + b5 + b7 < a1 + a3
            swap
            · -- branch
              by_cases c710 : 0 < a3
              swap
              · omega
              by_cases c711 : 0 < b5
              swap
              · omega
              by_cases c712 : a1 < b1 + b3 + b5
              swap
              · -- branch
                by_cases c713 : 0 < a5
                swap
                · omega
                by_cases c714 : 0 < b9
                swap
                · omega
                by_cases c715 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                swap
                · omega
                by_cases c716 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                swap
                · omega
                have f717 := pair_fact E (i := 5) (j := 9) rfl rfl c713 c714
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f717
                omega
              by_cases c718 : b1 + b3 < a1 + a3
              swap
              · omega
              have f719 := pair_fact E (i := 3) (j := 5) rfl rfl c710 c711
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f719
              by_cases c720 : 0 < a3
              swap
              · omega
              by_cases c721 : 0 < b7
              swap
              · omega
              by_cases c722 : a1 < b1 + b3 + b5 + b7
              swap
              · omega
              by_cases c723 : b1 + b3 + b5 < a1 + a3
              swap
              · -- branch
                by_cases c724 : 0 < a5
                swap
                · -- branch
                  by_cases c725 : 0 < a7
                  swap
                  · omega
                  by_cases c726 : 0 < b5
                  swap
                  · omega
                  by_cases c727 : a1 + a3 + a5 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c728 : b1 + b3 < a1 + a3 + a5 + a7
                  swap
                  · omega
                  have f729 := pair_fact E (i := 7) (j := 5) rfl rfl c725 c726
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f729
                  omega
                by_cases c730 : 0 < b1
                swap
                · -- branch
                  by_cases c731 : 0 < a5
                  swap
                  · omega
                  by_cases c732 : 0 < b3
                  swap
                  · omega
                  by_cases c733 : a1 + a3 < b1 + b3
                  swap
                  · -- branch
                    by_cases c734 : 0 < a5
                    swap
                    · omega
                    by_cases c735 : 0 < b5
                    swap
                    · omega
                    by_cases c736 : a1 + a3 < b1 + b3 + b5
                    swap
                    · -- branch
                      by_cases c737 : 0 < a5
                      swap
                      · omega
                      by_cases c738 : 0 < b9
                      swap
                      · omega
                      by_cases c739 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                      swap
                      · omega
                      by_cases c740 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                      swap
                      · omega
                      have f741 := pair_fact E (i := 5) (j := 9) rfl rfl c737 c738
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f741
                      omega
                    by_cases c742 : b1 + b3 < a1 + a3 + a5
                    swap
                    · omega
                    have f743 := pair_fact E (i := 5) (j := 5) rfl rfl c734 c735
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f743
                    omega
                  by_cases c744 : b1 < a1 + a3 + a5
                  swap
                  · omega
                  have f745 := pair_fact E (i := 5) (j := 3) rfl rfl c731 c732
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f745
                  omega
                by_cases c746 : a1 + a3 < 0 + b1
                swap
                · omega
                by_cases c747 : 0 < a1 + a3 + a5
                swap
                · omega
                have f748 := pair_fact E (i := 5) (j := 1) rfl rfl c724 c730
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f748
                omega
              have f749 := pair_fact E (i := 3) (j := 7) rfl rfl c720 c721
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f749
              by_cases c750 : 0 < a5
              swap
              · omega
              by_cases c751 : 0 < b7
              swap
              · omega
              by_cases c752 : a1 + a3 < b1 + b3 + b5 + b7
              swap
              · omega
              by_cases c753 : b1 + b3 + b5 < a1 + a3 + a5
              swap
              · omega
              have f754 := pair_fact E (i := 5) (j := 7) rfl rfl c750 c751
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f754
              omega
            have f755 := pair_fact E (i := 3) (j := 9) rfl rfl c706 c707
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f755
            omega
          by_cases c756 : b1 < a1 + a3
          swap
          · omega
          have f757 := pair_fact E (i := 3) (j := 3) rfl rfl c703 c704
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f757
          omega
        by_cases c758 : a1 < 0 + b1
        swap
        · omega
        by_cases c759 : 0 < a1 + a3
        swap
        · omega
        have f760 := pair_fact E (i := 3) (j := 1) rfl rfl c621 c697
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f760
        omega
      have f761 := pair_fact E (i := 1) (j := 9) rfl rfl c612 c613
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f761
      omega
    have f762 := pair_fact E (i := 1) (j := 7) rfl rfl c478 c479
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f762
    omega
  by_cases c763 : 0 < 0 + b1
  swap
  · omega
  by_cases c764 : 0 < 0 + a1
  swap
  · omega
  have f765 := pair_fact E (i := 1) (j := 1) rfl rfl c1 c272
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f765
  by_cases c766 : 0 < a1
  swap
  · omega
  by_cases c767 : 0 < b7
  swap
  · -- branch
    by_cases c768 : 0 < a7
    swap
    · omega
    by_cases c769 : 0 < b1
    swap
    · omega
    by_cases c770 : a1 + a3 + a5 < 0 + b1
    swap
    · -- branch
      by_cases c771 : 0 < a7
      swap
      · omega
      by_cases c772 : 0 < b7
      swap
      · -- branch
        by_cases c773 : 0 < a1
        swap
        · omega
        by_cases c774 : 0 < b5
        swap
        · omega
        by_cases c775 : 0 < b1 + b3 + b5
        swap
        · omega
        by_cases c776 : b1 + b3 < 0 + a1
        swap
        · -- branch
          by_cases c777 : 0 < a1
          swap
          · omega
          by_cases c778 : 0 < b9
          swap
          · -- branch
            by_cases c779 : 0 < a9
            swap
            · omega
            by_cases c780 : 0 < b5
            swap
            · omega
            by_cases c781 : a1 + a3 + a5 + a7 < b1 + b3 + b5
            swap
            · omega
            by_cases c782 : b1 + b3 < a1 + a3 + a5 + a7 + a9
            swap
            · omega
            have f783 := pair_fact E (i := 9) (j := 5) rfl rfl c779 c780
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f783
            omega
          by_cases c784 : 0 < b1 + b3 + b5 + b7 + b9
          swap
          · omega
          by_cases c785 : b1 + b3 + b5 + b7 < 0 + a1
          swap
          · -- branch
            by_cases c786 : 0 < a3
            swap
            · -- branch
              by_cases c787 : 0 < a3
              swap
              · -- branch
                by_cases c788 : 0 < a3
                swap
                · -- branch
                  by_cases c789 : 0 < a3
                  swap
                  · -- branch
                    by_cases c790 : 0 < a3
                    swap
                    · -- branch
                      by_cases c791 : 0 < a5
                      swap
                      · omega
                      by_cases c792 : 0 < b3
                      swap
                      · omega
                      by_cases c793 : a1 + a3 < b1 + b3
                      swap
                      · omega
                      by_cases c794 : b1 < a1 + a3 + a5
                      swap
                      · omega
                      have f795 := pair_fact E (i := 5) (j := 3) rfl rfl c791 c792
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f795
                      by_cases c796 : 0 < a1
                      swap
                      · omega
                      by_cases c797 : 0 < b3
                      swap
                      · omega
                      by_cases c798 : 0 < b1 + b3
                      swap
                      · omega
                      by_cases c799 : b1 < 0 + a1
                      swap
                      · -- branch
                        by_cases c800 : 0 < a5
                        swap
                        · omega
                        by_cases c801 : 0 < b1
                        swap
                        · omega
                        by_cases c802 : a1 + a3 < 0 + b1
                        swap
                        · omega
                        by_cases c803 : 0 < a1 + a3 + a5
                        swap
                        · omega
                        have f804 := pair_fact E (i := 5) (j := 1) rfl rfl c800 c801
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f804
                        omega
                      have f805 := pair_fact E (i := 1) (j := 3) rfl rfl c796 c797
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f805
                      omega
                    by_cases c806 : 0 < b9
                    swap
                    · omega
                    by_cases c807 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c808 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · omega
                    have f809 := pair_fact E (i := 3) (j := 9) rfl rfl c790 c806
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f809
                    omega
                  by_cases c810 : 0 < b5
                  swap
                  · omega
                  by_cases c811 : a1 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c812 : b1 + b3 < a1 + a3
                  swap
                  · omega
                  have f813 := pair_fact E (i := 3) (j := 5) rfl rfl c789 c810
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f813
                  omega
                by_cases c814 : 0 < b3
                swap
                · omega
                by_cases c815 : a1 < b1 + b3
                swap
                · omega
                by_cases c816 : b1 < a1 + a3
                swap
                · omega
                have f817 := pair_fact E (i := 3) (j := 3) rfl rfl c788 c814
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f817
                omega
              by_cases c818 : 0 < b1
              swap
              · omega
              by_cases c819 : a1 < 0 + b1
              swap
              · omega
              by_cases c820 : 0 < a1 + a3
              swap
              · omega
              have f821 := pair_fact E (i := 3) (j := 1) rfl rfl c787 c818
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f821
              omega
            by_cases c822 : 0 < b7
            swap
            · -- branch
              by_cases c823 : 0 < a3
              swap
              · omega
              by_cases c824 : 0 < b9
              swap
              · omega
              by_cases c825 : a1 < b1 + b3 + b5 + b7 + b9
              swap
              · omega
              by_cases c826 : b1 + b3 + b5 + b7 < a1 + a3
              swap
              · -- branch
                by_cases c827 : 0 < a3
                swap
                · omega
                by_cases c828 : 0 < b1
                swap
                · omega
                by_cases c829 : a1 < 0 + b1
                swap
                · -- branch
                  by_cases c830 : 0 < a1
                  swap
                  · omega
                  by_cases c831 : 0 < b3
                  swap
                  · omega
                  by_cases c832 : 0 < b1 + b3
                  swap
                  · omega
                  by_cases c833 : b1 < 0 + a1
                  swap
                  · omega
                  have f834 := pair_fact E (i := 1) (j := 3) rfl rfl c830 c831
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f834
                  by_cases c835 : 0 < a3
                  swap
                  · omega
                  by_cases c836 : 0 < b3
                  swap
                  · omega
                  by_cases c837 : a1 < b1 + b3
                  swap
                  · -- branch
                    by_cases c838 : 0 < a3
                    swap
                    · omega
                    by_cases c839 : 0 < b5
                    swap
                    · omega
                    by_cases c840 : a1 < b1 + b3 + b5
                    swap
                    · omega
                    by_cases c841 : b1 + b3 < a1 + a3
                    swap
                    · omega
                    have f842 := pair_fact E (i := 3) (j := 5) rfl rfl c838 c839
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f842
                    omega
                  by_cases c843 : b1 < a1 + a3
                  swap
                  · omega
                  have f844 := pair_fact E (i := 3) (j := 3) rfl rfl c835 c836
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f844
                  omega
                by_cases c845 : 0 < a1 + a3
                swap
                · omega
                have f846 := pair_fact E (i := 3) (j := 1) rfl rfl c827 c828
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f846
                by_cases c847 : 0 < a3
                swap
                · omega
                by_cases c848 : 0 < b5
                swap
                · omega
                by_cases c849 : a1 < b1 + b3 + b5
                swap
                · omega
                by_cases c850 : b1 + b3 < a1 + a3
                swap
                · -- branch
                  by_cases c851 : 0 < a1
                  swap
                  · omega
                  by_cases c852 : 0 < b3
                  swap
                  · omega
                  by_cases c853 : 0 < b1 + b3
                  swap
                  · omega
                  by_cases c854 : b1 < 0 + a1
                  swap
                  · -- branch
                    by_cases c855 : 0 < a3
                    swap
                    · omega
                    by_cases c856 : 0 < b3
                    swap
                    · omega
                    by_cases c857 : a1 < b1 + b3
                    swap
                    · omega
                    by_cases c858 : b1 < a1 + a3
                    swap
                    · -- branch
                      by_cases c859 : 0 < a5
                      swap
                      · omega
                      by_cases c860 : 0 < b3
                      swap
                      · omega
                      by_cases c861 : a1 + a3 < b1 + b3
                      swap
                      · omega
                      by_cases c862 : b1 < a1 + a3 + a5
                      swap
                      · omega
                      have f863 := pair_fact E (i := 5) (j := 3) rfl rfl c859 c860
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f863
                      omega
                    have f864 := pair_fact E (i := 3) (j := 3) rfl rfl c855 c856
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f864
                    omega
                  have f865 := pair_fact E (i := 1) (j := 3) rfl rfl c851 c852
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f865
                  omega
                have f866 := pair_fact E (i := 3) (j := 5) rfl rfl c847 c848
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f866
                omega
              have f867 := pair_fact E (i := 3) (j := 9) rfl rfl c823 c824
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f867
              omega
            by_cases c868 : a1 < b1 + b3 + b5 + b7
            swap
            · omega
            by_cases c869 : b1 + b3 + b5 < a1 + a3
            swap
            · omega
            have f870 := pair_fact E (i := 3) (j := 7) rfl rfl c786 c822
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f870
            omega
          have f871 := pair_fact E (i := 1) (j := 9) rfl rfl c777 c778
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f871
          omega
        have f872 := pair_fact E (i := 1) (j := 5) rfl rfl c773 c774
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f872
        by_cases c873 : 0 < a3
        swap
        · omega
        by_cases c874 : 0 < b5
        swap
        · omega
        by_cases c875 : a1 < b1 + b3 + b5
        swap
        · omega
        by_cases c876 : b1 + b3 < a1 + a3
        swap
        · omega
        have f877 := pair_fact E (i := 3) (j := 5) rfl rfl c873 c874
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f877
        omega
      by_cases c878 : a1 + a3 + a5 < b1 + b3 + b5 + b7
      swap
      · omega
      by_cases c879 : b1 + b3 + b5 < a1 + a3 + a5 + a7
      swap
      · omega
      have f880 := pair_fact E (i := 7) (j := 7) rfl rfl c771 c772
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f880
      omega
    by_cases c881 : 0 < a1 + a3 + a5 + a7
    swap
    · omega
    have f882 := pair_fact E (i := 7) (j := 1) rfl rfl c768 c769
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f882
    omega
  by_cases c883 : 0 < b1 + b3 + b5 + b7
  swap
  · omega
  by_cases c884 : b1 + b3 + b5 < 0 + a1
  swap
  · -- branch
    by_cases c885 : 0 < a1
    swap
    · omega
    by_cases c886 : 0 < b9
    swap
    · -- branch
      by_cases c887 : 0 < a9
      swap
      · omega
      by_cases c888 : 0 < b5
      swap
      · omega
      by_cases c889 : a1 + a3 + a5 + a7 < b1 + b3 + b5
      swap
      · omega
      by_cases c890 : b1 + b3 < a1 + a3 + a5 + a7 + a9
      swap
      · omega
      have f891 := pair_fact E (i := 9) (j := 5) rfl rfl c887 c888
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f891
      omega
    by_cases c892 : 0 < b1 + b3 + b5 + b7 + b9
    swap
    · omega
    by_cases c893 : b1 + b3 + b5 + b7 < 0 + a1
    swap
    · -- branch
      by_cases c894 : 0 < a3
      swap
      · -- branch
        by_cases c895 : 0 < a3
        swap
        · -- branch
          by_cases c896 : 0 < a3
          swap
          · -- branch
            by_cases c897 : 0 < a3
            swap
            · -- branch
              by_cases c898 : 0 < a3
              swap
              · -- branch
                by_cases c899 : 0 < a5
                swap
                · omega
                by_cases c900 : 0 < b3
                swap
                · omega
                by_cases c901 : a1 + a3 < b1 + b3
                swap
                · omega
                by_cases c902 : b1 < a1 + a3 + a5
                swap
                · omega
                have f903 := pair_fact E (i := 5) (j := 3) rfl rfl c899 c900
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f903
                by_cases c904 : 0 < a1
                swap
                · omega
                by_cases c905 : 0 < b3
                swap
                · omega
                by_cases c906 : 0 < b1 + b3
                swap
                · omega
                by_cases c907 : b1 < 0 + a1
                swap
                · -- branch
                  by_cases c908 : 0 < a5
                  swap
                  · omega
                  by_cases c909 : 0 < b1
                  swap
                  · omega
                  by_cases c910 : a1 + a3 < 0 + b1
                  swap
                  · omega
                  by_cases c911 : 0 < a1 + a3 + a5
                  swap
                  · omega
                  have f912 := pair_fact E (i := 5) (j := 1) rfl rfl c908 c909
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f912
                  omega
                have f913 := pair_fact E (i := 1) (j := 3) rfl rfl c904 c905
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f913
                omega
              by_cases c914 : 0 < b7
              swap
              · omega
              by_cases c915 : a1 < b1 + b3 + b5 + b7
              swap
              · omega
              by_cases c916 : b1 + b3 + b5 < a1 + a3
              swap
              · omega
              have f917 := pair_fact E (i := 3) (j := 7) rfl rfl c898 c914
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f917
              omega
            by_cases c918 : 0 < b5
            swap
            · omega
            by_cases c919 : a1 < b1 + b3 + b5
            swap
            · omega
            by_cases c920 : b1 + b3 < a1 + a3
            swap
            · omega
            have f921 := pair_fact E (i := 3) (j := 5) rfl rfl c897 c918
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f921
            omega
          by_cases c922 : 0 < b3
          swap
          · omega
          by_cases c923 : a1 < b1 + b3
          swap
          · omega
          by_cases c924 : b1 < a1 + a3
          swap
          · omega
          have f925 := pair_fact E (i := 3) (j := 3) rfl rfl c896 c922
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f925
          omega
        by_cases c926 : 0 < b1
        swap
        · omega
        by_cases c927 : a1 < 0 + b1
        swap
        · omega
        by_cases c928 : 0 < a1 + a3
        swap
        · omega
        have f929 := pair_fact E (i := 3) (j := 1) rfl rfl c895 c926
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f929
        omega
      by_cases c930 : 0 < b9
      swap
      · omega
      by_cases c931 : a1 < b1 + b3 + b5 + b7 + b9
      swap
      · omega
      by_cases c932 : b1 + b3 + b5 + b7 < a1 + a3
      swap
      · -- branch
        by_cases c933 : 0 < a3
        swap
        · omega
        by_cases c934 : 0 < b1
        swap
        · omega
        by_cases c935 : a1 < 0 + b1
        swap
        · -- branch
          by_cases c936 : 0 < a1
          swap
          · omega
          by_cases c937 : 0 < b3
          swap
          · -- branch
            by_cases c938 : 0 < a1
            swap
            · omega
            by_cases c939 : 0 < b5
            swap
            · omega
            by_cases c940 : 0 < b1 + b3 + b5
            swap
            · omega
            by_cases c941 : b1 + b3 < 0 + a1
            swap
            · omega
            have f942 := pair_fact E (i := 1) (j := 5) rfl rfl c938 c939
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f942
            by_cases c943 : 0 < a3
            swap
            · omega
            by_cases c944 : 0 < b5
            swap
            · omega
            by_cases c945 : a1 < b1 + b3 + b5
            swap
            · omega
            by_cases c946 : b1 + b3 < a1 + a3
            swap
            · omega
            have f947 := pair_fact E (i := 3) (j := 5) rfl rfl c943 c944
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f947
            omega
          by_cases c948 : 0 < b1 + b3
          swap
          · omega
          by_cases c949 : b1 < 0 + a1
          swap
          · omega
          have f950 := pair_fact E (i := 1) (j := 3) rfl rfl c936 c937
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f950
          by_cases c951 : 0 < a3
          swap
          · omega
          by_cases c952 : 0 < b3
          swap
          · omega
          by_cases c953 : a1 < b1 + b3
          swap
          · -- branch
            by_cases c954 : 0 < a3
            swap
            · omega
            by_cases c955 : 0 < b5
            swap
            · omega
            by_cases c956 : a1 < b1 + b3 + b5
            swap
            · omega
            by_cases c957 : b1 + b3 < a1 + a3
            swap
            · omega
            have f958 := pair_fact E (i := 3) (j := 5) rfl rfl c954 c955
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f958
            omega
          by_cases c959 : b1 < a1 + a3
          swap
          · omega
          have f960 := pair_fact E (i := 3) (j := 3) rfl rfl c951 c952
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f960
          omega
        by_cases c961 : 0 < a1 + a3
        swap
        · omega
        have f962 := pair_fact E (i := 3) (j := 1) rfl rfl c933 c934
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f962
        by_cases c963 : 0 < a3
        swap
        · omega
        by_cases c964 : 0 < b7
        swap
        · omega
        by_cases c965 : a1 < b1 + b3 + b5 + b7
        swap
        · omega
        by_cases c966 : b1 + b3 + b5 < a1 + a3
        swap
        · -- branch
          by_cases c967 : 0 < a1
          swap
          · omega
          by_cases c968 : 0 < b3
          swap
          · -- branch
            by_cases c969 : 0 < a3
            swap
            · omega
            by_cases c970 : 0 < b5
            swap
            · omega
            by_cases c971 : a1 < b1 + b3 + b5
            swap
            · omega
            by_cases c972 : b1 + b3 < a1 + a3
            swap
            · omega
            have f973 := pair_fact E (i := 3) (j := 5) rfl rfl c969 c970
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f973
            omega
          by_cases c974 : 0 < b1 + b3
          swap
          · omega
          by_cases c975 : b1 < 0 + a1
          swap
          · -- branch
            by_cases c976 : 0 < a3
            swap
            · omega
            by_cases c977 : 0 < b3
            swap
            · omega
            by_cases c978 : a1 < b1 + b3
            swap
            · omega
            by_cases c979 : b1 < a1 + a3
            swap
            · -- branch
              by_cases c980 : 0 < a5
              swap
              · omega
              by_cases c981 : 0 < b3
              swap
              · omega
              by_cases c982 : a1 + a3 < b1 + b3
              swap
              · omega
              by_cases c983 : b1 < a1 + a3 + a5
              swap
              · omega
              have f984 := pair_fact E (i := 5) (j := 3) rfl rfl c980 c981
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f984
              omega
            have f985 := pair_fact E (i := 3) (j := 3) rfl rfl c976 c977
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f985
            omega
          have f986 := pair_fact E (i := 1) (j := 3) rfl rfl c967 c968
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f986
          omega
        have f987 := pair_fact E (i := 3) (j := 7) rfl rfl c963 c964
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f987
        omega
      have f988 := pair_fact E (i := 3) (j := 9) rfl rfl c894 c930
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f988
      omega
    have f989 := pair_fact E (i := 1) (j := 9) rfl rfl c885 c886
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f989
    omega
  have f990 := pair_fact E (i := 1) (j := 7) rfl rfl c766 c767
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f990
  omega

end Blocks
