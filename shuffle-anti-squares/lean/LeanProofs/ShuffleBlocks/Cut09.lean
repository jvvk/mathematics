import LeanProofs.ShuffleBlocks.Basic

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Blocks

set_option maxHeartbeats 0 in
/-- Cut inside run 9 of `V`: no splitting of this rotation gives two equal copies. -/
theorem V_cut09 (L l m v k a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9 a10 b10 : Nat)
    (hl : 1 ≤ l) (hm : m = 2 * v + 1) (hL : 9 * l ≤ L) (hk : k ≤ 3 * m)
    (e0 : a0 + b0 = (3 * m - k))
    (e1 : a1 + b1 = L)
    (e2 : a2 + b2 = m)
    (e3 : a3 + b3 = 5 * l)
    (e4 : a4 + b4 = 2 * m)
    (e5 : a5 + b5 = L)
    (e6 : a6 + b6 = m)
    (e7 : a7 + b7 = 2 * l)
    (e8 : a8 + b8 = m)
    (e9 : a9 + b9 = l)
    (e10 : a10 + b10 = k)
    (E : rw [(true, a0), (false, a1), (true, a2), (false, a3), (true, a4), (false, a5), (true, a6), (false, a7), (true, a8), (false, a9), (true, a10)] = rw [(true, b0), (false, b1), (true, b2), (false, b3), (true, b4), (false, b5), (true, b6), (false, b7), (true, b8), (false, b9), (true, b10)]) : False := by
  have ho := congrArg (List.count true) E
  have hz := congrArg (List.count false) E
  simp only [count_rw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    Bool.true_eq_false, Bool.false_eq_true] at ho hz
  by_cases c1 : 0 < a0
  swap
  · -- branch
    by_cases c2 : 0 < a0
    swap
    · -- branch
      by_cases c3 : 0 < a0
      swap
      · -- branch
        by_cases c4 : 0 < a0
        swap
        · -- branch
          by_cases c5 : 0 < a0
          swap
          · -- branch
            by_cases c6 : 0 < a0
            swap
            · -- branch
              by_cases c7 : 0 < a2
              swap
              · -- branch
                by_cases c8 : 0 < a2
                swap
                · -- branch
                  by_cases c9 : 0 < a2
                  swap
                  · -- branch
                    by_cases c10 : 0 < a2
                    swap
                    · -- branch
                      by_cases c11 : 0 < a2
                      swap
                      · -- branch
                        by_cases c12 : 0 < a2
                        swap
                        · -- branch
                          by_cases c13 : 0 < a4
                          swap
                          · -- branch
                            by_cases c14 : 0 < a4
                            swap
                            · -- branch
                              by_cases c15 : 0 < a4
                              swap
                              · -- branch
                                by_cases c16 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c17 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c18 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c19 : 0 < a10
                                      swap
                                      · omega
                                      by_cases c20 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c21 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                                      swap
                                      · -- branch
                                        by_cases c22 : 0 < a10
                                        swap
                                        · omega
                                        by_cases c23 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c24 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c25 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                        swap
                                        · omega
                                        have f26 := pair_fact E (i := 10) (j := 4) rfl rfl c22 c23
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f26
                                        by_cases c27 : 0 < a6
                                        swap
                                        · -- branch
                                          by_cases c28 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c29 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c30 : a0 + a2 + a4 + a6 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c31 : b0 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f32 := pair_fact E (i := 8) (j := 2) rfl rfl c28 c29
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f32
                                          omega
                                        by_cases c33 : 0 < b0
                                        swap
                                        · -- branch
                                          by_cases c34 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c35 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c36 : a0 + a2 + a4 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c37 : b0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f38 := pair_fact E (i := 6) (j := 2) rfl rfl c34 c35
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f38
                                          omega
                                        by_cases c39 : a0 + a2 + a4 < 0 + b0
                                        swap
                                        · omega
                                        by_cases c40 : 0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f41 := pair_fact E (i := 6) (j := 0) rfl rfl c27 c33
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f41
                                        omega
                                      by_cases c42 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                                      swap
                                      · omega
                                      have f43 := pair_fact E (i := 10) (j := 2) rfl rfl c19 c20
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f43
                                      omega
                                    by_cases c44 : 0 < b10
                                    swap
                                    · omega
                                    by_cases c45 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c46 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f47 := pair_fact E (i := 4) (j := 10) rfl rfl c18 c44
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f47
                                    omega
                                  by_cases c48 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c49 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c50 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f51 := pair_fact E (i := 4) (j := 8) rfl rfl c17 c48
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f51
                                  omega
                                by_cases c52 : 0 < b6
                                swap
                                · omega
                                by_cases c53 : a0 + a2 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c54 : b0 + b2 + b4 < a0 + a2 + a4
                                swap
                                · omega
                                have f55 := pair_fact E (i := 4) (j := 6) rfl rfl c16 c52
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f55
                                omega
                              by_cases c56 : 0 < b4
                              swap
                              · omega
                              by_cases c57 : a0 + a2 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c58 : b0 + b2 < a0 + a2 + a4
                              swap
                              · omega
                              have f59 := pair_fact E (i := 4) (j := 4) rfl rfl c15 c56
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f59
                              omega
                            by_cases c60 : 0 < b2
                            swap
                            · omega
                            by_cases c61 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c62 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f63 := pair_fact E (i := 4) (j := 2) rfl rfl c14 c60
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f63
                            omega
                          by_cases c64 : 0 < b0
                          swap
                          · -- branch
                            by_cases c65 : 0 < a4
                            swap
                            · omega
                            by_cases c66 : 0 < b2
                            swap
                            · omega
                            by_cases c67 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c68 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f69 := pair_fact E (i := 4) (j := 2) rfl rfl c65 c66
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f69
                            by_cases c70 : 0 < a4
                            swap
                            · omega
                            by_cases c71 : 0 < b6
                            swap
                            · -- branch
                              by_cases c72 : 0 < a4
                              swap
                              · omega
                              by_cases c73 : 0 < b10
                              swap
                              · omega
                              by_cases c74 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c75 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c76 : 0 < a6
                                swap
                                · omega
                                by_cases c77 : 0 < b0
                                swap
                                · -- branch
                                  by_cases c78 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c79 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c80 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c81 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c82 : 0 < b6
                                    swap
                                    · -- branch
                                      by_cases c83 : 0 < a10
                                      swap
                                      · omega
                                      by_cases c84 : 0 < b0
                                      swap
                                      · -- branch
                                        by_cases c85 : 0 < a10
                                        swap
                                        · omega
                                        by_cases c86 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c87 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                                        swap
                                        · -- branch
                                          by_cases c88 : 0 < a10
                                          swap
                                          · omega
                                          by_cases c89 : 0 < b6
                                          swap
                                          · -- branch
                                            by_cases c90 : 0 < a10
                                            swap
                                            · omega
                                            by_cases c91 : 0 < b10
                                            swap
                                            · omega
                                            by_cases c92 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8 + b10
                                            swap
                                            · omega
                                            by_cases c93 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8 + a10
                                            swap
                                            · omega
                                            have f94 := pair_fact E (i := 10) (j := 10) rfl rfl c90 c91
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f94
                                            by_cases c95 : 0 < a4
                                            swap
                                            · omega
                                            by_cases c96 : 0 < b8
                                            swap
                                            · -- branch
                                              by_cases c97 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c98 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c99 : a0 + a2 + a4 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c100 : b0 + b2 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f101 := pair_fact E (i := 6) (j := 4) rfl rfl c97 c98
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f101
                                              omega
                                            by_cases c102 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                            swap
                                            · omega
                                            by_cases c103 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                            swap
                                            · -- branch
                                              by_cases c104 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c105 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c106 : a0 + a2 + a4 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c107 : b0 + b2 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f108 := pair_fact E (i := 6) (j := 4) rfl rfl c104 c105
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f108
                                              omega
                                            have f109 := pair_fact E (i := 4) (j := 8) rfl rfl c95 c96
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f109
                                            omega
                                          by_cases c110 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                          swap
                                          · omega
                                          by_cases c111 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                          swap
                                          · omega
                                          have f112 := pair_fact E (i := 10) (j := 6) rfl rfl c88 c89
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f112
                                          omega
                                        by_cases c113 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                                        swap
                                        · omega
                                        have f114 := pair_fact E (i := 10) (j := 2) rfl rfl c85 c86
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f114
                                        omega
                                      by_cases c115 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                                      swap
                                      · omega
                                      by_cases c116 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                                      swap
                                      · omega
                                      have f117 := pair_fact E (i := 10) (j := 0) rfl rfl c83 c84
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f117
                                      omega
                                    by_cases c118 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c119 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f120 := pair_fact E (i := 6) (j := 6) rfl rfl c81 c82
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f120
                                    omega
                                  by_cases c121 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f122 := pair_fact E (i := 6) (j := 2) rfl rfl c78 c79
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f122
                                  omega
                                by_cases c123 : a0 + a2 + a4 < 0 + b0
                                swap
                                · omega
                                by_cases c124 : 0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f125 := pair_fact E (i := 6) (j := 0) rfl rfl c76 c77
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f125
                                omega
                              have f126 := pair_fact E (i := 4) (j := 10) rfl rfl c72 c73
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f126
                              omega
                            by_cases c127 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c128 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c129 : 0 < a10
                              swap
                              · omega
                              by_cases c130 : 0 < b0
                              swap
                              · -- branch
                                by_cases c131 : 0 < a10
                                swap
                                · omega
                                by_cases c132 : 0 < b2
                                swap
                                · omega
                                by_cases c133 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                                swap
                                · -- branch
                                  by_cases c134 : 0 < a10
                                  swap
                                  · omega
                                  by_cases c135 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c136 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                  swap
                                  · -- branch
                                    by_cases c137 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c138 : 0 < b10
                                    swap
                                    · omega
                                    by_cases c139 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c140 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c141 : 0 < a6
                                      swap
                                      · -- branch
                                        by_cases c142 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c143 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c144 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c145 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f146 := pair_fact E (i := 8) (j := 4) rfl rfl c142 c143
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f146
                                        omega
                                      by_cases c147 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c148 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c149 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f150 := pair_fact E (i := 6) (j := 4) rfl rfl c141 c147
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f150
                                      omega
                                    have f151 := pair_fact E (i := 4) (j := 10) rfl rfl c137 c138
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f151
                                    omega
                                  by_cases c152 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                  swap
                                  · omega
                                  have f153 := pair_fact E (i := 10) (j := 4) rfl rfl c134 c135
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f153
                                  omega
                                by_cases c154 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f155 := pair_fact E (i := 10) (j := 2) rfl rfl c131 c132
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f155
                                omega
                              by_cases c156 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                              swap
                              · omega
                              by_cases c157 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                              swap
                              · omega
                              have f158 := pair_fact E (i := 10) (j := 0) rfl rfl c129 c130
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f158
                              omega
                            have f159 := pair_fact E (i := 4) (j := 6) rfl rfl c70 c71
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f159
                            omega
                          by_cases c160 : a0 + a2 < 0 + b0
                          swap
                          · omega
                          by_cases c161 : 0 < a0 + a2 + a4
                          swap
                          · omega
                          have f162 := pair_fact E (i := 4) (j := 0) rfl rfl c13 c64
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f162
                          omega
                        by_cases c163 : 0 < b10
                        swap
                        · omega
                        by_cases c164 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c165 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                        swap
                        · omega
                        have f166 := pair_fact E (i := 2) (j := 10) rfl rfl c12 c163
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f166
                        omega
                      by_cases c167 : 0 < b8
                      swap
                      · omega
                      by_cases c168 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c169 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · omega
                      have f170 := pair_fact E (i := 2) (j := 8) rfl rfl c11 c167
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f170
                      omega
                    by_cases c171 : 0 < b6
                    swap
                    · omega
                    by_cases c172 : a0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c173 : b0 + b2 + b4 < a0 + a2
                    swap
                    · omega
                    have f174 := pair_fact E (i := 2) (j := 6) rfl rfl c10 c171
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f174
                    omega
                  by_cases c175 : 0 < b4
                  swap
                  · omega
                  by_cases c176 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c177 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f178 := pair_fact E (i := 2) (j := 4) rfl rfl c9 c175
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f178
                  omega
                by_cases c179 : 0 < b2
                swap
                · omega
                by_cases c180 : a0 < b0 + b2
                swap
                · omega
                by_cases c181 : b0 < a0 + a2
                swap
                · omega
                have f182 := pair_fact E (i := 2) (j := 2) rfl rfl c8 c179
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f182
                omega
              by_cases c183 : 0 < b0
              swap
              · -- branch
                by_cases c184 : 0 < a2
                swap
                · omega
                by_cases c185 : 0 < b2
                swap
                · -- branch
                  by_cases c186 : 0 < a2
                  swap
                  · omega
                  by_cases c187 : 0 < b4
                  swap
                  · -- branch
                    by_cases c188 : 0 < a2
                    swap
                    · omega
                    by_cases c189 : 0 < b6
                    swap
                    · -- branch
                      by_cases c190 : 0 < a2
                      swap
                      · omega
                      by_cases c191 : 0 < b8
                      swap
                      · omega
                      by_cases c192 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c193 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · omega
                      have f194 := pair_fact E (i := 2) (j := 8) rfl rfl c190 c191
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f194
                      omega
                    by_cases c195 : a0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c196 : b0 + b2 + b4 < a0 + a2
                    swap
                    · omega
                    have f197 := pair_fact E (i := 2) (j := 6) rfl rfl c188 c189
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f197
                    omega
                  by_cases c198 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c199 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f200 := pair_fact E (i := 2) (j := 4) rfl rfl c186 c187
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f200
                  by_cases c201 : 0 < a2
                  swap
                  · omega
                  by_cases c202 : 0 < b6
                  swap
                  · -- branch
                    by_cases c203 : 0 < a2
                    swap
                    · omega
                    by_cases c204 : 0 < b10
                    swap
                    · omega
                    by_cases c205 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c206 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · -- branch
                      by_cases c207 : 0 < a6
                      swap
                      · omega
                      by_cases c208 : 0 < b0
                      swap
                      · -- branch
                        by_cases c209 : 0 < a6
                        swap
                        · omega
                        by_cases c210 : 0 < b2
                        swap
                        · -- branch
                          by_cases c211 : 0 < a6
                          swap
                          · omega
                          by_cases c212 : 0 < b4
                          swap
                          · omega
                          by_cases c213 : a0 + a2 + a4 < b0 + b2 + b4
                          swap
                          · -- branch
                            by_cases c214 : 0 < a4
                            swap
                            · omega
                            by_cases c215 : 0 < b0
                            swap
                            · -- branch
                              by_cases c216 : 0 < a4
                              swap
                              · omega
                              by_cases c217 : 0 < b2
                              swap
                              · -- branch
                                by_cases c218 : 0 < a4
                                swap
                                · omega
                                by_cases c219 : 0 < b6
                                swap
                                · -- branch
                                  by_cases c220 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c221 : 0 < b10
                                  swap
                                  · omega
                                  by_cases c222 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                  swap
                                  · omega
                                  by_cases c223 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c224 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c225 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c226 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c227 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f228 := pair_fact E (i := 4) (j := 8) rfl rfl c224 c225
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f228
                                    omega
                                  have f229 := pair_fact E (i := 4) (j := 10) rfl rfl c220 c221
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f229
                                  omega
                                by_cases c230 : a0 + a2 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c231 : b0 + b2 + b4 < a0 + a2 + a4
                                swap
                                · omega
                                have f232 := pair_fact E (i := 4) (j := 6) rfl rfl c218 c219
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f232
                                omega
                              by_cases c233 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c234 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f235 := pair_fact E (i := 4) (j := 2) rfl rfl c216 c217
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f235
                              omega
                            by_cases c236 : a0 + a2 < 0 + b0
                            swap
                            · omega
                            by_cases c237 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f238 := pair_fact E (i := 4) (j := 0) rfl rfl c214 c215
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f238
                            omega
                          by_cases c239 : b0 + b2 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f240 := pair_fact E (i := 6) (j := 4) rfl rfl c211 c212
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f240
                          omega
                        by_cases c241 : a0 + a2 + a4 < b0 + b2
                        swap
                        · omega
                        by_cases c242 : b0 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f243 := pair_fact E (i := 6) (j := 2) rfl rfl c209 c210
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f243
                        omega
                      by_cases c244 : a0 + a2 + a4 < 0 + b0
                      swap
                      · omega
                      by_cases c245 : 0 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f246 := pair_fact E (i := 6) (j := 0) rfl rfl c207 c208
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f246
                      omega
                    have f247 := pair_fact E (i := 2) (j := 10) rfl rfl c203 c204
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f247
                    omega
                  by_cases c248 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c249 : b0 + b2 + b4 < a0 + a2
                  swap
                  · -- branch
                    by_cases c250 : 0 < a10
                    swap
                    · omega
                    by_cases c251 : 0 < b0
                    swap
                    · -- branch
                      by_cases c252 : 0 < a10
                      swap
                      · omega
                      by_cases c253 : 0 < b2
                      swap
                      · -- branch
                        by_cases c254 : 0 < a10
                        swap
                        · omega
                        by_cases c255 : 0 < b4
                        swap
                        · omega
                        by_cases c256 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                        swap
                        · -- branch
                          by_cases c257 : 0 < a2
                          swap
                          · omega
                          by_cases c258 : 0 < b10
                          swap
                          · omega
                          by_cases c259 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c260 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · -- branch
                            by_cases c261 : 0 < a10
                            swap
                            · omega
                            by_cases c262 : 0 < b10
                            swap
                            · omega
                            by_cases c263 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c264 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f265 := pair_fact E (i := 10) (j := 10) rfl rfl c261 c262
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f265
                            by_cases c266 : 0 < a2
                            swap
                            · omega
                            by_cases c267 : 0 < b8
                            swap
                            · -- branch
                              by_cases c268 : 0 < a8
                              swap
                              · omega
                              by_cases c269 : 0 < b0
                              swap
                              · -- branch
                                by_cases c270 : 0 < a8
                                swap
                                · omega
                                by_cases c271 : 0 < b2
                                swap
                                · -- branch
                                  by_cases c272 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c273 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c274 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                  swap
                                  · -- branch
                                    by_cases c275 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c276 : 0 < b0
                                    swap
                                    · -- branch
                                      by_cases c277 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c278 : 0 < b2
                                      swap
                                      · -- branch
                                        by_cases c279 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c280 : 0 < b6
                                        swap
                                        · omega
                                        by_cases c281 : a0 + a2 < b0 + b2 + b4 + b6
                                        swap
                                        · omega
                                        by_cases c282 : b0 + b2 + b4 < a0 + a2 + a4
                                        swap
                                        · -- branch
                                          by_cases c283 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c284 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c285 : a0 + a2 + a4 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c286 : b0 + b2 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f287 := pair_fact E (i := 6) (j := 4) rfl rfl c283 c284
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f287
                                          omega
                                        have f288 := pair_fact E (i := 4) (j := 6) rfl rfl c279 c280
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f288
                                        omega
                                      by_cases c289 : a0 + a2 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c290 : b0 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f291 := pair_fact E (i := 4) (j := 2) rfl rfl c277 c278
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f291
                                      omega
                                    by_cases c292 : a0 + a2 < 0 + b0
                                    swap
                                    · omega
                                    by_cases c293 : 0 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f294 := pair_fact E (i := 4) (j := 0) rfl rfl c275 c276
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f294
                                    omega
                                  by_cases c295 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f296 := pair_fact E (i := 8) (j := 4) rfl rfl c272 c273
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f296
                                  omega
                                by_cases c297 : a0 + a2 + a4 + a6 < b0 + b2
                                swap
                                · omega
                                by_cases c298 : b0 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f299 := pair_fact E (i := 8) (j := 2) rfl rfl c270 c271
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f299
                                omega
                              by_cases c300 : a0 + a2 + a4 + a6 < 0 + b0
                              swap
                              · omega
                              by_cases c301 : 0 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f302 := pair_fact E (i := 8) (j := 0) rfl rfl c268 c269
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f302
                              omega
                            by_cases c303 : a0 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c304 : b0 + b2 + b4 + b6 < a0 + a2
                            swap
                            · -- branch
                              by_cases c305 : 0 < a4
                              swap
                              · -- branch
                                by_cases c306 : 0 < a6
                                swap
                                · omega
                                by_cases c307 : 0 < b4
                                swap
                                · omega
                                by_cases c308 : a0 + a2 + a4 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c309 : b0 + b2 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f310 := pair_fact E (i := 6) (j := 4) rfl rfl c306 c307
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f310
                                omega
                              by_cases c311 : 0 < b0
                              swap
                              · -- branch
                                by_cases c312 : 0 < a4
                                swap
                                · omega
                                by_cases c313 : 0 < b2
                                swap
                                · -- branch
                                  by_cases c314 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c315 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c316 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c317 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c318 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c319 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c320 : a0 + a2 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c321 : b0 + b2 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f322 := pair_fact E (i := 4) (j := 4) rfl rfl c318 c319
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f322
                                    by_cases c323 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c324 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c325 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c326 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c327 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c328 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c329 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c330 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c331 : 0 < a6
                                        swap
                                        · -- branch
                                          by_cases c332 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c333 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c334 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c335 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f336 := pair_fact E (i := 8) (j := 4) rfl rfl c332 c333
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f336
                                          omega
                                        by_cases c337 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c338 : a0 + a2 + a4 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c339 : b0 + b2 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f340 := pair_fact E (i := 6) (j := 4) rfl rfl c331 c337
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f340
                                        omega
                                      have f341 := pair_fact E (i := 4) (j := 10) rfl rfl c327 c328
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f341
                                      omega
                                    have f342 := pair_fact E (i := 4) (j := 8) rfl rfl c323 c324
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f342
                                    omega
                                  have f343 := pair_fact E (i := 4) (j := 6) rfl rfl c314 c315
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f343
                                  omega
                                by_cases c344 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c345 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f346 := pair_fact E (i := 4) (j := 2) rfl rfl c312 c313
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f346
                                omega
                              by_cases c347 : a0 + a2 < 0 + b0
                              swap
                              · omega
                              by_cases c348 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f349 := pair_fact E (i := 4) (j := 0) rfl rfl c305 c311
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f349
                              omega
                            have f350 := pair_fact E (i := 2) (j := 8) rfl rfl c266 c267
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f350
                            omega
                          have f351 := pair_fact E (i := 2) (j := 10) rfl rfl c257 c258
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f351
                          omega
                        by_cases c352 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                        swap
                        · omega
                        have f353 := pair_fact E (i := 10) (j := 4) rfl rfl c254 c255
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f353
                        omega
                      by_cases c354 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                      swap
                      · omega
                      by_cases c355 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f356 := pair_fact E (i := 10) (j := 2) rfl rfl c252 c253
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f356
                      omega
                    by_cases c357 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                    swap
                    · omega
                    by_cases c358 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                    swap
                    · omega
                    have f359 := pair_fact E (i := 10) (j := 0) rfl rfl c250 c251
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f359
                    omega
                  have f360 := pair_fact E (i := 2) (j := 6) rfl rfl c201 c202
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f360
                  omega
                by_cases c361 : a0 < b0 + b2
                swap
                · omega
                by_cases c362 : b0 < a0 + a2
                swap
                · omega
                have f363 := pair_fact E (i := 2) (j := 2) rfl rfl c184 c185
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f363
                by_cases c364 : 0 < a2
                swap
                · omega
                by_cases c365 : 0 < b6
                swap
                · -- branch
                  by_cases c366 : 0 < a2
                  swap
                  · omega
                  by_cases c367 : 0 < b10
                  swap
                  · omega
                  by_cases c368 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c369 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                  swap
                  · -- branch
                    by_cases c370 : 0 < a6
                    swap
                    · omega
                    by_cases c371 : 0 < b0
                    swap
                    · -- branch
                      by_cases c372 : 0 < a6
                      swap
                      · omega
                      by_cases c373 : 0 < b2
                      swap
                      · omega
                      by_cases c374 : a0 + a2 + a4 < b0 + b2
                      swap
                      · -- branch
                        by_cases c375 : 0 < a6
                        swap
                        · omega
                        by_cases c376 : 0 < b6
                        swap
                        · -- branch
                          by_cases c377 : 0 < a2
                          swap
                          · omega
                          by_cases c378 : 0 < b8
                          swap
                          · -- branch
                            by_cases c379 : 0 < a6
                            swap
                            · omega
                            by_cases c380 : 0 < b4
                            swap
                            · omega
                            by_cases c381 : a0 + a2 + a4 < b0 + b2 + b4
                            swap
                            · -- branch
                              by_cases c382 : 0 < a4
                              swap
                              · omega
                              by_cases c383 : 0 < b10
                              swap
                              · omega
                              by_cases c384 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c385 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · omega
                              have f386 := pair_fact E (i := 4) (j := 10) rfl rfl c382 c383
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f386
                              omega
                            by_cases c387 : b0 + b2 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f388 := pair_fact E (i := 6) (j := 4) rfl rfl c379 c380
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f388
                            omega
                          by_cases c389 : a0 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c390 : b0 + b2 + b4 + b6 < a0 + a2
                          swap
                          · -- branch
                            by_cases c391 : 0 < a4
                            swap
                            · -- branch
                              by_cases c392 : 0 < a6
                              swap
                              · omega
                              by_cases c393 : 0 < b4
                              swap
                              · omega
                              by_cases c394 : a0 + a2 + a4 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c395 : b0 + b2 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f396 := pair_fact E (i := 6) (j := 4) rfl rfl c392 c393
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f396
                              omega
                            by_cases c397 : 0 < b0
                            swap
                            · -- branch
                              by_cases c398 : 0 < a4
                              swap
                              · omega
                              by_cases c399 : 0 < b6
                              swap
                              · -- branch
                                by_cases c400 : 0 < a4
                                swap
                                · omega
                                by_cases c401 : 0 < b8
                                swap
                                · omega
                                by_cases c402 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                swap
                                · omega
                                by_cases c403 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c404 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c405 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c406 : a0 + a2 + a4 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c407 : b0 + b2 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f408 := pair_fact E (i := 6) (j := 4) rfl rfl c404 c405
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f408
                                  omega
                                have f409 := pair_fact E (i := 4) (j := 8) rfl rfl c400 c401
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f409
                                omega
                              by_cases c410 : a0 + a2 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c411 : b0 + b2 + b4 < a0 + a2 + a4
                              swap
                              · omega
                              have f412 := pair_fact E (i := 4) (j := 6) rfl rfl c398 c399
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f412
                              omega
                            by_cases c413 : a0 + a2 < 0 + b0
                            swap
                            · omega
                            by_cases c414 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f415 := pair_fact E (i := 4) (j := 0) rfl rfl c391 c397
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f415
                            omega
                          have f416 := pair_fact E (i := 2) (j := 8) rfl rfl c377 c378
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f416
                          omega
                        by_cases c417 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c418 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f419 := pair_fact E (i := 6) (j := 6) rfl rfl c375 c376
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f419
                        omega
                      by_cases c420 : b0 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f421 := pair_fact E (i := 6) (j := 2) rfl rfl c372 c373
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f421
                      omega
                    by_cases c422 : a0 + a2 + a4 < 0 + b0
                    swap
                    · omega
                    by_cases c423 : 0 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f424 := pair_fact E (i := 6) (j := 0) rfl rfl c370 c371
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f424
                    omega
                  have f425 := pair_fact E (i := 2) (j := 10) rfl rfl c366 c367
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f425
                  omega
                by_cases c426 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c427 : b0 + b2 + b4 < a0 + a2
                swap
                · -- branch
                  by_cases c428 : 0 < a2
                  swap
                  · omega
                  by_cases c429 : 0 < b8
                  swap
                  · -- branch
                    by_cases c430 : 0 < a2
                    swap
                    · omega
                    by_cases c431 : 0 < b10
                    swap
                    · omega
                    by_cases c432 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c433 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · -- branch
                      by_cases c434 : 0 < a8
                      swap
                      · omega
                      by_cases c435 : 0 < b0
                      swap
                      · -- branch
                        by_cases c436 : 0 < a8
                        swap
                        · omega
                        by_cases c437 : 0 < b2
                        swap
                        · omega
                        by_cases c438 : a0 + a2 + a4 + a6 < b0 + b2
                        swap
                        · -- branch
                          by_cases c439 : 0 < a8
                          swap
                          · omega
                          by_cases c440 : 0 < b8
                          swap
                          · -- branch
                            by_cases c441 : 0 < a4
                            swap
                            · -- branch
                              by_cases c442 : 0 < a8
                              swap
                              · omega
                              by_cases c443 : 0 < b4
                              swap
                              · omega
                              by_cases c444 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c445 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f446 := pair_fact E (i := 8) (j := 4) rfl rfl c442 c443
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f446
                              omega
                            by_cases c447 : 0 < b0
                            swap
                            · -- branch
                              by_cases c448 : 0 < a4
                              swap
                              · omega
                              by_cases c449 : 0 < b6
                              swap
                              · omega
                              by_cases c450 : a0 + a2 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c451 : b0 + b2 + b4 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c452 : 0 < a4
                                swap
                                · omega
                                by_cases c453 : 0 < b8
                                swap
                                · -- branch
                                  by_cases c454 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c455 : 0 < b10
                                  swap
                                  · omega
                                  by_cases c456 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                  swap
                                  · omega
                                  by_cases c457 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c458 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c459 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c460 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                    swap
                                    · -- branch
                                      by_cases c461 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c462 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c463 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c464 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f465 := pair_fact E (i := 6) (j := 4) rfl rfl c461 c462
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f465
                                      omega
                                    by_cases c466 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f467 := pair_fact E (i := 8) (j := 4) rfl rfl c458 c459
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f467
                                    omega
                                  have f468 := pair_fact E (i := 4) (j := 10) rfl rfl c454 c455
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f468
                                  omega
                                by_cases c469 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                swap
                                · omega
                                by_cases c470 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                swap
                                · omega
                                have f471 := pair_fact E (i := 4) (j := 8) rfl rfl c452 c453
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f471
                                omega
                              have f472 := pair_fact E (i := 4) (j := 6) rfl rfl c448 c449
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f472
                              omega
                            by_cases c473 : a0 + a2 < 0 + b0
                            swap
                            · omega
                            by_cases c474 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f475 := pair_fact E (i := 4) (j := 0) rfl rfl c441 c447
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f475
                            omega
                          by_cases c476 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c477 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f478 := pair_fact E (i := 8) (j := 8) rfl rfl c439 c440
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f478
                          omega
                        by_cases c479 : b0 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f480 := pair_fact E (i := 8) (j := 2) rfl rfl c436 c437
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f480
                        omega
                      by_cases c481 : a0 + a2 + a4 + a6 < 0 + b0
                      swap
                      · omega
                      by_cases c482 : 0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f483 := pair_fact E (i := 8) (j := 0) rfl rfl c434 c435
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f483
                      omega
                    have f484 := pair_fact E (i := 2) (j := 10) rfl rfl c430 c431
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f484
                    omega
                  by_cases c485 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c486 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · -- branch
                    by_cases c487 : 0 < a2
                    swap
                    · omega
                    by_cases c488 : 0 < b10
                    swap
                    · -- branch
                      by_cases c489 : 0 < a10
                      swap
                      · omega
                      by_cases c490 : 0 < b4
                      swap
                      · omega
                      by_cases c491 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c492 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f493 := pair_fact E (i := 10) (j := 4) rfl rfl c489 c490
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f493
                      omega
                    by_cases c494 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c495 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · -- branch
                      by_cases c496 : 0 < a4
                      swap
                      · -- branch
                        by_cases c497 : 0 < a4
                        swap
                        · -- branch
                          by_cases c498 : 0 < a4
                          swap
                          · -- branch
                            by_cases c499 : 0 < a4
                            swap
                            · -- branch
                              by_cases c500 : 0 < a4
                              swap
                              · -- branch
                                by_cases c501 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c502 : 0 < a8
                                  swap
                                  · -- branch
                                    by_cases c503 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c504 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c505 : a0 + a2 + a4 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c506 : b0 + b2 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f507 := pair_fact E (i := 6) (j := 4) rfl rfl c503 c504
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f507
                                    omega
                                  by_cases c508 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c509 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c510 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f511 := pair_fact E (i := 8) (j := 4) rfl rfl c502 c508
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f511
                                  omega
                                by_cases c512 : 0 < b10
                                swap
                                · omega
                                by_cases c513 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c514 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                swap
                                · omega
                                have f515 := pair_fact E (i := 4) (j := 10) rfl rfl c501 c512
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f515
                                omega
                              by_cases c516 : 0 < b8
                              swap
                              · omega
                              by_cases c517 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c518 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · omega
                              have f519 := pair_fact E (i := 4) (j := 8) rfl rfl c500 c516
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f519
                              omega
                            by_cases c520 : 0 < b6
                            swap
                            · omega
                            by_cases c521 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c522 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · omega
                            have f523 := pair_fact E (i := 4) (j := 6) rfl rfl c499 c520
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f523
                            omega
                          by_cases c524 : 0 < b4
                          swap
                          · omega
                          by_cases c525 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c526 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f527 := pair_fact E (i := 4) (j := 4) rfl rfl c498 c524
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f527
                          omega
                        by_cases c528 : 0 < b2
                        swap
                        · omega
                        by_cases c529 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c530 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f531 := pair_fact E (i := 4) (j := 2) rfl rfl c497 c528
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f531
                        omega
                      by_cases c532 : 0 < b0
                      swap
                      · -- branch
                        by_cases c533 : 0 < a4
                        swap
                        · omega
                        by_cases c534 : 0 < b6
                        swap
                        · omega
                        by_cases c535 : a0 + a2 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c536 : b0 + b2 + b4 < a0 + a2 + a4
                        swap
                        · -- branch
                          by_cases c537 : 0 < a4
                          swap
                          · omega
                          by_cases c538 : 0 < b8
                          swap
                          · omega
                          by_cases c539 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c540 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                          swap
                          · -- branch
                            by_cases c541 : 0 < a4
                            swap
                            · omega
                            by_cases c542 : 0 < b10
                            swap
                            · omega
                            by_cases c543 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c544 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c545 : 0 < a10
                              swap
                              · omega
                              by_cases c546 : 0 < b0
                              swap
                              · -- branch
                                by_cases c547 : 0 < a10
                                swap
                                · omega
                                by_cases c548 : 0 < b2
                                swap
                                · omega
                                by_cases c549 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                                swap
                                · -- branch
                                  by_cases c550 : 0 < a10
                                  swap
                                  · omega
                                  by_cases c551 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c552 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                  swap
                                  · -- branch
                                    by_cases c553 : 0 < a6
                                    swap
                                    · -- branch
                                      by_cases c554 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c555 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c556 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c557 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f558 := pair_fact E (i := 8) (j := 4) rfl rfl c554 c555
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f558
                                      omega
                                    by_cases c559 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c560 : a0 + a2 + a4 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c561 : b0 + b2 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f562 := pair_fact E (i := 6) (j := 4) rfl rfl c553 c559
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f562
                                    omega
                                  by_cases c563 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                  swap
                                  · omega
                                  have f564 := pair_fact E (i := 10) (j := 4) rfl rfl c550 c551
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f564
                                  omega
                                by_cases c565 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f566 := pair_fact E (i := 10) (j := 2) rfl rfl c547 c548
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f566
                                omega
                              by_cases c567 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                              swap
                              · omega
                              by_cases c568 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                              swap
                              · omega
                              have f569 := pair_fact E (i := 10) (j := 0) rfl rfl c545 c546
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f569
                              omega
                            have f570 := pair_fact E (i := 4) (j := 10) rfl rfl c541 c542
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f570
                            omega
                          have f571 := pair_fact E (i := 4) (j := 8) rfl rfl c537 c538
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f571
                          omega
                        have f572 := pair_fact E (i := 4) (j := 6) rfl rfl c533 c534
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f572
                        omega
                      by_cases c573 : a0 + a2 < 0 + b0
                      swap
                      · omega
                      by_cases c574 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f575 := pair_fact E (i := 4) (j := 0) rfl rfl c496 c532
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f575
                      omega
                    have f576 := pair_fact E (i := 2) (j := 10) rfl rfl c487 c488
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f576
                    omega
                  have f577 := pair_fact E (i := 2) (j := 8) rfl rfl c428 c429
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f577
                  omega
                have f578 := pair_fact E (i := 2) (j := 6) rfl rfl c364 c365
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f578
                omega
              by_cases c579 : a0 < 0 + b0
              swap
              · omega
              by_cases c580 : 0 < a0 + a2
              swap
              · omega
              have f581 := pair_fact E (i := 2) (j := 0) rfl rfl c7 c183
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f581
              by_cases c582 : 0 < a2
              swap
              · omega
              by_cases c583 : 0 < b2
              swap
              · -- branch
                by_cases c584 : 0 < a2
                swap
                · omega
                by_cases c585 : 0 < b4
                swap
                · -- branch
                  by_cases c586 : 0 < a4
                  swap
                  · omega
                  by_cases c587 : 0 < b0
                  swap
                  · omega
                  by_cases c588 : a0 + a2 < 0 + b0
                  swap
                  · -- branch
                    by_cases c589 : 0 < a2
                    swap
                    · omega
                    by_cases c590 : 0 < b10
                    swap
                    · omega
                    by_cases c591 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c592 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · -- branch
                      by_cases c593 : 0 < a4
                      swap
                      · omega
                      by_cases c594 : 0 < b2
                      swap
                      · -- branch
                        by_cases c595 : 0 < a4
                        swap
                        · omega
                        by_cases c596 : 0 < b4
                        swap
                        · -- branch
                          by_cases c597 : 0 < a4
                          swap
                          · omega
                          by_cases c598 : 0 < b8
                          swap
                          · -- branch
                            by_cases c599 : 0 < a4
                            swap
                            · omega
                            by_cases c600 : 0 < b6
                            swap
                            · omega
                            by_cases c601 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c602 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · omega
                            have f603 := pair_fact E (i := 4) (j := 6) rfl rfl c599 c600
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f603
                            omega
                          by_cases c604 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c605 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                          swap
                          · omega
                          have f606 := pair_fact E (i := 4) (j := 8) rfl rfl c597 c598
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f606
                          omega
                        by_cases c607 : a0 + a2 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c608 : b0 + b2 < a0 + a2 + a4
                        swap
                        · omega
                        have f609 := pair_fact E (i := 4) (j := 4) rfl rfl c595 c596
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f609
                        omega
                      by_cases c610 : a0 + a2 < b0 + b2
                      swap
                      · omega
                      by_cases c611 : b0 < a0 + a2 + a4
                      swap
                      · omega
                      have f612 := pair_fact E (i := 4) (j := 2) rfl rfl c593 c594
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f612
                      omega
                    have f613 := pair_fact E (i := 2) (j := 10) rfl rfl c589 c590
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f613
                    omega
                  by_cases c614 : 0 < a0 + a2 + a4
                  swap
                  · omega
                  have f615 := pair_fact E (i := 4) (j := 0) rfl rfl c586 c587
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f615
                  omega
                by_cases c616 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c617 : b0 + b2 < a0 + a2
                swap
                · -- branch
                  by_cases c618 : 0 < a2
                  swap
                  · omega
                  by_cases c619 : 0 < b6
                  swap
                  · -- branch
                    by_cases c620 : 0 < a6
                    swap
                    · omega
                    by_cases c621 : 0 < b0
                    swap
                    · omega
                    by_cases c622 : a0 + a2 + a4 < 0 + b0
                    swap
                    · -- branch
                      by_cases c623 : 0 < a6
                      swap
                      · omega
                      by_cases c624 : 0 < b2
                      swap
                      · -- branch
                        by_cases c625 : 0 < a6
                        swap
                        · omega
                        by_cases c626 : 0 < b6
                        swap
                        · -- branch
                          by_cases c627 : 0 < a2
                          swap
                          · omega
                          by_cases c628 : 0 < b8
                          swap
                          · -- branch
                            by_cases c629 : 0 < a2
                            swap
                            · omega
                            by_cases c630 : 0 < b10
                            swap
                            · omega
                            by_cases c631 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c632 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                            swap
                            · -- branch
                              by_cases c633 : 0 < a6
                              swap
                              · omega
                              by_cases c634 : 0 < b8
                              swap
                              · -- branch
                                by_cases c635 : 0 < a8
                                swap
                                · omega
                                by_cases c636 : 0 < b0
                                swap
                                · omega
                                by_cases c637 : a0 + a2 + a4 + a6 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c638 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c639 : 0 < b2
                                  swap
                                  · -- branch
                                    by_cases c640 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c641 : 0 < b6
                                    swap
                                    · -- branch
                                      by_cases c642 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c643 : 0 < b8
                                      swap
                                      · -- branch
                                        by_cases c644 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c645 : 0 < a4
                                          swap
                                          · -- branch
                                            by_cases c646 : 0 < a4
                                            swap
                                            · -- branch
                                              by_cases c647 : 0 < a4
                                              swap
                                              · -- branch
                                                by_cases c648 : 0 < a4
                                                swap
                                                · -- branch
                                                  by_cases c649 : 0 < a4
                                                  swap
                                                  · -- branch
                                                    by_cases c650 : 0 < a6
                                                    swap
                                                    · omega
                                                    by_cases c651 : 0 < b4
                                                    swap
                                                    · omega
                                                    by_cases c652 : a0 + a2 + a4 < b0 + b2 + b4
                                                    swap
                                                    · omega
                                                    by_cases c653 : b0 + b2 < a0 + a2 + a4 + a6
                                                    swap
                                                    · omega
                                                    have f654 := pair_fact E (i := 6) (j := 4) rfl rfl c650 c651
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f654
                                                    by_cases c655 : 0 < a8
                                                    swap
                                                    · omega
                                                    by_cases c656 : 0 < b4
                                                    swap
                                                    · omega
                                                    by_cases c657 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                                    swap
                                                    · omega
                                                    by_cases c658 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                                    swap
                                                    · omega
                                                    have f659 := pair_fact E (i := 8) (j := 4) rfl rfl c655 c656
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f659
                                                    omega
                                                  by_cases c660 : 0 < b10
                                                  swap
                                                  · omega
                                                  by_cases c661 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                                  swap
                                                  · omega
                                                  by_cases c662 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                                  swap
                                                  · omega
                                                  have f663 := pair_fact E (i := 4) (j := 10) rfl rfl c649 c660
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f663
                                                  omega
                                                by_cases c664 : 0 < b8
                                                swap
                                                · omega
                                                by_cases c665 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                                swap
                                                · omega
                                                by_cases c666 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                                swap
                                                · omega
                                                have f667 := pair_fact E (i := 4) (j := 8) rfl rfl c648 c664
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f667
                                                omega
                                              by_cases c668 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c669 : a0 + a2 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c670 : b0 + b2 + b4 < a0 + a2 + a4
                                              swap
                                              · omega
                                              have f671 := pair_fact E (i := 4) (j := 6) rfl rfl c647 c668
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f671
                                              omega
                                            by_cases c672 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c673 : a0 + a2 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c674 : b0 + b2 < a0 + a2 + a4
                                            swap
                                            · omega
                                            have f675 := pair_fact E (i := 4) (j := 4) rfl rfl c646 c672
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f675
                                            omega
                                          by_cases c676 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c677 : a0 + a2 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c678 : b0 < a0 + a2 + a4
                                          swap
                                          · omega
                                          have f679 := pair_fact E (i := 4) (j := 2) rfl rfl c645 c676
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f679
                                          omega
                                        by_cases c680 : 0 < b0
                                        swap
                                        · omega
                                        by_cases c681 : a0 + a2 < 0 + b0
                                        swap
                                        · -- branch
                                          by_cases c682 : 0 < a4
                                          swap
                                          · omega
                                          by_cases c683 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c684 : a0 + a2 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c685 : b0 + b2 < a0 + a2 + a4
                                          swap
                                          · omega
                                          have f686 := pair_fact E (i := 4) (j := 4) rfl rfl c682 c683
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f686
                                          omega
                                        by_cases c687 : 0 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f688 := pair_fact E (i := 4) (j := 0) rfl rfl c644 c680
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f688
                                        omega
                                      by_cases c689 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c690 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f691 := pair_fact E (i := 8) (j := 8) rfl rfl c642 c643
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f691
                                      omega
                                    by_cases c692 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c693 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f694 := pair_fact E (i := 8) (j := 6) rfl rfl c640 c641
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f694
                                    omega
                                  by_cases c695 : a0 + a2 + a4 + a6 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c696 : b0 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f697 := pair_fact E (i := 8) (j := 2) rfl rfl c638 c639
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f697
                                  omega
                                by_cases c698 : 0 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f699 := pair_fact E (i := 8) (j := 0) rfl rfl c635 c636
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f699
                                omega
                              by_cases c700 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c701 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f702 := pair_fact E (i := 6) (j := 8) rfl rfl c633 c634
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f702
                              omega
                            have f703 := pair_fact E (i := 2) (j := 10) rfl rfl c629 c630
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f703
                            omega
                          by_cases c704 : a0 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c705 : b0 + b2 + b4 + b6 < a0 + a2
                          swap
                          · -- branch
                            by_cases c706 : 0 < a2
                            swap
                            · omega
                            by_cases c707 : 0 < b10
                            swap
                            · -- branch
                              by_cases c708 : 0 < a4
                              swap
                              · -- branch
                                by_cases c709 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c710 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c711 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c712 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c713 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c714 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c715 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c716 : a0 + a2 + a4 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c717 : b0 + b2 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f718 := pair_fact E (i := 6) (j := 4) rfl rfl c714 c715
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f718
                                          by_cases c719 : 0 < a10
                                          swap
                                          · omega
                                          by_cases c720 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c721 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c722 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                          swap
                                          · omega
                                          have f723 := pair_fact E (i := 10) (j := 4) rfl rfl c719 c720
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f723
                                          omega
                                        by_cases c724 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c725 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c726 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f727 := pair_fact E (i := 4) (j := 10) rfl rfl c713 c724
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f727
                                        omega
                                      by_cases c728 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c729 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c730 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f731 := pair_fact E (i := 4) (j := 8) rfl rfl c712 c728
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f731
                                      omega
                                    by_cases c732 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c733 : a0 + a2 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c734 : b0 + b2 + b4 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f735 := pair_fact E (i := 4) (j := 6) rfl rfl c711 c732
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f735
                                    omega
                                  by_cases c736 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c737 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c738 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f739 := pair_fact E (i := 4) (j := 4) rfl rfl c710 c736
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f739
                                  omega
                                by_cases c740 : 0 < b2
                                swap
                                · omega
                                by_cases c741 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c742 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f743 := pair_fact E (i := 4) (j := 2) rfl rfl c709 c740
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f743
                                omega
                              by_cases c744 : 0 < b0
                              swap
                              · omega
                              by_cases c745 : a0 + a2 < 0 + b0
                              swap
                              · omega
                              by_cases c746 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f747 := pair_fact E (i := 4) (j := 0) rfl rfl c708 c744
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f747
                              omega
                            by_cases c748 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c749 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                            swap
                            · -- branch
                              by_cases c750 : 0 < a4
                              swap
                              · -- branch
                                by_cases c751 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c752 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c753 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c754 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c755 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c756 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c757 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c758 : a0 + a2 + a4 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c759 : b0 + b2 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f760 := pair_fact E (i := 6) (j := 4) rfl rfl c756 c757
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f760
                                          by_cases c761 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c762 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c763 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c764 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f765 := pair_fact E (i := 8) (j := 4) rfl rfl c761 c762
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f765
                                          omega
                                        by_cases c766 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c767 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c768 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f769 := pair_fact E (i := 4) (j := 10) rfl rfl c755 c766
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f769
                                        omega
                                      by_cases c770 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c771 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c772 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f773 := pair_fact E (i := 4) (j := 8) rfl rfl c754 c770
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f773
                                      omega
                                    by_cases c774 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c775 : a0 + a2 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c776 : b0 + b2 + b4 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f777 := pair_fact E (i := 4) (j := 6) rfl rfl c753 c774
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f777
                                    omega
                                  by_cases c778 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c779 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c780 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f781 := pair_fact E (i := 4) (j := 4) rfl rfl c752 c778
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f781
                                  omega
                                by_cases c782 : 0 < b2
                                swap
                                · omega
                                by_cases c783 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c784 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f785 := pair_fact E (i := 4) (j := 2) rfl rfl c751 c782
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f785
                                omega
                              by_cases c786 : 0 < b0
                              swap
                              · omega
                              by_cases c787 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c788 : 0 < a4
                                swap
                                · omega
                                by_cases c789 : 0 < b4
                                swap
                                · omega
                                by_cases c790 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c791 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f792 := pair_fact E (i := 4) (j := 4) rfl rfl c788 c789
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f792
                                omega
                              by_cases c793 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f794 := pair_fact E (i := 4) (j := 0) rfl rfl c750 c786
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f794
                              omega
                            have f795 := pair_fact E (i := 2) (j := 10) rfl rfl c706 c707
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f795
                            omega
                          have f796 := pair_fact E (i := 2) (j := 8) rfl rfl c627 c628
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f796
                          omega
                        by_cases c797 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c798 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f799 := pair_fact E (i := 6) (j := 6) rfl rfl c625 c626
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f799
                        omega
                      by_cases c800 : a0 + a2 + a4 < b0 + b2
                      swap
                      · omega
                      by_cases c801 : b0 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f802 := pair_fact E (i := 6) (j := 2) rfl rfl c623 c624
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f802
                      omega
                    by_cases c803 : 0 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f804 := pair_fact E (i := 6) (j := 0) rfl rfl c620 c621
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f804
                    omega
                  by_cases c805 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c806 : b0 + b2 + b4 < a0 + a2
                  swap
                  · -- branch
                    by_cases c807 : 0 < a2
                    swap
                    · omega
                    by_cases c808 : 0 < b8
                    swap
                    · -- branch
                      by_cases c809 : 0 < a8
                      swap
                      · omega
                      by_cases c810 : 0 < b0
                      swap
                      · omega
                      by_cases c811 : a0 + a2 + a4 + a6 < 0 + b0
                      swap
                      · -- branch
                        by_cases c812 : 0 < a8
                        swap
                        · omega
                        by_cases c813 : 0 < b2
                        swap
                        · -- branch
                          by_cases c814 : 0 < a8
                          swap
                          · omega
                          by_cases c815 : 0 < b8
                          swap
                          · -- branch
                            by_cases c816 : 0 < a2
                            swap
                            · omega
                            by_cases c817 : 0 < b10
                            swap
                            · -- branch
                              by_cases c818 : 0 < a4
                              swap
                              · -- branch
                                by_cases c819 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c820 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c821 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c822 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c823 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c824 : 0 < a6
                                          swap
                                          · -- branch
                                            by_cases c825 : 0 < a6
                                            swap
                                            · -- branch
                                              by_cases c826 : 0 < a6
                                              swap
                                              · -- branch
                                                by_cases c827 : 0 < a6
                                                swap
                                                · -- branch
                                                  by_cases c828 : 0 < a6
                                                  swap
                                                  · -- branch
                                                    by_cases c829 : 0 < a6
                                                    swap
                                                    · -- branch
                                                      by_cases c830 : 0 < a8
                                                      swap
                                                      · omega
                                                      by_cases c831 : 0 < b4
                                                      swap
                                                      · omega
                                                      by_cases c832 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                                      swap
                                                      · omega
                                                      by_cases c833 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                                      swap
                                                      · omega
                                                      have f834 := pair_fact E (i := 8) (j := 4) rfl rfl c830 c831
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f834
                                                      by_cases c835 : 0 < a10
                                                      swap
                                                      · omega
                                                      by_cases c836 : 0 < b4
                                                      swap
                                                      · omega
                                                      by_cases c837 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                                      swap
                                                      · omega
                                                      by_cases c838 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                                      swap
                                                      · omega
                                                      have f839 := pair_fact E (i := 10) (j := 4) rfl rfl c835 c836
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f839
                                                      omega
                                                    by_cases c840 : 0 < b10
                                                    swap
                                                    · omega
                                                    by_cases c841 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                                    swap
                                                    · omega
                                                    by_cases c842 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                                    swap
                                                    · omega
                                                    have f843 := pair_fact E (i := 6) (j := 10) rfl rfl c829 c840
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f843
                                                    omega
                                                  by_cases c844 : 0 < b8
                                                  swap
                                                  · omega
                                                  by_cases c845 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                                  swap
                                                  · omega
                                                  by_cases c846 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                                  swap
                                                  · omega
                                                  have f847 := pair_fact E (i := 6) (j := 8) rfl rfl c828 c844
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f847
                                                  omega
                                                by_cases c848 : 0 < b6
                                                swap
                                                · omega
                                                by_cases c849 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                                swap
                                                · omega
                                                by_cases c850 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                                swap
                                                · omega
                                                have f851 := pair_fact E (i := 6) (j := 6) rfl rfl c827 c848
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f851
                                                omega
                                              by_cases c852 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c853 : a0 + a2 + a4 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c854 : b0 + b2 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f855 := pair_fact E (i := 6) (j := 4) rfl rfl c826 c852
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f855
                                              omega
                                            by_cases c856 : 0 < b2
                                            swap
                                            · omega
                                            by_cases c857 : a0 + a2 + a4 < b0 + b2
                                            swap
                                            · omega
                                            by_cases c858 : b0 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f859 := pair_fact E (i := 6) (j := 2) rfl rfl c825 c856
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f859
                                            omega
                                          by_cases c860 : 0 < b0
                                          swap
                                          · omega
                                          by_cases c861 : a0 + a2 + a4 < 0 + b0
                                          swap
                                          · omega
                                          by_cases c862 : 0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f863 := pair_fact E (i := 6) (j := 0) rfl rfl c824 c860
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f863
                                          omega
                                        by_cases c864 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c865 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c866 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f867 := pair_fact E (i := 4) (j := 10) rfl rfl c823 c864
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f867
                                        omega
                                      by_cases c868 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c869 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c870 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f871 := pair_fact E (i := 4) (j := 8) rfl rfl c822 c868
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f871
                                      omega
                                    by_cases c872 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c873 : a0 + a2 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c874 : b0 + b2 + b4 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f875 := pair_fact E (i := 4) (j := 6) rfl rfl c821 c872
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f875
                                    omega
                                  by_cases c876 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c877 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c878 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f879 := pair_fact E (i := 4) (j := 4) rfl rfl c820 c876
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f879
                                  omega
                                by_cases c880 : 0 < b2
                                swap
                                · omega
                                by_cases c881 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c882 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f883 := pair_fact E (i := 4) (j := 2) rfl rfl c819 c880
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f883
                                omega
                              by_cases c884 : 0 < b0
                              swap
                              · omega
                              by_cases c885 : a0 + a2 < 0 + b0
                              swap
                              · omega
                              by_cases c886 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f887 := pair_fact E (i := 4) (j := 0) rfl rfl c818 c884
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f887
                              omega
                            by_cases c888 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c889 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                            swap
                            · -- branch
                              by_cases c890 : 0 < a4
                              swap
                              · -- branch
                                by_cases c891 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c892 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c893 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c894 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c895 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c896 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c897 : 0 < b0
                                          swap
                                          · omega
                                          by_cases c898 : a0 + a2 + a4 < 0 + b0
                                          swap
                                          · -- branch
                                            by_cases c899 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c900 : 0 < b2
                                            swap
                                            · -- branch
                                              by_cases c901 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c902 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c903 : a0 + a2 + a4 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c904 : b0 + b2 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f905 := pair_fact E (i := 6) (j := 4) rfl rfl c901 c902
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f905
                                              by_cases c906 : 0 < a8
                                              swap
                                              · omega
                                              by_cases c907 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c908 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c909 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                              swap
                                              · omega
                                              have f910 := pair_fact E (i := 8) (j := 4) rfl rfl c906 c907
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f910
                                              omega
                                            by_cases c911 : a0 + a2 + a4 < b0 + b2
                                            swap
                                            · omega
                                            by_cases c912 : b0 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f913 := pair_fact E (i := 6) (j := 2) rfl rfl c899 c900
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f913
                                            omega
                                          by_cases c914 : 0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f915 := pair_fact E (i := 6) (j := 0) rfl rfl c896 c897
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f915
                                          omega
                                        by_cases c916 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c917 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c918 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f919 := pair_fact E (i := 4) (j := 10) rfl rfl c895 c916
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f919
                                        omega
                                      by_cases c920 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c921 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c922 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f923 := pair_fact E (i := 4) (j := 8) rfl rfl c894 c920
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f923
                                      omega
                                    by_cases c924 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c925 : a0 + a2 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c926 : b0 + b2 + b4 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f927 := pair_fact E (i := 4) (j := 6) rfl rfl c893 c924
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f927
                                    omega
                                  by_cases c928 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c929 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c930 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f931 := pair_fact E (i := 4) (j := 4) rfl rfl c892 c928
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f931
                                  omega
                                by_cases c932 : 0 < b2
                                swap
                                · omega
                                by_cases c933 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c934 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f935 := pair_fact E (i := 4) (j := 2) rfl rfl c891 c932
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f935
                                omega
                              by_cases c936 : 0 < b0
                              swap
                              · omega
                              by_cases c937 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c938 : 0 < a4
                                swap
                                · omega
                                by_cases c939 : 0 < b4
                                swap
                                · omega
                                by_cases c940 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c941 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f942 := pair_fact E (i := 4) (j := 4) rfl rfl c938 c939
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f942
                                omega
                              by_cases c943 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f944 := pair_fact E (i := 4) (j := 0) rfl rfl c890 c936
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f944
                              omega
                            have f945 := pair_fact E (i := 2) (j := 10) rfl rfl c816 c817
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f945
                            omega
                          by_cases c946 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c947 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f948 := pair_fact E (i := 8) (j := 8) rfl rfl c814 c815
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f948
                          omega
                        by_cases c949 : a0 + a2 + a4 + a6 < b0 + b2
                        swap
                        · omega
                        by_cases c950 : b0 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f951 := pair_fact E (i := 8) (j := 2) rfl rfl c812 c813
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f951
                        omega
                      by_cases c952 : 0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f953 := pair_fact E (i := 8) (j := 0) rfl rfl c809 c810
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f953
                      omega
                    by_cases c954 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c955 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · -- branch
                      by_cases c956 : 0 < a2
                      swap
                      · omega
                      by_cases c957 : 0 < b10
                      swap
                      · -- branch
                        by_cases c958 : 0 < a4
                        swap
                        · -- branch
                          by_cases c959 : 0 < a4
                          swap
                          · -- branch
                            by_cases c960 : 0 < a4
                            swap
                            · -- branch
                              by_cases c961 : 0 < a4
                              swap
                              · -- branch
                                by_cases c962 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c963 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c964 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c965 : 0 < b0
                                    swap
                                    · omega
                                    by_cases c966 : a0 + a2 + a4 < 0 + b0
                                    swap
                                    · -- branch
                                      by_cases c967 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c968 : 0 < b2
                                      swap
                                      · -- branch
                                        by_cases c969 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c970 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c971 : a0 + a2 + a4 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c972 : b0 + b2 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f973 := pair_fact E (i := 6) (j := 4) rfl rfl c969 c970
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f973
                                        by_cases c974 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c975 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c976 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c977 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f978 := pair_fact E (i := 8) (j := 4) rfl rfl c974 c975
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f978
                                        omega
                                      by_cases c979 : a0 + a2 + a4 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c980 : b0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f981 := pair_fact E (i := 6) (j := 2) rfl rfl c967 c968
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f981
                                      omega
                                    by_cases c982 : 0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f983 := pair_fact E (i := 6) (j := 0) rfl rfl c964 c965
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f983
                                    omega
                                  by_cases c984 : 0 < b10
                                  swap
                                  · omega
                                  by_cases c985 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                  swap
                                  · omega
                                  by_cases c986 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f987 := pair_fact E (i := 4) (j := 10) rfl rfl c963 c984
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f987
                                  omega
                                by_cases c988 : 0 < b8
                                swap
                                · omega
                                by_cases c989 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                swap
                                · omega
                                by_cases c990 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                swap
                                · omega
                                have f991 := pair_fact E (i := 4) (j := 8) rfl rfl c962 c988
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f991
                                omega
                              by_cases c992 : 0 < b6
                              swap
                              · omega
                              by_cases c993 : a0 + a2 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c994 : b0 + b2 + b4 < a0 + a2 + a4
                              swap
                              · omega
                              have f995 := pair_fact E (i := 4) (j := 6) rfl rfl c961 c992
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f995
                              omega
                            by_cases c996 : 0 < b4
                            swap
                            · omega
                            by_cases c997 : a0 + a2 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c998 : b0 + b2 < a0 + a2 + a4
                            swap
                            · omega
                            have f999 := pair_fact E (i := 4) (j := 4) rfl rfl c960 c996
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f999
                            omega
                          by_cases c1000 : 0 < b2
                          swap
                          · omega
                          by_cases c1001 : a0 + a2 < b0 + b2
                          swap
                          · omega
                          by_cases c1002 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f1003 := pair_fact E (i := 4) (j := 2) rfl rfl c959 c1000
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1003
                          omega
                        by_cases c1004 : 0 < b0
                        swap
                        · omega
                        by_cases c1005 : a0 + a2 < 0 + b0
                        swap
                        · -- branch
                          by_cases c1006 : 0 < a4
                          swap
                          · omega
                          by_cases c1007 : 0 < b4
                          swap
                          · omega
                          by_cases c1008 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1009 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f1010 := pair_fact E (i := 4) (j := 4) rfl rfl c1006 c1007
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1010
                          omega
                        by_cases c1011 : 0 < a0 + a2 + a4
                        swap
                        · omega
                        have f1012 := pair_fact E (i := 4) (j := 0) rfl rfl c958 c1004
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1012
                        omega
                      by_cases c1013 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                      swap
                      · omega
                      by_cases c1014 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                      swap
                      · -- branch
                        by_cases c1015 : 0 < a4
                        swap
                        · -- branch
                          by_cases c1016 : 0 < a4
                          swap
                          · -- branch
                            by_cases c1017 : 0 < a4
                            swap
                            · -- branch
                              by_cases c1018 : 0 < a4
                              swap
                              · -- branch
                                by_cases c1019 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c1020 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c1021 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c1022 : 0 < b0
                                    swap
                                    · omega
                                    by_cases c1023 : a0 + a2 + a4 < 0 + b0
                                    swap
                                    · -- branch
                                      by_cases c1024 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c1025 : 0 < b2
                                      swap
                                      · -- branch
                                        by_cases c1026 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c1027 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c1028 : a0 + a2 + a4 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c1029 : b0 + b2 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f1030 := pair_fact E (i := 6) (j := 4) rfl rfl c1026 c1027
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1030
                                        by_cases c1031 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c1032 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c1033 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c1034 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f1035 := pair_fact E (i := 8) (j := 4) rfl rfl c1031 c1032
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1035
                                        omega
                                      by_cases c1036 : a0 + a2 + a4 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c1037 : b0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f1038 := pair_fact E (i := 6) (j := 2) rfl rfl c1024 c1025
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1038
                                      omega
                                    by_cases c1039 : 0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f1040 := pair_fact E (i := 6) (j := 0) rfl rfl c1021 c1022
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1040
                                    omega
                                  by_cases c1041 : 0 < b10
                                  swap
                                  · omega
                                  by_cases c1042 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                  swap
                                  · omega
                                  by_cases c1043 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f1044 := pair_fact E (i := 4) (j := 10) rfl rfl c1020 c1041
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1044
                                  omega
                                by_cases c1045 : 0 < b8
                                swap
                                · omega
                                by_cases c1046 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                swap
                                · omega
                                by_cases c1047 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                swap
                                · omega
                                have f1048 := pair_fact E (i := 4) (j := 8) rfl rfl c1019 c1045
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1048
                                omega
                              by_cases c1049 : 0 < b6
                              swap
                              · omega
                              by_cases c1050 : a0 + a2 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c1051 : b0 + b2 + b4 < a0 + a2 + a4
                              swap
                              · omega
                              have f1052 := pair_fact E (i := 4) (j := 6) rfl rfl c1018 c1049
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1052
                              omega
                            by_cases c1053 : 0 < b4
                            swap
                            · omega
                            by_cases c1054 : a0 + a2 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c1055 : b0 + b2 < a0 + a2 + a4
                            swap
                            · omega
                            have f1056 := pair_fact E (i := 4) (j := 4) rfl rfl c1017 c1053
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1056
                            omega
                          by_cases c1057 : 0 < b2
                          swap
                          · omega
                          by_cases c1058 : a0 + a2 < b0 + b2
                          swap
                          · omega
                          by_cases c1059 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f1060 := pair_fact E (i := 4) (j := 2) rfl rfl c1016 c1057
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1060
                          omega
                        by_cases c1061 : 0 < b0
                        swap
                        · omega
                        by_cases c1062 : a0 + a2 < 0 + b0
                        swap
                        · -- branch
                          by_cases c1063 : 0 < a4
                          swap
                          · omega
                          by_cases c1064 : 0 < b4
                          swap
                          · omega
                          by_cases c1065 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1066 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f1067 := pair_fact E (i := 4) (j := 4) rfl rfl c1063 c1064
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1067
                          omega
                        by_cases c1068 : 0 < a0 + a2 + a4
                        swap
                        · omega
                        have f1069 := pair_fact E (i := 4) (j := 0) rfl rfl c1015 c1061
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1069
                        omega
                      have f1070 := pair_fact E (i := 2) (j := 10) rfl rfl c956 c957
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1070
                      omega
                    have f1071 := pair_fact E (i := 2) (j := 8) rfl rfl c807 c808
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1071
                    omega
                  have f1072 := pair_fact E (i := 2) (j := 6) rfl rfl c618 c619
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1072
                  omega
                have f1073 := pair_fact E (i := 2) (j := 4) rfl rfl c584 c585
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1073
                omega
              by_cases c1074 : a0 < b0 + b2
              swap
              · omega
              by_cases c1075 : b0 < a0 + a2
              swap
              · -- branch
                by_cases c1076 : 0 < a2
                swap
                · omega
                by_cases c1077 : 0 < b4
                swap
                · -- branch
                  by_cases c1078 : 0 < a4
                  swap
                  · omega
                  by_cases c1079 : 0 < b0
                  swap
                  · omega
                  by_cases c1080 : a0 + a2 < 0 + b0
                  swap
                  · -- branch
                    by_cases c1081 : 0 < a4
                    swap
                    · omega
                    by_cases c1082 : 0 < b2
                    swap
                    · omega
                    by_cases c1083 : a0 + a2 < b0 + b2
                    swap
                    · omega
                    by_cases c1084 : b0 < a0 + a2 + a4
                    swap
                    · omega
                    have f1085 := pair_fact E (i := 4) (j := 2) rfl rfl c1081 c1082
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1085
                    omega
                  by_cases c1086 : 0 < a0 + a2 + a4
                  swap
                  · omega
                  have f1087 := pair_fact E (i := 4) (j := 0) rfl rfl c1078 c1079
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1087
                  omega
                by_cases c1088 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c1089 : b0 + b2 < a0 + a2
                swap
                · -- branch
                  by_cases c1090 : 0 < a2
                  swap
                  · omega
                  by_cases c1091 : 0 < b6
                  swap
                  · -- branch
                    by_cases c1092 : 0 < a6
                    swap
                    · omega
                    by_cases c1093 : 0 < b0
                    swap
                    · omega
                    by_cases c1094 : a0 + a2 + a4 < 0 + b0
                    swap
                    · -- branch
                      by_cases c1095 : 0 < a6
                      swap
                      · omega
                      by_cases c1096 : 0 < b2
                      swap
                      · omega
                      by_cases c1097 : a0 + a2 + a4 < b0 + b2
                      swap
                      · -- branch
                        by_cases c1098 : 0 < a4
                        swap
                        · omega
                        by_cases c1099 : 0 < b2
                        swap
                        · omega
                        by_cases c1100 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c1101 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f1102 := pair_fact E (i := 4) (j := 2) rfl rfl c1098 c1099
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1102
                        omega
                      by_cases c1103 : b0 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f1104 := pair_fact E (i := 6) (j := 2) rfl rfl c1095 c1096
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1104
                      omega
                    by_cases c1105 : 0 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f1106 := pair_fact E (i := 6) (j := 0) rfl rfl c1092 c1093
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1106
                    omega
                  by_cases c1107 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c1108 : b0 + b2 + b4 < a0 + a2
                  swap
                  · -- branch
                    by_cases c1109 : 0 < a2
                    swap
                    · omega
                    by_cases c1110 : 0 < b8
                    swap
                    · -- branch
                      by_cases c1111 : 0 < a8
                      swap
                      · omega
                      by_cases c1112 : 0 < b0
                      swap
                      · omega
                      by_cases c1113 : a0 + a2 + a4 + a6 < 0 + b0
                      swap
                      · -- branch
                        by_cases c1114 : 0 < a8
                        swap
                        · omega
                        by_cases c1115 : 0 < b2
                        swap
                        · omega
                        by_cases c1116 : a0 + a2 + a4 + a6 < b0 + b2
                        swap
                        · -- branch
                          by_cases c1117 : 0 < a2
                          swap
                          · omega
                          by_cases c1118 : 0 < b10
                          swap
                          · omega
                          by_cases c1119 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c1120 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · -- branch
                            by_cases c1121 : 0 < a8
                            swap
                            · omega
                            by_cases c1122 : 0 < b8
                            swap
                            · -- branch
                              by_cases c1123 : 0 < a4
                              swap
                              · -- branch
                                by_cases c1124 : 0 < a6
                                swap
                                · omega
                                by_cases c1125 : 0 < b2
                                swap
                                · omega
                                by_cases c1126 : a0 + a2 + a4 < b0 + b2
                                swap
                                · omega
                                by_cases c1127 : b0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f1128 := pair_fact E (i := 6) (j := 2) rfl rfl c1124 c1125
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1128
                                omega
                              by_cases c1129 : 0 < b0
                              swap
                              · omega
                              by_cases c1130 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c1131 : 0 < a4
                                swap
                                · omega
                                by_cases c1132 : 0 < b2
                                swap
                                · omega
                                by_cases c1133 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c1134 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f1135 := pair_fact E (i := 4) (j := 2) rfl rfl c1131 c1132
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1135
                                omega
                              by_cases c1136 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f1137 := pair_fact E (i := 4) (j := 0) rfl rfl c1123 c1129
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1137
                              omega
                            by_cases c1138 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1139 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f1140 := pair_fact E (i := 8) (j := 8) rfl rfl c1121 c1122
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1140
                            omega
                          have f1141 := pair_fact E (i := 2) (j := 10) rfl rfl c1117 c1118
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1141
                          omega
                        by_cases c1142 : b0 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f1143 := pair_fact E (i := 8) (j := 2) rfl rfl c1114 c1115
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1143
                        omega
                      by_cases c1144 : 0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f1145 := pair_fact E (i := 8) (j := 0) rfl rfl c1111 c1112
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1145
                      omega
                    by_cases c1146 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c1147 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · -- branch
                      by_cases c1148 : 0 < a2
                      swap
                      · omega
                      by_cases c1149 : 0 < b10
                      swap
                      · -- branch
                        by_cases c1150 : 0 < a4
                        swap
                        · -- branch
                          by_cases c1151 : 0 < a6
                          swap
                          · omega
                          by_cases c1152 : 0 < b2
                          swap
                          · omega
                          by_cases c1153 : a0 + a2 + a4 < b0 + b2
                          swap
                          · omega
                          by_cases c1154 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f1155 := pair_fact E (i := 6) (j := 2) rfl rfl c1151 c1152
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1155
                          omega
                        by_cases c1156 : 0 < b0
                        swap
                        · omega
                        by_cases c1157 : a0 + a2 < 0 + b0
                        swap
                        · -- branch
                          by_cases c1158 : 0 < a4
                          swap
                          · omega
                          by_cases c1159 : 0 < b2
                          swap
                          · omega
                          by_cases c1160 : a0 + a2 < b0 + b2
                          swap
                          · omega
                          by_cases c1161 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f1162 := pair_fact E (i := 4) (j := 2) rfl rfl c1158 c1159
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1162
                          omega
                        by_cases c1163 : 0 < a0 + a2 + a4
                        swap
                        · omega
                        have f1164 := pair_fact E (i := 4) (j := 0) rfl rfl c1150 c1156
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1164
                        omega
                      by_cases c1165 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                      swap
                      · omega
                      by_cases c1166 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                      swap
                      · -- branch
                        by_cases c1167 : 0 < a4
                        swap
                        · -- branch
                          by_cases c1168 : 0 < a6
                          swap
                          · omega
                          by_cases c1169 : 0 < b2
                          swap
                          · omega
                          by_cases c1170 : a0 + a2 + a4 < b0 + b2
                          swap
                          · omega
                          by_cases c1171 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f1172 := pair_fact E (i := 6) (j := 2) rfl rfl c1168 c1169
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1172
                          omega
                        by_cases c1173 : 0 < b0
                        swap
                        · omega
                        by_cases c1174 : a0 + a2 < 0 + b0
                        swap
                        · -- branch
                          by_cases c1175 : 0 < a4
                          swap
                          · omega
                          by_cases c1176 : 0 < b2
                          swap
                          · omega
                          by_cases c1177 : a0 + a2 < b0 + b2
                          swap
                          · omega
                          by_cases c1178 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f1179 := pair_fact E (i := 4) (j := 2) rfl rfl c1175 c1176
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1179
                          omega
                        by_cases c1180 : 0 < a0 + a2 + a4
                        swap
                        · omega
                        have f1181 := pair_fact E (i := 4) (j := 0) rfl rfl c1167 c1173
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1181
                        omega
                      have f1182 := pair_fact E (i := 2) (j := 10) rfl rfl c1148 c1149
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1182
                      omega
                    have f1183 := pair_fact E (i := 2) (j := 8) rfl rfl c1109 c1110
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1183
                    omega
                  have f1184 := pair_fact E (i := 2) (j := 6) rfl rfl c1090 c1091
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1184
                  omega
                have f1185 := pair_fact E (i := 2) (j := 4) rfl rfl c1076 c1077
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1185
                omega
              have f1186 := pair_fact E (i := 2) (j := 2) rfl rfl c582 c583
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1186
              omega
            by_cases c1187 : 0 < b10
            swap
            · omega
            by_cases c1188 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c1189 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · omega
            have f1190 := pair_fact E (i := 0) (j := 10) rfl rfl c6 c1187
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1190
            omega
          by_cases c1191 : 0 < b8
          swap
          · omega
          by_cases c1192 : 0 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c1193 : b0 + b2 + b4 + b6 < 0 + a0
          swap
          · omega
          have f1194 := pair_fact E (i := 0) (j := 8) rfl rfl c5 c1191
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1194
          omega
        by_cases c1195 : 0 < b6
        swap
        · omega
        by_cases c1196 : 0 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c1197 : b0 + b2 + b4 < 0 + a0
        swap
        · omega
        have f1198 := pair_fact E (i := 0) (j := 6) rfl rfl c4 c1195
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1198
        omega
      by_cases c1199 : 0 < b4
      swap
      · omega
      by_cases c1200 : 0 < b0 + b2 + b4
      swap
      · omega
      by_cases c1201 : b0 + b2 < 0 + a0
      swap
      · omega
      have f1202 := pair_fact E (i := 0) (j := 4) rfl rfl c3 c1199
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1202
      omega
    by_cases c1203 : 0 < b2
    swap
    · omega
    by_cases c1204 : 0 < b0 + b2
    swap
    · omega
    by_cases c1205 : b0 < 0 + a0
    swap
    · omega
    have f1206 := pair_fact E (i := 0) (j := 2) rfl rfl c2 c1203
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1206
    omega
  by_cases c1207 : 0 < b0
  swap
  · -- branch
    by_cases c1208 : 0 < a0
    swap
    · omega
    by_cases c1209 : 0 < b2
    swap
    · -- branch
      by_cases c1210 : 0 < a0
      swap
      · omega
      by_cases c1211 : 0 < b4
      swap
      · -- branch
        by_cases c1212 : 0 < a0
        swap
        · omega
        by_cases c1213 : 0 < b6
        swap
        · omega
        by_cases c1214 : 0 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c1215 : b0 + b2 + b4 < 0 + a0
        swap
        · omega
        have f1216 := pair_fact E (i := 0) (j := 6) rfl rfl c1212 c1213
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1216
        omega
      by_cases c1217 : 0 < b0 + b2 + b4
      swap
      · omega
      by_cases c1218 : b0 + b2 < 0 + a0
      swap
      · omega
      have f1219 := pair_fact E (i := 0) (j := 4) rfl rfl c1210 c1211
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1219
      omega
    by_cases c1220 : 0 < b0 + b2
    swap
    · omega
    by_cases c1221 : b0 < 0 + a0
    swap
    · omega
    have f1222 := pair_fact E (i := 0) (j := 2) rfl rfl c1208 c1209
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1222
    by_cases c1223 : 0 < a0
    swap
    · omega
    by_cases c1224 : 0 < b4
    swap
    · -- branch
      by_cases c1225 : 0 < a0
      swap
      · omega
      by_cases c1226 : 0 < b10
      swap
      · omega
      by_cases c1227 : 0 < b0 + b2 + b4 + b6 + b8 + b10
      swap
      · omega
      by_cases c1228 : b0 + b2 + b4 + b6 + b8 < 0 + a0
      swap
      · -- branch
        by_cases c1229 : 0 < a4
        swap
        · omega
        by_cases c1230 : 0 < b0
        swap
        · -- branch
          by_cases c1231 : 0 < a4
          swap
          · omega
          by_cases c1232 : 0 < b2
          swap
          · omega
          by_cases c1233 : a0 + a2 < b0 + b2
          swap
          · -- branch
            by_cases c1234 : 0 < a4
            swap
            · omega
            by_cases c1235 : 0 < b4
            swap
            · -- branch
              by_cases c1236 : 0 < a0
              swap
              · omega
              by_cases c1237 : 0 < b6
              swap
              · -- branch
                by_cases c1238 : 0 < a0
                swap
                · omega
                by_cases c1239 : 0 < b8
                swap
                · omega
                by_cases c1240 : 0 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c1241 : b0 + b2 + b4 + b6 < 0 + a0
                swap
                · -- branch
                  by_cases c1242 : 0 < a4
                  swap
                  · omega
                  by_cases c1243 : 0 < b6
                  swap
                  · -- branch
                    by_cases c1244 : 0 < a4
                    swap
                    · omega
                    by_cases c1245 : 0 < b8
                    swap
                    · omega
                    by_cases c1246 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c1247 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                    swap
                    · omega
                    have f1248 := pair_fact E (i := 4) (j := 8) rfl rfl c1244 c1245
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1248
                    by_cases c1249 : 0 < a4
                    swap
                    · omega
                    by_cases c1250 : 0 < b10
                    swap
                    · omega
                    by_cases c1251 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c1252 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                    swap
                    · omega
                    have f1253 := pair_fact E (i := 4) (j := 10) rfl rfl c1249 c1250
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1253
                    omega
                  by_cases c1254 : a0 + a2 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c1255 : b0 + b2 + b4 < a0 + a2 + a4
                  swap
                  · omega
                  have f1256 := pair_fact E (i := 4) (j := 6) rfl rfl c1242 c1243
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1256
                  omega
                have f1257 := pair_fact E (i := 0) (j := 8) rfl rfl c1238 c1239
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1257
                omega
              by_cases c1258 : 0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c1259 : b0 + b2 + b4 < 0 + a0
              swap
              · -- branch
                by_cases c1260 : 0 < a0
                swap
                · omega
                by_cases c1261 : 0 < b8
                swap
                · -- branch
                  by_cases c1262 : 0 < a4
                  swap
                  · omega
                  by_cases c1263 : 0 < b6
                  swap
                  · omega
                  by_cases c1264 : a0 + a2 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c1265 : b0 + b2 + b4 < a0 + a2 + a4
                  swap
                  · omega
                  have f1266 := pair_fact E (i := 4) (j := 6) rfl rfl c1262 c1263
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1266
                  by_cases c1267 : 0 < a4
                  swap
                  · omega
                  by_cases c1268 : 0 < b10
                  swap
                  · omega
                  by_cases c1269 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c1270 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                  swap
                  · omega
                  have f1271 := pair_fact E (i := 4) (j := 10) rfl rfl c1267 c1268
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1271
                  omega
                by_cases c1272 : 0 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c1273 : b0 + b2 + b4 + b6 < 0 + a0
                swap
                · -- branch
                  by_cases c1274 : 0 < a4
                  swap
                  · omega
                  by_cases c1275 : 0 < b8
                  swap
                  · omega
                  by_cases c1276 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c1277 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                  swap
                  · omega
                  have f1278 := pair_fact E (i := 4) (j := 8) rfl rfl c1274 c1275
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1278
                  by_cases c1279 : 0 < a4
                  swap
                  · omega
                  by_cases c1280 : 0 < b6
                  swap
                  · omega
                  by_cases c1281 : a0 + a2 < b0 + b2 + b4 + b6
                  swap
                  · -- branch
                    by_cases c1282 : 0 < a2
                    swap
                    · omega
                    by_cases c1283 : 0 < b6
                    swap
                    · omega
                    by_cases c1284 : a0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c1285 : b0 + b2 + b4 < a0 + a2
                    swap
                    · omega
                    have f1286 := pair_fact E (i := 2) (j := 6) rfl rfl c1282 c1283
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1286
                    omega
                  by_cases c1287 : b0 + b2 + b4 < a0 + a2 + a4
                  swap
                  · omega
                  have f1288 := pair_fact E (i := 4) (j := 6) rfl rfl c1279 c1280
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1288
                  omega
                have f1289 := pair_fact E (i := 0) (j := 8) rfl rfl c1260 c1261
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1289
                omega
              have f1290 := pair_fact E (i := 0) (j := 6) rfl rfl c1236 c1237
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1290
              omega
            by_cases c1291 : a0 + a2 < b0 + b2 + b4
            swap
            · omega
            by_cases c1292 : b0 + b2 < a0 + a2 + a4
            swap
            · omega
            have f1293 := pair_fact E (i := 4) (j := 4) rfl rfl c1234 c1235
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1293
            omega
          by_cases c1294 : b0 < a0 + a2 + a4
          swap
          · omega
          have f1295 := pair_fact E (i := 4) (j := 2) rfl rfl c1231 c1232
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1295
          omega
        by_cases c1296 : a0 + a2 < 0 + b0
        swap
        · omega
        by_cases c1297 : 0 < a0 + a2 + a4
        swap
        · omega
        have f1298 := pair_fact E (i := 4) (j := 0) rfl rfl c1229 c1230
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1298
        omega
      have f1299 := pair_fact E (i := 0) (j := 10) rfl rfl c1225 c1226
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1299
      omega
    by_cases c1300 : 0 < b0 + b2 + b4
    swap
    · omega
    by_cases c1301 : b0 + b2 < 0 + a0
    swap
    · -- branch
      by_cases c1302 : 0 < a0
      swap
      · omega
      by_cases c1303 : 0 < b6
      swap
      · -- branch
        by_cases c1304 : 0 < a6
        swap
        · omega
        by_cases c1305 : 0 < b0
        swap
        · -- branch
          by_cases c1306 : 0 < a6
          swap
          · omega
          by_cases c1307 : 0 < b2
          swap
          · omega
          by_cases c1308 : a0 + a2 + a4 < b0 + b2
          swap
          · -- branch
            by_cases c1309 : 0 < a6
            swap
            · omega
            by_cases c1310 : 0 < b4
            swap
            · omega
            by_cases c1311 : a0 + a2 + a4 < b0 + b2 + b4
            swap
            · -- branch
              by_cases c1312 : 0 < a0
              swap
              · omega
              by_cases c1313 : 0 < b10
              swap
              · omega
              by_cases c1314 : 0 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c1315 : b0 + b2 + b4 + b6 + b8 < 0 + a0
              swap
              · -- branch
                by_cases c1316 : 0 < a4
                swap
                · omega
                by_cases c1317 : 0 < b0
                swap
                · -- branch
                  by_cases c1318 : 0 < a4
                  swap
                  · omega
                  by_cases c1319 : 0 < b2
                  swap
                  · omega
                  by_cases c1320 : a0 + a2 < b0 + b2
                  swap
                  · -- branch
                    by_cases c1321 : 0 < a4
                    swap
                    · omega
                    by_cases c1322 : 0 < b4
                    swap
                    · omega
                    by_cases c1323 : a0 + a2 < b0 + b2 + b4
                    swap
                    · -- branch
                      by_cases c1324 : 0 < a2
                      swap
                      · omega
                      by_cases c1325 : 0 < b4
                      swap
                      · omega
                      by_cases c1326 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c1327 : b0 + b2 < a0 + a2
                      swap
                      · omega
                      have f1328 := pair_fact E (i := 2) (j := 4) rfl rfl c1324 c1325
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1328
                      omega
                    by_cases c1329 : b0 + b2 < a0 + a2 + a4
                    swap
                    · omega
                    have f1330 := pair_fact E (i := 4) (j := 4) rfl rfl c1321 c1322
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1330
                    omega
                  by_cases c1331 : b0 < a0 + a2 + a4
                  swap
                  · omega
                  have f1332 := pair_fact E (i := 4) (j := 2) rfl rfl c1318 c1319
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1332
                  omega
                by_cases c1333 : a0 + a2 < 0 + b0
                swap
                · omega
                by_cases c1334 : 0 < a0 + a2 + a4
                swap
                · omega
                have f1335 := pair_fact E (i := 4) (j := 0) rfl rfl c1316 c1317
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1335
                omega
              have f1336 := pair_fact E (i := 0) (j := 10) rfl rfl c1312 c1313
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1336
              omega
            by_cases c1337 : b0 + b2 < a0 + a2 + a4 + a6
            swap
            · omega
            have f1338 := pair_fact E (i := 6) (j := 4) rfl rfl c1309 c1310
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1338
            omega
          by_cases c1339 : b0 < a0 + a2 + a4 + a6
          swap
          · omega
          have f1340 := pair_fact E (i := 6) (j := 2) rfl rfl c1306 c1307
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1340
          omega
        by_cases c1341 : a0 + a2 + a4 < 0 + b0
        swap
        · omega
        by_cases c1342 : 0 < a0 + a2 + a4 + a6
        swap
        · omega
        have f1343 := pair_fact E (i := 6) (j := 0) rfl rfl c1304 c1305
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1343
        omega
      by_cases c1344 : 0 < b0 + b2 + b4 + b6
      swap
      · omega
      by_cases c1345 : b0 + b2 + b4 < 0 + a0
      swap
      · -- branch
        by_cases c1346 : 0 < a0
        swap
        · omega
        by_cases c1347 : 0 < b8
        swap
        · -- branch
          by_cases c1348 : 0 < a8
          swap
          · omega
          by_cases c1349 : 0 < b0
          swap
          · -- branch
            by_cases c1350 : 0 < a8
            swap
            · omega
            by_cases c1351 : 0 < b2
            swap
            · omega
            by_cases c1352 : a0 + a2 + a4 + a6 < b0 + b2
            swap
            · -- branch
              by_cases c1353 : 0 < a8
              swap
              · omega
              by_cases c1354 : 0 < b4
              swap
              · omega
              by_cases c1355 : a0 + a2 + a4 + a6 < b0 + b2 + b4
              swap
              · -- branch
                by_cases c1356 : 0 < a0
                swap
                · omega
                by_cases c1357 : 0 < b10
                swap
                · omega
                by_cases c1358 : 0 < b0 + b2 + b4 + b6 + b8 + b10
                swap
                · omega
                by_cases c1359 : b0 + b2 + b4 + b6 + b8 < 0 + a0
                swap
                · -- branch
                  by_cases c1360 : 0 < a4
                  swap
                  · omega
                  by_cases c1361 : 0 < b0
                  swap
                  · -- branch
                    by_cases c1362 : 0 < a4
                    swap
                    · omega
                    by_cases c1363 : 0 < b2
                    swap
                    · omega
                    by_cases c1364 : a0 + a2 < b0 + b2
                    swap
                    · -- branch
                      by_cases c1365 : 0 < a4
                      swap
                      · omega
                      by_cases c1366 : 0 < b4
                      swap
                      · omega
                      by_cases c1367 : a0 + a2 < b0 + b2 + b4
                      swap
                      · -- branch
                        by_cases c1368 : 0 < a2
                        swap
                        · omega
                        by_cases c1369 : 0 < b4
                        swap
                        · omega
                        by_cases c1370 : a0 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c1371 : b0 + b2 < a0 + a2
                        swap
                        · omega
                        have f1372 := pair_fact E (i := 2) (j := 4) rfl rfl c1368 c1369
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1372
                        omega
                      by_cases c1373 : b0 + b2 < a0 + a2 + a4
                      swap
                      · omega
                      have f1374 := pair_fact E (i := 4) (j := 4) rfl rfl c1365 c1366
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1374
                      omega
                    by_cases c1375 : b0 < a0 + a2 + a4
                    swap
                    · omega
                    have f1376 := pair_fact E (i := 4) (j := 2) rfl rfl c1362 c1363
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1376
                    omega
                  by_cases c1377 : a0 + a2 < 0 + b0
                  swap
                  · omega
                  by_cases c1378 : 0 < a0 + a2 + a4
                  swap
                  · omega
                  have f1379 := pair_fact E (i := 4) (j := 0) rfl rfl c1360 c1361
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1379
                  omega
                have f1380 := pair_fact E (i := 0) (j := 10) rfl rfl c1356 c1357
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1380
                omega
              by_cases c1381 : b0 + b2 < a0 + a2 + a4 + a6 + a8
              swap
              · omega
              have f1382 := pair_fact E (i := 8) (j := 4) rfl rfl c1353 c1354
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1382
              omega
            by_cases c1383 : b0 < a0 + a2 + a4 + a6 + a8
            swap
            · omega
            have f1384 := pair_fact E (i := 8) (j := 2) rfl rfl c1350 c1351
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1384
            omega
          by_cases c1385 : a0 + a2 + a4 + a6 < 0 + b0
          swap
          · omega
          by_cases c1386 : 0 < a0 + a2 + a4 + a6 + a8
          swap
          · omega
          have f1387 := pair_fact E (i := 8) (j := 0) rfl rfl c1348 c1349
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1387
          omega
        by_cases c1388 : 0 < b0 + b2 + b4 + b6 + b8
        swap
        · omega
        by_cases c1389 : b0 + b2 + b4 + b6 < 0 + a0
        swap
        · -- branch
          by_cases c1390 : 0 < a0
          swap
          · omega
          by_cases c1391 : 0 < b10
          swap
          · -- branch
            by_cases c1392 : 0 < a8
            swap
            · -- branch
              by_cases c1393 : 0 < a6
              swap
              · -- branch
                by_cases c1394 : 0 < a4
                swap
                · omega
                by_cases c1395 : 0 < b4
                swap
                · omega
                by_cases c1396 : a0 + a2 < b0 + b2 + b4
                swap
                · omega
                by_cases c1397 : b0 + b2 < a0 + a2 + a4
                swap
                · omega
                have f1398 := pair_fact E (i := 4) (j := 4) rfl rfl c1394 c1395
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1398
                omega
              by_cases c1399 : 0 < b4
              swap
              · omega
              by_cases c1400 : a0 + a2 + a4 < b0 + b2 + b4
              swap
              · omega
              by_cases c1401 : b0 + b2 < a0 + a2 + a4 + a6
              swap
              · omega
              have f1402 := pair_fact E (i := 6) (j := 4) rfl rfl c1393 c1399
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1402
              omega
            by_cases c1403 : 0 < b4
            swap
            · omega
            by_cases c1404 : a0 + a2 + a4 + a6 < b0 + b2 + b4
            swap
            · omega
            by_cases c1405 : b0 + b2 < a0 + a2 + a4 + a6 + a8
            swap
            · omega
            have f1406 := pair_fact E (i := 8) (j := 4) rfl rfl c1392 c1403
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1406
            omega
          by_cases c1407 : 0 < b0 + b2 + b4 + b6 + b8 + b10
          swap
          · omega
          by_cases c1408 : b0 + b2 + b4 + b6 + b8 < 0 + a0
          swap
          · -- branch
            by_cases c1409 : 0 < a2
            swap
            · -- branch
              by_cases c1410 : 0 < a2
              swap
              · -- branch
                by_cases c1411 : 0 < a2
                swap
                · -- branch
                  by_cases c1412 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1413 : 0 < a2
                    swap
                    · -- branch
                      by_cases c1414 : 0 < a2
                      swap
                      · -- branch
                        by_cases c1415 : 0 < a4
                        swap
                        · -- branch
                          by_cases c1416 : 0 < a8
                          swap
                          · omega
                          by_cases c1417 : 0 < b4
                          swap
                          · omega
                          by_cases c1418 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1419 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f1420 := pair_fact E (i := 8) (j := 4) rfl rfl c1416 c1417
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1420
                          omega
                        by_cases c1421 : 0 < b0
                        swap
                        · -- branch
                          by_cases c1422 : 0 < a4
                          swap
                          · omega
                          by_cases c1423 : 0 < b2
                          swap
                          · omega
                          by_cases c1424 : a0 + a2 < b0 + b2
                          swap
                          · -- branch
                            by_cases c1425 : 0 < a4
                            swap
                            · omega
                            by_cases c1426 : 0 < b4
                            swap
                            · omega
                            by_cases c1427 : a0 + a2 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c1428 : b0 + b2 < a0 + a2 + a4
                            swap
                            · omega
                            have f1429 := pair_fact E (i := 4) (j := 4) rfl rfl c1425 c1426
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1429
                            omega
                          by_cases c1430 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f1431 := pair_fact E (i := 4) (j := 2) rfl rfl c1422 c1423
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1431
                          omega
                        by_cases c1432 : a0 + a2 < 0 + b0
                        swap
                        · omega
                        by_cases c1433 : 0 < a0 + a2 + a4
                        swap
                        · omega
                        have f1434 := pair_fact E (i := 4) (j := 0) rfl rfl c1415 c1421
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1434
                        omega
                      by_cases c1435 : 0 < b10
                      swap
                      · omega
                      by_cases c1436 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                      swap
                      · omega
                      by_cases c1437 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                      swap
                      · omega
                      have f1438 := pair_fact E (i := 2) (j := 10) rfl rfl c1414 c1435
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1438
                      omega
                    by_cases c1439 : 0 < b8
                    swap
                    · omega
                    by_cases c1440 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c1441 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · omega
                    have f1442 := pair_fact E (i := 2) (j := 8) rfl rfl c1413 c1439
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1442
                    omega
                  by_cases c1443 : 0 < b6
                  swap
                  · omega
                  by_cases c1444 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c1445 : b0 + b2 + b4 < a0 + a2
                  swap
                  · omega
                  have f1446 := pair_fact E (i := 2) (j := 6) rfl rfl c1412 c1443
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1446
                  omega
                by_cases c1447 : 0 < b4
                swap
                · omega
                by_cases c1448 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c1449 : b0 + b2 < a0 + a2
                swap
                · omega
                have f1450 := pair_fact E (i := 2) (j := 4) rfl rfl c1411 c1447
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1450
                omega
              by_cases c1451 : 0 < b2
              swap
              · omega
              by_cases c1452 : a0 < b0 + b2
              swap
              · omega
              by_cases c1453 : b0 < a0 + a2
              swap
              · omega
              have f1454 := pair_fact E (i := 2) (j := 2) rfl rfl c1410 c1451
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1454
              omega
            by_cases c1455 : 0 < b0
            swap
            · -- branch
              by_cases c1456 : 0 < a2
              swap
              · omega
              by_cases c1457 : 0 < b2
              swap
              · omega
              by_cases c1458 : a0 < b0 + b2
              swap
              · -- branch
                by_cases c1459 : 0 < a2
                swap
                · omega
                by_cases c1460 : 0 < b4
                swap
                · omega
                by_cases c1461 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c1462 : b0 + b2 < a0 + a2
                swap
                · omega
                have f1463 := pair_fact E (i := 2) (j := 4) rfl rfl c1459 c1460
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1463
                omega
              by_cases c1464 : b0 < a0 + a2
              swap
              · omega
              have f1465 := pair_fact E (i := 2) (j := 2) rfl rfl c1456 c1457
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1465
              omega
            by_cases c1466 : a0 < 0 + b0
            swap
            · omega
            by_cases c1467 : 0 < a0 + a2
            swap
            · omega
            have f1468 := pair_fact E (i := 2) (j := 0) rfl rfl c1409 c1455
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1468
            omega
          have f1469 := pair_fact E (i := 0) (j := 10) rfl rfl c1390 c1391
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1469
          omega
        have f1470 := pair_fact E (i := 0) (j := 8) rfl rfl c1346 c1347
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1470
        omega
      have f1471 := pair_fact E (i := 0) (j := 6) rfl rfl c1302 c1303
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1471
      omega
    have f1472 := pair_fact E (i := 0) (j := 4) rfl rfl c1223 c1224
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1472
    omega
  by_cases c1473 : 0 < 0 + b0
  swap
  · omega
  by_cases c1474 : 0 < 0 + a0
  swap
  · omega
  have f1475 := pair_fact E (i := 0) (j := 0) rfl rfl c1 c1207
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1475
  by_cases c1476 : 0 < a0
  swap
  · omega
  by_cases c1477 : 0 < b4
  swap
  · -- branch
    by_cases c1478 : 0 < a4
    swap
    · omega
    by_cases c1479 : 0 < b0
    swap
    · omega
    by_cases c1480 : a0 + a2 < 0 + b0
    swap
    · -- branch
      by_cases c1481 : 0 < a4
      swap
      · omega
      by_cases c1482 : 0 < b4
      swap
      · -- branch
        by_cases c1483 : 0 < a0
        swap
        · omega
        by_cases c1484 : 0 < b6
        swap
        · -- branch
          by_cases c1485 : 0 < a0
          swap
          · omega
          by_cases c1486 : 0 < b8
          swap
          · omega
          by_cases c1487 : 0 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c1488 : b0 + b2 + b4 + b6 < 0 + a0
          swap
          · -- branch
            by_cases c1489 : 0 < a0
            swap
            · omega
            by_cases c1490 : 0 < b10
            swap
            · omega
            by_cases c1491 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c1492 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · -- branch
              by_cases c1493 : 0 < a4
              swap
              · omega
              by_cases c1494 : 0 < b6
              swap
              · -- branch
                by_cases c1495 : 0 < a4
                swap
                · omega
                by_cases c1496 : 0 < b8
                swap
                · omega
                by_cases c1497 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c1498 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                swap
                · omega
                have f1499 := pair_fact E (i := 4) (j := 8) rfl rfl c1495 c1496
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1499
                by_cases c1500 : 0 < a4
                swap
                · omega
                by_cases c1501 : 0 < b2
                swap
                · omega
                by_cases c1502 : a0 + a2 < b0 + b2
                swap
                · -- branch
                  by_cases c1503 : 0 < a2
                  swap
                  · omega
                  by_cases c1504 : 0 < b2
                  swap
                  · omega
                  by_cases c1505 : a0 < b0 + b2
                  swap
                  · omega
                  by_cases c1506 : b0 < a0 + a2
                  swap
                  · omega
                  have f1507 := pair_fact E (i := 2) (j := 2) rfl rfl c1503 c1504
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1507
                  omega
                by_cases c1508 : b0 < a0 + a2 + a4
                swap
                · omega
                have f1509 := pair_fact E (i := 4) (j := 2) rfl rfl c1500 c1501
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1509
                omega
              by_cases c1510 : a0 + a2 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c1511 : b0 + b2 + b4 < a0 + a2 + a4
              swap
              · omega
              have f1512 := pair_fact E (i := 4) (j := 6) rfl rfl c1493 c1494
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1512
              omega
            have f1513 := pair_fact E (i := 0) (j := 10) rfl rfl c1489 c1490
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1513
            omega
          have f1514 := pair_fact E (i := 0) (j := 8) rfl rfl c1485 c1486
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1514
          omega
        by_cases c1515 : 0 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c1516 : b0 + b2 + b4 < 0 + a0
        swap
        · -- branch
          by_cases c1517 : 0 < a0
          swap
          · omega
          by_cases c1518 : 0 < b8
          swap
          · -- branch
            by_cases c1519 : 0 < a0
            swap
            · omega
            by_cases c1520 : 0 < b10
            swap
            · omega
            by_cases c1521 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c1522 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · -- branch
              by_cases c1523 : 0 < a4
              swap
              · omega
              by_cases c1524 : 0 < b6
              swap
              · omega
              by_cases c1525 : a0 + a2 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c1526 : b0 + b2 + b4 < a0 + a2 + a4
              swap
              · omega
              have f1527 := pair_fact E (i := 4) (j := 6) rfl rfl c1523 c1524
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1527
              by_cases c1528 : 0 < a4
              swap
              · omega
              by_cases c1529 : 0 < b2
              swap
              · omega
              by_cases c1530 : a0 + a2 < b0 + b2
              swap
              · -- branch
                by_cases c1531 : 0 < a2
                swap
                · omega
                by_cases c1532 : 0 < b2
                swap
                · omega
                by_cases c1533 : a0 < b0 + b2
                swap
                · omega
                by_cases c1534 : b0 < a0 + a2
                swap
                · omega
                have f1535 := pair_fact E (i := 2) (j := 2) rfl rfl c1531 c1532
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1535
                omega
              by_cases c1536 : b0 < a0 + a2 + a4
              swap
              · omega
              have f1537 := pair_fact E (i := 4) (j := 2) rfl rfl c1528 c1529
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1537
              omega
            have f1538 := pair_fact E (i := 0) (j := 10) rfl rfl c1519 c1520
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1538
            omega
          by_cases c1539 : 0 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c1540 : b0 + b2 + b4 + b6 < 0 + a0
          swap
          · -- branch
            by_cases c1541 : 0 < a0
            swap
            · omega
            by_cases c1542 : 0 < b10
            swap
            · -- branch
              by_cases c1543 : 0 < a4
              swap
              · omega
              by_cases c1544 : 0 < b6
              swap
              · omega
              by_cases c1545 : a0 + a2 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c1546 : b0 + b2 + b4 < a0 + a2 + a4
              swap
              · omega
              have f1547 := pair_fact E (i := 4) (j := 6) rfl rfl c1543 c1544
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1547
              by_cases c1548 : 0 < a4
              swap
              · omega
              by_cases c1549 : 0 < b8
              swap
              · omega
              by_cases c1550 : a0 + a2 < b0 + b2 + b4 + b6 + b8
              swap
              · omega
              by_cases c1551 : b0 + b2 + b4 + b6 < a0 + a2 + a4
              swap
              · -- branch
                by_cases c1552 : 0 < a4
                swap
                · omega
                by_cases c1553 : 0 < b2
                swap
                · omega
                by_cases c1554 : a0 + a2 < b0 + b2
                swap
                · omega
                by_cases c1555 : b0 < a0 + a2 + a4
                swap
                · omega
                have f1556 := pair_fact E (i := 4) (j := 2) rfl rfl c1552 c1553
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1556
                omega
              have f1557 := pair_fact E (i := 4) (j := 8) rfl rfl c1548 c1549
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1557
              omega
            by_cases c1558 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c1559 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · -- branch
              by_cases c1560 : 0 < a2
              swap
              · -- branch
                by_cases c1561 : 0 < a2
                swap
                · -- branch
                  by_cases c1562 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1563 : 0 < a2
                    swap
                    · -- branch
                      by_cases c1564 : 0 < a2
                      swap
                      · -- branch
                        by_cases c1565 : 0 < a2
                        swap
                        · -- branch
                          by_cases c1566 : 0 < a4
                          swap
                          · omega
                          by_cases c1567 : 0 < b6
                          swap
                          · omega
                          by_cases c1568 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c1569 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · omega
                          have f1570 := pair_fact E (i := 4) (j := 6) rfl rfl c1566 c1567
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1570
                          by_cases c1571 : 0 < a4
                          swap
                          · omega
                          by_cases c1572 : 0 < b2
                          swap
                          · omega
                          by_cases c1573 : a0 + a2 < b0 + b2
                          swap
                          · -- branch
                            by_cases c1574 : 0 < a4
                            swap
                            · omega
                            by_cases c1575 : 0 < b8
                            swap
                            · omega
                            by_cases c1576 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1577 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · omega
                            have f1578 := pair_fact E (i := 4) (j := 8) rfl rfl c1574 c1575
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1578
                            omega
                          by_cases c1579 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f1580 := pair_fact E (i := 4) (j := 2) rfl rfl c1571 c1572
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1580
                          omega
                        by_cases c1581 : 0 < b10
                        swap
                        · omega
                        by_cases c1582 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c1583 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                        swap
                        · omega
                        have f1584 := pair_fact E (i := 2) (j := 10) rfl rfl c1565 c1581
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1584
                        omega
                      by_cases c1585 : 0 < b8
                      swap
                      · omega
                      by_cases c1586 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c1587 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · omega
                      have f1588 := pair_fact E (i := 2) (j := 8) rfl rfl c1564 c1585
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1588
                      omega
                    by_cases c1589 : 0 < b6
                    swap
                    · omega
                    by_cases c1590 : a0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c1591 : b0 + b2 + b4 < a0 + a2
                    swap
                    · omega
                    have f1592 := pair_fact E (i := 2) (j := 6) rfl rfl c1563 c1589
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1592
                    omega
                  by_cases c1593 : 0 < b2
                  swap
                  · omega
                  by_cases c1594 : a0 < b0 + b2
                  swap
                  · omega
                  by_cases c1595 : b0 < a0 + a2
                  swap
                  · omega
                  have f1596 := pair_fact E (i := 2) (j := 2) rfl rfl c1562 c1593
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1596
                  omega
                by_cases c1597 : 0 < b0
                swap
                · omega
                by_cases c1598 : a0 < 0 + b0
                swap
                · omega
                by_cases c1599 : 0 < a0 + a2
                swap
                · omega
                have f1600 := pair_fact E (i := 2) (j := 0) rfl rfl c1561 c1597
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1600
                omega
              by_cases c1601 : 0 < b4
              swap
              · -- branch
                by_cases c1602 : 0 < a2
                swap
                · omega
                by_cases c1603 : 0 < b6
                swap
                · omega
                by_cases c1604 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c1605 : b0 + b2 + b4 < a0 + a2
                swap
                · -- branch
                  by_cases c1606 : 0 < a2
                  swap
                  · omega
                  by_cases c1607 : 0 < b8
                  swap
                  · omega
                  by_cases c1608 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c1609 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · -- branch
                    by_cases c1610 : 0 < a2
                    swap
                    · omega
                    by_cases c1611 : 0 < b10
                    swap
                    · omega
                    by_cases c1612 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c1613 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · -- branch
                      by_cases c1614 : 0 < a4
                      swap
                      · omega
                      by_cases c1615 : 0 < b6
                      swap
                      · omega
                      by_cases c1616 : a0 + a2 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c1617 : b0 + b2 + b4 < a0 + a2 + a4
                      swap
                      · omega
                      have f1618 := pair_fact E (i := 4) (j := 6) rfl rfl c1614 c1615
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1618
                      by_cases c1619 : 0 < a4
                      swap
                      · omega
                      by_cases c1620 : 0 < b8
                      swap
                      · omega
                      by_cases c1621 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c1622 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                      swap
                      · omega
                      have f1623 := pair_fact E (i := 4) (j := 8) rfl rfl c1619 c1620
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1623
                      omega
                    have f1624 := pair_fact E (i := 2) (j := 10) rfl rfl c1610 c1611
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1624
                    omega
                  have f1625 := pair_fact E (i := 2) (j := 8) rfl rfl c1606 c1607
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1625
                  omega
                have f1626 := pair_fact E (i := 2) (j := 6) rfl rfl c1602 c1603
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1626
                omega
              by_cases c1627 : a0 < b0 + b2 + b4
              swap
              · omega
              by_cases c1628 : b0 + b2 < a0 + a2
              swap
              · omega
              have f1629 := pair_fact E (i := 2) (j := 4) rfl rfl c1560 c1601
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1629
              omega
            have f1630 := pair_fact E (i := 0) (j := 10) rfl rfl c1541 c1542
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1630
            omega
          have f1631 := pair_fact E (i := 0) (j := 8) rfl rfl c1517 c1518
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1631
          omega
        have f1632 := pair_fact E (i := 0) (j := 6) rfl rfl c1483 c1484
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1632
        omega
      by_cases c1633 : a0 + a2 < b0 + b2 + b4
      swap
      · omega
      by_cases c1634 : b0 + b2 < a0 + a2 + a4
      swap
      · omega
      have f1635 := pair_fact E (i := 4) (j := 4) rfl rfl c1481 c1482
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1635
      omega
    by_cases c1636 : 0 < a0 + a2 + a4
    swap
    · omega
    have f1637 := pair_fact E (i := 4) (j := 0) rfl rfl c1478 c1479
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1637
    omega
  by_cases c1638 : 0 < b0 + b2 + b4
  swap
  · omega
  by_cases c1639 : b0 + b2 < 0 + a0
  swap
  · -- branch
    by_cases c1640 : 0 < a0
    swap
    · omega
    by_cases c1641 : 0 < b6
    swap
    · -- branch
      by_cases c1642 : 0 < a6
      swap
      · omega
      by_cases c1643 : 0 < b0
      swap
      · omega
      by_cases c1644 : a0 + a2 + a4 < 0 + b0
      swap
      · -- branch
        by_cases c1645 : 0 < a6
        swap
        · omega
        by_cases c1646 : 0 < b6
        swap
        · -- branch
          by_cases c1647 : 0 < a0
          swap
          · omega
          by_cases c1648 : 0 < b8
          swap
          · -- branch
            by_cases c1649 : 0 < a6
            swap
            · omega
            by_cases c1650 : 0 < b8
            swap
            · -- branch
              by_cases c1651 : 0 < a8
              swap
              · omega
              by_cases c1652 : 0 < b0
              swap
              · omega
              by_cases c1653 : a0 + a2 + a4 + a6 < 0 + b0
              swap
              · -- branch
                by_cases c1654 : 0 < a8
                swap
                · omega
                by_cases c1655 : 0 < b6
                swap
                · -- branch
                  by_cases c1656 : 0 < a8
                  swap
                  · omega
                  by_cases c1657 : 0 < b8
                  swap
                  · -- branch
                    by_cases c1658 : 0 < a0
                    swap
                    · omega
                    by_cases c1659 : 0 < b10
                    swap
                    · -- branch
                      by_cases c1660 : 0 < a6
                      swap
                      · omega
                      by_cases c1661 : 0 < b10
                      swap
                      · -- branch
                        by_cases c1662 : 0 < a8
                        swap
                        · omega
                        by_cases c1663 : 0 < b4
                        swap
                        · omega
                        by_cases c1664 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c1665 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f1666 := pair_fact E (i := 8) (j := 4) rfl rfl c1662 c1663
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1666
                        by_cases c1667 : 0 < a6
                        swap
                        · omega
                        by_cases c1668 : 0 < b4
                        swap
                        · omega
                        by_cases c1669 : a0 + a2 + a4 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c1670 : b0 + b2 < a0 + a2 + a4 + a6
                        swap
                        · -- branch
                          by_cases c1671 : 0 < a6
                          swap
                          · omega
                          by_cases c1672 : 0 < b2
                          swap
                          · omega
                          by_cases c1673 : a0 + a2 + a4 < b0 + b2
                          swap
                          · omega
                          by_cases c1674 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f1675 := pair_fact E (i := 6) (j := 2) rfl rfl c1671 c1672
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1675
                          omega
                        have f1676 := pair_fact E (i := 6) (j := 4) rfl rfl c1667 c1668
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1676
                        omega
                      by_cases c1677 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                      swap
                      · omega
                      by_cases c1678 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f1679 := pair_fact E (i := 6) (j := 10) rfl rfl c1660 c1661
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1679
                      omega
                    by_cases c1680 : 0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c1681 : b0 + b2 + b4 + b6 + b8 < 0 + a0
                    swap
                    · -- branch
                      by_cases c1682 : 0 < a2
                      swap
                      · -- branch
                        by_cases c1683 : 0 < a2
                        swap
                        · -- branch
                          by_cases c1684 : 0 < a2
                          swap
                          · -- branch
                            by_cases c1685 : 0 < a2
                            swap
                            · -- branch
                              by_cases c1686 : 0 < a2
                              swap
                              · -- branch
                                by_cases c1687 : 0 < a2
                                swap
                                · -- branch
                                  by_cases c1688 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1689 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c1690 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c1691 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c1692 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c1693 : a0 + a2 + a4 + a6 < b0 + b2
                                    swap
                                    · -- branch
                                      by_cases c1694 : 0 < a0
                                      swap
                                      · omega
                                      by_cases c1695 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c1696 : 0 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c1697 : b0 < 0 + a0
                                      swap
                                      · -- branch
                                        by_cases c1698 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c1699 : 0 < b0
                                        swap
                                        · omega
                                        by_cases c1700 : a0 + a2 < 0 + b0
                                        swap
                                        · -- branch
                                          by_cases c1701 : 0 < a4
                                          swap
                                          · omega
                                          by_cases c1702 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c1703 : a0 + a2 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c1704 : b0 < a0 + a2 + a4
                                          swap
                                          · omega
                                          have f1705 := pair_fact E (i := 4) (j := 2) rfl rfl c1701 c1702
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1705
                                          by_cases c1706 : 0 < a4
                                          swap
                                          · omega
                                          by_cases c1707 : 0 < b6
                                          swap
                                          · -- branch
                                            by_cases c1708 : 0 < a4
                                            swap
                                            · omega
                                            by_cases c1709 : 0 < b8
                                            swap
                                            · -- branch
                                              by_cases c1710 : 0 < a4
                                              swap
                                              · omega
                                              by_cases c1711 : 0 < b10
                                              swap
                                              · omega
                                              by_cases c1712 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                              swap
                                              · omega
                                              by_cases c1713 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                              swap
                                              · -- branch
                                                by_cases c1714 : 0 < a6
                                                swap
                                                · omega
                                                by_cases c1715 : 0 < b4
                                                swap
                                                · omega
                                                by_cases c1716 : a0 + a2 + a4 < b0 + b2 + b4
                                                swap
                                                · omega
                                                by_cases c1717 : b0 + b2 < a0 + a2 + a4 + a6
                                                swap
                                                · omega
                                                have f1718 := pair_fact E (i := 6) (j := 4) rfl rfl c1714 c1715
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1718
                                                omega
                                              have f1719 := pair_fact E (i := 4) (j := 10) rfl rfl c1710 c1711
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1719
                                              omega
                                            by_cases c1720 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                            swap
                                            · omega
                                            by_cases c1721 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                            swap
                                            · omega
                                            have f1722 := pair_fact E (i := 4) (j := 8) rfl rfl c1708 c1709
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1722
                                            omega
                                          by_cases c1723 : a0 + a2 < b0 + b2 + b4 + b6
                                          swap
                                          · omega
                                          by_cases c1724 : b0 + b2 + b4 < a0 + a2 + a4
                                          swap
                                          · omega
                                          have f1725 := pair_fact E (i := 4) (j := 6) rfl rfl c1706 c1707
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1725
                                          omega
                                        by_cases c1726 : 0 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f1727 := pair_fact E (i := 4) (j := 0) rfl rfl c1698 c1699
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1727
                                        omega
                                      have f1728 := pair_fact E (i := 0) (j := 2) rfl rfl c1694 c1695
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1728
                                      by_cases c1729 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c1730 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c1731 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · -- branch
                                        by_cases c1732 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c1733 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c1734 : a0 + a2 < b0 + b2
                                        swap
                                        · omega
                                        by_cases c1735 : b0 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f1736 := pair_fact E (i := 4) (j := 2) rfl rfl c1732 c1733
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1736
                                        omega
                                      by_cases c1737 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f1738 := pair_fact E (i := 6) (j := 4) rfl rfl c1729 c1730
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1738
                                      omega
                                    by_cases c1739 : b0 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f1740 := pair_fact E (i := 8) (j := 2) rfl rfl c1691 c1692
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1740
                                    omega
                                  by_cases c1741 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1742 := pair_fact E (i := 6) (j := 2) rfl rfl c1688 c1689
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1742
                                  omega
                                by_cases c1743 : 0 < b10
                                swap
                                · omega
                                by_cases c1744 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c1745 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                                swap
                                · omega
                                have f1746 := pair_fact E (i := 2) (j := 10) rfl rfl c1687 c1743
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1746
                                omega
                              by_cases c1747 : 0 < b8
                              swap
                              · omega
                              by_cases c1748 : a0 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c1749 : b0 + b2 + b4 + b6 < a0 + a2
                              swap
                              · omega
                              have f1750 := pair_fact E (i := 2) (j := 8) rfl rfl c1686 c1747
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1750
                              omega
                            by_cases c1751 : 0 < b4
                            swap
                            · omega
                            by_cases c1752 : a0 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c1753 : b0 + b2 < a0 + a2
                            swap
                            · omega
                            have f1754 := pair_fact E (i := 2) (j := 4) rfl rfl c1685 c1751
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1754
                            omega
                          by_cases c1755 : 0 < b2
                          swap
                          · omega
                          by_cases c1756 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c1757 : b0 < a0 + a2
                          swap
                          · omega
                          have f1758 := pair_fact E (i := 2) (j := 2) rfl rfl c1684 c1755
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1758
                          omega
                        by_cases c1759 : 0 < b0
                        swap
                        · omega
                        by_cases c1760 : a0 < 0 + b0
                        swap
                        · omega
                        by_cases c1761 : 0 < a0 + a2
                        swap
                        · omega
                        have f1762 := pair_fact E (i := 2) (j := 0) rfl rfl c1683 c1759
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1762
                        omega
                      by_cases c1763 : 0 < b6
                      swap
                      · -- branch
                        by_cases c1764 : 0 < a2
                        swap
                        · omega
                        by_cases c1765 : 0 < b8
                        swap
                        · -- branch
                          by_cases c1766 : 0 < a2
                          swap
                          · omega
                          by_cases c1767 : 0 < b10
                          swap
                          · omega
                          by_cases c1768 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c1769 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · -- branch
                            by_cases c1770 : 0 < a2
                            swap
                            · omega
                            by_cases c1771 : 0 < b0
                            swap
                            · omega
                            by_cases c1772 : a0 < 0 + b0
                            swap
                            · -- branch
                              by_cases c1773 : 0 < a2
                              swap
                              · omega
                              by_cases c1774 : 0 < b4
                              swap
                              · omega
                              by_cases c1775 : a0 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c1776 : b0 + b2 < a0 + a2
                              swap
                              · -- branch
                                by_cases c1777 : 0 < a2
                                swap
                                · omega
                                by_cases c1778 : 0 < b2
                                swap
                                · omega
                                by_cases c1779 : a0 < b0 + b2
                                swap
                                · omega
                                by_cases c1780 : b0 < a0 + a2
                                swap
                                · omega
                                have f1781 := pair_fact E (i := 2) (j := 2) rfl rfl c1777 c1778
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1781
                                by_cases c1782 : 0 < a0
                                swap
                                · omega
                                by_cases c1783 : 0 < b2
                                swap
                                · omega
                                by_cases c1784 : 0 < b0 + b2
                                swap
                                · omega
                                by_cases c1785 : b0 < 0 + a0
                                swap
                                · -- branch
                                  by_cases c1786 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1787 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c1788 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c1789 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1790 : 0 < b0
                                    swap
                                    · omega
                                    by_cases c1791 : a0 + a2 < 0 + b0
                                    swap
                                    · -- branch
                                      by_cases c1792 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c1793 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c1794 : a0 + a2 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c1795 : b0 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f1796 := pair_fact E (i := 4) (j := 2) rfl rfl c1792 c1793
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1796
                                      by_cases c1797 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c1798 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c1799 : a0 + a2 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c1800 : b0 + b2 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c1801 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c1802 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c1803 : a0 + a2 + a4 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c1804 : b0 + b2 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f1805 := pair_fact E (i := 6) (j := 4) rfl rfl c1801 c1802
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1805
                                        omega
                                      have f1806 := pair_fact E (i := 4) (j := 4) rfl rfl c1797 c1798
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1806
                                      omega
                                    by_cases c1807 : 0 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f1808 := pair_fact E (i := 4) (j := 0) rfl rfl c1789 c1790
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1808
                                    omega
                                  by_cases c1809 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1810 := pair_fact E (i := 6) (j := 2) rfl rfl c1786 c1787
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1810
                                  omega
                                have f1811 := pair_fact E (i := 0) (j := 2) rfl rfl c1782 c1783
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1811
                                omega
                              have f1812 := pair_fact E (i := 2) (j := 4) rfl rfl c1773 c1774
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1812
                              by_cases c1813 : 0 < a6
                              swap
                              · omega
                              by_cases c1814 : 0 < b4
                              swap
                              · omega
                              by_cases c1815 : a0 + a2 + a4 < b0 + b2 + b4
                              swap
                              · -- branch
                                by_cases c1816 : 0 < a4
                                swap
                                · omega
                                by_cases c1817 : 0 < b0
                                swap
                                · omega
                                by_cases c1818 : a0 + a2 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c1819 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c1820 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c1821 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c1822 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f1823 := pair_fact E (i := 4) (j := 4) rfl rfl c1819 c1820
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1823
                                  by_cases c1824 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c1825 : 0 < b6
                                  swap
                                  · -- branch
                                    by_cases c1826 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1827 : 0 < b8
                                    swap
                                    · -- branch
                                      by_cases c1828 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c1829 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c1830 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c1831 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c1832 : 0 < a0
                                        swap
                                        · omega
                                        by_cases c1833 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c1834 : 0 < b0 + b2
                                        swap
                                        · omega
                                        by_cases c1835 : b0 < 0 + a0
                                        swap
                                        · omega
                                        have f1836 := pair_fact E (i := 0) (j := 2) rfl rfl c1832 c1833
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1836
                                        omega
                                      have f1837 := pair_fact E (i := 4) (j := 10) rfl rfl c1828 c1829
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1837
                                      omega
                                    by_cases c1838 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c1839 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f1840 := pair_fact E (i := 4) (j := 8) rfl rfl c1826 c1827
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1840
                                    omega
                                  by_cases c1841 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c1842 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f1843 := pair_fact E (i := 4) (j := 6) rfl rfl c1824 c1825
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1843
                                  omega
                                by_cases c1844 : 0 < a0 + a2 + a4
                                swap
                                · omega
                                have f1845 := pair_fact E (i := 4) (j := 0) rfl rfl c1816 c1817
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1845
                                omega
                              by_cases c1846 : b0 + b2 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f1847 := pair_fact E (i := 6) (j := 4) rfl rfl c1813 c1814
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1847
                              omega
                            by_cases c1848 : 0 < a0 + a2
                            swap
                            · omega
                            have f1849 := pair_fact E (i := 2) (j := 0) rfl rfl c1770 c1771
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1849
                            by_cases c1850 : 0 < a2
                            swap
                            · omega
                            by_cases c1851 : 0 < b4
                            swap
                            · omega
                            by_cases c1852 : a0 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c1853 : b0 + b2 < a0 + a2
                            swap
                            · -- branch
                              by_cases c1854 : 0 < a0
                              swap
                              · omega
                              by_cases c1855 : 0 < b2
                              swap
                              · -- branch
                                by_cases c1856 : 0 < a2
                                swap
                                · omega
                                by_cases c1857 : 0 < b2
                                swap
                                · -- branch
                                  by_cases c1858 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1859 : 0 < b2
                                  swap
                                  · -- branch
                                    by_cases c1860 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c1861 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c1862 : a0 + a2 + a4 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c1863 : b0 + b2 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f1864 := pair_fact E (i := 6) (j := 4) rfl rfl c1860 c1861
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1864
                                    by_cases c1865 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c1866 : 0 < b10
                                    swap
                                    · omega
                                    by_cases c1867 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c1868 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                    swap
                                    · -- branch
                                      by_cases c1869 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c1870 : 0 < b2
                                      swap
                                      · -- branch
                                        by_cases c1871 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c1872 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c1873 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                        swap
                                        · -- branch
                                          by_cases c1874 : 0 < a4
                                          swap
                                          · omega
                                          by_cases c1875 : 0 < b0
                                          swap
                                          · omega
                                          by_cases c1876 : a0 + a2 < 0 + b0
                                          swap
                                          · omega
                                          by_cases c1877 : 0 < a0 + a2 + a4
                                          swap
                                          · omega
                                          have f1878 := pair_fact E (i := 4) (j := 0) rfl rfl c1874 c1875
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1878
                                          omega
                                        by_cases c1879 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f1880 := pair_fact E (i := 8) (j := 4) rfl rfl c1871 c1872
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1880
                                        omega
                                      by_cases c1881 : a0 + a2 + a4 + a6 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c1882 : b0 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f1883 := pair_fact E (i := 8) (j := 2) rfl rfl c1869 c1870
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1883
                                      omega
                                    have f1884 := pair_fact E (i := 6) (j := 10) rfl rfl c1865 c1866
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1884
                                    omega
                                  by_cases c1885 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c1886 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1887 := pair_fact E (i := 6) (j := 2) rfl rfl c1858 c1859
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1887
                                  omega
                                by_cases c1888 : a0 < b0 + b2
                                swap
                                · omega
                                by_cases c1889 : b0 < a0 + a2
                                swap
                                · omega
                                have f1890 := pair_fact E (i := 2) (j := 2) rfl rfl c1856 c1857
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1890
                                omega
                              by_cases c1891 : 0 < b0 + b2
                              swap
                              · omega
                              by_cases c1892 : b0 < 0 + a0
                              swap
                              · -- branch
                                by_cases c1893 : 0 < a2
                                swap
                                · omega
                                by_cases c1894 : 0 < b2
                                swap
                                · omega
                                by_cases c1895 : a0 < b0 + b2
                                swap
                                · omega
                                by_cases c1896 : b0 < a0 + a2
                                swap
                                · -- branch
                                  by_cases c1897 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1898 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c1899 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c1900 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1901 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c1902 : a0 + a2 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c1903 : b0 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f1904 := pair_fact E (i := 4) (j := 2) rfl rfl c1900 c1901
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1904
                                    omega
                                  by_cases c1905 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1906 := pair_fact E (i := 6) (j := 2) rfl rfl c1897 c1898
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1906
                                  omega
                                have f1907 := pair_fact E (i := 2) (j := 2) rfl rfl c1893 c1894
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1907
                                omega
                              have f1908 := pair_fact E (i := 0) (j := 2) rfl rfl c1854 c1855
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1908
                              omega
                            have f1909 := pair_fact E (i := 2) (j := 4) rfl rfl c1850 c1851
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1909
                            omega
                          have f1910 := pair_fact E (i := 2) (j := 10) rfl rfl c1766 c1767
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1910
                          omega
                        by_cases c1911 : a0 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1912 : b0 + b2 + b4 + b6 < a0 + a2
                        swap
                        · omega
                        have f1913 := pair_fact E (i := 2) (j := 8) rfl rfl c1764 c1765
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1913
                        omega
                      by_cases c1914 : a0 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c1915 : b0 + b2 + b4 < a0 + a2
                      swap
                      · omega
                      have f1916 := pair_fact E (i := 2) (j := 6) rfl rfl c1682 c1763
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1916
                      omega
                    have f1917 := pair_fact E (i := 0) (j := 10) rfl rfl c1658 c1659
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1917
                    omega
                  by_cases c1918 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c1919 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                  swap
                  · omega
                  have f1920 := pair_fact E (i := 8) (j := 8) rfl rfl c1656 c1657
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1920
                  omega
                by_cases c1921 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c1922 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                swap
                · omega
                have f1923 := pair_fact E (i := 8) (j := 6) rfl rfl c1654 c1655
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1923
                omega
              by_cases c1924 : 0 < a0 + a2 + a4 + a6 + a8
              swap
              · omega
              have f1925 := pair_fact E (i := 8) (j := 0) rfl rfl c1651 c1652
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1925
              omega
            by_cases c1926 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
            swap
            · omega
            by_cases c1927 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
            swap
            · omega
            have f1928 := pair_fact E (i := 6) (j := 8) rfl rfl c1649 c1650
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1928
            omega
          by_cases c1929 : 0 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c1930 : b0 + b2 + b4 + b6 < 0 + a0
          swap
          · -- branch
            by_cases c1931 : 0 < a0
            swap
            · omega
            by_cases c1932 : 0 < b10
            swap
            · -- branch
              by_cases c1933 : 0 < a6
              swap
              · omega
              by_cases c1934 : 0 < b10
              swap
              · -- branch
                by_cases c1935 : 0 < a2
                swap
                · -- branch
                  by_cases c1936 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1937 : 0 < a2
                    swap
                    · -- branch
                      by_cases c1938 : 0 < a2
                      swap
                      · -- branch
                        by_cases c1939 : 0 < a2
                        swap
                        · -- branch
                          by_cases c1940 : 0 < a2
                          swap
                          · -- branch
                            by_cases c1941 : 0 < a6
                            swap
                            · omega
                            by_cases c1942 : 0 < b2
                            swap
                            · omega
                            by_cases c1943 : a0 + a2 + a4 < b0 + b2
                            swap
                            · -- branch
                              by_cases c1944 : 0 < a0
                              swap
                              · omega
                              by_cases c1945 : 0 < b2
                              swap
                              · omega
                              by_cases c1946 : 0 < b0 + b2
                              swap
                              · omega
                              by_cases c1947 : b0 < 0 + a0
                              swap
                              · -- branch
                                by_cases c1948 : 0 < a4
                                swap
                                · omega
                                by_cases c1949 : 0 < b0
                                swap
                                · omega
                                by_cases c1950 : a0 + a2 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c1951 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c1952 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c1953 : a0 + a2 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c1954 : b0 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f1955 := pair_fact E (i := 4) (j := 2) rfl rfl c1951 c1952
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1955
                                  by_cases c1956 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1957 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c1958 : a0 + a2 + a4 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c1959 : b0 + b2 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1960 := pair_fact E (i := 6) (j := 4) rfl rfl c1956 c1957
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1960
                                  omega
                                by_cases c1961 : 0 < a0 + a2 + a4
                                swap
                                · omega
                                have f1962 := pair_fact E (i := 4) (j := 0) rfl rfl c1948 c1949
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1962
                                omega
                              have f1963 := pair_fact E (i := 0) (j := 2) rfl rfl c1944 c1945
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1963
                              by_cases c1964 : 0 < a6
                              swap
                              · omega
                              by_cases c1965 : 0 < b4
                              swap
                              · omega
                              by_cases c1966 : a0 + a2 + a4 < b0 + b2 + b4
                              swap
                              · -- branch
                                by_cases c1967 : 0 < a4
                                swap
                                · omega
                                by_cases c1968 : 0 < b4
                                swap
                                · omega
                                by_cases c1969 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c1970 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f1971 := pair_fact E (i := 4) (j := 4) rfl rfl c1967 c1968
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1971
                                omega
                              by_cases c1972 : b0 + b2 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f1973 := pair_fact E (i := 6) (j := 4) rfl rfl c1964 c1965
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1973
                              omega
                            by_cases c1974 : b0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f1975 := pair_fact E (i := 6) (j := 2) rfl rfl c1941 c1942
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1975
                            omega
                          by_cases c1976 : 0 < b10
                          swap
                          · omega
                          by_cases c1977 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c1978 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · omega
                          have f1979 := pair_fact E (i := 2) (j := 10) rfl rfl c1940 c1976
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1979
                          omega
                        by_cases c1980 : 0 < b8
                        swap
                        · omega
                        by_cases c1981 : a0 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1982 : b0 + b2 + b4 + b6 < a0 + a2
                        swap
                        · omega
                        have f1983 := pair_fact E (i := 2) (j := 8) rfl rfl c1939 c1980
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1983
                        omega
                      by_cases c1984 : 0 < b4
                      swap
                      · omega
                      by_cases c1985 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c1986 : b0 + b2 < a0 + a2
                      swap
                      · omega
                      have f1987 := pair_fact E (i := 2) (j := 4) rfl rfl c1938 c1984
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1987
                      omega
                    by_cases c1988 : 0 < b2
                    swap
                    · omega
                    by_cases c1989 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c1990 : b0 < a0 + a2
                    swap
                    · omega
                    have f1991 := pair_fact E (i := 2) (j := 2) rfl rfl c1937 c1988
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1991
                    omega
                  by_cases c1992 : 0 < b0
                  swap
                  · omega
                  by_cases c1993 : a0 < 0 + b0
                  swap
                  · omega
                  by_cases c1994 : 0 < a0 + a2
                  swap
                  · omega
                  have f1995 := pair_fact E (i := 2) (j := 0) rfl rfl c1936 c1992
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1995
                  omega
                by_cases c1996 : 0 < b6
                swap
                · -- branch
                  by_cases c1997 : 0 < a2
                  swap
                  · omega
                  by_cases c1998 : 0 < b8
                  swap
                  · omega
                  by_cases c1999 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c2000 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · -- branch
                    by_cases c2001 : 0 < a2
                    swap
                    · omega
                    by_cases c2002 : 0 < b10
                    swap
                    · -- branch
                      by_cases c2003 : 0 < a2
                      swap
                      · omega
                      by_cases c2004 : 0 < b0
                      swap
                      · omega
                      by_cases c2005 : a0 < 0 + b0
                      swap
                      · -- branch
                        by_cases c2006 : 0 < a2
                        swap
                        · omega
                        by_cases c2007 : 0 < b4
                        swap
                        · omega
                        by_cases c2008 : a0 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c2009 : b0 + b2 < a0 + a2
                        swap
                        · -- branch
                          by_cases c2010 : 0 < a2
                          swap
                          · omega
                          by_cases c2011 : 0 < b2
                          swap
                          · omega
                          by_cases c2012 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c2013 : b0 < a0 + a2
                          swap
                          · omega
                          have f2014 := pair_fact E (i := 2) (j := 2) rfl rfl c2010 c2011
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2014
                          by_cases c2015 : 0 < a0
                          swap
                          · omega
                          by_cases c2016 : 0 < b2
                          swap
                          · omega
                          by_cases c2017 : 0 < b0 + b2
                          swap
                          · omega
                          by_cases c2018 : b0 < 0 + a0
                          swap
                          · -- branch
                            by_cases c2019 : 0 < a6
                            swap
                            · omega
                            by_cases c2020 : 0 < b4
                            swap
                            · omega
                            by_cases c2021 : a0 + a2 + a4 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c2022 : b0 + b2 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f2023 := pair_fact E (i := 6) (j := 4) rfl rfl c2019 c2020
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2023
                            omega
                          have f2024 := pair_fact E (i := 0) (j := 2) rfl rfl c2015 c2016
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2024
                          omega
                        have f2025 := pair_fact E (i := 2) (j := 4) rfl rfl c2006 c2007
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2025
                        by_cases c2026 : 0 < a6
                        swap
                        · omega
                        by_cases c2027 : 0 < b4
                        swap
                        · omega
                        by_cases c2028 : a0 + a2 + a4 < b0 + b2 + b4
                        swap
                        · -- branch
                          by_cases c2029 : 0 < a0
                          swap
                          · omega
                          by_cases c2030 : 0 < b2
                          swap
                          · omega
                          by_cases c2031 : 0 < b0 + b2
                          swap
                          · omega
                          by_cases c2032 : b0 < 0 + a0
                          swap
                          · omega
                          have f2033 := pair_fact E (i := 0) (j := 2) rfl rfl c2029 c2030
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2033
                          omega
                        by_cases c2034 : b0 + b2 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f2035 := pair_fact E (i := 6) (j := 4) rfl rfl c2026 c2027
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2035
                        omega
                      by_cases c2036 : 0 < a0 + a2
                      swap
                      · omega
                      have f2037 := pair_fact E (i := 2) (j := 0) rfl rfl c2003 c2004
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2037
                      by_cases c2038 : 0 < a2
                      swap
                      · omega
                      by_cases c2039 : 0 < b4
                      swap
                      · omega
                      by_cases c2040 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c2041 : b0 + b2 < a0 + a2
                      swap
                      · -- branch
                        by_cases c2042 : 0 < a0
                        swap
                        · omega
                        by_cases c2043 : 0 < b2
                        swap
                        · -- branch
                          by_cases c2044 : 0 < a2
                          swap
                          · omega
                          by_cases c2045 : 0 < b2
                          swap
                          · -- branch
                            by_cases c2046 : 0 < a6
                            swap
                            · omega
                            by_cases c2047 : 0 < b2
                            swap
                            · -- branch
                              by_cases c2048 : 0 < a4
                              swap
                              · -- branch
                                by_cases c2049 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c2050 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c2051 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c2052 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c2053 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c2054 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c2055 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c2056 : a0 + a2 + a4 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c2057 : b0 + b2 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f2058 := pair_fact E (i := 6) (j := 4) rfl rfl c2054 c2055
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2058
                                          by_cases c2059 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c2060 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c2061 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c2062 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f2063 := pair_fact E (i := 8) (j := 4) rfl rfl c2059 c2060
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2063
                                          omega
                                        by_cases c2064 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c2065 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c2066 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f2067 := pair_fact E (i := 4) (j := 10) rfl rfl c2053 c2064
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2067
                                        omega
                                      by_cases c2068 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c2069 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c2070 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f2071 := pair_fact E (i := 4) (j := 8) rfl rfl c2052 c2068
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2071
                                      omega
                                    by_cases c2072 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c2073 : a0 + a2 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c2074 : b0 + b2 + b4 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f2075 := pair_fact E (i := 4) (j := 6) rfl rfl c2051 c2072
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2075
                                    omega
                                  by_cases c2076 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c2077 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c2078 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f2079 := pair_fact E (i := 4) (j := 4) rfl rfl c2050 c2076
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2079
                                  omega
                                by_cases c2080 : 0 < b2
                                swap
                                · omega
                                by_cases c2081 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c2082 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f2083 := pair_fact E (i := 4) (j := 2) rfl rfl c2049 c2080
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2083
                                omega
                              by_cases c2084 : 0 < b0
                              swap
                              · omega
                              by_cases c2085 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c2086 : 0 < a4
                                swap
                                · omega
                                by_cases c2087 : 0 < b4
                                swap
                                · omega
                                by_cases c2088 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c2089 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f2090 := pair_fact E (i := 4) (j := 4) rfl rfl c2086 c2087
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2090
                                omega
                              by_cases c2091 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2092 := pair_fact E (i := 4) (j := 0) rfl rfl c2048 c2084
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2092
                              omega
                            by_cases c2093 : a0 + a2 + a4 < b0 + b2
                            swap
                            · omega
                            by_cases c2094 : b0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f2095 := pair_fact E (i := 6) (j := 2) rfl rfl c2046 c2047
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2095
                            omega
                          by_cases c2096 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c2097 : b0 < a0 + a2
                          swap
                          · omega
                          have f2098 := pair_fact E (i := 2) (j := 2) rfl rfl c2044 c2045
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2098
                          omega
                        by_cases c2099 : 0 < b0 + b2
                        swap
                        · omega
                        by_cases c2100 : b0 < 0 + a0
                        swap
                        · -- branch
                          by_cases c2101 : 0 < a2
                          swap
                          · omega
                          by_cases c2102 : 0 < b2
                          swap
                          · omega
                          by_cases c2103 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c2104 : b0 < a0 + a2
                          swap
                          · -- branch
                            by_cases c2105 : 0 < a6
                            swap
                            · omega
                            by_cases c2106 : 0 < b2
                            swap
                            · omega
                            by_cases c2107 : a0 + a2 + a4 < b0 + b2
                            swap
                            · -- branch
                              by_cases c2108 : 0 < a4
                              swap
                              · omega
                              by_cases c2109 : 0 < b2
                              swap
                              · omega
                              by_cases c2110 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c2111 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2112 := pair_fact E (i := 4) (j := 2) rfl rfl c2108 c2109
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2112
                              omega
                            by_cases c2113 : b0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f2114 := pair_fact E (i := 6) (j := 2) rfl rfl c2105 c2106
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2114
                            omega
                          have f2115 := pair_fact E (i := 2) (j := 2) rfl rfl c2101 c2102
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2115
                          omega
                        have f2116 := pair_fact E (i := 0) (j := 2) rfl rfl c2042 c2043
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2116
                        omega
                      have f2117 := pair_fact E (i := 2) (j := 4) rfl rfl c2038 c2039
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2117
                      omega
                    by_cases c2118 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c2119 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · omega
                    have f2120 := pair_fact E (i := 2) (j := 10) rfl rfl c2001 c2002
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2120
                    omega
                  have f2121 := pair_fact E (i := 2) (j := 8) rfl rfl c1997 c1998
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2121
                  omega
                by_cases c2122 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c2123 : b0 + b2 + b4 < a0 + a2
                swap
                · omega
                have f2124 := pair_fact E (i := 2) (j := 6) rfl rfl c1935 c1996
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2124
                omega
              by_cases c2125 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c2126 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
              swap
              · omega
              have f2127 := pair_fact E (i := 6) (j := 10) rfl rfl c1933 c1934
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2127
              omega
            by_cases c2128 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c2129 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · -- branch
              by_cases c2130 : 0 < a2
              swap
              · -- branch
                by_cases c2131 : 0 < a2
                swap
                · -- branch
                  by_cases c2132 : 0 < a2
                  swap
                  · -- branch
                    by_cases c2133 : 0 < a2
                    swap
                    · -- branch
                      by_cases c2134 : 0 < a2
                      swap
                      · -- branch
                        by_cases c2135 : 0 < a2
                        swap
                        · -- branch
                          by_cases c2136 : 0 < a6
                          swap
                          · omega
                          by_cases c2137 : 0 < b2
                          swap
                          · omega
                          by_cases c2138 : a0 + a2 + a4 < b0 + b2
                          swap
                          · -- branch
                            by_cases c2139 : 0 < a0
                            swap
                            · omega
                            by_cases c2140 : 0 < b2
                            swap
                            · omega
                            by_cases c2141 : 0 < b0 + b2
                            swap
                            · omega
                            by_cases c2142 : b0 < 0 + a0
                            swap
                            · -- branch
                              by_cases c2143 : 0 < a4
                              swap
                              · omega
                              by_cases c2144 : 0 < b0
                              swap
                              · omega
                              by_cases c2145 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c2146 : 0 < a4
                                swap
                                · omega
                                by_cases c2147 : 0 < b2
                                swap
                                · omega
                                by_cases c2148 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c2149 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f2150 := pair_fact E (i := 4) (j := 2) rfl rfl c2146 c2147
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2150
                                by_cases c2151 : 0 < a4
                                swap
                                · omega
                                by_cases c2152 : 0 < b6
                                swap
                                · -- branch
                                  by_cases c2153 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c2154 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c2155 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c2156 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c2157 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c2158 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c2159 : a0 + a2 + a4 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c2160 : b0 + b2 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f2161 := pair_fact E (i := 6) (j := 4) rfl rfl c2157 c2158
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2161
                                    omega
                                  have f2162 := pair_fact E (i := 4) (j := 8) rfl rfl c2153 c2154
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2162
                                  omega
                                by_cases c2163 : a0 + a2 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c2164 : b0 + b2 + b4 < a0 + a2 + a4
                                swap
                                · omega
                                have f2165 := pair_fact E (i := 4) (j := 6) rfl rfl c2151 c2152
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2165
                                omega
                              by_cases c2166 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2167 := pair_fact E (i := 4) (j := 0) rfl rfl c2143 c2144
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2167
                              omega
                            have f2168 := pair_fact E (i := 0) (j := 2) rfl rfl c2139 c2140
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2168
                            by_cases c2169 : 0 < a6
                            swap
                            · omega
                            by_cases c2170 : 0 < b4
                            swap
                            · omega
                            by_cases c2171 : a0 + a2 + a4 < b0 + b2 + b4
                            swap
                            · -- branch
                              by_cases c2172 : 0 < a4
                              swap
                              · omega
                              by_cases c2173 : 0 < b4
                              swap
                              · omega
                              by_cases c2174 : a0 + a2 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c2175 : b0 + b2 < a0 + a2 + a4
                              swap
                              · omega
                              have f2176 := pair_fact E (i := 4) (j := 4) rfl rfl c2172 c2173
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2176
                              omega
                            by_cases c2177 : b0 + b2 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f2178 := pair_fact E (i := 6) (j := 4) rfl rfl c2169 c2170
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2178
                            omega
                          by_cases c2179 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f2180 := pair_fact E (i := 6) (j := 2) rfl rfl c2136 c2137
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2180
                          omega
                        by_cases c2181 : 0 < b10
                        swap
                        · omega
                        by_cases c2182 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c2183 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                        swap
                        · omega
                        have f2184 := pair_fact E (i := 2) (j := 10) rfl rfl c2135 c2181
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2184
                        omega
                      by_cases c2185 : 0 < b8
                      swap
                      · omega
                      by_cases c2186 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c2187 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · omega
                      have f2188 := pair_fact E (i := 2) (j := 8) rfl rfl c2134 c2185
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2188
                      omega
                    by_cases c2189 : 0 < b4
                    swap
                    · omega
                    by_cases c2190 : a0 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c2191 : b0 + b2 < a0 + a2
                    swap
                    · omega
                    have f2192 := pair_fact E (i := 2) (j := 4) rfl rfl c2133 c2189
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2192
                    omega
                  by_cases c2193 : 0 < b2
                  swap
                  · omega
                  by_cases c2194 : a0 < b0 + b2
                  swap
                  · omega
                  by_cases c2195 : b0 < a0 + a2
                  swap
                  · omega
                  have f2196 := pair_fact E (i := 2) (j := 2) rfl rfl c2132 c2193
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2196
                  omega
                by_cases c2197 : 0 < b0
                swap
                · omega
                by_cases c2198 : a0 < 0 + b0
                swap
                · omega
                by_cases c2199 : 0 < a0 + a2
                swap
                · omega
                have f2200 := pair_fact E (i := 2) (j := 0) rfl rfl c2131 c2197
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2200
                omega
              by_cases c2201 : 0 < b6
              swap
              · -- branch
                by_cases c2202 : 0 < a2
                swap
                · omega
                by_cases c2203 : 0 < b8
                swap
                · omega
                by_cases c2204 : a0 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c2205 : b0 + b2 + b4 + b6 < a0 + a2
                swap
                · -- branch
                  by_cases c2206 : 0 < a2
                  swap
                  · omega
                  by_cases c2207 : 0 < b10
                  swap
                  · omega
                  by_cases c2208 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c2209 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                  swap
                  · -- branch
                    by_cases c2210 : 0 < a2
                    swap
                    · omega
                    by_cases c2211 : 0 < b0
                    swap
                    · omega
                    by_cases c2212 : a0 < 0 + b0
                    swap
                    · -- branch
                      by_cases c2213 : 0 < a2
                      swap
                      · omega
                      by_cases c2214 : 0 < b4
                      swap
                      · omega
                      by_cases c2215 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c2216 : b0 + b2 < a0 + a2
                      swap
                      · -- branch
                        by_cases c2217 : 0 < a2
                        swap
                        · omega
                        by_cases c2218 : 0 < b2
                        swap
                        · omega
                        by_cases c2219 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c2220 : b0 < a0 + a2
                        swap
                        · omega
                        have f2221 := pair_fact E (i := 2) (j := 2) rfl rfl c2217 c2218
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2221
                        by_cases c2222 : 0 < a0
                        swap
                        · omega
                        by_cases c2223 : 0 < b2
                        swap
                        · omega
                        by_cases c2224 : 0 < b0 + b2
                        swap
                        · omega
                        by_cases c2225 : b0 < 0 + a0
                        swap
                        · -- branch
                          by_cases c2226 : 0 < a6
                          swap
                          · omega
                          by_cases c2227 : 0 < b2
                          swap
                          · omega
                          by_cases c2228 : a0 + a2 + a4 < b0 + b2
                          swap
                          · -- branch
                            by_cases c2229 : 0 < a4
                            swap
                            · omega
                            by_cases c2230 : 0 < b0
                            swap
                            · omega
                            by_cases c2231 : a0 + a2 < 0 + b0
                            swap
                            · -- branch
                              by_cases c2232 : 0 < a4
                              swap
                              · omega
                              by_cases c2233 : 0 < b2
                              swap
                              · omega
                              by_cases c2234 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c2235 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2236 := pair_fact E (i := 4) (j := 2) rfl rfl c2232 c2233
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2236
                              by_cases c2237 : 0 < a4
                              swap
                              · omega
                              by_cases c2238 : 0 < b4
                              swap
                              · omega
                              by_cases c2239 : a0 + a2 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c2240 : b0 + b2 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c2241 : 0 < a6
                                swap
                                · omega
                                by_cases c2242 : 0 < b4
                                swap
                                · omega
                                by_cases c2243 : a0 + a2 + a4 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c2244 : b0 + b2 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f2245 := pair_fact E (i := 6) (j := 4) rfl rfl c2241 c2242
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2245
                                omega
                              have f2246 := pair_fact E (i := 4) (j := 4) rfl rfl c2237 c2238
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2246
                              omega
                            by_cases c2247 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f2248 := pair_fact E (i := 4) (j := 0) rfl rfl c2229 c2230
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2248
                            omega
                          by_cases c2249 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f2250 := pair_fact E (i := 6) (j := 2) rfl rfl c2226 c2227
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2250
                          omega
                        have f2251 := pair_fact E (i := 0) (j := 2) rfl rfl c2222 c2223
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2251
                        omega
                      have f2252 := pair_fact E (i := 2) (j := 4) rfl rfl c2213 c2214
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2252
                      by_cases c2253 : 0 < a6
                      swap
                      · omega
                      by_cases c2254 : 0 < b4
                      swap
                      · omega
                      by_cases c2255 : a0 + a2 + a4 < b0 + b2 + b4
                      swap
                      · -- branch
                        by_cases c2256 : 0 < a4
                        swap
                        · omega
                        by_cases c2257 : 0 < b0
                        swap
                        · omega
                        by_cases c2258 : a0 + a2 < 0 + b0
                        swap
                        · -- branch
                          by_cases c2259 : 0 < a4
                          swap
                          · omega
                          by_cases c2260 : 0 < b6
                          swap
                          · -- branch
                            by_cases c2261 : 0 < a4
                            swap
                            · omega
                            by_cases c2262 : 0 < b8
                            swap
                            · omega
                            by_cases c2263 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c2264 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c2265 : 0 < a0
                              swap
                              · omega
                              by_cases c2266 : 0 < b2
                              swap
                              · omega
                              by_cases c2267 : 0 < b0 + b2
                              swap
                              · omega
                              by_cases c2268 : b0 < 0 + a0
                              swap
                              · omega
                              have f2269 := pair_fact E (i := 0) (j := 2) rfl rfl c2265 c2266
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2269
                              omega
                            have f2270 := pair_fact E (i := 4) (j := 8) rfl rfl c2261 c2262
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2270
                            omega
                          by_cases c2271 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c2272 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · omega
                          have f2273 := pair_fact E (i := 4) (j := 6) rfl rfl c2259 c2260
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2273
                          omega
                        by_cases c2274 : 0 < a0 + a2 + a4
                        swap
                        · omega
                        have f2275 := pair_fact E (i := 4) (j := 0) rfl rfl c2256 c2257
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2275
                        omega
                      by_cases c2276 : b0 + b2 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f2277 := pair_fact E (i := 6) (j := 4) rfl rfl c2253 c2254
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2277
                      omega
                    by_cases c2278 : 0 < a0 + a2
                    swap
                    · omega
                    have f2279 := pair_fact E (i := 2) (j := 0) rfl rfl c2210 c2211
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2279
                    by_cases c2280 : 0 < a2
                    swap
                    · omega
                    by_cases c2281 : 0 < b4
                    swap
                    · omega
                    by_cases c2282 : a0 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c2283 : b0 + b2 < a0 + a2
                    swap
                    · -- branch
                      by_cases c2284 : 0 < a0
                      swap
                      · omega
                      by_cases c2285 : 0 < b2
                      swap
                      · -- branch
                        by_cases c2286 : 0 < a2
                        swap
                        · omega
                        by_cases c2287 : 0 < b2
                        swap
                        · -- branch
                          by_cases c2288 : 0 < a6
                          swap
                          · omega
                          by_cases c2289 : 0 < b2
                          swap
                          · -- branch
                            by_cases c2290 : 0 < a4
                            swap
                            · -- branch
                              by_cases c2291 : 0 < a4
                              swap
                              · -- branch
                                by_cases c2292 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c2293 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c2294 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c2295 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c2296 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c2297 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c2298 : a0 + a2 + a4 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c2299 : b0 + b2 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f2300 := pair_fact E (i := 6) (j := 4) rfl rfl c2296 c2297
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2300
                                        by_cases c2301 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c2302 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c2303 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c2304 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f2305 := pair_fact E (i := 8) (j := 4) rfl rfl c2301 c2302
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2305
                                        omega
                                      by_cases c2306 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c2307 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c2308 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f2309 := pair_fact E (i := 4) (j := 10) rfl rfl c2295 c2306
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2309
                                      omega
                                    by_cases c2310 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c2311 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c2312 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f2313 := pair_fact E (i := 4) (j := 8) rfl rfl c2294 c2310
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2313
                                    omega
                                  by_cases c2314 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c2315 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c2316 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f2317 := pair_fact E (i := 4) (j := 6) rfl rfl c2293 c2314
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2317
                                  omega
                                by_cases c2318 : 0 < b4
                                swap
                                · omega
                                by_cases c2319 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c2320 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f2321 := pair_fact E (i := 4) (j := 4) rfl rfl c2292 c2318
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2321
                                omega
                              by_cases c2322 : 0 < b2
                              swap
                              · omega
                              by_cases c2323 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c2324 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2325 := pair_fact E (i := 4) (j := 2) rfl rfl c2291 c2322
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2325
                              omega
                            by_cases c2326 : 0 < b0
                            swap
                            · omega
                            by_cases c2327 : a0 + a2 < 0 + b0
                            swap
                            · -- branch
                              by_cases c2328 : 0 < a4
                              swap
                              · omega
                              by_cases c2329 : 0 < b4
                              swap
                              · omega
                              by_cases c2330 : a0 + a2 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c2331 : b0 + b2 < a0 + a2 + a4
                              swap
                              · omega
                              have f2332 := pair_fact E (i := 4) (j := 4) rfl rfl c2328 c2329
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2332
                              omega
                            by_cases c2333 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f2334 := pair_fact E (i := 4) (j := 0) rfl rfl c2290 c2326
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2334
                            omega
                          by_cases c2335 : a0 + a2 + a4 < b0 + b2
                          swap
                          · omega
                          by_cases c2336 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f2337 := pair_fact E (i := 6) (j := 2) rfl rfl c2288 c2289
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2337
                          omega
                        by_cases c2338 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c2339 : b0 < a0 + a2
                        swap
                        · omega
                        have f2340 := pair_fact E (i := 2) (j := 2) rfl rfl c2286 c2287
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2340
                        omega
                      by_cases c2341 : 0 < b0 + b2
                      swap
                      · omega
                      by_cases c2342 : b0 < 0 + a0
                      swap
                      · -- branch
                        by_cases c2343 : 0 < a2
                        swap
                        · omega
                        by_cases c2344 : 0 < b2
                        swap
                        · omega
                        by_cases c2345 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c2346 : b0 < a0 + a2
                        swap
                        · -- branch
                          by_cases c2347 : 0 < a6
                          swap
                          · omega
                          by_cases c2348 : 0 < b2
                          swap
                          · omega
                          by_cases c2349 : a0 + a2 + a4 < b0 + b2
                          swap
                          · -- branch
                            by_cases c2350 : 0 < a4
                            swap
                            · omega
                            by_cases c2351 : 0 < b2
                            swap
                            · omega
                            by_cases c2352 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c2353 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f2354 := pair_fact E (i := 4) (j := 2) rfl rfl c2350 c2351
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2354
                            omega
                          by_cases c2355 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f2356 := pair_fact E (i := 6) (j := 2) rfl rfl c2347 c2348
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2356
                          omega
                        have f2357 := pair_fact E (i := 2) (j := 2) rfl rfl c2343 c2344
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2357
                        omega
                      have f2358 := pair_fact E (i := 0) (j := 2) rfl rfl c2284 c2285
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2358
                      omega
                    have f2359 := pair_fact E (i := 2) (j := 4) rfl rfl c2280 c2281
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2359
                    omega
                  have f2360 := pair_fact E (i := 2) (j := 10) rfl rfl c2206 c2207
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2360
                  omega
                have f2361 := pair_fact E (i := 2) (j := 8) rfl rfl c2202 c2203
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2361
                omega
              by_cases c2362 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c2363 : b0 + b2 + b4 < a0 + a2
              swap
              · omega
              have f2364 := pair_fact E (i := 2) (j := 6) rfl rfl c2130 c2201
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2364
              omega
            have f2365 := pair_fact E (i := 0) (j := 10) rfl rfl c1931 c1932
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2365
            omega
          have f2366 := pair_fact E (i := 0) (j := 8) rfl rfl c1647 c1648
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2366
          omega
        by_cases c2367 : a0 + a2 + a4 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c2368 : b0 + b2 + b4 < a0 + a2 + a4 + a6
        swap
        · omega
        have f2369 := pair_fact E (i := 6) (j := 6) rfl rfl c1645 c1646
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2369
        omega
      by_cases c2370 : 0 < a0 + a2 + a4 + a6
      swap
      · omega
      have f2371 := pair_fact E (i := 6) (j := 0) rfl rfl c1642 c1643
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2371
      omega
    by_cases c2372 : 0 < b0 + b2 + b4 + b6
    swap
    · omega
    by_cases c2373 : b0 + b2 + b4 < 0 + a0
    swap
    · -- branch
      by_cases c2374 : 0 < a0
      swap
      · omega
      by_cases c2375 : 0 < b8
      swap
      · -- branch
        by_cases c2376 : 0 < a8
        swap
        · omega
        by_cases c2377 : 0 < b0
        swap
        · omega
        by_cases c2378 : a0 + a2 + a4 + a6 < 0 + b0
        swap
        · -- branch
          by_cases c2379 : 0 < a8
          swap
          · omega
          by_cases c2380 : 0 < b8
          swap
          · -- branch
            by_cases c2381 : 0 < a0
            swap
            · omega
            by_cases c2382 : 0 < b10
            swap
            · -- branch
              by_cases c2383 : 0 < a8
              swap
              · omega
              by_cases c2384 : 0 < b10
              swap
              · -- branch
                by_cases c2385 : 0 < a2
                swap
                · -- branch
                  by_cases c2386 : 0 < a2
                  swap
                  · -- branch
                    by_cases c2387 : 0 < a2
                    swap
                    · -- branch
                      by_cases c2388 : 0 < a2
                      swap
                      · -- branch
                        by_cases c2389 : 0 < a2
                        swap
                        · -- branch
                          by_cases c2390 : 0 < a2
                          swap
                          · -- branch
                            by_cases c2391 : 0 < a8
                            swap
                            · omega
                            by_cases c2392 : 0 < b2
                            swap
                            · omega
                            by_cases c2393 : a0 + a2 + a4 + a6 < b0 + b2
                            swap
                            · -- branch
                              by_cases c2394 : 0 < a0
                              swap
                              · omega
                              by_cases c2395 : 0 < b2
                              swap
                              · omega
                              by_cases c2396 : 0 < b0 + b2
                              swap
                              · omega
                              by_cases c2397 : b0 < 0 + a0
                              swap
                              · -- branch
                                by_cases c2398 : 0 < a4
                                swap
                                · omega
                                by_cases c2399 : 0 < b0
                                swap
                                · omega
                                by_cases c2400 : a0 + a2 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c2401 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c2402 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c2403 : a0 + a2 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c2404 : b0 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f2405 := pair_fact E (i := 4) (j := 2) rfl rfl c2401 c2402
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2405
                                  by_cases c2406 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c2407 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c2408 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c2409 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f2410 := pair_fact E (i := 8) (j := 4) rfl rfl c2406 c2407
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2410
                                  omega
                                by_cases c2411 : 0 < a0 + a2 + a4
                                swap
                                · omega
                                have f2412 := pair_fact E (i := 4) (j := 0) rfl rfl c2398 c2399
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2412
                                omega
                              have f2413 := pair_fact E (i := 0) (j := 2) rfl rfl c2394 c2395
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2413
                              by_cases c2414 : 0 < a8
                              swap
                              · omega
                              by_cases c2415 : 0 < b4
                              swap
                              · omega
                              by_cases c2416 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                              swap
                              · -- branch
                                by_cases c2417 : 0 < a4
                                swap
                                · omega
                                by_cases c2418 : 0 < b4
                                swap
                                · omega
                                by_cases c2419 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c2420 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f2421 := pair_fact E (i := 4) (j := 4) rfl rfl c2417 c2418
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2421
                                omega
                              by_cases c2422 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f2423 := pair_fact E (i := 8) (j := 4) rfl rfl c2414 c2415
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2423
                              omega
                            by_cases c2424 : b0 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f2425 := pair_fact E (i := 8) (j := 2) rfl rfl c2391 c2392
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2425
                            omega
                          by_cases c2426 : 0 < b10
                          swap
                          · omega
                          by_cases c2427 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c2428 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · omega
                          have f2429 := pair_fact E (i := 2) (j := 10) rfl rfl c2390 c2426
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2429
                          omega
                        by_cases c2430 : 0 < b8
                        swap
                        · omega
                        by_cases c2431 : a0 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c2432 : b0 + b2 + b4 + b6 < a0 + a2
                        swap
                        · omega
                        have f2433 := pair_fact E (i := 2) (j := 8) rfl rfl c2389 c2430
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2433
                        omega
                      by_cases c2434 : 0 < b4
                      swap
                      · omega
                      by_cases c2435 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c2436 : b0 + b2 < a0 + a2
                      swap
                      · omega
                      have f2437 := pair_fact E (i := 2) (j := 4) rfl rfl c2388 c2434
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2437
                      omega
                    by_cases c2438 : 0 < b2
                    swap
                    · omega
                    by_cases c2439 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c2440 : b0 < a0 + a2
                    swap
                    · omega
                    have f2441 := pair_fact E (i := 2) (j := 2) rfl rfl c2387 c2438
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2441
                    omega
                  by_cases c2442 : 0 < b0
                  swap
                  · omega
                  by_cases c2443 : a0 < 0 + b0
                  swap
                  · omega
                  by_cases c2444 : 0 < a0 + a2
                  swap
                  · omega
                  have f2445 := pair_fact E (i := 2) (j := 0) rfl rfl c2386 c2442
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2445
                  omega
                by_cases c2446 : 0 < b6
                swap
                · omega
                by_cases c2447 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c2448 : b0 + b2 + b4 < a0 + a2
                swap
                · -- branch
                  by_cases c2449 : 0 < a2
                  swap
                  · omega
                  by_cases c2450 : 0 < b8
                  swap
                  · -- branch
                    by_cases c2451 : 0 < a2
                    swap
                    · omega
                    by_cases c2452 : 0 < b10
                    swap
                    · -- branch
                      by_cases c2453 : 0 < a2
                      swap
                      · omega
                      by_cases c2454 : 0 < b0
                      swap
                      · omega
                      by_cases c2455 : a0 < 0 + b0
                      swap
                      · -- branch
                        by_cases c2456 : 0 < a2
                        swap
                        · omega
                        by_cases c2457 : 0 < b4
                        swap
                        · omega
                        by_cases c2458 : a0 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c2459 : b0 + b2 < a0 + a2
                        swap
                        · -- branch
                          by_cases c2460 : 0 < a2
                          swap
                          · omega
                          by_cases c2461 : 0 < b2
                          swap
                          · omega
                          by_cases c2462 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c2463 : b0 < a0 + a2
                          swap
                          · omega
                          have f2464 := pair_fact E (i := 2) (j := 2) rfl rfl c2460 c2461
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2464
                          by_cases c2465 : 0 < a0
                          swap
                          · omega
                          by_cases c2466 : 0 < b2
                          swap
                          · omega
                          by_cases c2467 : 0 < b0 + b2
                          swap
                          · omega
                          by_cases c2468 : b0 < 0 + a0
                          swap
                          · -- branch
                            by_cases c2469 : 0 < a8
                            swap
                            · omega
                            by_cases c2470 : 0 < b4
                            swap
                            · omega
                            by_cases c2471 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c2472 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f2473 := pair_fact E (i := 8) (j := 4) rfl rfl c2469 c2470
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2473
                            omega
                          have f2474 := pair_fact E (i := 0) (j := 2) rfl rfl c2465 c2466
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2474
                          omega
                        have f2475 := pair_fact E (i := 2) (j := 4) rfl rfl c2456 c2457
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2475
                        by_cases c2476 : 0 < a6
                        swap
                        · -- branch
                          by_cases c2477 : 0 < a6
                          swap
                          · -- branch
                            by_cases c2478 : 0 < a6
                            swap
                            · -- branch
                              by_cases c2479 : 0 < a6
                              swap
                              · -- branch
                                by_cases c2480 : 0 < a6
                                swap
                                · -- branch
                                  by_cases c2481 : 0 < a6
                                  swap
                                  · -- branch
                                    by_cases c2482 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c2483 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c2484 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                    swap
                                    · -- branch
                                      by_cases c2485 : 0 < a0
                                      swap
                                      · omega
                                      by_cases c2486 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c2487 : 0 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c2488 : b0 < 0 + a0
                                      swap
                                      · omega
                                      have f2489 := pair_fact E (i := 0) (j := 2) rfl rfl c2485 c2486
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2489
                                      omega
                                    by_cases c2490 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f2491 := pair_fact E (i := 8) (j := 4) rfl rfl c2482 c2483
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2491
                                    omega
                                  by_cases c2492 : 0 < b10
                                  swap
                                  · omega
                                  by_cases c2493 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                  swap
                                  · omega
                                  by_cases c2494 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f2495 := pair_fact E (i := 6) (j := 10) rfl rfl c2481 c2492
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2495
                                  omega
                                by_cases c2496 : 0 < b8
                                swap
                                · omega
                                by_cases c2497 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                swap
                                · omega
                                by_cases c2498 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f2499 := pair_fact E (i := 6) (j := 8) rfl rfl c2480 c2496
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2499
                                omega
                              by_cases c2500 : 0 < b6
                              swap
                              · omega
                              by_cases c2501 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c2502 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f2503 := pair_fact E (i := 6) (j := 6) rfl rfl c2479 c2500
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2503
                              omega
                            by_cases c2504 : 0 < b2
                            swap
                            · omega
                            by_cases c2505 : a0 + a2 + a4 < b0 + b2
                            swap
                            · omega
                            by_cases c2506 : b0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f2507 := pair_fact E (i := 6) (j := 2) rfl rfl c2478 c2504
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2507
                            omega
                          by_cases c2508 : 0 < b0
                          swap
                          · omega
                          by_cases c2509 : a0 + a2 + a4 < 0 + b0
                          swap
                          · omega
                          by_cases c2510 : 0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f2511 := pair_fact E (i := 6) (j := 0) rfl rfl c2477 c2508
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2511
                          omega
                        by_cases c2512 : 0 < b4
                        swap
                        · omega
                        by_cases c2513 : a0 + a2 + a4 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c2514 : b0 + b2 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f2515 := pair_fact E (i := 6) (j := 4) rfl rfl c2476 c2512
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2515
                        omega
                      by_cases c2516 : 0 < a0 + a2
                      swap
                      · omega
                      have f2517 := pair_fact E (i := 2) (j := 0) rfl rfl c2453 c2454
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2517
                      by_cases c2518 : 0 < a2
                      swap
                      · omega
                      by_cases c2519 : 0 < b4
                      swap
                      · omega
                      by_cases c2520 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c2521 : b0 + b2 < a0 + a2
                      swap
                      · -- branch
                        by_cases c2522 : 0 < a0
                        swap
                        · omega
                        by_cases c2523 : 0 < b2
                        swap
                        · -- branch
                          by_cases c2524 : 0 < a2
                          swap
                          · omega
                          by_cases c2525 : 0 < b2
                          swap
                          · -- branch
                            by_cases c2526 : 0 < a8
                            swap
                            · omega
                            by_cases c2527 : 0 < b2
                            swap
                            · -- branch
                              by_cases c2528 : 0 < a4
                              swap
                              · -- branch
                                by_cases c2529 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c2530 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c2531 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c2532 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c2533 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c2534 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c2535 : 0 < b0
                                          swap
                                          · omega
                                          by_cases c2536 : a0 + a2 + a4 < 0 + b0
                                          swap
                                          · -- branch
                                            by_cases c2537 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c2538 : 0 < b2
                                            swap
                                            · -- branch
                                              by_cases c2539 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c2540 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c2541 : a0 + a2 + a4 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c2542 : b0 + b2 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f2543 := pair_fact E (i := 6) (j := 4) rfl rfl c2539 c2540
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2543
                                              by_cases c2544 : 0 < a8
                                              swap
                                              · omega
                                              by_cases c2545 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c2546 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c2547 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                              swap
                                              · omega
                                              have f2548 := pair_fact E (i := 8) (j := 4) rfl rfl c2544 c2545
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2548
                                              omega
                                            by_cases c2549 : a0 + a2 + a4 < b0 + b2
                                            swap
                                            · omega
                                            by_cases c2550 : b0 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f2551 := pair_fact E (i := 6) (j := 2) rfl rfl c2537 c2538
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2551
                                            omega
                                          by_cases c2552 : 0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f2553 := pair_fact E (i := 6) (j := 0) rfl rfl c2534 c2535
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2553
                                          omega
                                        by_cases c2554 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c2555 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c2556 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f2557 := pair_fact E (i := 4) (j := 10) rfl rfl c2533 c2554
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2557
                                        omega
                                      by_cases c2558 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c2559 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c2560 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f2561 := pair_fact E (i := 4) (j := 8) rfl rfl c2532 c2558
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2561
                                      omega
                                    by_cases c2562 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c2563 : a0 + a2 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c2564 : b0 + b2 + b4 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f2565 := pair_fact E (i := 4) (j := 6) rfl rfl c2531 c2562
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2565
                                    omega
                                  by_cases c2566 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c2567 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c2568 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f2569 := pair_fact E (i := 4) (j := 4) rfl rfl c2530 c2566
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2569
                                  omega
                                by_cases c2570 : 0 < b2
                                swap
                                · omega
                                by_cases c2571 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c2572 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f2573 := pair_fact E (i := 4) (j := 2) rfl rfl c2529 c2570
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2573
                                omega
                              by_cases c2574 : 0 < b0
                              swap
                              · omega
                              by_cases c2575 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c2576 : 0 < a4
                                swap
                                · omega
                                by_cases c2577 : 0 < b4
                                swap
                                · omega
                                by_cases c2578 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c2579 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f2580 := pair_fact E (i := 4) (j := 4) rfl rfl c2576 c2577
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2580
                                omega
                              by_cases c2581 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2582 := pair_fact E (i := 4) (j := 0) rfl rfl c2528 c2574
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2582
                              omega
                            by_cases c2583 : a0 + a2 + a4 + a6 < b0 + b2
                            swap
                            · omega
                            by_cases c2584 : b0 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f2585 := pair_fact E (i := 8) (j := 2) rfl rfl c2526 c2527
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2585
                            omega
                          by_cases c2586 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c2587 : b0 < a0 + a2
                          swap
                          · omega
                          have f2588 := pair_fact E (i := 2) (j := 2) rfl rfl c2524 c2525
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2588
                          omega
                        by_cases c2589 : 0 < b0 + b2
                        swap
                        · omega
                        by_cases c2590 : b0 < 0 + a0
                        swap
                        · -- branch
                          by_cases c2591 : 0 < a2
                          swap
                          · omega
                          by_cases c2592 : 0 < b2
                          swap
                          · omega
                          by_cases c2593 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c2594 : b0 < a0 + a2
                          swap
                          · -- branch
                            by_cases c2595 : 0 < a8
                            swap
                            · omega
                            by_cases c2596 : 0 < b2
                            swap
                            · omega
                            by_cases c2597 : a0 + a2 + a4 + a6 < b0 + b2
                            swap
                            · -- branch
                              by_cases c2598 : 0 < a4
                              swap
                              · -- branch
                                by_cases c2599 : 0 < a6
                                swap
                                · omega
                                by_cases c2600 : 0 < b2
                                swap
                                · omega
                                by_cases c2601 : a0 + a2 + a4 < b0 + b2
                                swap
                                · omega
                                by_cases c2602 : b0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f2603 := pair_fact E (i := 6) (j := 2) rfl rfl c2599 c2600
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2603
                                omega
                              by_cases c2604 : 0 < b0
                              swap
                              · omega
                              by_cases c2605 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c2606 : 0 < a4
                                swap
                                · omega
                                by_cases c2607 : 0 < b2
                                swap
                                · omega
                                by_cases c2608 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c2609 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f2610 := pair_fact E (i := 4) (j := 2) rfl rfl c2606 c2607
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2610
                                omega
                              by_cases c2611 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2612 := pair_fact E (i := 4) (j := 0) rfl rfl c2598 c2604
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2612
                              omega
                            by_cases c2613 : b0 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f2614 := pair_fact E (i := 8) (j := 2) rfl rfl c2595 c2596
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2614
                            omega
                          have f2615 := pair_fact E (i := 2) (j := 2) rfl rfl c2591 c2592
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2615
                          omega
                        have f2616 := pair_fact E (i := 0) (j := 2) rfl rfl c2522 c2523
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2616
                        omega
                      have f2617 := pair_fact E (i := 2) (j := 4) rfl rfl c2518 c2519
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2617
                      omega
                    by_cases c2618 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c2619 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · omega
                    have f2620 := pair_fact E (i := 2) (j := 10) rfl rfl c2451 c2452
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2620
                    omega
                  by_cases c2621 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c2622 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · omega
                  have f2623 := pair_fact E (i := 2) (j := 8) rfl rfl c2449 c2450
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2623
                  omega
                have f2624 := pair_fact E (i := 2) (j := 6) rfl rfl c2385 c2446
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2624
                omega
              by_cases c2625 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c2626 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
              swap
              · omega
              have f2627 := pair_fact E (i := 8) (j := 10) rfl rfl c2383 c2384
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2627
              omega
            by_cases c2628 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c2629 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · -- branch
              by_cases c2630 : 0 < a2
              swap
              · -- branch
                by_cases c2631 : 0 < a2
                swap
                · -- branch
                  by_cases c2632 : 0 < a2
                  swap
                  · -- branch
                    by_cases c2633 : 0 < a2
                    swap
                    · -- branch
                      by_cases c2634 : 0 < a2
                      swap
                      · -- branch
                        by_cases c2635 : 0 < a2
                        swap
                        · -- branch
                          by_cases c2636 : 0 < a8
                          swap
                          · omega
                          by_cases c2637 : 0 < b2
                          swap
                          · omega
                          by_cases c2638 : a0 + a2 + a4 + a6 < b0 + b2
                          swap
                          · -- branch
                            by_cases c2639 : 0 < a0
                            swap
                            · omega
                            by_cases c2640 : 0 < b2
                            swap
                            · omega
                            by_cases c2641 : 0 < b0 + b2
                            swap
                            · omega
                            by_cases c2642 : b0 < 0 + a0
                            swap
                            · -- branch
                              by_cases c2643 : 0 < a4
                              swap
                              · omega
                              by_cases c2644 : 0 < b0
                              swap
                              · omega
                              by_cases c2645 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c2646 : 0 < a4
                                swap
                                · omega
                                by_cases c2647 : 0 < b2
                                swap
                                · omega
                                by_cases c2648 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c2649 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f2650 := pair_fact E (i := 4) (j := 2) rfl rfl c2646 c2647
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2650
                                by_cases c2651 : 0 < a4
                                swap
                                · omega
                                by_cases c2652 : 0 < b6
                                swap
                                · omega
                                by_cases c2653 : a0 + a2 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c2654 : b0 + b2 + b4 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c2655 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c2656 : 0 < b8
                                  swap
                                  · -- branch
                                    by_cases c2657 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c2658 : 0 < b10
                                    swap
                                    · omega
                                    by_cases c2659 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c2660 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c2661 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c2662 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c2663 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                      swap
                                      · -- branch
                                        by_cases c2664 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c2665 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c2666 : a0 + a2 + a4 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c2667 : b0 + b2 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f2668 := pair_fact E (i := 6) (j := 4) rfl rfl c2664 c2665
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2668
                                        omega
                                      by_cases c2669 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f2670 := pair_fact E (i := 8) (j := 4) rfl rfl c2661 c2662
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2670
                                      omega
                                    have f2671 := pair_fact E (i := 4) (j := 10) rfl rfl c2657 c2658
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2671
                                    omega
                                  by_cases c2672 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c2673 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f2674 := pair_fact E (i := 4) (j := 8) rfl rfl c2655 c2656
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2674
                                  omega
                                have f2675 := pair_fact E (i := 4) (j := 6) rfl rfl c2651 c2652
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2675
                                omega
                              by_cases c2676 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2677 := pair_fact E (i := 4) (j := 0) rfl rfl c2643 c2644
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2677
                              omega
                            have f2678 := pair_fact E (i := 0) (j := 2) rfl rfl c2639 c2640
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2678
                            by_cases c2679 : 0 < a8
                            swap
                            · omega
                            by_cases c2680 : 0 < b4
                            swap
                            · omega
                            by_cases c2681 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                            swap
                            · -- branch
                              by_cases c2682 : 0 < a4
                              swap
                              · omega
                              by_cases c2683 : 0 < b4
                              swap
                              · omega
                              by_cases c2684 : a0 + a2 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c2685 : b0 + b2 < a0 + a2 + a4
                              swap
                              · omega
                              have f2686 := pair_fact E (i := 4) (j := 4) rfl rfl c2682 c2683
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2686
                              omega
                            by_cases c2687 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f2688 := pair_fact E (i := 8) (j := 4) rfl rfl c2679 c2680
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2688
                            omega
                          by_cases c2689 : b0 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f2690 := pair_fact E (i := 8) (j := 2) rfl rfl c2636 c2637
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2690
                          omega
                        by_cases c2691 : 0 < b10
                        swap
                        · omega
                        by_cases c2692 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c2693 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                        swap
                        · omega
                        have f2694 := pair_fact E (i := 2) (j := 10) rfl rfl c2635 c2691
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2694
                        omega
                      by_cases c2695 : 0 < b8
                      swap
                      · omega
                      by_cases c2696 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c2697 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · omega
                      have f2698 := pair_fact E (i := 2) (j := 8) rfl rfl c2634 c2695
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2698
                      omega
                    by_cases c2699 : 0 < b4
                    swap
                    · omega
                    by_cases c2700 : a0 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c2701 : b0 + b2 < a0 + a2
                    swap
                    · omega
                    have f2702 := pair_fact E (i := 2) (j := 4) rfl rfl c2633 c2699
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2702
                    omega
                  by_cases c2703 : 0 < b2
                  swap
                  · omega
                  by_cases c2704 : a0 < b0 + b2
                  swap
                  · omega
                  by_cases c2705 : b0 < a0 + a2
                  swap
                  · omega
                  have f2706 := pair_fact E (i := 2) (j := 2) rfl rfl c2632 c2703
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2706
                  omega
                by_cases c2707 : 0 < b0
                swap
                · omega
                by_cases c2708 : a0 < 0 + b0
                swap
                · omega
                by_cases c2709 : 0 < a0 + a2
                swap
                · omega
                have f2710 := pair_fact E (i := 2) (j := 0) rfl rfl c2631 c2707
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2710
                omega
              by_cases c2711 : 0 < b6
              swap
              · omega
              by_cases c2712 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c2713 : b0 + b2 + b4 < a0 + a2
              swap
              · -- branch
                by_cases c2714 : 0 < a2
                swap
                · omega
                by_cases c2715 : 0 < b8
                swap
                · -- branch
                  by_cases c2716 : 0 < a2
                  swap
                  · omega
                  by_cases c2717 : 0 < b10
                  swap
                  · omega
                  by_cases c2718 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c2719 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                  swap
                  · -- branch
                    by_cases c2720 : 0 < a2
                    swap
                    · omega
                    by_cases c2721 : 0 < b0
                    swap
                    · omega
                    by_cases c2722 : a0 < 0 + b0
                    swap
                    · -- branch
                      by_cases c2723 : 0 < a2
                      swap
                      · omega
                      by_cases c2724 : 0 < b4
                      swap
                      · omega
                      by_cases c2725 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c2726 : b0 + b2 < a0 + a2
                      swap
                      · -- branch
                        by_cases c2727 : 0 < a2
                        swap
                        · omega
                        by_cases c2728 : 0 < b2
                        swap
                        · omega
                        by_cases c2729 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c2730 : b0 < a0 + a2
                        swap
                        · omega
                        have f2731 := pair_fact E (i := 2) (j := 2) rfl rfl c2727 c2728
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2731
                        by_cases c2732 : 0 < a0
                        swap
                        · omega
                        by_cases c2733 : 0 < b2
                        swap
                        · omega
                        by_cases c2734 : 0 < b0 + b2
                        swap
                        · omega
                        by_cases c2735 : b0 < 0 + a0
                        swap
                        · -- branch
                          by_cases c2736 : 0 < a8
                          swap
                          · omega
                          by_cases c2737 : 0 < b2
                          swap
                          · omega
                          by_cases c2738 : a0 + a2 + a4 + a6 < b0 + b2
                          swap
                          · -- branch
                            by_cases c2739 : 0 < a8
                            swap
                            · omega
                            by_cases c2740 : 0 < b4
                            swap
                            · omega
                            by_cases c2741 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                            swap
                            · -- branch
                              by_cases c2742 : 0 < a4
                              swap
                              · omega
                              by_cases c2743 : 0 < b0
                              swap
                              · omega
                              by_cases c2744 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c2745 : 0 < a4
                                swap
                                · omega
                                by_cases c2746 : 0 < b2
                                swap
                                · omega
                                by_cases c2747 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c2748 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f2749 := pair_fact E (i := 4) (j := 2) rfl rfl c2745 c2746
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2749
                                by_cases c2750 : 0 < a4
                                swap
                                · omega
                                by_cases c2751 : 0 < b4
                                swap
                                · omega
                                by_cases c2752 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c2753 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f2754 := pair_fact E (i := 4) (j := 4) rfl rfl c2750 c2751
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2754
                                omega
                              by_cases c2755 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2756 := pair_fact E (i := 4) (j := 0) rfl rfl c2742 c2743
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2756
                              omega
                            by_cases c2757 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f2758 := pair_fact E (i := 8) (j := 4) rfl rfl c2739 c2740
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2758
                            omega
                          by_cases c2759 : b0 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f2760 := pair_fact E (i := 8) (j := 2) rfl rfl c2736 c2737
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2760
                          omega
                        have f2761 := pair_fact E (i := 0) (j := 2) rfl rfl c2732 c2733
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2761
                        omega
                      have f2762 := pair_fact E (i := 2) (j := 4) rfl rfl c2723 c2724
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2762
                      by_cases c2763 : 0 < a8
                      swap
                      · omega
                      by_cases c2764 : 0 < b4
                      swap
                      · omega
                      by_cases c2765 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                      swap
                      · -- branch
                        by_cases c2766 : 0 < a4
                        swap
                        · omega
                        by_cases c2767 : 0 < b0
                        swap
                        · omega
                        by_cases c2768 : a0 + a2 < 0 + b0
                        swap
                        · -- branch
                          by_cases c2769 : 0 < a4
                          swap
                          · omega
                          by_cases c2770 : 0 < b6
                          swap
                          · omega
                          by_cases c2771 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c2772 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · -- branch
                            by_cases c2773 : 0 < a4
                            swap
                            · omega
                            by_cases c2774 : 0 < b4
                            swap
                            · omega
                            by_cases c2775 : a0 + a2 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c2776 : b0 + b2 < a0 + a2 + a4
                            swap
                            · omega
                            have f2777 := pair_fact E (i := 4) (j := 4) rfl rfl c2773 c2774
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2777
                            by_cases c2778 : 0 < a4
                            swap
                            · omega
                            by_cases c2779 : 0 < b8
                            swap
                            · -- branch
                              by_cases c2780 : 0 < a4
                              swap
                              · omega
                              by_cases c2781 : 0 < b10
                              swap
                              · omega
                              by_cases c2782 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c2783 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c2784 : 0 < a0
                                swap
                                · omega
                                by_cases c2785 : 0 < b2
                                swap
                                · -- branch
                                  by_cases c2786 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c2787 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c2788 : a0 + a2 + a4 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c2789 : b0 + b2 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f2790 := pair_fact E (i := 6) (j := 4) rfl rfl c2786 c2787
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2790
                                  omega
                                by_cases c2791 : 0 < b0 + b2
                                swap
                                · omega
                                by_cases c2792 : b0 < 0 + a0
                                swap
                                · -- branch
                                  by_cases c2793 : 0 < a2
                                  swap
                                  · omega
                                  by_cases c2794 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c2795 : a0 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c2796 : b0 < a0 + a2
                                  swap
                                  · omega
                                  have f2797 := pair_fact E (i := 2) (j := 2) rfl rfl c2793 c2794
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2797
                                  omega
                                have f2798 := pair_fact E (i := 0) (j := 2) rfl rfl c2784 c2785
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2798
                                omega
                              have f2799 := pair_fact E (i := 4) (j := 10) rfl rfl c2780 c2781
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2799
                              omega
                            by_cases c2800 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c2801 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · omega
                            have f2802 := pair_fact E (i := 4) (j := 8) rfl rfl c2778 c2779
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2802
                            omega
                          have f2803 := pair_fact E (i := 4) (j := 6) rfl rfl c2769 c2770
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2803
                          omega
                        by_cases c2804 : 0 < a0 + a2 + a4
                        swap
                        · omega
                        have f2805 := pair_fact E (i := 4) (j := 0) rfl rfl c2766 c2767
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2805
                        omega
                      by_cases c2806 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f2807 := pair_fact E (i := 8) (j := 4) rfl rfl c2763 c2764
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2807
                      omega
                    by_cases c2808 : 0 < a0 + a2
                    swap
                    · omega
                    have f2809 := pair_fact E (i := 2) (j := 0) rfl rfl c2720 c2721
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2809
                    by_cases c2810 : 0 < a2
                    swap
                    · omega
                    by_cases c2811 : 0 < b4
                    swap
                    · omega
                    by_cases c2812 : a0 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c2813 : b0 + b2 < a0 + a2
                    swap
                    · -- branch
                      by_cases c2814 : 0 < a0
                      swap
                      · omega
                      by_cases c2815 : 0 < b2
                      swap
                      · -- branch
                        by_cases c2816 : 0 < a2
                        swap
                        · omega
                        by_cases c2817 : 0 < b2
                        swap
                        · -- branch
                          by_cases c2818 : 0 < a8
                          swap
                          · omega
                          by_cases c2819 : 0 < b2
                          swap
                          · -- branch
                            by_cases c2820 : 0 < a4
                            swap
                            · -- branch
                              by_cases c2821 : 0 < a4
                              swap
                              · -- branch
                                by_cases c2822 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c2823 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c2824 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c2825 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c2826 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c2827 : 0 < b0
                                        swap
                                        · omega
                                        by_cases c2828 : a0 + a2 + a4 < 0 + b0
                                        swap
                                        · -- branch
                                          by_cases c2829 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c2830 : 0 < b2
                                          swap
                                          · -- branch
                                            by_cases c2831 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c2832 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c2833 : a0 + a2 + a4 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c2834 : b0 + b2 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f2835 := pair_fact E (i := 6) (j := 4) rfl rfl c2831 c2832
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2835
                                            by_cases c2836 : 0 < a8
                                            swap
                                            · omega
                                            by_cases c2837 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c2838 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c2839 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f2840 := pair_fact E (i := 8) (j := 4) rfl rfl c2836 c2837
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2840
                                            omega
                                          by_cases c2841 : a0 + a2 + a4 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c2842 : b0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f2843 := pair_fact E (i := 6) (j := 2) rfl rfl c2829 c2830
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2843
                                          omega
                                        by_cases c2844 : 0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f2845 := pair_fact E (i := 6) (j := 0) rfl rfl c2826 c2827
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2845
                                        omega
                                      by_cases c2846 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c2847 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c2848 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f2849 := pair_fact E (i := 4) (j := 10) rfl rfl c2825 c2846
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2849
                                      omega
                                    by_cases c2850 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c2851 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c2852 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f2853 := pair_fact E (i := 4) (j := 8) rfl rfl c2824 c2850
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2853
                                    omega
                                  by_cases c2854 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c2855 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c2856 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f2857 := pair_fact E (i := 4) (j := 6) rfl rfl c2823 c2854
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2857
                                  omega
                                by_cases c2858 : 0 < b4
                                swap
                                · omega
                                by_cases c2859 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c2860 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f2861 := pair_fact E (i := 4) (j := 4) rfl rfl c2822 c2858
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2861
                                omega
                              by_cases c2862 : 0 < b2
                              swap
                              · omega
                              by_cases c2863 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c2864 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2865 := pair_fact E (i := 4) (j := 2) rfl rfl c2821 c2862
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2865
                              omega
                            by_cases c2866 : 0 < b0
                            swap
                            · omega
                            by_cases c2867 : a0 + a2 < 0 + b0
                            swap
                            · -- branch
                              by_cases c2868 : 0 < a4
                              swap
                              · omega
                              by_cases c2869 : 0 < b4
                              swap
                              · omega
                              by_cases c2870 : a0 + a2 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c2871 : b0 + b2 < a0 + a2 + a4
                              swap
                              · omega
                              have f2872 := pair_fact E (i := 4) (j := 4) rfl rfl c2868 c2869
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2872
                              omega
                            by_cases c2873 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f2874 := pair_fact E (i := 4) (j := 0) rfl rfl c2820 c2866
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2874
                            omega
                          by_cases c2875 : a0 + a2 + a4 + a6 < b0 + b2
                          swap
                          · omega
                          by_cases c2876 : b0 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f2877 := pair_fact E (i := 8) (j := 2) rfl rfl c2818 c2819
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2877
                          omega
                        by_cases c2878 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c2879 : b0 < a0 + a2
                        swap
                        · omega
                        have f2880 := pair_fact E (i := 2) (j := 2) rfl rfl c2816 c2817
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2880
                        omega
                      by_cases c2881 : 0 < b0 + b2
                      swap
                      · omega
                      by_cases c2882 : b0 < 0 + a0
                      swap
                      · -- branch
                        by_cases c2883 : 0 < a2
                        swap
                        · omega
                        by_cases c2884 : 0 < b2
                        swap
                        · omega
                        by_cases c2885 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c2886 : b0 < a0 + a2
                        swap
                        · -- branch
                          by_cases c2887 : 0 < a8
                          swap
                          · omega
                          by_cases c2888 : 0 < b2
                          swap
                          · omega
                          by_cases c2889 : a0 + a2 + a4 + a6 < b0 + b2
                          swap
                          · -- branch
                            by_cases c2890 : 0 < a4
                            swap
                            · -- branch
                              by_cases c2891 : 0 < a6
                              swap
                              · omega
                              by_cases c2892 : 0 < b2
                              swap
                              · omega
                              by_cases c2893 : a0 + a2 + a4 < b0 + b2
                              swap
                              · omega
                              by_cases c2894 : b0 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f2895 := pair_fact E (i := 6) (j := 2) rfl rfl c2891 c2892
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2895
                              omega
                            by_cases c2896 : 0 < b0
                            swap
                            · omega
                            by_cases c2897 : a0 + a2 < 0 + b0
                            swap
                            · -- branch
                              by_cases c2898 : 0 < a4
                              swap
                              · omega
                              by_cases c2899 : 0 < b2
                              swap
                              · omega
                              by_cases c2900 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c2901 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2902 := pair_fact E (i := 4) (j := 2) rfl rfl c2898 c2899
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2902
                              omega
                            by_cases c2903 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f2904 := pair_fact E (i := 4) (j := 0) rfl rfl c2890 c2896
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2904
                            omega
                          by_cases c2905 : b0 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f2906 := pair_fact E (i := 8) (j := 2) rfl rfl c2887 c2888
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2906
                          omega
                        have f2907 := pair_fact E (i := 2) (j := 2) rfl rfl c2883 c2884
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2907
                        omega
                      have f2908 := pair_fact E (i := 0) (j := 2) rfl rfl c2814 c2815
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2908
                      omega
                    have f2909 := pair_fact E (i := 2) (j := 4) rfl rfl c2810 c2811
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2909
                    omega
                  have f2910 := pair_fact E (i := 2) (j := 10) rfl rfl c2716 c2717
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2910
                  omega
                by_cases c2911 : a0 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c2912 : b0 + b2 + b4 + b6 < a0 + a2
                swap
                · omega
                have f2913 := pair_fact E (i := 2) (j := 8) rfl rfl c2714 c2715
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2913
                omega
              have f2914 := pair_fact E (i := 2) (j := 6) rfl rfl c2630 c2711
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2914
              omega
            have f2915 := pair_fact E (i := 0) (j := 10) rfl rfl c2381 c2382
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2915
            omega
          by_cases c2916 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c2917 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
          swap
          · omega
          have f2918 := pair_fact E (i := 8) (j := 8) rfl rfl c2379 c2380
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2918
          omega
        by_cases c2919 : 0 < a0 + a2 + a4 + a6 + a8
        swap
        · omega
        have f2920 := pair_fact E (i := 8) (j := 0) rfl rfl c2376 c2377
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2920
        omega
      by_cases c2921 : 0 < b0 + b2 + b4 + b6 + b8
      swap
      · omega
      by_cases c2922 : b0 + b2 + b4 + b6 < 0 + a0
      swap
      · -- branch
        by_cases c2923 : 0 < a0
        swap
        · omega
        by_cases c2924 : 0 < b10
        swap
        · -- branch
          by_cases c2925 : 0 < a2
          swap
          · -- branch
            by_cases c2926 : 0 < a2
            swap
            · -- branch
              by_cases c2927 : 0 < a2
              swap
              · -- branch
                by_cases c2928 : 0 < a2
                swap
                · -- branch
                  by_cases c2929 : 0 < a2
                  swap
                  · -- branch
                    by_cases c2930 : 0 < a2
                    swap
                    · -- branch
                      by_cases c2931 : 0 < a0
                      swap
                      · omega
                      by_cases c2932 : 0 < b2
                      swap
                      · omega
                      by_cases c2933 : 0 < b0 + b2
                      swap
                      · omega
                      by_cases c2934 : b0 < 0 + a0
                      swap
                      · -- branch
                        by_cases c2935 : 0 < a4
                        swap
                        · -- branch
                          by_cases c2936 : 0 < a6
                          swap
                          · omega
                          by_cases c2937 : 0 < b2
                          swap
                          · omega
                          by_cases c2938 : a0 + a2 + a4 < b0 + b2
                          swap
                          · omega
                          by_cases c2939 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f2940 := pair_fact E (i := 6) (j := 2) rfl rfl c2936 c2937
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2940
                          omega
                        by_cases c2941 : 0 < b0
                        swap
                        · omega
                        by_cases c2942 : a0 + a2 < 0 + b0
                        swap
                        · -- branch
                          by_cases c2943 : 0 < a4
                          swap
                          · omega
                          by_cases c2944 : 0 < b2
                          swap
                          · omega
                          by_cases c2945 : a0 + a2 < b0 + b2
                          swap
                          · omega
                          by_cases c2946 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f2947 := pair_fact E (i := 4) (j := 2) rfl rfl c2943 c2944
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2947
                          by_cases c2948 : 0 < a4
                          swap
                          · omega
                          by_cases c2949 : 0 < b6
                          swap
                          · omega
                          by_cases c2950 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c2951 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · -- branch
                            by_cases c2952 : 0 < a4
                            swap
                            · omega
                            by_cases c2953 : 0 < b8
                            swap
                            · omega
                            by_cases c2954 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c2955 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c2956 : 0 < a4
                              swap
                              · omega
                              by_cases c2957 : 0 < b10
                              swap
                              · -- branch
                                by_cases c2958 : 0 < a10
                                swap
                                · omega
                                by_cases c2959 : 0 < b0
                                swap
                                · omega
                                by_cases c2960 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c2961 : 0 < a10
                                  swap
                                  · omega
                                  by_cases c2962 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c2963 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c2964 : 0 < a10
                                    swap
                                    · omega
                                    by_cases c2965 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c2966 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                    swap
                                    · -- branch
                                      by_cases c2967 : 0 < a6
                                      swap
                                      · -- branch
                                        by_cases c2968 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c2969 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c2970 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c2971 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f2972 := pair_fact E (i := 8) (j := 4) rfl rfl c2968 c2969
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2972
                                        omega
                                      by_cases c2973 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c2974 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c2975 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f2976 := pair_fact E (i := 6) (j := 4) rfl rfl c2967 c2973
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2976
                                      omega
                                    by_cases c2977 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                    swap
                                    · omega
                                    have f2978 := pair_fact E (i := 10) (j := 4) rfl rfl c2964 c2965
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2978
                                    omega
                                  by_cases c2979 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                                  swap
                                  · omega
                                  have f2980 := pair_fact E (i := 10) (j := 2) rfl rfl c2961 c2962
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2980
                                  omega
                                by_cases c2981 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f2982 := pair_fact E (i := 10) (j := 0) rfl rfl c2958 c2959
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2982
                                omega
                              by_cases c2983 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c2984 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · omega
                              have f2985 := pair_fact E (i := 4) (j := 10) rfl rfl c2956 c2957
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2985
                              omega
                            have f2986 := pair_fact E (i := 4) (j := 8) rfl rfl c2952 c2953
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2986
                            omega
                          have f2987 := pair_fact E (i := 4) (j := 6) rfl rfl c2948 c2949
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2987
                          omega
                        by_cases c2988 : 0 < a0 + a2 + a4
                        swap
                        · omega
                        have f2989 := pair_fact E (i := 4) (j := 0) rfl rfl c2935 c2941
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2989
                        omega
                      have f2990 := pair_fact E (i := 0) (j := 2) rfl rfl c2931 c2932
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2990
                      by_cases c2991 : 0 < a4
                      swap
                      · -- branch
                        by_cases c2992 : 0 < a8
                        swap
                        · omega
                        by_cases c2993 : 0 < b4
                        swap
                        · omega
                        by_cases c2994 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c2995 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f2996 := pair_fact E (i := 8) (j := 4) rfl rfl c2992 c2993
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2996
                        omega
                      by_cases c2997 : 0 < b0
                      swap
                      · omega
                      by_cases c2998 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c2999 : 0 < a4
                        swap
                        · omega
                        by_cases c3000 : 0 < b2
                        swap
                        · omega
                        by_cases c3001 : a0 + a2 < b0 + b2
                        swap
                        · -- branch
                          by_cases c3002 : 0 < a4
                          swap
                          · omega
                          by_cases c3003 : 0 < b4
                          swap
                          · omega
                          by_cases c3004 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c3005 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f3006 := pair_fact E (i := 4) (j := 4) rfl rfl c3002 c3003
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3006
                          omega
                        by_cases c3007 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f3008 := pair_fact E (i := 4) (j := 2) rfl rfl c2999 c3000
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3008
                        omega
                      by_cases c3009 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f3010 := pair_fact E (i := 4) (j := 0) rfl rfl c2991 c2997
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3010
                      omega
                    by_cases c3011 : 0 < b10
                    swap
                    · omega
                    by_cases c3012 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c3013 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · omega
                    have f3014 := pair_fact E (i := 2) (j := 10) rfl rfl c2930 c3011
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3014
                    omega
                  by_cases c3015 : 0 < b8
                  swap
                  · omega
                  by_cases c3016 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c3017 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · omega
                  have f3018 := pair_fact E (i := 2) (j := 8) rfl rfl c2929 c3015
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3018
                  omega
                by_cases c3019 : 0 < b4
                swap
                · omega
                by_cases c3020 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c3021 : b0 + b2 < a0 + a2
                swap
                · omega
                have f3022 := pair_fact E (i := 2) (j := 4) rfl rfl c2928 c3019
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3022
                omega
              by_cases c3023 : 0 < b2
              swap
              · omega
              by_cases c3024 : a0 < b0 + b2
              swap
              · omega
              by_cases c3025 : b0 < a0 + a2
              swap
              · omega
              have f3026 := pair_fact E (i := 2) (j := 2) rfl rfl c2927 c3023
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3026
              omega
            by_cases c3027 : 0 < b0
            swap
            · omega
            by_cases c3028 : a0 < 0 + b0
            swap
            · omega
            by_cases c3029 : 0 < a0 + a2
            swap
            · omega
            have f3030 := pair_fact E (i := 2) (j := 0) rfl rfl c2926 c3027
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3030
            omega
          by_cases c3031 : 0 < b6
          swap
          · omega
          by_cases c3032 : a0 < b0 + b2 + b4 + b6
          swap
          · omega
          by_cases c3033 : b0 + b2 + b4 < a0 + a2
          swap
          · -- branch
            by_cases c3034 : 0 < a2
            swap
            · omega
            by_cases c3035 : 0 < b8
            swap
            · omega
            by_cases c3036 : a0 < b0 + b2 + b4 + b6 + b8
            swap
            · omega
            by_cases c3037 : b0 + b2 + b4 + b6 < a0 + a2
            swap
            · -- branch
              by_cases c3038 : 0 < a2
              swap
              · omega
              by_cases c3039 : 0 < b10
              swap
              · -- branch
                by_cases c3040 : 0 < a2
                swap
                · omega
                by_cases c3041 : 0 < b0
                swap
                · omega
                by_cases c3042 : a0 < 0 + b0
                swap
                · -- branch
                  by_cases c3043 : 0 < a2
                  swap
                  · omega
                  by_cases c3044 : 0 < b4
                  swap
                  · omega
                  by_cases c3045 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c3046 : b0 + b2 < a0 + a2
                  swap
                  · -- branch
                    by_cases c3047 : 0 < a2
                    swap
                    · omega
                    by_cases c3048 : 0 < b2
                    swap
                    · omega
                    by_cases c3049 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c3050 : b0 < a0 + a2
                    swap
                    · omega
                    have f3051 := pair_fact E (i := 2) (j := 2) rfl rfl c3047 c3048
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3051
                    by_cases c3052 : 0 < a0
                    swap
                    · omega
                    by_cases c3053 : 0 < b2
                    swap
                    · omega
                    by_cases c3054 : 0 < b0 + b2
                    swap
                    · omega
                    by_cases c3055 : b0 < 0 + a0
                    swap
                    · -- branch
                      by_cases c3056 : 0 < a10
                      swap
                      · omega
                      by_cases c3057 : 0 < b0
                      swap
                      · omega
                      by_cases c3058 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                      swap
                      · -- branch
                        by_cases c3059 : 0 < a10
                        swap
                        · omega
                        by_cases c3060 : 0 < b2
                        swap
                        · omega
                        by_cases c3061 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                        swap
                        · -- branch
                          by_cases c3062 : 0 < a10
                          swap
                          · omega
                          by_cases c3063 : 0 < b4
                          swap
                          · omega
                          by_cases c3064 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                          swap
                          · -- branch
                            by_cases c3065 : 0 < a4
                            swap
                            · omega
                            by_cases c3066 : 0 < b0
                            swap
                            · omega
                            by_cases c3067 : a0 + a2 < 0 + b0
                            swap
                            · -- branch
                              by_cases c3068 : 0 < a4
                              swap
                              · omega
                              by_cases c3069 : 0 < b2
                              swap
                              · omega
                              by_cases c3070 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c3071 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f3072 := pair_fact E (i := 4) (j := 2) rfl rfl c3068 c3069
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3072
                              by_cases c3073 : 0 < a4
                              swap
                              · omega
                              by_cases c3074 : 0 < b4
                              swap
                              · omega
                              by_cases c3075 : a0 + a2 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c3076 : b0 + b2 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c3077 : 0 < a6
                                swap
                                · omega
                                by_cases c3078 : 0 < b4
                                swap
                                · omega
                                by_cases c3079 : a0 + a2 + a4 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c3080 : b0 + b2 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f3081 := pair_fact E (i := 6) (j := 4) rfl rfl c3077 c3078
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3081
                                omega
                              have f3082 := pair_fact E (i := 4) (j := 4) rfl rfl c3073 c3074
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3082
                              omega
                            by_cases c3083 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f3084 := pair_fact E (i := 4) (j := 0) rfl rfl c3065 c3066
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3084
                            omega
                          by_cases c3085 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                          swap
                          · omega
                          have f3086 := pair_fact E (i := 10) (j := 4) rfl rfl c3062 c3063
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3086
                          omega
                        by_cases c3087 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                        swap
                        · omega
                        have f3088 := pair_fact E (i := 10) (j := 2) rfl rfl c3059 c3060
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3088
                        omega
                      by_cases c3089 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f3090 := pair_fact E (i := 10) (j := 0) rfl rfl c3056 c3057
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3090
                      omega
                    have f3091 := pair_fact E (i := 0) (j := 2) rfl rfl c3052 c3053
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3091
                    omega
                  have f3092 := pair_fact E (i := 2) (j := 4) rfl rfl c3043 c3044
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3092
                  by_cases c3093 : 0 < a0
                  swap
                  · omega
                  by_cases c3094 : 0 < b2
                  swap
                  · -- branch
                    by_cases c3095 : 0 < a2
                    swap
                    · omega
                    by_cases c3096 : 0 < b2
                    swap
                    · -- branch
                      by_cases c3097 : 0 < a10
                      swap
                      · omega
                      by_cases c3098 : 0 < b0
                      swap
                      · omega
                      by_cases c3099 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                      swap
                      · -- branch
                        by_cases c3100 : 0 < a10
                        swap
                        · omega
                        by_cases c3101 : 0 < b2
                        swap
                        · -- branch
                          by_cases c3102 : 0 < a10
                          swap
                          · omega
                          by_cases c3103 : 0 < b4
                          swap
                          · omega
                          by_cases c3104 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                          swap
                          · -- branch
                            by_cases c3105 : 0 < a10
                            swap
                            · omega
                            by_cases c3106 : 0 < b8
                            swap
                            · omega
                            by_cases c3107 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c3108 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f3109 := pair_fact E (i := 10) (j := 8) rfl rfl c3105 c3106
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3109
                            by_cases c3110 : 0 < a10
                            swap
                            · omega
                            by_cases c3111 : 0 < b10
                            swap
                            · -- branch
                              by_cases c3112 : 0 < a4
                              swap
                              · -- branch
                                by_cases c3113 : 0 < a6
                                swap
                                · omega
                                by_cases c3114 : 0 < b4
                                swap
                                · omega
                                by_cases c3115 : a0 + a2 + a4 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c3116 : b0 + b2 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f3117 := pair_fact E (i := 6) (j := 4) rfl rfl c3113 c3114
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3117
                                omega
                              by_cases c3118 : 0 < b0
                              swap
                              · omega
                              by_cases c3119 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c3120 : 0 < a4
                                swap
                                · omega
                                by_cases c3121 : 0 < b2
                                swap
                                · -- branch
                                  by_cases c3122 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c3123 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c3124 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c3125 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c3126 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c3127 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c3128 : a0 + a2 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c3129 : b0 + b2 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f3130 := pair_fact E (i := 4) (j := 4) rfl rfl c3126 c3127
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3130
                                    by_cases c3131 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c3132 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c3133 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c3134 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c3135 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c3136 : 0 < b10
                                      swap
                                      · -- branch
                                        by_cases c3137 : 0 < a6
                                        swap
                                        · -- branch
                                          by_cases c3138 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c3139 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c3140 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c3141 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f3142 := pair_fact E (i := 8) (j := 4) rfl rfl c3138 c3139
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3142
                                          omega
                                        by_cases c3143 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c3144 : a0 + a2 + a4 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c3145 : b0 + b2 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f3146 := pair_fact E (i := 6) (j := 4) rfl rfl c3137 c3143
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3146
                                        omega
                                      by_cases c3147 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c3148 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f3149 := pair_fact E (i := 4) (j := 10) rfl rfl c3135 c3136
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3149
                                      omega
                                    have f3150 := pair_fact E (i := 4) (j := 8) rfl rfl c3131 c3132
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3150
                                    omega
                                  have f3151 := pair_fact E (i := 4) (j := 6) rfl rfl c3122 c3123
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3151
                                  omega
                                by_cases c3152 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c3153 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f3154 := pair_fact E (i := 4) (j := 2) rfl rfl c3120 c3121
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3154
                                omega
                              by_cases c3155 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f3156 := pair_fact E (i := 4) (j := 0) rfl rfl c3112 c3118
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3156
                              omega
                            by_cases c3157 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c3158 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f3159 := pair_fact E (i := 10) (j := 10) rfl rfl c3110 c3111
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3159
                            omega
                          by_cases c3160 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                          swap
                          · omega
                          have f3161 := pair_fact E (i := 10) (j := 4) rfl rfl c3102 c3103
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3161
                          omega
                        by_cases c3162 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                        swap
                        · omega
                        by_cases c3163 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                        swap
                        · omega
                        have f3164 := pair_fact E (i := 10) (j := 2) rfl rfl c3100 c3101
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3164
                        omega
                      by_cases c3165 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f3166 := pair_fact E (i := 10) (j := 0) rfl rfl c3097 c3098
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3166
                      omega
                    by_cases c3167 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c3168 : b0 < a0 + a2
                    swap
                    · omega
                    have f3169 := pair_fact E (i := 2) (j := 2) rfl rfl c3095 c3096
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3169
                    omega
                  by_cases c3170 : 0 < b0 + b2
                  swap
                  · omega
                  by_cases c3171 : b0 < 0 + a0
                  swap
                  · -- branch
                    by_cases c3172 : 0 < a2
                    swap
                    · omega
                    by_cases c3173 : 0 < b2
                    swap
                    · omega
                    by_cases c3174 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c3175 : b0 < a0 + a2
                    swap
                    · omega
                    have f3176 := pair_fact E (i := 2) (j := 2) rfl rfl c3172 c3173
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3176
                    by_cases c3177 : 0 < a10
                    swap
                    · omega
                    by_cases c3178 : 0 < b0
                    swap
                    · omega
                    by_cases c3179 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                    swap
                    · -- branch
                      by_cases c3180 : 0 < a10
                      swap
                      · omega
                      by_cases c3181 : 0 < b2
                      swap
                      · omega
                      by_cases c3182 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                      swap
                      · -- branch
                        by_cases c3183 : 0 < a10
                        swap
                        · omega
                        by_cases c3184 : 0 < b4
                        swap
                        · omega
                        by_cases c3185 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                        swap
                        · -- branch
                          by_cases c3186 : 0 < a10
                          swap
                          · omega
                          by_cases c3187 : 0 < b8
                          swap
                          · omega
                          by_cases c3188 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c3189 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                          swap
                          · omega
                          have f3190 := pair_fact E (i := 10) (j := 8) rfl rfl c3186 c3187
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3190
                          by_cases c3191 : 0 < a10
                          swap
                          · omega
                          by_cases c3192 : 0 < b10
                          swap
                          · -- branch
                            by_cases c3193 : 0 < a4
                            swap
                            · -- branch
                              by_cases c3194 : 0 < a6
                              swap
                              · omega
                              by_cases c3195 : 0 < b4
                              swap
                              · omega
                              by_cases c3196 : a0 + a2 + a4 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c3197 : b0 + b2 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f3198 := pair_fact E (i := 6) (j := 4) rfl rfl c3194 c3195
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3198
                              omega
                            by_cases c3199 : 0 < b0
                            swap
                            · omega
                            by_cases c3200 : a0 + a2 < 0 + b0
                            swap
                            · -- branch
                              by_cases c3201 : 0 < a4
                              swap
                              · omega
                              by_cases c3202 : 0 < b2
                              swap
                              · omega
                              by_cases c3203 : a0 + a2 < b0 + b2
                              swap
                              · -- branch
                                by_cases c3204 : 0 < a4
                                swap
                                · omega
                                by_cases c3205 : 0 < b4
                                swap
                                · omega
                                by_cases c3206 : a0 + a2 < b0 + b2 + b4
                                swap
                                · -- branch
                                  by_cases c3207 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c3208 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c3209 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c3210 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f3211 := pair_fact E (i := 4) (j := 6) rfl rfl c3207 c3208
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3211
                                  omega
                                by_cases c3212 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f3213 := pair_fact E (i := 4) (j := 4) rfl rfl c3204 c3205
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3213
                                omega
                              by_cases c3214 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f3215 := pair_fact E (i := 4) (j := 2) rfl rfl c3201 c3202
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3215
                              omega
                            by_cases c3216 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f3217 := pair_fact E (i := 4) (j := 0) rfl rfl c3193 c3199
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3217
                            omega
                          by_cases c3218 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c3219 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8 + a10
                          swap
                          · omega
                          have f3220 := pair_fact E (i := 10) (j := 10) rfl rfl c3191 c3192
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3220
                          omega
                        by_cases c3221 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                        swap
                        · omega
                        have f3222 := pair_fact E (i := 10) (j := 4) rfl rfl c3183 c3184
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3222
                        omega
                      by_cases c3223 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f3224 := pair_fact E (i := 10) (j := 2) rfl rfl c3180 c3181
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3224
                      omega
                    by_cases c3225 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                    swap
                    · omega
                    have f3226 := pair_fact E (i := 10) (j := 0) rfl rfl c3177 c3178
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3226
                    omega
                  have f3227 := pair_fact E (i := 0) (j := 2) rfl rfl c3093 c3094
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3227
                  omega
                by_cases c3228 : 0 < a0 + a2
                swap
                · omega
                have f3229 := pair_fact E (i := 2) (j := 0) rfl rfl c3040 c3041
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3229
                by_cases c3230 : 0 < a2
                swap
                · omega
                by_cases c3231 : 0 < b4
                swap
                · omega
                by_cases c3232 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c3233 : b0 + b2 < a0 + a2
                swap
                · -- branch
                  by_cases c3234 : 0 < a0
                  swap
                  · omega
                  by_cases c3235 : 0 < b2
                  swap
                  · -- branch
                    by_cases c3236 : 0 < a2
                    swap
                    · omega
                    by_cases c3237 : 0 < b2
                    swap
                    · -- branch
                      by_cases c3238 : 0 < a4
                      swap
                      · -- branch
                        by_cases c3239 : 0 < a4
                        swap
                        · -- branch
                          by_cases c3240 : 0 < a4
                          swap
                          · -- branch
                            by_cases c3241 : 0 < a4
                            swap
                            · -- branch
                              by_cases c3242 : 0 < a4
                              swap
                              · -- branch
                                by_cases c3243 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c3244 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c3245 : 0 < b0
                                  swap
                                  · omega
                                  by_cases c3246 : a0 + a2 + a4 < 0 + b0
                                  swap
                                  · -- branch
                                    by_cases c3247 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c3248 : 0 < b2
                                    swap
                                    · -- branch
                                      by_cases c3249 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c3250 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c3251 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c3252 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f3253 := pair_fact E (i := 6) (j := 4) rfl rfl c3249 c3250
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3253
                                      by_cases c3254 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c3255 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c3256 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c3257 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f3258 := pair_fact E (i := 8) (j := 4) rfl rfl c3254 c3255
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3258
                                      omega
                                    by_cases c3259 : a0 + a2 + a4 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c3260 : b0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f3261 := pair_fact E (i := 6) (j := 2) rfl rfl c3247 c3248
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3261
                                    omega
                                  by_cases c3262 : 0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f3263 := pair_fact E (i := 6) (j := 0) rfl rfl c3244 c3245
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3263
                                  omega
                                by_cases c3264 : 0 < b10
                                swap
                                · omega
                                by_cases c3265 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c3266 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                swap
                                · omega
                                have f3267 := pair_fact E (i := 4) (j := 10) rfl rfl c3243 c3264
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3267
                                omega
                              by_cases c3268 : 0 < b8
                              swap
                              · omega
                              by_cases c3269 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c3270 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · omega
                              have f3271 := pair_fact E (i := 4) (j := 8) rfl rfl c3242 c3268
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3271
                              omega
                            by_cases c3272 : 0 < b6
                            swap
                            · omega
                            by_cases c3273 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c3274 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · omega
                            have f3275 := pair_fact E (i := 4) (j := 6) rfl rfl c3241 c3272
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3275
                            omega
                          by_cases c3276 : 0 < b4
                          swap
                          · omega
                          by_cases c3277 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c3278 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f3279 := pair_fact E (i := 4) (j := 4) rfl rfl c3240 c3276
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3279
                          omega
                        by_cases c3280 : 0 < b2
                        swap
                        · omega
                        by_cases c3281 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c3282 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f3283 := pair_fact E (i := 4) (j := 2) rfl rfl c3239 c3280
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3283
                        omega
                      by_cases c3284 : 0 < b0
                      swap
                      · omega
                      by_cases c3285 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c3286 : 0 < a4
                        swap
                        · omega
                        by_cases c3287 : 0 < b4
                        swap
                        · omega
                        by_cases c3288 : a0 + a2 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c3289 : b0 + b2 < a0 + a2 + a4
                        swap
                        · omega
                        have f3290 := pair_fact E (i := 4) (j := 4) rfl rfl c3286 c3287
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3290
                        omega
                      by_cases c3291 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f3292 := pair_fact E (i := 4) (j := 0) rfl rfl c3238 c3284
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3292
                      omega
                    by_cases c3293 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c3294 : b0 < a0 + a2
                    swap
                    · omega
                    have f3295 := pair_fact E (i := 2) (j := 2) rfl rfl c3236 c3237
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3295
                    omega
                  by_cases c3296 : 0 < b0 + b2
                  swap
                  · omega
                  by_cases c3297 : b0 < 0 + a0
                  swap
                  · -- branch
                    by_cases c3298 : 0 < a2
                    swap
                    · omega
                    by_cases c3299 : 0 < b2
                    swap
                    · omega
                    by_cases c3300 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c3301 : b0 < a0 + a2
                    swap
                    · -- branch
                      by_cases c3302 : 0 < a4
                      swap
                      · -- branch
                        by_cases c3303 : 0 < a6
                        swap
                        · omega
                        by_cases c3304 : 0 < b2
                        swap
                        · omega
                        by_cases c3305 : a0 + a2 + a4 < b0 + b2
                        swap
                        · omega
                        by_cases c3306 : b0 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f3307 := pair_fact E (i := 6) (j := 2) rfl rfl c3303 c3304
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3307
                        omega
                      by_cases c3308 : 0 < b0
                      swap
                      · omega
                      by_cases c3309 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c3310 : 0 < a4
                        swap
                        · omega
                        by_cases c3311 : 0 < b2
                        swap
                        · omega
                        by_cases c3312 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c3313 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f3314 := pair_fact E (i := 4) (j := 2) rfl rfl c3310 c3311
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3314
                        omega
                      by_cases c3315 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f3316 := pair_fact E (i := 4) (j := 0) rfl rfl c3302 c3308
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3316
                      omega
                    have f3317 := pair_fact E (i := 2) (j := 2) rfl rfl c3298 c3299
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3317
                    omega
                  have f3318 := pair_fact E (i := 0) (j := 2) rfl rfl c3234 c3235
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3318
                  omega
                have f3319 := pair_fact E (i := 2) (j := 4) rfl rfl c3230 c3231
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3319
                omega
              by_cases c3320 : a0 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c3321 : b0 + b2 + b4 + b6 + b8 < a0 + a2
              swap
              · omega
              have f3322 := pair_fact E (i := 2) (j := 10) rfl rfl c3038 c3039
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3322
              omega
            have f3323 := pair_fact E (i := 2) (j := 8) rfl rfl c3034 c3035
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3323
            omega
          have f3324 := pair_fact E (i := 2) (j := 6) rfl rfl c2925 c3031
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3324
          omega
        by_cases c3325 : 0 < b0 + b2 + b4 + b6 + b8 + b10
        swap
        · omega
        by_cases c3326 : b0 + b2 + b4 + b6 + b8 < 0 + a0
        swap
        · -- branch
          by_cases c3327 : 0 < a2
          swap
          · -- branch
            by_cases c3328 : 0 < a2
            swap
            · -- branch
              by_cases c3329 : 0 < a2
              swap
              · -- branch
                by_cases c3330 : 0 < a2
                swap
                · -- branch
                  by_cases c3331 : 0 < a2
                  swap
                  · -- branch
                    by_cases c3332 : 0 < a2
                    swap
                    · -- branch
                      by_cases c3333 : 0 < a0
                      swap
                      · omega
                      by_cases c3334 : 0 < b2
                      swap
                      · omega
                      by_cases c3335 : 0 < b0 + b2
                      swap
                      · omega
                      by_cases c3336 : b0 < 0 + a0
                      swap
                      · -- branch
                        by_cases c3337 : 0 < a4
                        swap
                        · -- branch
                          by_cases c3338 : 0 < a6
                          swap
                          · omega
                          by_cases c3339 : 0 < b2
                          swap
                          · omega
                          by_cases c3340 : a0 + a2 + a4 < b0 + b2
                          swap
                          · omega
                          by_cases c3341 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f3342 := pair_fact E (i := 6) (j := 2) rfl rfl c3338 c3339
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3342
                          omega
                        by_cases c3343 : 0 < b0
                        swap
                        · omega
                        by_cases c3344 : a0 + a2 < 0 + b0
                        swap
                        · -- branch
                          by_cases c3345 : 0 < a4
                          swap
                          · omega
                          by_cases c3346 : 0 < b2
                          swap
                          · omega
                          by_cases c3347 : a0 + a2 < b0 + b2
                          swap
                          · omega
                          by_cases c3348 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f3349 := pair_fact E (i := 4) (j := 2) rfl rfl c3345 c3346
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3349
                          by_cases c3350 : 0 < a4
                          swap
                          · omega
                          by_cases c3351 : 0 < b6
                          swap
                          · omega
                          by_cases c3352 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c3353 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · -- branch
                            by_cases c3354 : 0 < a4
                            swap
                            · omega
                            by_cases c3355 : 0 < b8
                            swap
                            · omega
                            by_cases c3356 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c3357 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c3358 : 0 < a4
                              swap
                              · omega
                              by_cases c3359 : 0 < b10
                              swap
                              · omega
                              by_cases c3360 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c3361 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c3362 : 0 < a4
                                swap
                                · omega
                                by_cases c3363 : 0 < b4
                                swap
                                · omega
                                by_cases c3364 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c3365 : b0 + b2 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c3366 : 0 < a8
                                  swap
                                  · -- branch
                                    by_cases c3367 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c3368 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c3369 : a0 + a2 + a4 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c3370 : b0 + b2 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f3371 := pair_fact E (i := 6) (j := 4) rfl rfl c3367 c3368
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3371
                                    omega
                                  by_cases c3372 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c3373 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c3374 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f3375 := pair_fact E (i := 8) (j := 4) rfl rfl c3366 c3372
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3375
                                  omega
                                have f3376 := pair_fact E (i := 4) (j := 4) rfl rfl c3362 c3363
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3376
                                by_cases c3377 : 0 < a6
                                swap
                                · -- branch
                                  by_cases c3378 : 0 < a6
                                  swap
                                  · -- branch
                                    by_cases c3379 : 0 < a6
                                    swap
                                    · -- branch
                                      by_cases c3380 : 0 < a6
                                      swap
                                      · -- branch
                                        by_cases c3381 : 0 < a6
                                        swap
                                        · -- branch
                                          by_cases c3382 : 0 < a6
                                          swap
                                          · -- branch
                                            by_cases c3383 : 0 < a8
                                            swap
                                            · -- branch
                                              by_cases c3384 : 0 < a10
                                              swap
                                              · omega
                                              by_cases c3385 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c3386 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c3387 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                              swap
                                              · omega
                                              have f3388 := pair_fact E (i := 10) (j := 4) rfl rfl c3384 c3385
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3388
                                              omega
                                            by_cases c3389 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c3390 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c3391 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f3392 := pair_fact E (i := 8) (j := 4) rfl rfl c3383 c3389
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3392
                                            omega
                                          by_cases c3393 : 0 < b10
                                          swap
                                          · omega
                                          by_cases c3394 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                          swap
                                          · omega
                                          by_cases c3395 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f3396 := pair_fact E (i := 6) (j := 10) rfl rfl c3382 c3393
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3396
                                          omega
                                        by_cases c3397 : 0 < b8
                                        swap
                                        · omega
                                        by_cases c3398 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                        swap
                                        · omega
                                        by_cases c3399 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f3400 := pair_fact E (i := 6) (j := 8) rfl rfl c3381 c3397
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3400
                                        omega
                                      by_cases c3401 : 0 < b6
                                      swap
                                      · omega
                                      by_cases c3402 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                      swap
                                      · omega
                                      by_cases c3403 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f3404 := pair_fact E (i := 6) (j := 6) rfl rfl c3380 c3401
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3404
                                      omega
                                    by_cases c3405 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c3406 : a0 + a2 + a4 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c3407 : b0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f3408 := pair_fact E (i := 6) (j := 2) rfl rfl c3379 c3405
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3408
                                    omega
                                  by_cases c3409 : 0 < b0
                                  swap
                                  · omega
                                  by_cases c3410 : a0 + a2 + a4 < 0 + b0
                                  swap
                                  · omega
                                  by_cases c3411 : 0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f3412 := pair_fact E (i := 6) (j := 0) rfl rfl c3378 c3409
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3412
                                  omega
                                by_cases c3413 : 0 < b4
                                swap
                                · omega
                                by_cases c3414 : a0 + a2 + a4 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c3415 : b0 + b2 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f3416 := pair_fact E (i := 6) (j := 4) rfl rfl c3377 c3413
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3416
                                omega
                              have f3417 := pair_fact E (i := 4) (j := 10) rfl rfl c3358 c3359
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3417
                              omega
                            have f3418 := pair_fact E (i := 4) (j := 8) rfl rfl c3354 c3355
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3418
                            omega
                          have f3419 := pair_fact E (i := 4) (j := 6) rfl rfl c3350 c3351
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3419
                          omega
                        by_cases c3420 : 0 < a0 + a2 + a4
                        swap
                        · omega
                        have f3421 := pair_fact E (i := 4) (j := 0) rfl rfl c3337 c3343
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3421
                        omega
                      have f3422 := pair_fact E (i := 0) (j := 2) rfl rfl c3333 c3334
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3422
                      by_cases c3423 : 0 < a4
                      swap
                      · -- branch
                        by_cases c3424 : 0 < a8
                        swap
                        · omega
                        by_cases c3425 : 0 < b4
                        swap
                        · omega
                        by_cases c3426 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c3427 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f3428 := pair_fact E (i := 8) (j := 4) rfl rfl c3424 c3425
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3428
                        omega
                      by_cases c3429 : 0 < b0
                      swap
                      · omega
                      by_cases c3430 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c3431 : 0 < a4
                        swap
                        · omega
                        by_cases c3432 : 0 < b2
                        swap
                        · omega
                        by_cases c3433 : a0 + a2 < b0 + b2
                        swap
                        · -- branch
                          by_cases c3434 : 0 < a4
                          swap
                          · omega
                          by_cases c3435 : 0 < b4
                          swap
                          · omega
                          by_cases c3436 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c3437 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f3438 := pair_fact E (i := 4) (j := 4) rfl rfl c3434 c3435
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3438
                          omega
                        by_cases c3439 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f3440 := pair_fact E (i := 4) (j := 2) rfl rfl c3431 c3432
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3440
                        omega
                      by_cases c3441 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f3442 := pair_fact E (i := 4) (j := 0) rfl rfl c3423 c3429
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3442
                      omega
                    by_cases c3443 : 0 < b10
                    swap
                    · omega
                    by_cases c3444 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c3445 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · omega
                    have f3446 := pair_fact E (i := 2) (j := 10) rfl rfl c3332 c3443
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3446
                    omega
                  by_cases c3447 : 0 < b8
                  swap
                  · omega
                  by_cases c3448 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c3449 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · omega
                  have f3450 := pair_fact E (i := 2) (j := 8) rfl rfl c3331 c3447
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3450
                  omega
                by_cases c3451 : 0 < b4
                swap
                · omega
                by_cases c3452 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c3453 : b0 + b2 < a0 + a2
                swap
                · omega
                have f3454 := pair_fact E (i := 2) (j := 4) rfl rfl c3330 c3451
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3454
                omega
              by_cases c3455 : 0 < b2
              swap
              · omega
              by_cases c3456 : a0 < b0 + b2
              swap
              · omega
              by_cases c3457 : b0 < a0 + a2
              swap
              · omega
              have f3458 := pair_fact E (i := 2) (j := 2) rfl rfl c3329 c3455
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3458
              omega
            by_cases c3459 : 0 < b0
            swap
            · omega
            by_cases c3460 : a0 < 0 + b0
            swap
            · omega
            by_cases c3461 : 0 < a0 + a2
            swap
            · omega
            have f3462 := pair_fact E (i := 2) (j := 0) rfl rfl c3328 c3459
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3462
            omega
          by_cases c3463 : 0 < b6
          swap
          · omega
          by_cases c3464 : a0 < b0 + b2 + b4 + b6
          swap
          · omega
          by_cases c3465 : b0 + b2 + b4 < a0 + a2
          swap
          · -- branch
            by_cases c3466 : 0 < a2
            swap
            · omega
            by_cases c3467 : 0 < b8
            swap
            · omega
            by_cases c3468 : a0 < b0 + b2 + b4 + b6 + b8
            swap
            · omega
            by_cases c3469 : b0 + b2 + b4 + b6 < a0 + a2
            swap
            · -- branch
              by_cases c3470 : 0 < a2
              swap
              · omega
              by_cases c3471 : 0 < b10
              swap
              · omega
              by_cases c3472 : a0 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c3473 : b0 + b2 + b4 + b6 + b8 < a0 + a2
              swap
              · -- branch
                by_cases c3474 : 0 < a2
                swap
                · omega
                by_cases c3475 : 0 < b0
                swap
                · omega
                by_cases c3476 : a0 < 0 + b0
                swap
                · -- branch
                  by_cases c3477 : 0 < a2
                  swap
                  · omega
                  by_cases c3478 : 0 < b4
                  swap
                  · omega
                  by_cases c3479 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c3480 : b0 + b2 < a0 + a2
                  swap
                  · -- branch
                    by_cases c3481 : 0 < a2
                    swap
                    · omega
                    by_cases c3482 : 0 < b2
                    swap
                    · omega
                    by_cases c3483 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c3484 : b0 < a0 + a2
                    swap
                    · omega
                    have f3485 := pair_fact E (i := 2) (j := 2) rfl rfl c3481 c3482
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3485
                    by_cases c3486 : 0 < a0
                    swap
                    · omega
                    by_cases c3487 : 0 < b2
                    swap
                    · omega
                    by_cases c3488 : 0 < b0 + b2
                    swap
                    · omega
                    by_cases c3489 : b0 < 0 + a0
                    swap
                    · -- branch
                      by_cases c3490 : 0 < a4
                      swap
                      · -- branch
                        by_cases c3491 : 0 < a10
                        swap
                        · omega
                        by_cases c3492 : 0 < b4
                        swap
                        · omega
                        by_cases c3493 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c3494 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                        swap
                        · omega
                        have f3495 := pair_fact E (i := 10) (j := 4) rfl rfl c3491 c3492
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3495
                        omega
                      by_cases c3496 : 0 < b0
                      swap
                      · omega
                      by_cases c3497 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c3498 : 0 < a4
                        swap
                        · omega
                        by_cases c3499 : 0 < b2
                        swap
                        · omega
                        by_cases c3500 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c3501 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f3502 := pair_fact E (i := 4) (j := 2) rfl rfl c3498 c3499
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3502
                        by_cases c3503 : 0 < a4
                        swap
                        · omega
                        by_cases c3504 : 0 < b4
                        swap
                        · omega
                        by_cases c3505 : a0 + a2 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c3506 : b0 + b2 < a0 + a2 + a4
                        swap
                        · -- branch
                          by_cases c3507 : 0 < a4
                          swap
                          · omega
                          by_cases c3508 : 0 < b6
                          swap
                          · omega
                          by_cases c3509 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c3510 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · -- branch
                            by_cases c3511 : 0 < a4
                            swap
                            · omega
                            by_cases c3512 : 0 < b8
                            swap
                            · omega
                            by_cases c3513 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c3514 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c3515 : 0 < a4
                              swap
                              · omega
                              by_cases c3516 : 0 < b10
                              swap
                              · omega
                              by_cases c3517 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c3518 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c3519 : 0 < a8
                                swap
                                · -- branch
                                  by_cases c3520 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c3521 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c3522 : a0 + a2 + a4 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c3523 : b0 + b2 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f3524 := pair_fact E (i := 6) (j := 4) rfl rfl c3520 c3521
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3524
                                  omega
                                by_cases c3525 : 0 < b4
                                swap
                                · omega
                                by_cases c3526 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c3527 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f3528 := pair_fact E (i := 8) (j := 4) rfl rfl c3519 c3525
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3528
                                omega
                              have f3529 := pair_fact E (i := 4) (j := 10) rfl rfl c3515 c3516
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3529
                              omega
                            have f3530 := pair_fact E (i := 4) (j := 8) rfl rfl c3511 c3512
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3530
                            omega
                          have f3531 := pair_fact E (i := 4) (j := 6) rfl rfl c3507 c3508
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3531
                          omega
                        have f3532 := pair_fact E (i := 4) (j := 4) rfl rfl c3503 c3504
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3532
                        omega
                      by_cases c3533 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f3534 := pair_fact E (i := 4) (j := 0) rfl rfl c3490 c3496
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3534
                      omega
                    have f3535 := pair_fact E (i := 0) (j := 2) rfl rfl c3486 c3487
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3535
                    omega
                  have f3536 := pair_fact E (i := 2) (j := 4) rfl rfl c3477 c3478
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3536
                  by_cases c3537 : 0 < a0
                  swap
                  · omega
                  by_cases c3538 : 0 < b2
                  swap
                  · -- branch
                    by_cases c3539 : 0 < a2
                    swap
                    · omega
                    by_cases c3540 : 0 < b2
                    swap
                    · -- branch
                      by_cases c3541 : 0 < a4
                      swap
                      · -- branch
                        by_cases c3542 : 0 < a4
                        swap
                        · -- branch
                          by_cases c3543 : 0 < a4
                          swap
                          · -- branch
                            by_cases c3544 : 0 < a4
                            swap
                            · -- branch
                              by_cases c3545 : 0 < a4
                              swap
                              · -- branch
                                by_cases c3546 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c3547 : 0 < a6
                                  swap
                                  · -- branch
                                    by_cases c3548 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c3549 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c3550 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c3551 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f3552 := pair_fact E (i := 8) (j := 4) rfl rfl c3548 c3549
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3552
                                    omega
                                  by_cases c3553 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c3554 : a0 + a2 + a4 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c3555 : b0 + b2 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f3556 := pair_fact E (i := 6) (j := 4) rfl rfl c3547 c3553
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3556
                                  omega
                                by_cases c3557 : 0 < b10
                                swap
                                · omega
                                by_cases c3558 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c3559 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                swap
                                · omega
                                have f3560 := pair_fact E (i := 4) (j := 10) rfl rfl c3546 c3557
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3560
                                omega
                              by_cases c3561 : 0 < b8
                              swap
                              · omega
                              by_cases c3562 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c3563 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · omega
                              have f3564 := pair_fact E (i := 4) (j := 8) rfl rfl c3545 c3561
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3564
                              omega
                            by_cases c3565 : 0 < b6
                            swap
                            · omega
                            by_cases c3566 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c3567 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · omega
                            have f3568 := pair_fact E (i := 4) (j := 6) rfl rfl c3544 c3565
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3568
                            omega
                          by_cases c3569 : 0 < b4
                          swap
                          · omega
                          by_cases c3570 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c3571 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f3572 := pair_fact E (i := 4) (j := 4) rfl rfl c3543 c3569
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3572
                          omega
                        by_cases c3573 : 0 < b2
                        swap
                        · omega
                        by_cases c3574 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c3575 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f3576 := pair_fact E (i := 4) (j := 2) rfl rfl c3542 c3573
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3576
                        omega
                      by_cases c3577 : 0 < b0
                      swap
                      · omega
                      by_cases c3578 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c3579 : 0 < a4
                        swap
                        · omega
                        by_cases c3580 : 0 < b2
                        swap
                        · -- branch
                          by_cases c3581 : 0 < a4
                          swap
                          · omega
                          by_cases c3582 : 0 < b6
                          swap
                          · omega
                          by_cases c3583 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c3584 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · -- branch
                            by_cases c3585 : 0 < a4
                            swap
                            · omega
                            by_cases c3586 : 0 < b4
                            swap
                            · omega
                            by_cases c3587 : a0 + a2 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c3588 : b0 + b2 < a0 + a2 + a4
                            swap
                            · omega
                            have f3589 := pair_fact E (i := 4) (j := 4) rfl rfl c3585 c3586
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3589
                            by_cases c3590 : 0 < a4
                            swap
                            · omega
                            by_cases c3591 : 0 < b8
                            swap
                            · omega
                            by_cases c3592 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c3593 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c3594 : 0 < a4
                              swap
                              · omega
                              by_cases c3595 : 0 < b10
                              swap
                              · omega
                              by_cases c3596 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c3597 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c3598 : 0 < a6
                                swap
                                · -- branch
                                  by_cases c3599 : 0 < a6
                                  swap
                                  · -- branch
                                    by_cases c3600 : 0 < a6
                                    swap
                                    · -- branch
                                      by_cases c3601 : 0 < a6
                                      swap
                                      · -- branch
                                        by_cases c3602 : 0 < a6
                                        swap
                                        · -- branch
                                          by_cases c3603 : 0 < a6
                                          swap
                                          · -- branch
                                            by_cases c3604 : 0 < a8
                                            swap
                                            · -- branch
                                              by_cases c3605 : 0 < a10
                                              swap
                                              · omega
                                              by_cases c3606 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c3607 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c3608 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                              swap
                                              · omega
                                              have f3609 := pair_fact E (i := 10) (j := 4) rfl rfl c3605 c3606
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3609
                                              omega
                                            by_cases c3610 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c3611 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c3612 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f3613 := pair_fact E (i := 8) (j := 4) rfl rfl c3604 c3610
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3613
                                            omega
                                          by_cases c3614 : 0 < b10
                                          swap
                                          · omega
                                          by_cases c3615 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                          swap
                                          · omega
                                          by_cases c3616 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f3617 := pair_fact E (i := 6) (j := 10) rfl rfl c3603 c3614
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3617
                                          omega
                                        by_cases c3618 : 0 < b8
                                        swap
                                        · omega
                                        by_cases c3619 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                        swap
                                        · omega
                                        by_cases c3620 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f3621 := pair_fact E (i := 6) (j := 8) rfl rfl c3602 c3618
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3621
                                        omega
                                      by_cases c3622 : 0 < b6
                                      swap
                                      · omega
                                      by_cases c3623 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                      swap
                                      · omega
                                      by_cases c3624 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f3625 := pair_fact E (i := 6) (j := 6) rfl rfl c3601 c3622
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3625
                                      omega
                                    by_cases c3626 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c3627 : a0 + a2 + a4 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c3628 : b0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f3629 := pair_fact E (i := 6) (j := 2) rfl rfl c3600 c3626
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3629
                                    omega
                                  by_cases c3630 : 0 < b0
                                  swap
                                  · omega
                                  by_cases c3631 : a0 + a2 + a4 < 0 + b0
                                  swap
                                  · omega
                                  by_cases c3632 : 0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f3633 := pair_fact E (i := 6) (j := 0) rfl rfl c3599 c3630
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3633
                                  omega
                                by_cases c3634 : 0 < b4
                                swap
                                · omega
                                by_cases c3635 : a0 + a2 + a4 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c3636 : b0 + b2 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f3637 := pair_fact E (i := 6) (j := 4) rfl rfl c3598 c3634
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3637
                                omega
                              have f3638 := pair_fact E (i := 4) (j := 10) rfl rfl c3594 c3595
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3638
                              omega
                            have f3639 := pair_fact E (i := 4) (j := 8) rfl rfl c3590 c3591
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3639
                            omega
                          have f3640 := pair_fact E (i := 4) (j := 6) rfl rfl c3581 c3582
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3640
                          omega
                        by_cases c3641 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c3642 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f3643 := pair_fact E (i := 4) (j := 2) rfl rfl c3579 c3580
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3643
                        omega
                      by_cases c3644 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f3645 := pair_fact E (i := 4) (j := 0) rfl rfl c3541 c3577
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3645
                      omega
                    by_cases c3646 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c3647 : b0 < a0 + a2
                    swap
                    · omega
                    have f3648 := pair_fact E (i := 2) (j := 2) rfl rfl c3539 c3540
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3648
                    omega
                  by_cases c3649 : 0 < b0 + b2
                  swap
                  · omega
                  by_cases c3650 : b0 < 0 + a0
                  swap
                  · -- branch
                    by_cases c3651 : 0 < a2
                    swap
                    · omega
                    by_cases c3652 : 0 < b2
                    swap
                    · omega
                    by_cases c3653 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c3654 : b0 < a0 + a2
                    swap
                    · omega
                    have f3655 := pair_fact E (i := 2) (j := 2) rfl rfl c3651 c3652
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3655
                    by_cases c3656 : 0 < a4
                    swap
                    · -- branch
                      by_cases c3657 : 0 < a4
                      swap
                      · -- branch
                        by_cases c3658 : 0 < a4
                        swap
                        · -- branch
                          by_cases c3659 : 0 < a4
                          swap
                          · -- branch
                            by_cases c3660 : 0 < a4
                            swap
                            · -- branch
                              by_cases c3661 : 0 < a4
                              swap
                              · -- branch
                                by_cases c3662 : 0 < a6
                                swap
                                · -- branch
                                  by_cases c3663 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c3664 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c3665 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c3666 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f3667 := pair_fact E (i := 8) (j := 4) rfl rfl c3663 c3664
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3667
                                  omega
                                by_cases c3668 : 0 < b4
                                swap
                                · omega
                                by_cases c3669 : a0 + a2 + a4 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c3670 : b0 + b2 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f3671 := pair_fact E (i := 6) (j := 4) rfl rfl c3662 c3668
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3671
                                omega
                              by_cases c3672 : 0 < b10
                              swap
                              · omega
                              by_cases c3673 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c3674 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · omega
                              have f3675 := pair_fact E (i := 4) (j := 10) rfl rfl c3661 c3672
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3675
                              omega
                            by_cases c3676 : 0 < b8
                            swap
                            · omega
                            by_cases c3677 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c3678 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · omega
                            have f3679 := pair_fact E (i := 4) (j := 8) rfl rfl c3660 c3676
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3679
                            omega
                          by_cases c3680 : 0 < b6
                          swap
                          · omega
                          by_cases c3681 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c3682 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · omega
                          have f3683 := pair_fact E (i := 4) (j := 6) rfl rfl c3659 c3680
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3683
                          omega
                        by_cases c3684 : 0 < b4
                        swap
                        · omega
                        by_cases c3685 : a0 + a2 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c3686 : b0 + b2 < a0 + a2 + a4
                        swap
                        · omega
                        have f3687 := pair_fact E (i := 4) (j := 4) rfl rfl c3658 c3684
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3687
                        omega
                      by_cases c3688 : 0 < b2
                      swap
                      · omega
                      by_cases c3689 : a0 + a2 < b0 + b2
                      swap
                      · omega
                      by_cases c3690 : b0 < a0 + a2 + a4
                      swap
                      · omega
                      have f3691 := pair_fact E (i := 4) (j := 2) rfl rfl c3657 c3688
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3691
                      omega
                    by_cases c3692 : 0 < b0
                    swap
                    · omega
                    by_cases c3693 : a0 + a2 < 0 + b0
                    swap
                    · -- branch
                      by_cases c3694 : 0 < a4
                      swap
                      · omega
                      by_cases c3695 : 0 < b2
                      swap
                      · omega
                      by_cases c3696 : a0 + a2 < b0 + b2
                      swap
                      · -- branch
                        by_cases c3697 : 0 < a4
                        swap
                        · omega
                        by_cases c3698 : 0 < b4
                        swap
                        · omega
                        by_cases c3699 : a0 + a2 < b0 + b2 + b4
                        swap
                        · -- branch
                          by_cases c3700 : 0 < a4
                          swap
                          · omega
                          by_cases c3701 : 0 < b6
                          swap
                          · omega
                          by_cases c3702 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c3703 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · omega
                          have f3704 := pair_fact E (i := 4) (j := 6) rfl rfl c3700 c3701
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3704
                          omega
                        by_cases c3705 : b0 + b2 < a0 + a2 + a4
                        swap
                        · omega
                        have f3706 := pair_fact E (i := 4) (j := 4) rfl rfl c3697 c3698
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3706
                        omega
                      by_cases c3707 : b0 < a0 + a2 + a4
                      swap
                      · omega
                      have f3708 := pair_fact E (i := 4) (j := 2) rfl rfl c3694 c3695
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3708
                      omega
                    by_cases c3709 : 0 < a0 + a2 + a4
                    swap
                    · omega
                    have f3710 := pair_fact E (i := 4) (j := 0) rfl rfl c3656 c3692
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3710
                    omega
                  have f3711 := pair_fact E (i := 0) (j := 2) rfl rfl c3537 c3538
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3711
                  omega
                by_cases c3712 : 0 < a0 + a2
                swap
                · omega
                have f3713 := pair_fact E (i := 2) (j := 0) rfl rfl c3474 c3475
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3713
                by_cases c3714 : 0 < a2
                swap
                · omega
                by_cases c3715 : 0 < b4
                swap
                · omega
                by_cases c3716 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c3717 : b0 + b2 < a0 + a2
                swap
                · -- branch
                  by_cases c3718 : 0 < a0
                  swap
                  · omega
                  by_cases c3719 : 0 < b2
                  swap
                  · -- branch
                    by_cases c3720 : 0 < a2
                    swap
                    · omega
                    by_cases c3721 : 0 < b2
                    swap
                    · -- branch
                      by_cases c3722 : 0 < a4
                      swap
                      · -- branch
                        by_cases c3723 : 0 < a4
                        swap
                        · -- branch
                          by_cases c3724 : 0 < a4
                          swap
                          · -- branch
                            by_cases c3725 : 0 < a4
                            swap
                            · -- branch
                              by_cases c3726 : 0 < a4
                              swap
                              · -- branch
                                by_cases c3727 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c3728 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c3729 : 0 < b0
                                  swap
                                  · omega
                                  by_cases c3730 : a0 + a2 + a4 < 0 + b0
                                  swap
                                  · -- branch
                                    by_cases c3731 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c3732 : 0 < b2
                                    swap
                                    · -- branch
                                      by_cases c3733 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c3734 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c3735 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c3736 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f3737 := pair_fact E (i := 6) (j := 4) rfl rfl c3733 c3734
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3737
                                      by_cases c3738 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c3739 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c3740 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c3741 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f3742 := pair_fact E (i := 8) (j := 4) rfl rfl c3738 c3739
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3742
                                      omega
                                    by_cases c3743 : a0 + a2 + a4 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c3744 : b0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f3745 := pair_fact E (i := 6) (j := 2) rfl rfl c3731 c3732
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3745
                                    omega
                                  by_cases c3746 : 0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f3747 := pair_fact E (i := 6) (j := 0) rfl rfl c3728 c3729
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3747
                                  omega
                                by_cases c3748 : 0 < b10
                                swap
                                · omega
                                by_cases c3749 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c3750 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                swap
                                · omega
                                have f3751 := pair_fact E (i := 4) (j := 10) rfl rfl c3727 c3748
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3751
                                omega
                              by_cases c3752 : 0 < b8
                              swap
                              · omega
                              by_cases c3753 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c3754 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · omega
                              have f3755 := pair_fact E (i := 4) (j := 8) rfl rfl c3726 c3752
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3755
                              omega
                            by_cases c3756 : 0 < b6
                            swap
                            · omega
                            by_cases c3757 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c3758 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · omega
                            have f3759 := pair_fact E (i := 4) (j := 6) rfl rfl c3725 c3756
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3759
                            omega
                          by_cases c3760 : 0 < b4
                          swap
                          · omega
                          by_cases c3761 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c3762 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f3763 := pair_fact E (i := 4) (j := 4) rfl rfl c3724 c3760
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3763
                          omega
                        by_cases c3764 : 0 < b2
                        swap
                        · omega
                        by_cases c3765 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c3766 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f3767 := pair_fact E (i := 4) (j := 2) rfl rfl c3723 c3764
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3767
                        omega
                      by_cases c3768 : 0 < b0
                      swap
                      · omega
                      by_cases c3769 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c3770 : 0 < a4
                        swap
                        · omega
                        by_cases c3771 : 0 < b4
                        swap
                        · omega
                        by_cases c3772 : a0 + a2 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c3773 : b0 + b2 < a0 + a2 + a4
                        swap
                        · omega
                        have f3774 := pair_fact E (i := 4) (j := 4) rfl rfl c3770 c3771
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3774
                        omega
                      by_cases c3775 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f3776 := pair_fact E (i := 4) (j := 0) rfl rfl c3722 c3768
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3776
                      omega
                    by_cases c3777 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c3778 : b0 < a0 + a2
                    swap
                    · omega
                    have f3779 := pair_fact E (i := 2) (j := 2) rfl rfl c3720 c3721
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3779
                    omega
                  by_cases c3780 : 0 < b0 + b2
                  swap
                  · omega
                  by_cases c3781 : b0 < 0 + a0
                  swap
                  · -- branch
                    by_cases c3782 : 0 < a2
                    swap
                    · omega
                    by_cases c3783 : 0 < b2
                    swap
                    · omega
                    by_cases c3784 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c3785 : b0 < a0 + a2
                    swap
                    · -- branch
                      by_cases c3786 : 0 < a4
                      swap
                      · -- branch
                        by_cases c3787 : 0 < a6
                        swap
                        · omega
                        by_cases c3788 : 0 < b2
                        swap
                        · omega
                        by_cases c3789 : a0 + a2 + a4 < b0 + b2
                        swap
                        · omega
                        by_cases c3790 : b0 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f3791 := pair_fact E (i := 6) (j := 2) rfl rfl c3787 c3788
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3791
                        omega
                      by_cases c3792 : 0 < b0
                      swap
                      · omega
                      by_cases c3793 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c3794 : 0 < a4
                        swap
                        · omega
                        by_cases c3795 : 0 < b2
                        swap
                        · omega
                        by_cases c3796 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c3797 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f3798 := pair_fact E (i := 4) (j := 2) rfl rfl c3794 c3795
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3798
                        omega
                      by_cases c3799 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f3800 := pair_fact E (i := 4) (j := 0) rfl rfl c3786 c3792
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3800
                      omega
                    have f3801 := pair_fact E (i := 2) (j := 2) rfl rfl c3782 c3783
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3801
                    omega
                  have f3802 := pair_fact E (i := 0) (j := 2) rfl rfl c3718 c3719
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3802
                  omega
                have f3803 := pair_fact E (i := 2) (j := 4) rfl rfl c3714 c3715
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3803
                omega
              have f3804 := pair_fact E (i := 2) (j := 10) rfl rfl c3470 c3471
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3804
              omega
            have f3805 := pair_fact E (i := 2) (j := 8) rfl rfl c3466 c3467
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3805
            omega
          have f3806 := pair_fact E (i := 2) (j := 6) rfl rfl c3327 c3463
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3806
          omega
        have f3807 := pair_fact E (i := 0) (j := 10) rfl rfl c2923 c2924
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3807
        omega
      have f3808 := pair_fact E (i := 0) (j := 8) rfl rfl c2374 c2375
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3808
      omega
    have f3809 := pair_fact E (i := 0) (j := 6) rfl rfl c1640 c1641
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3809
    omega
  have f3810 := pair_fact E (i := 0) (j := 4) rfl rfl c1476 c1477
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f3810
  omega

end Blocks
