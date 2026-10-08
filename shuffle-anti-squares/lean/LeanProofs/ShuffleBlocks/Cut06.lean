import LeanProofs.ShuffleBlocks.Basic

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Blocks

set_option maxHeartbeats 0 in
/-- Cut inside run 6 of `V`: no splitting of this rotation gives two equal copies. -/
theorem V_cut06 (L l m v k a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9 a10 b10 : Nat)
    (hl : 1 ≤ l) (hm : m = 2 * v + 1) (hL : 9 * l ≤ L) (hk : k ≤ 2 * l)
    (e0 : a0 + b0 = (2 * l - k))
    (e1 : a1 + b1 = m)
    (e2 : a2 + b2 = l)
    (e3 : a3 + b3 = 3 * m)
    (e4 : a4 + b4 = L)
    (e5 : a5 + b5 = m)
    (e6 : a6 + b6 = 5 * l)
    (e7 : a7 + b7 = 2 * m)
    (e8 : a8 + b8 = L)
    (e9 : a9 + b9 = m)
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
              by_cases c7 : 0 < a7
              swap
              · omega
              by_cases c8 : 0 < b3
              swap
              · omega
              by_cases c9 : a1 + a3 + a5 < b1 + b3
              swap
              · omega
              by_cases c10 : b1 < a1 + a3 + a5 + a7
              swap
              · omega
              have f11 := pair_fact E (i := 7) (j := 3) rfl rfl c7 c8
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f11
              omega
            by_cases c12 : 0 < b1
            swap
            · omega
            by_cases c13 : a1 < 0 + b1
            swap
            · omega
            by_cases c14 : 0 < a1 + a3
            swap
            · omega
            have f15 := pair_fact E (i := 3) (j := 1) rfl rfl c6 c12
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f15
            by_cases c16 : 0 < a3
            swap
            · omega
            by_cases c17 : 0 < b7
            swap
            · -- branch
              by_cases c18 : 0 < a7
              swap
              · omega
              by_cases c19 : 0 < b1
              swap
              · omega
              by_cases c20 : a1 + a3 + a5 < 0 + b1
              swap
              · -- branch
                by_cases c21 : 0 < a7
                swap
                · omega
                by_cases c22 : 0 < b3
                swap
                · omega
                by_cases c23 : a1 + a3 + a5 < b1 + b3
                swap
                · -- branch
                  by_cases c24 : 0 < a3
                  swap
                  · omega
                  by_cases c25 : 0 < b3
                  swap
                  · omega
                  by_cases c26 : a1 < b1 + b3
                  swap
                  · omega
                  by_cases c27 : b1 < a1 + a3
                  swap
                  · omega
                  have f28 := pair_fact E (i := 3) (j := 3) rfl rfl c24 c25
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f28
                  by_cases c29 : 0 < a3
                  swap
                  · omega
                  by_cases c30 : 0 < b5
                  swap
                  · omega
                  by_cases c31 : a1 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c32 : b1 + b3 < a1 + a3
                  swap
                  · -- branch
                    by_cases c33 : 0 < a3
                    swap
                    · omega
                    by_cases c34 : 0 < b9
                    swap
                    · omega
                    by_cases c35 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c36 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · -- branch
                      by_cases c37 : 0 < a5
                      swap
                      · -- branch
                        by_cases c38 : 0 < a5
                        swap
                        · -- branch
                          by_cases c39 : 0 < a5
                          swap
                          · -- branch
                            by_cases c40 : 0 < a5
                            swap
                            · -- branch
                              by_cases c41 : 0 < a5
                              swap
                              · -- branch
                                by_cases c42 : 0 < a7
                                swap
                                · omega
                                by_cases c43 : 0 < b5
                                swap
                                · omega
                                by_cases c44 : a1 + a3 + a5 < b1 + b3 + b5
                                swap
                                · omega
                                by_cases c45 : b1 + b3 < a1 + a3 + a5 + a7
                                swap
                                · omega
                                have f46 := pair_fact E (i := 7) (j := 5) rfl rfl c42 c43
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f46
                                by_cases c47 : 0 < a7
                                swap
                                · omega
                                by_cases c48 : 0 < b9
                                swap
                                · omega
                                by_cases c49 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
                                swap
                                · omega
                                by_cases c50 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
                                swap
                                · omega
                                have f51 := pair_fact E (i := 7) (j := 9) rfl rfl c47 c48
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f51
                                omega
                              by_cases c52 : 0 < b9
                              swap
                              · omega
                              by_cases c53 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                              swap
                              · omega
                              by_cases c54 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                              swap
                              · omega
                              have f55 := pair_fact E (i := 5) (j := 9) rfl rfl c41 c52
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f55
                              omega
                            by_cases c56 : 0 < b7
                            swap
                            · omega
                            by_cases c57 : a1 + a3 < b1 + b3 + b5 + b7
                            swap
                            · omega
                            by_cases c58 : b1 + b3 + b5 < a1 + a3 + a5
                            swap
                            · omega
                            have f59 := pair_fact E (i := 5) (j := 7) rfl rfl c40 c56
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f59
                            omega
                          by_cases c60 : 0 < b5
                          swap
                          · omega
                          by_cases c61 : a1 + a3 < b1 + b3 + b5
                          swap
                          · omega
                          by_cases c62 : b1 + b3 < a1 + a3 + a5
                          swap
                          · omega
                          have f63 := pair_fact E (i := 5) (j := 5) rfl rfl c39 c60
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f63
                          omega
                        by_cases c64 : 0 < b3
                        swap
                        · omega
                        by_cases c65 : a1 + a3 < b1 + b3
                        swap
                        · omega
                        by_cases c66 : b1 < a1 + a3 + a5
                        swap
                        · omega
                        have f67 := pair_fact E (i := 5) (j := 3) rfl rfl c38 c64
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f67
                        omega
                      by_cases c68 : 0 < b1
                      swap
                      · omega
                      by_cases c69 : a1 + a3 < 0 + b1
                      swap
                      · omega
                      by_cases c70 : 0 < a1 + a3 + a5
                      swap
                      · omega
                      have f71 := pair_fact E (i := 5) (j := 1) rfl rfl c37 c68
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f71
                      omega
                    have f72 := pair_fact E (i := 3) (j := 9) rfl rfl c33 c34
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f72
                    omega
                  have f73 := pair_fact E (i := 3) (j := 5) rfl rfl c29 c30
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f73
                  omega
                by_cases c74 : b1 < a1 + a3 + a5 + a7
                swap
                · omega
                have f75 := pair_fact E (i := 7) (j := 3) rfl rfl c21 c22
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f75
                omega
              by_cases c76 : 0 < a1 + a3 + a5 + a7
              swap
              · omega
              have f77 := pair_fact E (i := 7) (j := 1) rfl rfl c18 c19
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f77
              omega
            by_cases c78 : a1 < b1 + b3 + b5 + b7
            swap
            · omega
            by_cases c79 : b1 + b3 + b5 < a1 + a3
            swap
            · -- branch
              by_cases c80 : 0 < a3
              swap
              · omega
              by_cases c81 : 0 < b3
              swap
              · omega
              by_cases c82 : a1 < b1 + b3
              swap
              · omega
              by_cases c83 : b1 < a1 + a3
              swap
              · -- branch
                by_cases c84 : 0 < a7
                swap
                · omega
                by_cases c85 : 0 < b3
                swap
                · omega
                by_cases c86 : a1 + a3 + a5 < b1 + b3
                swap
                · omega
                by_cases c87 : b1 < a1 + a3 + a5 + a7
                swap
                · omega
                have f88 := pair_fact E (i := 7) (j := 3) rfl rfl c84 c85
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f88
                omega
              have f89 := pair_fact E (i := 3) (j := 3) rfl rfl c80 c81
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f89
              by_cases c90 : 0 < a3
              swap
              · omega
              by_cases c91 : 0 < b9
              swap
              · -- branch
                by_cases c92 : 0 < a9
                swap
                · omega
                by_cases c93 : 0 < b1
                swap
                · omega
                by_cases c94 : a1 + a3 + a5 + a7 < 0 + b1
                swap
                · -- branch
                  by_cases c95 : 0 < a9
                  swap
                  · omega
                  by_cases c96 : 0 < b3
                  swap
                  · omega
                  by_cases c97 : a1 + a3 + a5 + a7 < b1 + b3
                  swap
                  · -- branch
                    by_cases c98 : 0 < a9
                    swap
                    · omega
                    by_cases c99 : 0 < b7
                    swap
                    · omega
                    by_cases c100 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7
                    swap
                    · omega
                    by_cases c101 : b1 + b3 + b5 < a1 + a3 + a5 + a7 + a9
                    swap
                    · omega
                    have f102 := pair_fact E (i := 9) (j := 7) rfl rfl c98 c99
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f102
                    by_cases c103 : 0 < a9
                    swap
                    · omega
                    by_cases c104 : 0 < b9
                    swap
                    · -- branch
                      by_cases c105 : 0 < a3
                      swap
                      · omega
                      by_cases c106 : 0 < b5
                      swap
                      · -- branch
                        by_cases c107 : 0 < a5
                        swap
                        · omega
                        by_cases c108 : 0 < b1
                        swap
                        · omega
                        by_cases c109 : a1 + a3 < 0 + b1
                        swap
                        · -- branch
                          by_cases c110 : 0 < a5
                          swap
                          · omega
                          by_cases c111 : 0 < b5
                          swap
                          · -- branch
                            by_cases c112 : 0 < a5
                            swap
                            · omega
                            by_cases c113 : 0 < b7
                            swap
                            · omega
                            by_cases c114 : a1 + a3 < b1 + b3 + b5 + b7
                            swap
                            · omega
                            by_cases c115 : b1 + b3 + b5 < a1 + a3 + a5
                            swap
                            · -- branch
                              by_cases c116 : 0 < a7
                              swap
                              · omega
                              by_cases c117 : 0 < b3
                              swap
                              · omega
                              by_cases c118 : a1 + a3 + a5 < b1 + b3
                              swap
                              · omega
                              by_cases c119 : b1 < a1 + a3 + a5 + a7
                              swap
                              · omega
                              have f120 := pair_fact E (i := 7) (j := 3) rfl rfl c116 c117
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f120
                              omega
                            have f121 := pair_fact E (i := 5) (j := 7) rfl rfl c112 c113
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f121
                            omega
                          by_cases c122 : a1 + a3 < b1 + b3 + b5
                          swap
                          · omega
                          by_cases c123 : b1 + b3 < a1 + a3 + a5
                          swap
                          · omega
                          have f124 := pair_fact E (i := 5) (j := 5) rfl rfl c110 c111
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f124
                          omega
                        by_cases c125 : 0 < a1 + a3 + a5
                        swap
                        · omega
                        have f126 := pair_fact E (i := 5) (j := 1) rfl rfl c107 c108
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f126
                        omega
                      by_cases c127 : a1 < b1 + b3 + b5
                      swap
                      · omega
                      by_cases c128 : b1 + b3 < a1 + a3
                      swap
                      · -- branch
                        by_cases c129 : 0 < a7
                        swap
                        · omega
                        by_cases c130 : 0 < b1
                        swap
                        · omega
                        by_cases c131 : a1 + a3 + a5 < 0 + b1
                        swap
                        · -- branch
                          by_cases c132 : 0 < a7
                          swap
                          · omega
                          by_cases c133 : 0 < b3
                          swap
                          · omega
                          by_cases c134 : a1 + a3 + a5 < b1 + b3
                          swap
                          · -- branch
                            by_cases c135 : 0 < a7
                            swap
                            · omega
                            by_cases c136 : 0 < b5
                            swap
                            · omega
                            by_cases c137 : a1 + a3 + a5 < b1 + b3 + b5
                            swap
                            · -- branch
                              by_cases c138 : 0 < a5
                              swap
                              · omega
                              by_cases c139 : 0 < b5
                              swap
                              · omega
                              by_cases c140 : a1 + a3 < b1 + b3 + b5
                              swap
                              · omega
                              by_cases c141 : b1 + b3 < a1 + a3 + a5
                              swap
                              · omega
                              have f142 := pair_fact E (i := 5) (j := 5) rfl rfl c138 c139
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f142
                              omega
                            by_cases c143 : b1 + b3 < a1 + a3 + a5 + a7
                            swap
                            · omega
                            have f144 := pair_fact E (i := 7) (j := 5) rfl rfl c135 c136
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f144
                            omega
                          by_cases c145 : b1 < a1 + a3 + a5 + a7
                          swap
                          · omega
                          have f146 := pair_fact E (i := 7) (j := 3) rfl rfl c132 c133
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f146
                          omega
                        by_cases c147 : 0 < a1 + a3 + a5 + a7
                        swap
                        · omega
                        have f148 := pair_fact E (i := 7) (j := 1) rfl rfl c129 c130
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f148
                        omega
                      have f149 := pair_fact E (i := 3) (j := 5) rfl rfl c105 c106
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f149
                      omega
                    by_cases c150 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c151 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
                    swap
                    · omega
                    have f152 := pair_fact E (i := 9) (j := 9) rfl rfl c103 c104
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f152
                    omega
                  by_cases c153 : b1 < a1 + a3 + a5 + a7 + a9
                  swap
                  · omega
                  have f154 := pair_fact E (i := 9) (j := 3) rfl rfl c95 c96
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f154
                  omega
                by_cases c155 : 0 < a1 + a3 + a5 + a7 + a9
                swap
                · omega
                have f156 := pair_fact E (i := 9) (j := 1) rfl rfl c92 c93
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f156
                omega
              by_cases c157 : a1 < b1 + b3 + b5 + b7 + b9
              swap
              · omega
              by_cases c158 : b1 + b3 + b5 + b7 < a1 + a3
              swap
              · -- branch
                by_cases c159 : 0 < a7
                swap
                · omega
                by_cases c160 : 0 < b1
                swap
                · omega
                by_cases c161 : a1 + a3 + a5 < 0 + b1
                swap
                · -- branch
                  by_cases c162 : 0 < a7
                  swap
                  · omega
                  by_cases c163 : 0 < b3
                  swap
                  · omega
                  by_cases c164 : a1 + a3 + a5 < b1 + b3
                  swap
                  · -- branch
                    by_cases c165 : 0 < a5
                    swap
                    · -- branch
                      by_cases c166 : 0 < a5
                      swap
                      · -- branch
                        by_cases c167 : 0 < a5
                        swap
                        · -- branch
                          by_cases c168 : 0 < a5
                          swap
                          · -- branch
                            by_cases c169 : 0 < a5
                            swap
                            · -- branch
                              by_cases c170 : 0 < a7
                              swap
                              · omega
                              by_cases c171 : 0 < b5
                              swap
                              · omega
                              by_cases c172 : a1 + a3 + a5 < b1 + b3 + b5
                              swap
                              · omega
                              by_cases c173 : b1 + b3 < a1 + a3 + a5 + a7
                              swap
                              · omega
                              have f174 := pair_fact E (i := 7) (j := 5) rfl rfl c170 c171
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f174
                              by_cases c175 : 0 < a3
                              swap
                              · omega
                              by_cases c176 : 0 < b5
                              swap
                              · omega
                              by_cases c177 : a1 < b1 + b3 + b5
                              swap
                              · omega
                              by_cases c178 : b1 + b3 < a1 + a3
                              swap
                              · -- branch
                                by_cases c179 : 0 < a7
                                swap
                                · omega
                                by_cases c180 : 0 < b7
                                swap
                                · omega
                                by_cases c181 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                                swap
                                · omega
                                by_cases c182 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                                swap
                                · omega
                                have f183 := pair_fact E (i := 7) (j := 7) rfl rfl c179 c180
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f183
                                by_cases c184 : 0 < a7
                                swap
                                · omega
                                by_cases c185 : 0 < b9
                                swap
                                · omega
                                by_cases c186 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
                                swap
                                · omega
                                by_cases c187 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
                                swap
                                · -- branch
                                  by_cases c188 : 0 < a9
                                  swap
                                  · omega
                                  by_cases c189 : 0 < b7
                                  swap
                                  · omega
                                  by_cases c190 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7
                                  swap
                                  · omega
                                  by_cases c191 : b1 + b3 + b5 < a1 + a3 + a5 + a7 + a9
                                  swap
                                  · omega
                                  have f192 := pair_fact E (i := 9) (j := 7) rfl rfl c188 c189
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f192
                                  omega
                                have f193 := pair_fact E (i := 7) (j := 9) rfl rfl c184 c185
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f193
                                omega
                              have f194 := pair_fact E (i := 3) (j := 5) rfl rfl c175 c176
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f194
                              omega
                            by_cases c195 : 0 < b9
                            swap
                            · omega
                            by_cases c196 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                            swap
                            · omega
                            by_cases c197 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                            swap
                            · omega
                            have f198 := pair_fact E (i := 5) (j := 9) rfl rfl c169 c195
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f198
                            omega
                          by_cases c199 : 0 < b7
                          swap
                          · omega
                          by_cases c200 : a1 + a3 < b1 + b3 + b5 + b7
                          swap
                          · omega
                          by_cases c201 : b1 + b3 + b5 < a1 + a3 + a5
                          swap
                          · omega
                          have f202 := pair_fact E (i := 5) (j := 7) rfl rfl c168 c199
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f202
                          omega
                        by_cases c203 : 0 < b5
                        swap
                        · omega
                        by_cases c204 : a1 + a3 < b1 + b3 + b5
                        swap
                        · omega
                        by_cases c205 : b1 + b3 < a1 + a3 + a5
                        swap
                        · omega
                        have f206 := pair_fact E (i := 5) (j := 5) rfl rfl c167 c203
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f206
                        omega
                      by_cases c207 : 0 < b3
                      swap
                      · omega
                      by_cases c208 : a1 + a3 < b1 + b3
                      swap
                      · omega
                      by_cases c209 : b1 < a1 + a3 + a5
                      swap
                      · omega
                      have f210 := pair_fact E (i := 5) (j := 3) rfl rfl c166 c207
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f210
                      omega
                    by_cases c211 : 0 < b1
                    swap
                    · omega
                    by_cases c212 : a1 + a3 < 0 + b1
                    swap
                    · -- branch
                      by_cases c213 : 0 < a5
                      swap
                      · omega
                      by_cases c214 : 0 < b9
                      swap
                      · omega
                      by_cases c215 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                      swap
                      · omega
                      by_cases c216 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                      swap
                      · -- branch
                        by_cases c217 : 0 < a5
                        swap
                        · omega
                        by_cases c218 : 0 < b3
                        swap
                        · omega
                        by_cases c219 : a1 + a3 < b1 + b3
                        swap
                        · -- branch
                          by_cases c220 : 0 < a5
                          swap
                          · omega
                          by_cases c221 : 0 < b7
                          swap
                          · omega
                          by_cases c222 : a1 + a3 < b1 + b3 + b5 + b7
                          swap
                          · omega
                          by_cases c223 : b1 + b3 + b5 < a1 + a3 + a5
                          swap
                          · -- branch
                            by_cases c224 : 0 < a5
                            swap
                            · omega
                            by_cases c225 : 0 < b5
                            swap
                            · omega
                            by_cases c226 : a1 + a3 < b1 + b3 + b5
                            swap
                            · omega
                            by_cases c227 : b1 + b3 < a1 + a3 + a5
                            swap
                            · omega
                            have f228 := pair_fact E (i := 5) (j := 5) rfl rfl c224 c225
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f228
                            by_cases c229 : 0 < a3
                            swap
                            · omega
                            by_cases c230 : 0 < b5
                            swap
                            · omega
                            by_cases c231 : a1 < b1 + b3 + b5
                            swap
                            · omega
                            by_cases c232 : b1 + b3 < a1 + a3
                            swap
                            · -- branch
                              by_cases c233 : 0 < a7
                              swap
                              · omega
                              by_cases c234 : 0 < b5
                              swap
                              · omega
                              by_cases c235 : a1 + a3 + a5 < b1 + b3 + b5
                              swap
                              · omega
                              by_cases c236 : b1 + b3 < a1 + a3 + a5 + a7
                              swap
                              · omega
                              have f237 := pair_fact E (i := 7) (j := 5) rfl rfl c233 c234
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f237
                              by_cases c238 : 0 < a7
                              swap
                              · omega
                              by_cases c239 : 0 < b7
                              swap
                              · omega
                              by_cases c240 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                              swap
                              · omega
                              by_cases c241 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                              swap
                              · omega
                              have f242 := pair_fact E (i := 7) (j := 7) rfl rfl c238 c239
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f242
                              omega
                            have f243 := pair_fact E (i := 3) (j := 5) rfl rfl c229 c230
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f243
                            omega
                          have f244 := pair_fact E (i := 5) (j := 7) rfl rfl c220 c221
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f244
                          by_cases c245 : 0 < a7
                          swap
                          · omega
                          by_cases c246 : 0 < b9
                          swap
                          · omega
                          by_cases c247 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
                          swap
                          · omega
                          by_cases c248 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
                          swap
                          · -- branch
                            by_cases c249 : 0 < a9
                            swap
                            · omega
                            by_cases c250 : 0 < b7
                            swap
                            · omega
                            by_cases c251 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7
                            swap
                            · omega
                            by_cases c252 : b1 + b3 + b5 < a1 + a3 + a5 + a7 + a9
                            swap
                            · omega
                            have f253 := pair_fact E (i := 9) (j := 7) rfl rfl c249 c250
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f253
                            omega
                          have f254 := pair_fact E (i := 7) (j := 9) rfl rfl c245 c246
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f254
                          omega
                        by_cases c255 : b1 < a1 + a3 + a5
                        swap
                        · omega
                        have f256 := pair_fact E (i := 5) (j := 3) rfl rfl c217 c218
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f256
                        by_cases c257 : 0 < a7
                        swap
                        · omega
                        by_cases c258 : 0 < b7
                        swap
                        · omega
                        by_cases c259 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                        swap
                        · omega
                        by_cases c260 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                        swap
                        · omega
                        have f261 := pair_fact E (i := 7) (j := 7) rfl rfl c257 c258
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f261
                        omega
                      have f262 := pair_fact E (i := 5) (j := 9) rfl rfl c213 c214
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f262
                      omega
                    by_cases c263 : 0 < a1 + a3 + a5
                    swap
                    · omega
                    have f264 := pair_fact E (i := 5) (j := 1) rfl rfl c165 c211
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f264
                    omega
                  by_cases c265 : b1 < a1 + a3 + a5 + a7
                  swap
                  · omega
                  have f266 := pair_fact E (i := 7) (j := 3) rfl rfl c162 c163
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f266
                  omega
                by_cases c267 : 0 < a1 + a3 + a5 + a7
                swap
                · omega
                have f268 := pair_fact E (i := 7) (j := 1) rfl rfl c159 c160
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f268
                omega
              have f269 := pair_fact E (i := 3) (j := 9) rfl rfl c90 c91
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f269
              omega
            have f270 := pair_fact E (i := 3) (j := 7) rfl rfl c16 c17
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f270
            omega
          by_cases c271 : 0 < b9
          swap
          · omega
          by_cases c272 : 0 < b1 + b3 + b5 + b7 + b9
          swap
          · omega
          by_cases c273 : b1 + b3 + b5 + b7 < 0 + a1
          swap
          · omega
          have f274 := pair_fact E (i := 1) (j := 9) rfl rfl c5 c271
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f274
          omega
        by_cases c275 : 0 < b7
        swap
        · omega
        by_cases c276 : 0 < b1 + b3 + b5 + b7
        swap
        · omega
        by_cases c277 : b1 + b3 + b5 < 0 + a1
        swap
        · omega
        have f278 := pair_fact E (i := 1) (j := 7) rfl rfl c4 c275
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f278
        omega
      by_cases c279 : 0 < b5
      swap
      · omega
      by_cases c280 : 0 < b1 + b3 + b5
      swap
      · omega
      by_cases c281 : b1 + b3 < 0 + a1
      swap
      · omega
      have f282 := pair_fact E (i := 1) (j := 5) rfl rfl c3 c279
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f282
      omega
    by_cases c283 : 0 < b3
    swap
    · omega
    by_cases c284 : 0 < b1 + b3
    swap
    · omega
    by_cases c285 : b1 < 0 + a1
    swap
    · omega
    have f286 := pair_fact E (i := 1) (j := 3) rfl rfl c2 c283
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f286
    omega
  by_cases c287 : 0 < b1
  swap
  · -- branch
    by_cases c288 : 0 < a1
    swap
    · omega
    by_cases c289 : 0 < b3
    swap
    · -- branch
      by_cases c290 : 0 < a3
      swap
      · omega
      by_cases c291 : 0 < b7
      swap
      · omega
      by_cases c292 : a1 < b1 + b3 + b5 + b7
      swap
      · omega
      by_cases c293 : b1 + b3 + b5 < a1 + a3
      swap
      · omega
      have f294 := pair_fact E (i := 3) (j := 7) rfl rfl c290 c291
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f294
      omega
    by_cases c295 : 0 < b1 + b3
    swap
    · omega
    by_cases c296 : b1 < 0 + a1
    swap
    · omega
    have f297 := pair_fact E (i := 1) (j := 3) rfl rfl c288 c289
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f297
    by_cases c298 : 0 < a1
    swap
    · omega
    by_cases c299 : 0 < b7
    swap
    · -- branch
      by_cases c300 : 0 < a7
      swap
      · omega
      by_cases c301 : 0 < b1
      swap
      · -- branch
        by_cases c302 : 0 < a7
        swap
        · omega
        by_cases c303 : 0 < b3
        swap
        · omega
        by_cases c304 : a1 + a3 + a5 < b1 + b3
        swap
        · -- branch
          by_cases c305 : 0 < a1
          swap
          · omega
          by_cases c306 : 0 < b5
          swap
          · omega
          by_cases c307 : 0 < b1 + b3 + b5
          swap
          · omega
          by_cases c308 : b1 + b3 < 0 + a1
          swap
          · -- branch
            by_cases c309 : 0 < a1
            swap
            · omega
            by_cases c310 : 0 < b9
            swap
            · omega
            by_cases c311 : 0 < b1 + b3 + b5 + b7 + b9
            swap
            · omega
            by_cases c312 : b1 + b3 + b5 + b7 < 0 + a1
            swap
            · -- branch
              by_cases c313 : 0 < a3
              swap
              · omega
              by_cases c314 : 0 < b1
              swap
              · -- branch
                by_cases c315 : 0 < a3
                swap
                · omega
                by_cases c316 : 0 < b3
                swap
                · omega
                by_cases c317 : a1 < b1 + b3
                swap
                · omega
                by_cases c318 : b1 < a1 + a3
                swap
                · omega
                have f319 := pair_fact E (i := 3) (j := 3) rfl rfl c315 c316
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f319
                by_cases c320 : 0 < a3
                swap
                · omega
                by_cases c321 : 0 < b5
                swap
                · omega
                by_cases c322 : a1 < b1 + b3 + b5
                swap
                · omega
                by_cases c323 : b1 + b3 < a1 + a3
                swap
                · -- branch
                  by_cases c324 : 0 < a3
                  swap
                  · omega
                  by_cases c325 : 0 < b7
                  swap
                  · -- branch
                    by_cases c326 : 0 < a3
                    swap
                    · omega
                    by_cases c327 : 0 < b9
                    swap
                    · omega
                    by_cases c328 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c329 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · -- branch
                      by_cases c330 : 0 < a5
                      swap
                      · -- branch
                        by_cases c331 : 0 < a5
                        swap
                        · -- branch
                          by_cases c332 : 0 < a5
                          swap
                          · -- branch
                            by_cases c333 : 0 < a5
                            swap
                            · -- branch
                              by_cases c334 : 0 < a5
                              swap
                              · -- branch
                                by_cases c335 : 0 < a7
                                swap
                                · omega
                                by_cases c336 : 0 < b5
                                swap
                                · omega
                                by_cases c337 : a1 + a3 + a5 < b1 + b3 + b5
                                swap
                                · omega
                                by_cases c338 : b1 + b3 < a1 + a3 + a5 + a7
                                swap
                                · omega
                                have f339 := pair_fact E (i := 7) (j := 5) rfl rfl c335 c336
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f339
                                by_cases c340 : 0 < a7
                                swap
                                · omega
                                by_cases c341 : 0 < b9
                                swap
                                · omega
                                by_cases c342 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
                                swap
                                · omega
                                by_cases c343 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
                                swap
                                · omega
                                have f344 := pair_fact E (i := 7) (j := 9) rfl rfl c340 c341
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f344
                                omega
                              by_cases c345 : 0 < b9
                              swap
                              · omega
                              by_cases c346 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                              swap
                              · omega
                              by_cases c347 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                              swap
                              · omega
                              have f348 := pair_fact E (i := 5) (j := 9) rfl rfl c334 c345
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f348
                              omega
                            by_cases c349 : 0 < b7
                            swap
                            · omega
                            by_cases c350 : a1 + a3 < b1 + b3 + b5 + b7
                            swap
                            · omega
                            by_cases c351 : b1 + b3 + b5 < a1 + a3 + a5
                            swap
                            · omega
                            have f352 := pair_fact E (i := 5) (j := 7) rfl rfl c333 c349
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f352
                            omega
                          by_cases c353 : 0 < b5
                          swap
                          · omega
                          by_cases c354 : a1 + a3 < b1 + b3 + b5
                          swap
                          · omega
                          by_cases c355 : b1 + b3 < a1 + a3 + a5
                          swap
                          · omega
                          have f356 := pair_fact E (i := 5) (j := 5) rfl rfl c332 c353
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f356
                          omega
                        by_cases c357 : 0 < b3
                        swap
                        · omega
                        by_cases c358 : a1 + a3 < b1 + b3
                        swap
                        · omega
                        by_cases c359 : b1 < a1 + a3 + a5
                        swap
                        · omega
                        have f360 := pair_fact E (i := 5) (j := 3) rfl rfl c331 c357
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f360
                        omega
                      by_cases c361 : 0 < b1
                      swap
                      · omega
                      by_cases c362 : a1 + a3 < 0 + b1
                      swap
                      · omega
                      by_cases c363 : 0 < a1 + a3 + a5
                      swap
                      · omega
                      have f364 := pair_fact E (i := 5) (j := 1) rfl rfl c330 c361
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f364
                      omega
                    have f365 := pair_fact E (i := 3) (j := 9) rfl rfl c326 c327
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f365
                    omega
                  by_cases c366 : a1 < b1 + b3 + b5 + b7
                  swap
                  · omega
                  by_cases c367 : b1 + b3 + b5 < a1 + a3
                  swap
                  · omega
                  have f368 := pair_fact E (i := 3) (j := 7) rfl rfl c324 c325
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f368
                  omega
                have f369 := pair_fact E (i := 3) (j := 5) rfl rfl c320 c321
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f369
                omega
              by_cases c370 : a1 < 0 + b1
              swap
              · omega
              by_cases c371 : 0 < a1 + a3
              swap
              · omega
              have f372 := pair_fact E (i := 3) (j := 1) rfl rfl c313 c314
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f372
              omega
            have f373 := pair_fact E (i := 1) (j := 9) rfl rfl c309 c310
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f373
            omega
          have f374 := pair_fact E (i := 1) (j := 5) rfl rfl c305 c306
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f374
          omega
        by_cases c375 : b1 < a1 + a3 + a5 + a7
        swap
        · omega
        have f376 := pair_fact E (i := 7) (j := 3) rfl rfl c302 c303
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f376
        omega
      by_cases c377 : a1 + a3 + a5 < 0 + b1
      swap
      · omega
      by_cases c378 : 0 < a1 + a3 + a5 + a7
      swap
      · omega
      have f379 := pair_fact E (i := 7) (j := 1) rfl rfl c300 c301
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f379
      omega
    by_cases c380 : 0 < b1 + b3 + b5 + b7
    swap
    · omega
    by_cases c381 : b1 + b3 + b5 < 0 + a1
    swap
    · -- branch
      by_cases c382 : 0 < a1
      swap
      · omega
      by_cases c383 : 0 < b9
      swap
      · -- branch
        by_cases c384 : 0 < a9
        swap
        · omega
        by_cases c385 : 0 < b1
        swap
        · -- branch
          by_cases c386 : 0 < a9
          swap
          · omega
          by_cases c387 : 0 < b3
          swap
          · omega
          by_cases c388 : a1 + a3 + a5 + a7 < b1 + b3
          swap
          · -- branch
            by_cases c389 : 0 < a9
            swap
            · omega
            by_cases c390 : 0 < b7
            swap
            · omega
            by_cases c391 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7
            swap
            · omega
            by_cases c392 : b1 + b3 + b5 < a1 + a3 + a5 + a7 + a9
            swap
            · omega
            have f393 := pair_fact E (i := 9) (j := 7) rfl rfl c389 c390
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f393
            by_cases c394 : 0 < a9
            swap
            · omega
            by_cases c395 : 0 < b9
            swap
            · -- branch
              by_cases c396 : 0 < a1
              swap
              · omega
              by_cases c397 : 0 < b5
              swap
              · -- branch
                by_cases c398 : 0 < a5
                swap
                · omega
                by_cases c399 : 0 < b1
                swap
                · -- branch
                  by_cases c400 : 0 < a5
                  swap
                  · omega
                  by_cases c401 : 0 < b5
                  swap
                  · -- branch
                    by_cases c402 : 0 < a5
                    swap
                    · omega
                    by_cases c403 : 0 < b7
                    swap
                    · omega
                    by_cases c404 : a1 + a3 < b1 + b3 + b5 + b7
                    swap
                    · omega
                    by_cases c405 : b1 + b3 + b5 < a1 + a3 + a5
                    swap
                    · -- branch
                      by_cases c406 : 0 < a7
                      swap
                      · omega
                      by_cases c407 : 0 < b3
                      swap
                      · omega
                      by_cases c408 : a1 + a3 + a5 < b1 + b3
                      swap
                      · omega
                      by_cases c409 : b1 < a1 + a3 + a5 + a7
                      swap
                      · omega
                      have f410 := pair_fact E (i := 7) (j := 3) rfl rfl c406 c407
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f410
                      omega
                    have f411 := pair_fact E (i := 5) (j := 7) rfl rfl c402 c403
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f411
                    omega
                  by_cases c412 : a1 + a3 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c413 : b1 + b3 < a1 + a3 + a5
                  swap
                  · omega
                  have f414 := pair_fact E (i := 5) (j := 5) rfl rfl c400 c401
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f414
                  omega
                by_cases c415 : a1 + a3 < 0 + b1
                swap
                · omega
                by_cases c416 : 0 < a1 + a3 + a5
                swap
                · omega
                have f417 := pair_fact E (i := 5) (j := 1) rfl rfl c398 c399
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f417
                omega
              by_cases c418 : 0 < b1 + b3 + b5
              swap
              · omega
              by_cases c419 : b1 + b3 < 0 + a1
              swap
              · -- branch
                by_cases c420 : 0 < a9
                swap
                · omega
                by_cases c421 : 0 < b5
                swap
                · omega
                by_cases c422 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                swap
                · -- branch
                  by_cases c423 : 0 < a3
                  swap
                  · omega
                  by_cases c424 : 0 < b1
                  swap
                  · -- branch
                    by_cases c425 : 0 < a3
                    swap
                    · omega
                    by_cases c426 : 0 < b5
                    swap
                    · omega
                    by_cases c427 : a1 < b1 + b3 + b5
                    swap
                    · omega
                    by_cases c428 : b1 + b3 < a1 + a3
                    swap
                    · -- branch
                      by_cases c429 : 0 < a3
                      swap
                      · omega
                      by_cases c430 : 0 < b3
                      swap
                      · omega
                      by_cases c431 : a1 < b1 + b3
                      swap
                      · omega
                      by_cases c432 : b1 < a1 + a3
                      swap
                      · omega
                      have f433 := pair_fact E (i := 3) (j := 3) rfl rfl c429 c430
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f433
                      by_cases c434 : 0 < a3
                      swap
                      · omega
                      by_cases c435 : 0 < b7
                      swap
                      · omega
                      by_cases c436 : a1 < b1 + b3 + b5 + b7
                      swap
                      · omega
                      by_cases c437 : b1 + b3 + b5 < a1 + a3
                      swap
                      · -- branch
                        by_cases c438 : 0 < a3
                        swap
                        · omega
                        by_cases c439 : 0 < b9
                        swap
                        · -- branch
                          by_cases c440 : 0 < a7
                          swap
                          · omega
                          by_cases c441 : 0 < b1
                          swap
                          · -- branch
                            by_cases c442 : 0 < a7
                            swap
                            · omega
                            by_cases c443 : 0 < b3
                            swap
                            · omega
                            by_cases c444 : a1 + a3 + a5 < b1 + b3
                            swap
                            · -- branch
                              by_cases c445 : 0 < a7
                              swap
                              · omega
                              by_cases c446 : 0 < b5
                              swap
                              · omega
                              by_cases c447 : a1 + a3 + a5 < b1 + b3 + b5
                              swap
                              · -- branch
                                by_cases c448 : 0 < a5
                                swap
                                · omega
                                by_cases c449 : 0 < b5
                                swap
                                · omega
                                by_cases c450 : a1 + a3 < b1 + b3 + b5
                                swap
                                · omega
                                by_cases c451 : b1 + b3 < a1 + a3 + a5
                                swap
                                · omega
                                have f452 := pair_fact E (i := 5) (j := 5) rfl rfl c448 c449
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f452
                                omega
                              by_cases c453 : b1 + b3 < a1 + a3 + a5 + a7
                              swap
                              · omega
                              have f454 := pair_fact E (i := 7) (j := 5) rfl rfl c445 c446
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f454
                              omega
                            by_cases c455 : b1 < a1 + a3 + a5 + a7
                            swap
                            · omega
                            have f456 := pair_fact E (i := 7) (j := 3) rfl rfl c442 c443
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f456
                            omega
                          by_cases c457 : a1 + a3 + a5 < 0 + b1
                          swap
                          · omega
                          by_cases c458 : 0 < a1 + a3 + a5 + a7
                          swap
                          · omega
                          have f459 := pair_fact E (i := 7) (j := 1) rfl rfl c440 c441
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f459
                          omega
                        by_cases c460 : a1 < b1 + b3 + b5 + b7 + b9
                        swap
                        · omega
                        by_cases c461 : b1 + b3 + b5 + b7 < a1 + a3
                        swap
                        · omega
                        have f462 := pair_fact E (i := 3) (j := 9) rfl rfl c438 c439
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f462
                        omega
                      have f463 := pair_fact E (i := 3) (j := 7) rfl rfl c434 c435
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f463
                      omega
                    have f464 := pair_fact E (i := 3) (j := 5) rfl rfl c425 c426
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f464
                    omega
                  by_cases c465 : a1 < 0 + b1
                  swap
                  · omega
                  by_cases c466 : 0 < a1 + a3
                  swap
                  · omega
                  have f467 := pair_fact E (i := 3) (j := 1) rfl rfl c423 c424
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f467
                  omega
                by_cases c468 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                swap
                · omega
                have f469 := pair_fact E (i := 9) (j := 5) rfl rfl c420 c421
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f469
                omega
              have f470 := pair_fact E (i := 1) (j := 5) rfl rfl c396 c397
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f470
              omega
            by_cases c471 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
            swap
            · omega
            by_cases c472 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
            swap
            · omega
            have f473 := pair_fact E (i := 9) (j := 9) rfl rfl c394 c395
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f473
            omega
          by_cases c474 : b1 < a1 + a3 + a5 + a7 + a9
          swap
          · omega
          have f475 := pair_fact E (i := 9) (j := 3) rfl rfl c386 c387
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f475
          omega
        by_cases c476 : a1 + a3 + a5 + a7 < 0 + b1
        swap
        · omega
        by_cases c477 : 0 < a1 + a3 + a5 + a7 + a9
        swap
        · omega
        have f478 := pair_fact E (i := 9) (j := 1) rfl rfl c384 c385
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f478
        omega
      by_cases c479 : 0 < b1 + b3 + b5 + b7 + b9
      swap
      · omega
      by_cases c480 : b1 + b3 + b5 + b7 < 0 + a1
      swap
      · -- branch
        by_cases c481 : 0 < a3
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
          · omega
          by_cases c485 : b1 < a1 + a3 + a5 + a7
          swap
          · omega
          have f486 := pair_fact E (i := 7) (j := 3) rfl rfl c482 c483
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f486
          omega
        by_cases c487 : 0 < b1
        swap
        · -- branch
          by_cases c488 : 0 < a3
          swap
          · omega
          by_cases c489 : 0 < b7
          swap
          · omega
          by_cases c490 : a1 < b1 + b3 + b5 + b7
          swap
          · omega
          by_cases c491 : b1 + b3 + b5 < a1 + a3
          swap
          · -- branch
            by_cases c492 : 0 < a3
            swap
            · omega
            by_cases c493 : 0 < b3
            swap
            · omega
            by_cases c494 : a1 < b1 + b3
            swap
            · omega
            by_cases c495 : b1 < a1 + a3
            swap
            · omega
            have f496 := pair_fact E (i := 3) (j := 3) rfl rfl c492 c493
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f496
            by_cases c497 : 0 < a3
            swap
            · omega
            by_cases c498 : 0 < b9
            swap
            · omega
            by_cases c499 : a1 < b1 + b3 + b5 + b7 + b9
            swap
            · omega
            by_cases c500 : b1 + b3 + b5 + b7 < a1 + a3
            swap
            · -- branch
              by_cases c501 : 0 < a7
              swap
              · omega
              by_cases c502 : 0 < b1
              swap
              · -- branch
                by_cases c503 : 0 < a7
                swap
                · omega
                by_cases c504 : 0 < b3
                swap
                · omega
                by_cases c505 : a1 + a3 + a5 < b1 + b3
                swap
                · -- branch
                  by_cases c506 : 0 < a1
                  swap
                  · omega
                  by_cases c507 : 0 < b5
                  swap
                  · -- branch
                    by_cases c508 : 0 < a3
                    swap
                    · omega
                    by_cases c509 : 0 < b5
                    swap
                    · -- branch
                      by_cases c510 : 0 < a5
                      swap
                      · omega
                      by_cases c511 : 0 < b1
                      swap
                      · -- branch
                        by_cases c512 : 0 < a5
                        swap
                        · omega
                        by_cases c513 : 0 < b5
                        swap
                        · -- branch
                          by_cases c514 : 0 < a5
                          swap
                          · omega
                          by_cases c515 : 0 < b7
                          swap
                          · omega
                          by_cases c516 : a1 + a3 < b1 + b3 + b5 + b7
                          swap
                          · omega
                          by_cases c517 : b1 + b3 + b5 < a1 + a3 + a5
                          swap
                          · omega
                          have f518 := pair_fact E (i := 5) (j := 7) rfl rfl c514 c515
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f518
                          by_cases c519 : 0 < a5
                          swap
                          · omega
                          by_cases c520 : 0 < b3
                          swap
                          · omega
                          by_cases c521 : a1 + a3 < b1 + b3
                          swap
                          · -- branch
                            by_cases c522 : 0 < a5
                            swap
                            · omega
                            by_cases c523 : 0 < b9
                            swap
                            · omega
                            by_cases c524 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                            swap
                            · omega
                            by_cases c525 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                            swap
                            · -- branch
                              by_cases c526 : 0 < a7
                              swap
                              · omega
                              by_cases c527 : 0 < b5
                              swap
                              · -- branch
                                by_cases c528 : 0 < a7
                                swap
                                · omega
                                by_cases c529 : 0 < b9
                                swap
                                · omega
                                by_cases c530 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
                                swap
                                · omega
                                by_cases c531 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
                                swap
                                · -- branch
                                  by_cases c532 : 0 < a9
                                  swap
                                  · omega
                                  by_cases c533 : 0 < b7
                                  swap
                                  · omega
                                  by_cases c534 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7
                                  swap
                                  · omega
                                  by_cases c535 : b1 + b3 + b5 < a1 + a3 + a5 + a7 + a9
                                  swap
                                  · omega
                                  have f536 := pair_fact E (i := 9) (j := 7) rfl rfl c532 c533
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f536
                                  omega
                                have f537 := pair_fact E (i := 7) (j := 9) rfl rfl c528 c529
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f537
                                omega
                              by_cases c538 : a1 + a3 + a5 < b1 + b3 + b5
                              swap
                              · omega
                              by_cases c539 : b1 + b3 < a1 + a3 + a5 + a7
                              swap
                              · omega
                              have f540 := pair_fact E (i := 7) (j := 5) rfl rfl c526 c527
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f540
                              omega
                            have f541 := pair_fact E (i := 5) (j := 9) rfl rfl c522 c523
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f541
                            omega
                          by_cases c542 : b1 < a1 + a3 + a5
                          swap
                          · omega
                          have f543 := pair_fact E (i := 5) (j := 3) rfl rfl c519 c520
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f543
                          omega
                        by_cases c544 : a1 + a3 < b1 + b3 + b5
                        swap
                        · omega
                        by_cases c545 : b1 + b3 < a1 + a3 + a5
                        swap
                        · omega
                        have f546 := pair_fact E (i := 5) (j := 5) rfl rfl c512 c513
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f546
                        omega
                      by_cases c547 : a1 + a3 < 0 + b1
                      swap
                      · omega
                      by_cases c548 : 0 < a1 + a3 + a5
                      swap
                      · omega
                      have f549 := pair_fact E (i := 5) (j := 1) rfl rfl c510 c511
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f549
                      omega
                    by_cases c550 : a1 < b1 + b3 + b5
                    swap
                    · omega
                    by_cases c551 : b1 + b3 < a1 + a3
                    swap
                    · omega
                    have f552 := pair_fact E (i := 3) (j := 5) rfl rfl c508 c509
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f552
                    omega
                  by_cases c553 : 0 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c554 : b1 + b3 < 0 + a1
                  swap
                  · -- branch
                    by_cases c555 : 0 < a7
                    swap
                    · omega
                    by_cases c556 : 0 < b7
                    swap
                    · omega
                    by_cases c557 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                    swap
                    · omega
                    by_cases c558 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                    swap
                    · omega
                    have f559 := pair_fact E (i := 7) (j := 7) rfl rfl c555 c556
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f559
                    by_cases c560 : 0 < a3
                    swap
                    · omega
                    by_cases c561 : 0 < b5
                    swap
                    · omega
                    by_cases c562 : a1 < b1 + b3 + b5
                    swap
                    · omega
                    by_cases c563 : b1 + b3 < a1 + a3
                    swap
                    · -- branch
                      by_cases c564 : 0 < a7
                      swap
                      · omega
                      by_cases c565 : 0 < b9
                      swap
                      · omega
                      by_cases c566 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
                      swap
                      · omega
                      by_cases c567 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
                      swap
                      · -- branch
                        by_cases c568 : 0 < a9
                        swap
                        · omega
                        by_cases c569 : 0 < b7
                        swap
                        · omega
                        by_cases c570 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7
                        swap
                        · omega
                        by_cases c571 : b1 + b3 + b5 < a1 + a3 + a5 + a7 + a9
                        swap
                        · omega
                        have f572 := pair_fact E (i := 9) (j := 7) rfl rfl c568 c569
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f572
                        omega
                      have f573 := pair_fact E (i := 7) (j := 9) rfl rfl c564 c565
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f573
                      omega
                    have f574 := pair_fact E (i := 3) (j := 5) rfl rfl c560 c561
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f574
                    omega
                  have f575 := pair_fact E (i := 1) (j := 5) rfl rfl c506 c507
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f575
                  omega
                by_cases c576 : b1 < a1 + a3 + a5 + a7
                swap
                · omega
                have f577 := pair_fact E (i := 7) (j := 3) rfl rfl c503 c504
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f577
                omega
              by_cases c578 : a1 + a3 + a5 < 0 + b1
              swap
              · omega
              by_cases c579 : 0 < a1 + a3 + a5 + a7
              swap
              · omega
              have f580 := pair_fact E (i := 7) (j := 1) rfl rfl c501 c502
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f580
              omega
            have f581 := pair_fact E (i := 3) (j := 9) rfl rfl c497 c498
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f581
            omega
          have f582 := pair_fact E (i := 3) (j := 7) rfl rfl c488 c489
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f582
          omega
        by_cases c583 : a1 < 0 + b1
        swap
        · omega
        by_cases c584 : 0 < a1 + a3
        swap
        · omega
        have f585 := pair_fact E (i := 3) (j := 1) rfl rfl c481 c487
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f585
        omega
      have f586 := pair_fact E (i := 1) (j := 9) rfl rfl c382 c383
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f586
      omega
    have f587 := pair_fact E (i := 1) (j := 7) rfl rfl c298 c299
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f587
    omega
  by_cases c588 : 0 < 0 + b1
  swap
  · omega
  by_cases c589 : 0 < 0 + a1
  swap
  · omega
  have f590 := pair_fact E (i := 1) (j := 1) rfl rfl c1 c287
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f590
  by_cases c591 : 0 < a1
  swap
  · omega
  by_cases c592 : 0 < b7
  swap
  · -- branch
    by_cases c593 : 0 < a7
    swap
    · omega
    by_cases c594 : 0 < b1
    swap
    · omega
    by_cases c595 : a1 + a3 + a5 < 0 + b1
    swap
    · -- branch
      by_cases c596 : 0 < a7
      swap
      · omega
      by_cases c597 : 0 < b3
      swap
      · omega
      by_cases c598 : a1 + a3 + a5 < b1 + b3
      swap
      · -- branch
        by_cases c599 : 0 < a1
        swap
        · omega
        by_cases c600 : 0 < b5
        swap
        · omega
        by_cases c601 : 0 < b1 + b3 + b5
        swap
        · omega
        by_cases c602 : b1 + b3 < 0 + a1
        swap
        · -- branch
          by_cases c603 : 0 < a1
          swap
          · omega
          by_cases c604 : 0 < b9
          swap
          · omega
          by_cases c605 : 0 < b1 + b3 + b5 + b7 + b9
          swap
          · omega
          by_cases c606 : b1 + b3 + b5 + b7 < 0 + a1
          swap
          · -- branch
            by_cases c607 : 0 < a3
            swap
            · omega
            by_cases c608 : 0 < b3
            swap
            · omega
            by_cases c609 : a1 < b1 + b3
            swap
            · omega
            by_cases c610 : b1 < a1 + a3
            swap
            · omega
            have f611 := pair_fact E (i := 3) (j := 3) rfl rfl c607 c608
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f611
            by_cases c612 : 0 < a1
            swap
            · omega
            by_cases c613 : 0 < b3
            swap
            · omega
            by_cases c614 : 0 < b1 + b3
            swap
            · omega
            by_cases c615 : b1 < 0 + a1
            swap
            · -- branch
              by_cases c616 : 0 < a3
              swap
              · omega
              by_cases c617 : 0 < b1
              swap
              · omega
              by_cases c618 : a1 < 0 + b1
              swap
              · omega
              by_cases c619 : 0 < a1 + a3
              swap
              · omega
              have f620 := pair_fact E (i := 3) (j := 1) rfl rfl c616 c617
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f620
              omega
            have f621 := pair_fact E (i := 1) (j := 3) rfl rfl c612 c613
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f621
            omega
          have f622 := pair_fact E (i := 1) (j := 9) rfl rfl c603 c604
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f622
          omega
        have f623 := pair_fact E (i := 1) (j := 5) rfl rfl c599 c600
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f623
        omega
      by_cases c624 : b1 < a1 + a3 + a5 + a7
      swap
      · omega
      have f625 := pair_fact E (i := 7) (j := 3) rfl rfl c596 c597
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f625
      omega
    by_cases c626 : 0 < a1 + a3 + a5 + a7
    swap
    · omega
    have f627 := pair_fact E (i := 7) (j := 1) rfl rfl c593 c594
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f627
    omega
  by_cases c628 : 0 < b1 + b3 + b5 + b7
  swap
  · omega
  by_cases c629 : b1 + b3 + b5 < 0 + a1
  swap
  · -- branch
    by_cases c630 : 0 < a1
    swap
    · omega
    by_cases c631 : 0 < b9
    swap
    · -- branch
      by_cases c632 : 0 < a9
      swap
      · omega
      by_cases c633 : 0 < b1
      swap
      · omega
      by_cases c634 : a1 + a3 + a5 + a7 < 0 + b1
      swap
      · -- branch
        by_cases c635 : 0 < a9
        swap
        · omega
        by_cases c636 : 0 < b3
        swap
        · omega
        by_cases c637 : a1 + a3 + a5 + a7 < b1 + b3
        swap
        · -- branch
          by_cases c638 : 0 < a3
          swap
          · omega
          by_cases c639 : 0 < b3
          swap
          · omega
          by_cases c640 : a1 < b1 + b3
          swap
          · omega
          by_cases c641 : b1 < a1 + a3
          swap
          · omega
          have f642 := pair_fact E (i := 3) (j := 3) rfl rfl c638 c639
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f642
          by_cases c643 : 0 < a1
          swap
          · omega
          by_cases c644 : 0 < b3
          swap
          · omega
          by_cases c645 : 0 < b1 + b3
          swap
          · omega
          by_cases c646 : b1 < 0 + a1
          swap
          · -- branch
            by_cases c647 : 0 < a3
            swap
            · omega
            by_cases c648 : 0 < b1
            swap
            · omega
            by_cases c649 : a1 < 0 + b1
            swap
            · omega
            by_cases c650 : 0 < a1 + a3
            swap
            · omega
            have f651 := pair_fact E (i := 3) (j := 1) rfl rfl c647 c648
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f651
            omega
          have f652 := pair_fact E (i := 1) (j := 3) rfl rfl c643 c644
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f652
          omega
        by_cases c653 : b1 < a1 + a3 + a5 + a7 + a9
        swap
        · omega
        have f654 := pair_fact E (i := 9) (j := 3) rfl rfl c635 c636
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f654
        omega
      by_cases c655 : 0 < a1 + a3 + a5 + a7 + a9
      swap
      · omega
      have f656 := pair_fact E (i := 9) (j := 1) rfl rfl c632 c633
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f656
      omega
    by_cases c657 : 0 < b1 + b3 + b5 + b7 + b9
    swap
    · omega
    by_cases c658 : b1 + b3 + b5 + b7 < 0 + a1
    swap
    · -- branch
      by_cases c659 : 0 < a3
      swap
      · -- branch
        by_cases c660 : 0 < a7
        swap
        · omega
        by_cases c661 : 0 < b3
        swap
        · omega
        by_cases c662 : a1 + a3 + a5 < b1 + b3
        swap
        · omega
        by_cases c663 : b1 < a1 + a3 + a5 + a7
        swap
        · omega
        have f664 := pair_fact E (i := 7) (j := 3) rfl rfl c660 c661
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f664
        omega
      by_cases c665 : 0 < b7
      swap
      · omega
      by_cases c666 : a1 < b1 + b3 + b5 + b7
      swap
      · omega
      by_cases c667 : b1 + b3 + b5 < a1 + a3
      swap
      · -- branch
        by_cases c668 : 0 < a3
        swap
        · omega
        by_cases c669 : 0 < b9
        swap
        · omega
        by_cases c670 : a1 < b1 + b3 + b5 + b7 + b9
        swap
        · omega
        by_cases c671 : b1 + b3 + b5 + b7 < a1 + a3
        swap
        · -- branch
          by_cases c672 : 0 < a7
          swap
          · omega
          by_cases c673 : 0 < b1
          swap
          · omega
          by_cases c674 : a1 + a3 + a5 < 0 + b1
          swap
          · -- branch
            by_cases c675 : 0 < a7
            swap
            · omega
            by_cases c676 : 0 < b3
            swap
            · omega
            by_cases c677 : a1 + a3 + a5 < b1 + b3
            swap
            · -- branch
              by_cases c678 : 0 < a3
              swap
              · omega
              by_cases c679 : 0 < b3
              swap
              · omega
              by_cases c680 : a1 < b1 + b3
              swap
              · omega
              by_cases c681 : b1 < a1 + a3
              swap
              · omega
              have f682 := pair_fact E (i := 3) (j := 3) rfl rfl c678 c679
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f682
              by_cases c683 : 0 < a1
              swap
              · omega
              by_cases c684 : 0 < b3
              swap
              · omega
              by_cases c685 : 0 < b1 + b3
              swap
              · omega
              by_cases c686 : b1 < 0 + a1
              swap
              · -- branch
                by_cases c687 : 0 < a3
                swap
                · omega
                by_cases c688 : 0 < b1
                swap
                · omega
                by_cases c689 : a1 < 0 + b1
                swap
                · omega
                by_cases c690 : 0 < a1 + a3
                swap
                · omega
                have f691 := pair_fact E (i := 3) (j := 1) rfl rfl c687 c688
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f691
                omega
              have f692 := pair_fact E (i := 1) (j := 3) rfl rfl c683 c684
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f692
              omega
            by_cases c693 : b1 < a1 + a3 + a5 + a7
            swap
            · omega
            have f694 := pair_fact E (i := 7) (j := 3) rfl rfl c675 c676
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f694
            omega
          by_cases c695 : 0 < a1 + a3 + a5 + a7
          swap
          · omega
          have f696 := pair_fact E (i := 7) (j := 1) rfl rfl c672 c673
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f696
          omega
        have f697 := pair_fact E (i := 3) (j := 9) rfl rfl c668 c669
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f697
        omega
      have f698 := pair_fact E (i := 3) (j := 7) rfl rfl c659 c665
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f698
      omega
    have f699 := pair_fact E (i := 1) (j := 9) rfl rfl c630 c631
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f699
    omega
  have f700 := pair_fact E (i := 1) (j := 7) rfl rfl c591 c592
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f700
  omega

end Blocks
