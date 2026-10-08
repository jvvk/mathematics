import LeanProofs.ShuffleBlocks.Basic

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Blocks

set_option maxHeartbeats 0 in
/-- Cut inside run 7 of `V`: no splitting of this rotation gives two equal copies. -/
theorem V_cut07 (L l m v k a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9 a10 b10 : Nat)
    (hl : 1 ≤ l) (hm : m = 2 * v + 1) (hL : 9 * l ≤ L) (hk : k ≤ m)
    (e0 : a0 + b0 = (m - k))
    (e1 : a1 + b1 = l)
    (e2 : a2 + b2 = 3 * m)
    (e3 : a3 + b3 = L)
    (e4 : a4 + b4 = m)
    (e5 : a5 + b5 = 5 * l)
    (e6 : a6 + b6 = 2 * m)
    (e7 : a7 + b7 = L)
    (e8 : a8 + b8 = m)
    (e9 : a9 + b9 = 2 * l)
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
                by_cases c8 : 0 < a6
                swap
                · omega
                by_cases c9 : 0 < b2
                swap
                · omega
                by_cases c10 : a0 + a2 + a4 < b0 + b2
                swap
                · omega
                by_cases c11 : b0 < a0 + a2 + a4 + a6
                swap
                · omega
                have f12 := pair_fact E (i := 6) (j := 2) rfl rfl c8 c9
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f12
                omega
              by_cases c13 : 0 < b0
              swap
              · -- branch
                by_cases c14 : 0 < a2
                swap
                · omega
                by_cases c15 : 0 < b2
                swap
                · -- branch
                  by_cases c16 : 0 < a2
                  swap
                  · omega
                  by_cases c17 : 0 < b6
                  swap
                  · omega
                  by_cases c18 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c19 : b0 + b2 + b4 < a0 + a2
                  swap
                  · omega
                  have f20 := pair_fact E (i := 2) (j := 6) rfl rfl c16 c17
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f20
                  omega
                by_cases c21 : a0 < b0 + b2
                swap
                · omega
                by_cases c22 : b0 < a0 + a2
                swap
                · omega
                have f23 := pair_fact E (i := 2) (j := 2) rfl rfl c14 c15
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f23
                by_cases c24 : 0 < a2
                swap
                · omega
                by_cases c25 : 0 < b6
                swap
                · -- branch
                  by_cases c26 : 0 < a6
                  swap
                  · omega
                  by_cases c27 : 0 < b0
                  swap
                  · -- branch
                    by_cases c28 : 0 < a6
                    swap
                    · omega
                    by_cases c29 : 0 < b2
                    swap
                    · omega
                    by_cases c30 : a0 + a2 + a4 < b0 + b2
                    swap
                    · -- branch
                      by_cases c31 : 0 < a2
                      swap
                      · omega
                      by_cases c32 : 0 < b8
                      swap
                      · omega
                      by_cases c33 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c34 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · -- branch
                        by_cases c35 : 0 < a2
                        swap
                        · omega
                        by_cases c36 : 0 < b10
                        swap
                        · omega
                        by_cases c37 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c38 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                        swap
                        · -- branch
                          by_cases c39 : 0 < a6
                          swap
                          · omega
                          by_cases c40 : 0 < b6
                          swap
                          · -- branch
                            by_cases c41 : 0 < a6
                            swap
                            · omega
                            by_cases c42 : 0 < b8
                            swap
                            · omega
                            by_cases c43 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c44 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f45 := pair_fact E (i := 6) (j := 8) rfl rfl c41 c42
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f45
                            by_cases c46 : 0 < a6
                            swap
                            · omega
                            by_cases c47 : 0 < b10
                            swap
                            · omega
                            by_cases c48 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c49 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f50 := pair_fact E (i := 6) (j := 10) rfl rfl c46 c47
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f50
                            omega
                          by_cases c51 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c52 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f53 := pair_fact E (i := 6) (j := 6) rfl rfl c39 c40
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f53
                          omega
                        have f54 := pair_fact E (i := 2) (j := 10) rfl rfl c35 c36
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f54
                        omega
                      have f55 := pair_fact E (i := 2) (j := 8) rfl rfl c31 c32
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f55
                      omega
                    by_cases c56 : b0 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f57 := pair_fact E (i := 6) (j := 2) rfl rfl c28 c29
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f57
                    omega
                  by_cases c58 : a0 + a2 + a4 < 0 + b0
                  swap
                  · omega
                  by_cases c59 : 0 < a0 + a2 + a4 + a6
                  swap
                  · omega
                  have f60 := pair_fact E (i := 6) (j := 0) rfl rfl c26 c27
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f60
                  omega
                by_cases c61 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c62 : b0 + b2 + b4 < a0 + a2
                swap
                · -- branch
                  by_cases c63 : 0 < a2
                  swap
                  · omega
                  by_cases c64 : 0 < b8
                  swap
                  · -- branch
                    by_cases c65 : 0 < a8
                    swap
                    · omega
                    by_cases c66 : 0 < b0
                    swap
                    · -- branch
                      by_cases c67 : 0 < a8
                      swap
                      · omega
                      by_cases c68 : 0 < b2
                      swap
                      · omega
                      by_cases c69 : a0 + a2 + a4 + a6 < b0 + b2
                      swap
                      · -- branch
                        by_cases c70 : 0 < a8
                        swap
                        · omega
                        by_cases c71 : 0 < b8
                        swap
                        · -- branch
                          by_cases c72 : 0 < a2
                          swap
                          · omega
                          by_cases c73 : 0 < b10
                          swap
                          · -- branch
                            by_cases c74 : 0 < a8
                            swap
                            · omega
                            by_cases c75 : 0 < b10
                            swap
                            · -- branch
                              by_cases c76 : 0 < a10
                              swap
                              · omega
                              by_cases c77 : 0 < b0
                              swap
                              · -- branch
                                by_cases c78 : 0 < a10
                                swap
                                · omega
                                by_cases c79 : 0 < b2
                                swap
                                · omega
                                by_cases c80 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                                swap
                                · -- branch
                                  by_cases c81 : 0 < a10
                                  swap
                                  · omega
                                  by_cases c82 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c83 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c84 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                  swap
                                  · omega
                                  have f85 := pair_fact E (i := 10) (j := 6) rfl rfl c81 c82
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f85
                                  by_cases c86 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c87 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c88 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c89 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · -- branch
                                    by_cases c90 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c91 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c92 : a0 + a2 + a4 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c93 : b0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f94 := pair_fact E (i := 6) (j := 2) rfl rfl c90 c91
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f94
                                    omega
                                  have f95 := pair_fact E (i := 8) (j := 6) rfl rfl c86 c87
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f95
                                  omega
                                by_cases c96 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f97 := pair_fact E (i := 10) (j := 2) rfl rfl c78 c79
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f97
                                omega
                              by_cases c98 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                              swap
                              · omega
                              by_cases c99 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                              swap
                              · omega
                              have f100 := pair_fact E (i := 10) (j := 0) rfl rfl c76 c77
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f100
                              omega
                            by_cases c101 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c102 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f103 := pair_fact E (i := 8) (j := 10) rfl rfl c74 c75
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f103
                            omega
                          by_cases c104 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c105 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · -- branch
                            by_cases c106 : 0 < a4
                            swap
                            · -- branch
                              by_cases c107 : 0 < a4
                              swap
                              · -- branch
                                by_cases c108 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c109 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c110 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c111 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c112 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c113 : 0 < b0
                                        swap
                                        · -- branch
                                          by_cases c114 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c115 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c116 : a0 + a2 + a4 < b0 + b2
                                          swap
                                          · -- branch
                                            by_cases c117 : 0 < a2
                                            swap
                                            · omega
                                            by_cases c118 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c119 : a0 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c120 : b0 + b2 < a0 + a2
                                            swap
                                            · omega
                                            have f121 := pair_fact E (i := 2) (j := 4) rfl rfl c117 c118
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f121
                                            by_cases c122 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c123 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c124 : a0 + a2 + a4 < b0 + b2 + b4
                                            swap
                                            · -- branch
                                              by_cases c125 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c126 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c127 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c128 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f129 := pair_fact E (i := 6) (j := 6) rfl rfl c125 c126
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f129
                                              omega
                                            by_cases c130 : b0 + b2 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f131 := pair_fact E (i := 6) (j := 4) rfl rfl c122 c123
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f131
                                            omega
                                          by_cases c132 : b0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f133 := pair_fact E (i := 6) (j := 2) rfl rfl c114 c115
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f133
                                          omega
                                        by_cases c134 : a0 + a2 + a4 < 0 + b0
                                        swap
                                        · omega
                                        by_cases c135 : 0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f136 := pair_fact E (i := 6) (j := 0) rfl rfl c112 c113
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f136
                                        omega
                                      by_cases c137 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c138 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c139 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f140 := pair_fact E (i := 4) (j := 10) rfl rfl c111 c137
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f140
                                      omega
                                    by_cases c141 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c142 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c143 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f144 := pair_fact E (i := 4) (j := 8) rfl rfl c110 c141
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f144
                                    omega
                                  by_cases c145 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c146 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c147 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f148 := pair_fact E (i := 4) (j := 6) rfl rfl c109 c145
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f148
                                  omega
                                by_cases c149 : 0 < b4
                                swap
                                · omega
                                by_cases c150 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c151 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f152 := pair_fact E (i := 4) (j := 4) rfl rfl c108 c149
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f152
                                omega
                              by_cases c153 : 0 < b2
                              swap
                              · omega
                              by_cases c154 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c155 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f156 := pair_fact E (i := 4) (j := 2) rfl rfl c107 c153
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f156
                              omega
                            by_cases c157 : 0 < b0
                            swap
                            · -- branch
                              by_cases c158 : 0 < a4
                              swap
                              · omega
                              by_cases c159 : 0 < b8
                              swap
                              · -- branch
                                by_cases c160 : 0 < a4
                                swap
                                · omega
                                by_cases c161 : 0 < b10
                                swap
                                · omega
                                by_cases c162 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c163 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c164 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c165 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c166 : a0 + a2 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c167 : 0 < a2
                                    swap
                                    · omega
                                    by_cases c168 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c169 : a0 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c170 : b0 + b2 < a0 + a2
                                    swap
                                    · omega
                                    have f171 := pair_fact E (i := 2) (j := 4) rfl rfl c167 c168
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f171
                                    by_cases c172 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c173 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c174 : a0 + a2 < b0 + b2 + b4
                                    swap
                                    · -- branch
                                      by_cases c175 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c176 : 0 < b6
                                      swap
                                      · omega
                                      by_cases c177 : a0 + a2 < b0 + b2 + b4 + b6
                                      swap
                                      · omega
                                      by_cases c178 : b0 + b2 + b4 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f179 := pair_fact E (i := 4) (j := 6) rfl rfl c175 c176
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f179
                                      omega
                                    by_cases c180 : b0 + b2 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f181 := pair_fact E (i := 4) (j := 4) rfl rfl c172 c173
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f181
                                    omega
                                  by_cases c182 : b0 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f183 := pair_fact E (i := 4) (j := 2) rfl rfl c164 c165
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f183
                                  by_cases c184 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c185 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c186 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c187 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c188 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c189 : 0 < b0
                                    swap
                                    · -- branch
                                      by_cases c190 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c191 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c192 : a0 + a2 + a4 < b0 + b2
                                      swap
                                      · -- branch
                                        by_cases c193 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c194 : 0 < b6
                                        swap
                                        · omega
                                        by_cases c195 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                        swap
                                        · omega
                                        by_cases c196 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                        swap
                                        · -- branch
                                          by_cases c197 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c198 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c199 : a0 + a2 + a4 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c200 : b0 + b2 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f201 := pair_fact E (i := 6) (j := 4) rfl rfl c197 c198
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f201
                                          omega
                                        have f202 := pair_fact E (i := 6) (j := 6) rfl rfl c193 c194
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f202
                                        omega
                                      by_cases c203 : b0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f204 := pair_fact E (i := 6) (j := 2) rfl rfl c190 c191
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f204
                                      omega
                                    by_cases c205 : a0 + a2 + a4 < 0 + b0
                                    swap
                                    · omega
                                    by_cases c206 : 0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f207 := pair_fact E (i := 6) (j := 0) rfl rfl c188 c189
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f207
                                    omega
                                  have f208 := pair_fact E (i := 4) (j := 6) rfl rfl c184 c185
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f208
                                  omega
                                have f209 := pair_fact E (i := 4) (j := 10) rfl rfl c160 c161
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f209
                                omega
                              by_cases c210 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c211 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · omega
                              have f212 := pair_fact E (i := 4) (j := 8) rfl rfl c158 c159
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f212
                              omega
                            by_cases c213 : a0 + a2 < 0 + b0
                            swap
                            · omega
                            by_cases c214 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f215 := pair_fact E (i := 4) (j := 0) rfl rfl c106 c157
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f215
                            omega
                          have f216 := pair_fact E (i := 2) (j := 10) rfl rfl c72 c73
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f216
                          omega
                        by_cases c217 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c218 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f219 := pair_fact E (i := 8) (j := 8) rfl rfl c70 c71
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f219
                        omega
                      by_cases c220 : b0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f221 := pair_fact E (i := 8) (j := 2) rfl rfl c67 c68
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f221
                      omega
                    by_cases c222 : a0 + a2 + a4 + a6 < 0 + b0
                    swap
                    · omega
                    by_cases c223 : 0 < a0 + a2 + a4 + a6 + a8
                    swap
                    · omega
                    have f224 := pair_fact E (i := 8) (j := 0) rfl rfl c65 c66
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f224
                    omega
                  by_cases c225 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c226 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · -- branch
                    by_cases c227 : 0 < a2
                    swap
                    · omega
                    by_cases c228 : 0 < b10
                    swap
                    · -- branch
                      by_cases c229 : 0 < a10
                      swap
                      · omega
                      by_cases c230 : 0 < b0
                      swap
                      · -- branch
                        by_cases c231 : 0 < a10
                        swap
                        · omega
                        by_cases c232 : 0 < b2
                        swap
                        · omega
                        by_cases c233 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                        swap
                        · -- branch
                          by_cases c234 : 0 < a10
                          swap
                          · omega
                          by_cases c235 : 0 < b8
                          swap
                          · omega
                          by_cases c236 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c237 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                          swap
                          · omega
                          have f238 := pair_fact E (i := 10) (j := 8) rfl rfl c234 c235
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f238
                          by_cases c239 : 0 < a10
                          swap
                          · omega
                          by_cases c240 : 0 < b10
                          swap
                          · -- branch
                            by_cases c241 : 0 < a4
                            swap
                            · -- branch
                              by_cases c242 : 0 < a4
                              swap
                              · -- branch
                                by_cases c243 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c244 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c245 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c246 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c247 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c248 : 0 < b0
                                        swap
                                        · -- branch
                                          by_cases c249 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c250 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c251 : a0 + a2 + a4 < b0 + b2
                                          swap
                                          · -- branch
                                            by_cases c252 : 0 < a2
                                            swap
                                            · omega
                                            by_cases c253 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c254 : a0 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c255 : b0 + b2 < a0 + a2
                                            swap
                                            · omega
                                            have f256 := pair_fact E (i := 2) (j := 4) rfl rfl c252 c253
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f256
                                            by_cases c257 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c258 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c259 : a0 + a2 + a4 < b0 + b2 + b4
                                            swap
                                            · -- branch
                                              by_cases c260 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c261 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c262 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c263 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f264 := pair_fact E (i := 6) (j := 6) rfl rfl c260 c261
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f264
                                              omega
                                            by_cases c265 : b0 + b2 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f266 := pair_fact E (i := 6) (j := 4) rfl rfl c257 c258
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f266
                                            omega
                                          by_cases c267 : b0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f268 := pair_fact E (i := 6) (j := 2) rfl rfl c249 c250
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f268
                                          omega
                                        by_cases c269 : a0 + a2 + a4 < 0 + b0
                                        swap
                                        · omega
                                        by_cases c270 : 0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f271 := pair_fact E (i := 6) (j := 0) rfl rfl c247 c248
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f271
                                        omega
                                      by_cases c272 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c273 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c274 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f275 := pair_fact E (i := 4) (j := 10) rfl rfl c246 c272
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f275
                                      omega
                                    by_cases c276 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c277 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c278 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f279 := pair_fact E (i := 4) (j := 8) rfl rfl c245 c276
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f279
                                    omega
                                  by_cases c280 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c281 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c282 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f283 := pair_fact E (i := 4) (j := 6) rfl rfl c244 c280
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f283
                                  omega
                                by_cases c284 : 0 < b4
                                swap
                                · omega
                                by_cases c285 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c286 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f287 := pair_fact E (i := 4) (j := 4) rfl rfl c243 c284
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f287
                                omega
                              by_cases c288 : 0 < b2
                              swap
                              · omega
                              by_cases c289 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c290 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f291 := pair_fact E (i := 4) (j := 2) rfl rfl c242 c288
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f291
                              omega
                            by_cases c292 : 0 < b0
                            swap
                            · -- branch
                              by_cases c293 : 0 < a4
                              swap
                              · omega
                              by_cases c294 : 0 < b8
                              swap
                              · omega
                              by_cases c295 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c296 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c297 : 0 < a4
                                swap
                                · omega
                                by_cases c298 : 0 < b10
                                swap
                                · -- branch
                                  by_cases c299 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c300 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c301 : a0 + a2 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c302 : 0 < a2
                                    swap
                                    · omega
                                    by_cases c303 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c304 : a0 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c305 : b0 + b2 < a0 + a2
                                    swap
                                    · omega
                                    have f306 := pair_fact E (i := 2) (j := 4) rfl rfl c302 c303
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f306
                                    by_cases c307 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c308 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c309 : a0 + a2 < b0 + b2 + b4
                                    swap
                                    · -- branch
                                      by_cases c310 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c311 : 0 < b6
                                      swap
                                      · omega
                                      by_cases c312 : a0 + a2 < b0 + b2 + b4 + b6
                                      swap
                                      · omega
                                      by_cases c313 : b0 + b2 + b4 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f314 := pair_fact E (i := 4) (j := 6) rfl rfl c310 c311
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f314
                                      omega
                                    by_cases c315 : b0 + b2 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f316 := pair_fact E (i := 4) (j := 4) rfl rfl c307 c308
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f316
                                    omega
                                  by_cases c317 : b0 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f318 := pair_fact E (i := 4) (j := 2) rfl rfl c299 c300
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f318
                                  by_cases c319 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c320 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c321 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c322 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c323 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c324 : 0 < b0
                                    swap
                                    · -- branch
                                      by_cases c325 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c326 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c327 : a0 + a2 + a4 < b0 + b2
                                      swap
                                      · -- branch
                                        by_cases c328 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c329 : 0 < b6
                                        swap
                                        · omega
                                        by_cases c330 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                        swap
                                        · omega
                                        by_cases c331 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                        swap
                                        · -- branch
                                          by_cases c332 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c333 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c334 : a0 + a2 + a4 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c335 : b0 + b2 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f336 := pair_fact E (i := 6) (j := 4) rfl rfl c332 c333
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f336
                                          omega
                                        have f337 := pair_fact E (i := 6) (j := 6) rfl rfl c328 c329
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f337
                                        omega
                                      by_cases c338 : b0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f339 := pair_fact E (i := 6) (j := 2) rfl rfl c325 c326
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f339
                                      omega
                                    by_cases c340 : a0 + a2 + a4 < 0 + b0
                                    swap
                                    · omega
                                    by_cases c341 : 0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f342 := pair_fact E (i := 6) (j := 0) rfl rfl c323 c324
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f342
                                    omega
                                  have f343 := pair_fact E (i := 4) (j := 6) rfl rfl c319 c320
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f343
                                  omega
                                by_cases c344 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c345 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                swap
                                · omega
                                have f346 := pair_fact E (i := 4) (j := 10) rfl rfl c297 c298
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f346
                                omega
                              have f347 := pair_fact E (i := 4) (j := 8) rfl rfl c293 c294
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f347
                              omega
                            by_cases c348 : a0 + a2 < 0 + b0
                            swap
                            · omega
                            by_cases c349 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f350 := pair_fact E (i := 4) (j := 0) rfl rfl c241 c292
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f350
                            omega
                          by_cases c351 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c352 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8 + a10
                          swap
                          · omega
                          have f353 := pair_fact E (i := 10) (j := 10) rfl rfl c239 c240
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f353
                          omega
                        by_cases c354 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                        swap
                        · omega
                        have f355 := pair_fact E (i := 10) (j := 2) rfl rfl c231 c232
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f355
                        omega
                      by_cases c356 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                      swap
                      · omega
                      by_cases c357 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f358 := pair_fact E (i := 10) (j := 0) rfl rfl c229 c230
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f358
                      omega
                    by_cases c359 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c360 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · -- branch
                      by_cases c361 : 0 < a4
                      swap
                      · -- branch
                        by_cases c362 : 0 < a4
                        swap
                        · -- branch
                          by_cases c363 : 0 < a4
                          swap
                          · -- branch
                            by_cases c364 : 0 < a4
                            swap
                            · -- branch
                              by_cases c365 : 0 < a4
                              swap
                              · -- branch
                                by_cases c366 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c367 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c368 : 0 < b0
                                  swap
                                  · -- branch
                                    by_cases c369 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c370 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c371 : a0 + a2 + a4 < b0 + b2
                                    swap
                                    · -- branch
                                      by_cases c372 : 0 < a2
                                      swap
                                      · omega
                                      by_cases c373 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c374 : a0 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c375 : b0 + b2 < a0 + a2
                                      swap
                                      · omega
                                      have f376 := pair_fact E (i := 2) (j := 4) rfl rfl c372 c373
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f376
                                      by_cases c377 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c378 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c379 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · -- branch
                                        by_cases c380 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c381 : 0 < b6
                                        swap
                                        · omega
                                        by_cases c382 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                        swap
                                        · omega
                                        by_cases c383 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f384 := pair_fact E (i := 6) (j := 6) rfl rfl c380 c381
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f384
                                        omega
                                      by_cases c385 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f386 := pair_fact E (i := 6) (j := 4) rfl rfl c377 c378
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f386
                                      omega
                                    by_cases c387 : b0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f388 := pair_fact E (i := 6) (j := 2) rfl rfl c369 c370
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f388
                                    omega
                                  by_cases c389 : a0 + a2 + a4 < 0 + b0
                                  swap
                                  · omega
                                  by_cases c390 : 0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f391 := pair_fact E (i := 6) (j := 0) rfl rfl c367 c368
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f391
                                  omega
                                by_cases c392 : 0 < b10
                                swap
                                · omega
                                by_cases c393 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c394 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                swap
                                · omega
                                have f395 := pair_fact E (i := 4) (j := 10) rfl rfl c366 c392
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f395
                                omega
                              by_cases c396 : 0 < b8
                              swap
                              · omega
                              by_cases c397 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c398 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · omega
                              have f399 := pair_fact E (i := 4) (j := 8) rfl rfl c365 c396
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f399
                              omega
                            by_cases c400 : 0 < b6
                            swap
                            · omega
                            by_cases c401 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c402 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · omega
                            have f403 := pair_fact E (i := 4) (j := 6) rfl rfl c364 c400
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f403
                            omega
                          by_cases c404 : 0 < b4
                          swap
                          · omega
                          by_cases c405 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c406 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f407 := pair_fact E (i := 4) (j := 4) rfl rfl c363 c404
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f407
                          omega
                        by_cases c408 : 0 < b2
                        swap
                        · omega
                        by_cases c409 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c410 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f411 := pair_fact E (i := 4) (j := 2) rfl rfl c362 c408
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f411
                        omega
                      by_cases c412 : 0 < b0
                      swap
                      · -- branch
                        by_cases c413 : 0 < a4
                        swap
                        · omega
                        by_cases c414 : 0 < b8
                        swap
                        · omega
                        by_cases c415 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c416 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                        swap
                        · -- branch
                          by_cases c417 : 0 < a4
                          swap
                          · omega
                          by_cases c418 : 0 < b10
                          swap
                          · omega
                          by_cases c419 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c420 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                          swap
                          · -- branch
                            by_cases c421 : 0 < a4
                            swap
                            · omega
                            by_cases c422 : 0 < b2
                            swap
                            · omega
                            by_cases c423 : a0 + a2 < b0 + b2
                            swap
                            · -- branch
                              by_cases c424 : 0 < a2
                              swap
                              · omega
                              by_cases c425 : 0 < b4
                              swap
                              · omega
                              by_cases c426 : a0 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c427 : b0 + b2 < a0 + a2
                              swap
                              · omega
                              have f428 := pair_fact E (i := 2) (j := 4) rfl rfl c424 c425
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f428
                              by_cases c429 : 0 < a4
                              swap
                              · omega
                              by_cases c430 : 0 < b4
                              swap
                              · omega
                              by_cases c431 : a0 + a2 < b0 + b2 + b4
                              swap
                              · -- branch
                                by_cases c432 : 0 < a4
                                swap
                                · omega
                                by_cases c433 : 0 < b6
                                swap
                                · omega
                                by_cases c434 : a0 + a2 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c435 : b0 + b2 + b4 < a0 + a2 + a4
                                swap
                                · omega
                                have f436 := pair_fact E (i := 4) (j := 6) rfl rfl c432 c433
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f436
                                omega
                              by_cases c437 : b0 + b2 < a0 + a2 + a4
                              swap
                              · omega
                              have f438 := pair_fact E (i := 4) (j := 4) rfl rfl c429 c430
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f438
                              omega
                            by_cases c439 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f440 := pair_fact E (i := 4) (j := 2) rfl rfl c421 c422
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f440
                            by_cases c441 : 0 < a4
                            swap
                            · omega
                            by_cases c442 : 0 < b6
                            swap
                            · omega
                            by_cases c443 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c444 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c445 : 0 < a6
                              swap
                              · omega
                              by_cases c446 : 0 < b0
                              swap
                              · -- branch
                                by_cases c447 : 0 < a6
                                swap
                                · omega
                                by_cases c448 : 0 < b2
                                swap
                                · omega
                                by_cases c449 : a0 + a2 + a4 < b0 + b2
                                swap
                                · -- branch
                                  by_cases c450 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c451 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c452 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c453 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                  swap
                                  · -- branch
                                    by_cases c454 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c455 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c456 : a0 + a2 + a4 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c457 : b0 + b2 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f458 := pair_fact E (i := 6) (j := 4) rfl rfl c454 c455
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f458
                                    omega
                                  have f459 := pair_fact E (i := 6) (j := 6) rfl rfl c450 c451
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f459
                                  omega
                                by_cases c460 : b0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f461 := pair_fact E (i := 6) (j := 2) rfl rfl c447 c448
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f461
                                omega
                              by_cases c462 : a0 + a2 + a4 < 0 + b0
                              swap
                              · omega
                              by_cases c463 : 0 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f464 := pair_fact E (i := 6) (j := 0) rfl rfl c445 c446
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f464
                              omega
                            have f465 := pair_fact E (i := 4) (j := 6) rfl rfl c441 c442
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f465
                            omega
                          have f466 := pair_fact E (i := 4) (j := 10) rfl rfl c417 c418
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f466
                          omega
                        have f467 := pair_fact E (i := 4) (j := 8) rfl rfl c413 c414
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f467
                        omega
                      by_cases c468 : a0 + a2 < 0 + b0
                      swap
                      · omega
                      by_cases c469 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f470 := pair_fact E (i := 4) (j := 0) rfl rfl c361 c412
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f470
                      omega
                    have f471 := pair_fact E (i := 2) (j := 10) rfl rfl c227 c228
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f471
                    omega
                  have f472 := pair_fact E (i := 2) (j := 8) rfl rfl c63 c64
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f472
                  omega
                have f473 := pair_fact E (i := 2) (j := 6) rfl rfl c24 c25
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f473
                omega
              by_cases c474 : a0 < 0 + b0
              swap
              · omega
              by_cases c475 : 0 < a0 + a2
              swap
              · omega
              have f476 := pair_fact E (i := 2) (j := 0) rfl rfl c7 c13
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f476
              by_cases c477 : 0 < a2
              swap
              · omega
              by_cases c478 : 0 < b2
              swap
              · -- branch
                by_cases c479 : 0 < a2
                swap
                · omega
                by_cases c480 : 0 < b6
                swap
                · omega
                by_cases c481 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c482 : b0 + b2 + b4 < a0 + a2
                swap
                · omega
                have f483 := pair_fact E (i := 2) (j := 6) rfl rfl c479 c480
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f483
                omega
              by_cases c484 : a0 < b0 + b2
              swap
              · omega
              by_cases c485 : b0 < a0 + a2
              swap
              · -- branch
                by_cases c486 : 0 < a6
                swap
                · omega
                by_cases c487 : 0 < b2
                swap
                · omega
                by_cases c488 : a0 + a2 + a4 < b0 + b2
                swap
                · omega
                by_cases c489 : b0 < a0 + a2 + a4 + a6
                swap
                · omega
                have f490 := pair_fact E (i := 6) (j := 2) rfl rfl c486 c487
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f490
                omega
              have f491 := pair_fact E (i := 2) (j := 2) rfl rfl c477 c478
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f491
              omega
            by_cases c492 : 0 < b10
            swap
            · omega
            by_cases c493 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c494 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · omega
            have f495 := pair_fact E (i := 0) (j := 10) rfl rfl c6 c492
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f495
            omega
          by_cases c496 : 0 < b8
          swap
          · omega
          by_cases c497 : 0 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c498 : b0 + b2 + b4 + b6 < 0 + a0
          swap
          · omega
          have f499 := pair_fact E (i := 0) (j := 8) rfl rfl c5 c496
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f499
          omega
        by_cases c500 : 0 < b6
        swap
        · omega
        by_cases c501 : 0 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c502 : b0 + b2 + b4 < 0 + a0
        swap
        · omega
        have f503 := pair_fact E (i := 0) (j := 6) rfl rfl c4 c500
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f503
        omega
      by_cases c504 : 0 < b4
      swap
      · omega
      by_cases c505 : 0 < b0 + b2 + b4
      swap
      · omega
      by_cases c506 : b0 + b2 < 0 + a0
      swap
      · omega
      have f507 := pair_fact E (i := 0) (j := 4) rfl rfl c3 c504
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f507
      omega
    by_cases c508 : 0 < b2
    swap
    · omega
    by_cases c509 : 0 < b0 + b2
    swap
    · omega
    by_cases c510 : b0 < 0 + a0
    swap
    · omega
    have f511 := pair_fact E (i := 0) (j := 2) rfl rfl c2 c508
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f511
    omega
  by_cases c512 : 0 < b0
  swap
  · -- branch
    by_cases c513 : 0 < a0
    swap
    · omega
    by_cases c514 : 0 < b2
    swap
    · -- branch
      by_cases c515 : 0 < a2
      swap
      · omega
      by_cases c516 : 0 < b6
      swap
      · omega
      by_cases c517 : a0 < b0 + b2 + b4 + b6
      swap
      · omega
      by_cases c518 : b0 + b2 + b4 < a0 + a2
      swap
      · omega
      have f519 := pair_fact E (i := 2) (j := 6) rfl rfl c515 c516
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f519
      omega
    by_cases c520 : 0 < b0 + b2
    swap
    · omega
    by_cases c521 : b0 < 0 + a0
    swap
    · omega
    have f522 := pair_fact E (i := 0) (j := 2) rfl rfl c513 c514
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f522
    by_cases c523 : 0 < a0
    swap
    · omega
    by_cases c524 : 0 < b6
    swap
    · -- branch
      by_cases c525 : 0 < a2
      swap
      · -- branch
        by_cases c526 : 0 < a6
        swap
        · omega
        by_cases c527 : 0 < b2
        swap
        · omega
        by_cases c528 : a0 + a2 + a4 < b0 + b2
        swap
        · omega
        by_cases c529 : b0 < a0 + a2 + a4 + a6
        swap
        · omega
        have f530 := pair_fact E (i := 6) (j := 2) rfl rfl c526 c527
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f530
        omega
      by_cases c531 : 0 < b2
      swap
      · omega
      by_cases c532 : a0 < b0 + b2
      swap
      · omega
      by_cases c533 : b0 < a0 + a2
      swap
      · omega
      have f534 := pair_fact E (i := 2) (j := 2) rfl rfl c525 c531
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f534
      omega
    by_cases c535 : 0 < b0 + b2 + b4 + b6
    swap
    · omega
    by_cases c536 : b0 + b2 + b4 < 0 + a0
    swap
    · -- branch
      by_cases c537 : 0 < a0
      swap
      · omega
      by_cases c538 : 0 < b8
      swap
      · -- branch
        by_cases c539 : 0 < a8
        swap
        · omega
        by_cases c540 : 0 < b0
        swap
        · -- branch
          by_cases c541 : 0 < a8
          swap
          · omega
          by_cases c542 : 0 < b2
          swap
          · omega
          by_cases c543 : a0 + a2 + a4 + a6 < b0 + b2
          swap
          · -- branch
            by_cases c544 : 0 < a8
            swap
            · omega
            by_cases c545 : 0 < b8
            swap
            · -- branch
              by_cases c546 : 0 < a0
              swap
              · omega
              by_cases c547 : 0 < b4
              swap
              · -- branch
                by_cases c548 : 0 < a2
                swap
                · -- branch
                  by_cases c549 : 0 < a4
                  swap
                  · omega
                  by_cases c550 : 0 < b2
                  swap
                  · omega
                  by_cases c551 : a0 + a2 < b0 + b2
                  swap
                  · omega
                  by_cases c552 : b0 < a0 + a2 + a4
                  swap
                  · omega
                  have f553 := pair_fact E (i := 4) (j := 2) rfl rfl c549 c550
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f553
                  omega
                by_cases c554 : 0 < b2
                swap
                · omega
                by_cases c555 : a0 < b0 + b2
                swap
                · omega
                by_cases c556 : b0 < a0 + a2
                swap
                · omega
                have f557 := pair_fact E (i := 2) (j := 2) rfl rfl c548 c554
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f557
                omega
              by_cases c558 : 0 < b0 + b2 + b4
              swap
              · omega
              by_cases c559 : b0 + b2 < 0 + a0
              swap
              · -- branch
                by_cases c560 : 0 < a8
                swap
                · omega
                by_cases c561 : 0 < b4
                swap
                · omega
                by_cases c562 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                swap
                · -- branch
                  by_cases c563 : 0 < a2
                  swap
                  · omega
                  by_cases c564 : 0 < b0
                  swap
                  · -- branch
                    by_cases c565 : 0 < a2
                    swap
                    · omega
                    by_cases c566 : 0 < b2
                    swap
                    · omega
                    by_cases c567 : a0 < b0 + b2
                    swap
                    · -- branch
                      by_cases c568 : 0 < a2
                      swap
                      · omega
                      by_cases c569 : 0 < b6
                      swap
                      · omega
                      by_cases c570 : a0 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c571 : b0 + b2 + b4 < a0 + a2
                      swap
                      · omega
                      have f572 := pair_fact E (i := 2) (j := 6) rfl rfl c568 c569
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f572
                      omega
                    by_cases c573 : b0 < a0 + a2
                    swap
                    · omega
                    have f574 := pair_fact E (i := 2) (j := 2) rfl rfl c565 c566
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f574
                    omega
                  by_cases c575 : a0 < 0 + b0
                  swap
                  · omega
                  by_cases c576 : 0 < a0 + a2
                  swap
                  · omega
                  have f577 := pair_fact E (i := 2) (j := 0) rfl rfl c563 c564
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f577
                  omega
                by_cases c578 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                swap
                · omega
                have f579 := pair_fact E (i := 8) (j := 4) rfl rfl c560 c561
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f579
                omega
              have f580 := pair_fact E (i := 0) (j := 4) rfl rfl c546 c547
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f580
              omega
            by_cases c581 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
            swap
            · omega
            by_cases c582 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
            swap
            · omega
            have f583 := pair_fact E (i := 8) (j := 8) rfl rfl c544 c545
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f583
            omega
          by_cases c584 : b0 < a0 + a2 + a4 + a6 + a8
          swap
          · omega
          have f585 := pair_fact E (i := 8) (j := 2) rfl rfl c541 c542
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f585
          omega
        by_cases c586 : a0 + a2 + a4 + a6 < 0 + b0
        swap
        · omega
        by_cases c587 : 0 < a0 + a2 + a4 + a6 + a8
        swap
        · omega
        have f588 := pair_fact E (i := 8) (j := 0) rfl rfl c539 c540
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f588
        omega
      by_cases c589 : 0 < b0 + b2 + b4 + b6 + b8
      swap
      · omega
      by_cases c590 : b0 + b2 + b4 + b6 < 0 + a0
      swap
      · -- branch
        by_cases c591 : 0 < a0
        swap
        · omega
        by_cases c592 : 0 < b10
        swap
        · -- branch
          by_cases c593 : 0 < a2
          swap
          · -- branch
            by_cases c594 : 0 < a4
            swap
            · omega
            by_cases c595 : 0 < b2
            swap
            · omega
            by_cases c596 : a0 + a2 < b0 + b2
            swap
            · omega
            by_cases c597 : b0 < a0 + a2 + a4
            swap
            · omega
            have f598 := pair_fact E (i := 4) (j := 2) rfl rfl c594 c595
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f598
            omega
          by_cases c599 : 0 < b0
          swap
          · -- branch
            by_cases c600 : 0 < a2
            swap
            · omega
            by_cases c601 : 0 < b2
            swap
            · omega
            by_cases c602 : a0 < b0 + b2
            swap
            · -- branch
              by_cases c603 : 0 < a2
              swap
              · omega
              by_cases c604 : 0 < b6
              swap
              · omega
              by_cases c605 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c606 : b0 + b2 + b4 < a0 + a2
              swap
              · omega
              have f607 := pair_fact E (i := 2) (j := 6) rfl rfl c603 c604
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f607
              omega
            by_cases c608 : b0 < a0 + a2
            swap
            · omega
            have f609 := pair_fact E (i := 2) (j := 2) rfl rfl c600 c601
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f609
            omega
          by_cases c610 : a0 < 0 + b0
          swap
          · omega
          by_cases c611 : 0 < a0 + a2
          swap
          · omega
          have f612 := pair_fact E (i := 2) (j := 0) rfl rfl c593 c599
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f612
          omega
        by_cases c613 : 0 < b0 + b2 + b4 + b6 + b8 + b10
        swap
        · omega
        by_cases c614 : b0 + b2 + b4 + b6 + b8 < 0 + a0
        swap
        · -- branch
          by_cases c615 : 0 < a2
          swap
          · -- branch
            by_cases c616 : 0 < a4
            swap
            · omega
            by_cases c617 : 0 < b2
            swap
            · omega
            by_cases c618 : a0 + a2 < b0 + b2
            swap
            · omega
            by_cases c619 : b0 < a0 + a2 + a4
            swap
            · omega
            have f620 := pair_fact E (i := 4) (j := 2) rfl rfl c616 c617
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f620
            omega
          by_cases c621 : 0 < b0
          swap
          · -- branch
            by_cases c622 : 0 < a2
            swap
            · omega
            by_cases c623 : 0 < b2
            swap
            · omega
            by_cases c624 : a0 < b0 + b2
            swap
            · -- branch
              by_cases c625 : 0 < a2
              swap
              · omega
              by_cases c626 : 0 < b6
              swap
              · omega
              by_cases c627 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c628 : b0 + b2 + b4 < a0 + a2
              swap
              · omega
              have f629 := pair_fact E (i := 2) (j := 6) rfl rfl c625 c626
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f629
              omega
            by_cases c630 : b0 < a0 + a2
            swap
            · omega
            have f631 := pair_fact E (i := 2) (j := 2) rfl rfl c622 c623
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f631
            omega
          by_cases c632 : a0 < 0 + b0
          swap
          · omega
          by_cases c633 : 0 < a0 + a2
          swap
          · omega
          have f634 := pair_fact E (i := 2) (j := 0) rfl rfl c615 c621
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f634
          omega
        have f635 := pair_fact E (i := 0) (j := 10) rfl rfl c591 c592
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f635
        omega
      have f636 := pair_fact E (i := 0) (j := 8) rfl rfl c537 c538
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f636
      omega
    have f637 := pair_fact E (i := 0) (j := 6) rfl rfl c523 c524
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f637
    omega
  by_cases c638 : 0 < 0 + b0
  swap
  · omega
  by_cases c639 : 0 < 0 + a0
  swap
  · omega
  have f640 := pair_fact E (i := 0) (j := 0) rfl rfl c1 c512
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f640
  by_cases c641 : 0 < a0
  swap
  · omega
  by_cases c642 : 0 < b6
  swap
  · -- branch
    by_cases c643 : 0 < a6
    swap
    · omega
    by_cases c644 : 0 < b0
    swap
    · omega
    by_cases c645 : a0 + a2 + a4 < 0 + b0
    swap
    · -- branch
      by_cases c646 : 0 < a6
      swap
      · omega
      by_cases c647 : 0 < b2
      swap
      · omega
      by_cases c648 : a0 + a2 + a4 < b0 + b2
      swap
      · -- branch
        by_cases c649 : 0 < a0
        swap
        · omega
        by_cases c650 : 0 < b4
        swap
        · omega
        by_cases c651 : 0 < b0 + b2 + b4
        swap
        · omega
        by_cases c652 : b0 + b2 < 0 + a0
        swap
        · -- branch
          by_cases c653 : 0 < a0
          swap
          · omega
          by_cases c654 : 0 < b8
          swap
          · omega
          by_cases c655 : 0 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c656 : b0 + b2 + b4 + b6 < 0 + a0
          swap
          · -- branch
            by_cases c657 : 0 < a2
            swap
            · omega
            by_cases c658 : 0 < b2
            swap
            · omega
            by_cases c659 : a0 < b0 + b2
            swap
            · omega
            by_cases c660 : b0 < a0 + a2
            swap
            · omega
            have f661 := pair_fact E (i := 2) (j := 2) rfl rfl c657 c658
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f661
            by_cases c662 : 0 < a0
            swap
            · omega
            by_cases c663 : 0 < b2
            swap
            · omega
            by_cases c664 : 0 < b0 + b2
            swap
            · omega
            by_cases c665 : b0 < 0 + a0
            swap
            · -- branch
              by_cases c666 : 0 < a2
              swap
              · omega
              by_cases c667 : 0 < b0
              swap
              · omega
              by_cases c668 : a0 < 0 + b0
              swap
              · -- branch
                by_cases c669 : 0 < a0
                swap
                · omega
                by_cases c670 : 0 < b10
                swap
                · omega
                by_cases c671 : 0 < b0 + b2 + b4 + b6 + b8 + b10
                swap
                · omega
                by_cases c672 : b0 + b2 + b4 + b6 + b8 < 0 + a0
                swap
                · -- branch
                  by_cases c673 : 0 < a2
                  swap
                  · omega
                  by_cases c674 : 0 < b6
                  swap
                  · -- branch
                    by_cases c675 : 0 < a2
                    swap
                    · omega
                    by_cases c676 : 0 < b8
                    swap
                    · omega
                    by_cases c677 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c678 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · -- branch
                      by_cases c679 : 0 < a2
                      swap
                      · omega
                      by_cases c680 : 0 < b10
                      swap
                      · omega
                      by_cases c681 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                      swap
                      · omega
                      by_cases c682 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                      swap
                      · -- branch
                        by_cases c683 : 0 < a6
                        swap
                        · omega
                        by_cases c684 : 0 < b4
                        swap
                        · omega
                        by_cases c685 : a0 + a2 + a4 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c686 : b0 + b2 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f687 := pair_fact E (i := 6) (j := 4) rfl rfl c683 c684
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f687
                        by_cases c688 : 0 < a6
                        swap
                        · omega
                        by_cases c689 : 0 < b8
                        swap
                        · omega
                        by_cases c690 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c691 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f692 := pair_fact E (i := 6) (j := 8) rfl rfl c688 c689
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f692
                        omega
                      have f693 := pair_fact E (i := 2) (j := 10) rfl rfl c679 c680
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f693
                      omega
                    have f694 := pair_fact E (i := 2) (j := 8) rfl rfl c675 c676
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f694
                    omega
                  by_cases c695 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c696 : b0 + b2 + b4 < a0 + a2
                  swap
                  · omega
                  have f697 := pair_fact E (i := 2) (j := 6) rfl rfl c673 c674
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f697
                  omega
                have f698 := pair_fact E (i := 0) (j := 10) rfl rfl c669 c670
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f698
                omega
              by_cases c699 : 0 < a0 + a2
              swap
              · omega
              have f700 := pair_fact E (i := 2) (j := 0) rfl rfl c666 c667
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f700
              omega
            have f701 := pair_fact E (i := 0) (j := 2) rfl rfl c662 c663
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f701
            omega
          have f702 := pair_fact E (i := 0) (j := 8) rfl rfl c653 c654
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f702
          omega
        have f703 := pair_fact E (i := 0) (j := 4) rfl rfl c649 c650
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f703
        omega
      by_cases c704 : b0 < a0 + a2 + a4 + a6
      swap
      · omega
      have f705 := pair_fact E (i := 6) (j := 2) rfl rfl c646 c647
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f705
      omega
    by_cases c706 : 0 < a0 + a2 + a4 + a6
    swap
    · omega
    have f707 := pair_fact E (i := 6) (j := 0) rfl rfl c643 c644
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f707
    omega
  by_cases c708 : 0 < b0 + b2 + b4 + b6
  swap
  · omega
  by_cases c709 : b0 + b2 + b4 < 0 + a0
  swap
  · -- branch
    by_cases c710 : 0 < a0
    swap
    · omega
    by_cases c711 : 0 < b8
    swap
    · -- branch
      by_cases c712 : 0 < a8
      swap
      · omega
      by_cases c713 : 0 < b0
      swap
      · omega
      by_cases c714 : a0 + a2 + a4 + a6 < 0 + b0
      swap
      · -- branch
        by_cases c715 : 0 < a8
        swap
        · omega
        by_cases c716 : 0 < b2
        swap
        · omega
        by_cases c717 : a0 + a2 + a4 + a6 < b0 + b2
        swap
        · -- branch
          by_cases c718 : 0 < a2
          swap
          · omega
          by_cases c719 : 0 < b2
          swap
          · omega
          by_cases c720 : a0 < b0 + b2
          swap
          · omega
          by_cases c721 : b0 < a0 + a2
          swap
          · omega
          have f722 := pair_fact E (i := 2) (j := 2) rfl rfl c718 c719
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f722
          by_cases c723 : 0 < a0
          swap
          · omega
          by_cases c724 : 0 < b2
          swap
          · omega
          by_cases c725 : 0 < b0 + b2
          swap
          · omega
          by_cases c726 : b0 < 0 + a0
          swap
          · -- branch
            by_cases c727 : 0 < a2
            swap
            · omega
            by_cases c728 : 0 < b0
            swap
            · omega
            by_cases c729 : a0 < 0 + b0
            swap
            · -- branch
              by_cases c730 : 0 < a2
              swap
              · omega
              by_cases c731 : 0 < b6
              swap
              · omega
              by_cases c732 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c733 : b0 + b2 + b4 < a0 + a2
              swap
              · -- branch
                by_cases c734 : 0 < a2
                swap
                · omega
                by_cases c735 : 0 < b8
                swap
                · -- branch
                  by_cases c736 : 0 < a8
                  swap
                  · omega
                  by_cases c737 : 0 < b8
                  swap
                  · -- branch
                    by_cases c738 : 0 < a0
                    swap
                    · omega
                    by_cases c739 : 0 < b4
                    swap
                    · -- branch
                      by_cases c740 : 0 < a2
                      swap
                      · omega
                      by_cases c741 : 0 < b4
                      swap
                      · -- branch
                        by_cases c742 : 0 < a4
                        swap
                        · omega
                        by_cases c743 : 0 < b0
                        swap
                        · omega
                        by_cases c744 : a0 + a2 < 0 + b0
                        swap
                        · -- branch
                          by_cases c745 : 0 < a4
                          swap
                          · omega
                          by_cases c746 : 0 < b2
                          swap
                          · omega
                          by_cases c747 : a0 + a2 < b0 + b2
                          swap
                          · omega
                          by_cases c748 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f749 := pair_fact E (i := 4) (j := 2) rfl rfl c745 c746
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f749
                          by_cases c750 : 0 < a4
                          swap
                          · omega
                          by_cases c751 : 0 < b4
                          swap
                          · -- branch
                            by_cases c752 : 0 < a4
                            swap
                            · omega
                            by_cases c753 : 0 < b6
                            swap
                            · omega
                            by_cases c754 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c755 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c756 : 0 < a4
                              swap
                              · omega
                              by_cases c757 : 0 < b8
                              swap
                              · -- branch
                                by_cases c758 : 0 < a6
                                swap
                                · omega
                                by_cases c759 : 0 < b0
                                swap
                                · omega
                                by_cases c760 : a0 + a2 + a4 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c761 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c762 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c763 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c764 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c765 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c766 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c767 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f768 := pair_fact E (i := 6) (j := 6) rfl rfl c764 c765
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f768
                                    omega
                                  by_cases c769 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f770 := pair_fact E (i := 6) (j := 2) rfl rfl c761 c762
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f770
                                  omega
                                by_cases c771 : 0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f772 := pair_fact E (i := 6) (j := 0) rfl rfl c758 c759
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f772
                                omega
                              by_cases c773 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c774 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · omega
                              have f775 := pair_fact E (i := 4) (j := 8) rfl rfl c756 c757
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f775
                              omega
                            have f776 := pair_fact E (i := 4) (j := 6) rfl rfl c752 c753
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f776
                            omega
                          by_cases c777 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c778 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f779 := pair_fact E (i := 4) (j := 4) rfl rfl c750 c751
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f779
                          omega
                        by_cases c780 : 0 < a0 + a2 + a4
                        swap
                        · omega
                        have f781 := pair_fact E (i := 4) (j := 0) rfl rfl c742 c743
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f781
                        omega
                      by_cases c782 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c783 : b0 + b2 < a0 + a2
                      swap
                      · omega
                      have f784 := pair_fact E (i := 2) (j := 4) rfl rfl c740 c741
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f784
                      omega
                    by_cases c785 : 0 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c786 : b0 + b2 < 0 + a0
                    swap
                    · -- branch
                      by_cases c787 : 0 < a8
                      swap
                      · omega
                      by_cases c788 : 0 < b4
                      swap
                      · omega
                      by_cases c789 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                      swap
                      · -- branch
                        by_cases c790 : 0 < a8
                        swap
                        · omega
                        by_cases c791 : 0 < b6
                        swap
                        · omega
                        by_cases c792 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c793 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f794 := pair_fact E (i := 8) (j := 6) rfl rfl c790 c791
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f794
                        by_cases c795 : 0 < a2
                        swap
                        · omega
                        by_cases c796 : 0 < b4
                        swap
                        · omega
                        by_cases c797 : a0 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c798 : b0 + b2 < a0 + a2
                        swap
                        · -- branch
                          by_cases c799 : 0 < a0
                          swap
                          · omega
                          by_cases c800 : 0 < b10
                          swap
                          · -- branch
                            by_cases c801 : 0 < a10
                            swap
                            · omega
                            by_cases c802 : 0 < b6
                            swap
                            · omega
                            by_cases c803 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c804 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f805 := pair_fact E (i := 10) (j := 6) rfl rfl c801 c802
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f805
                            omega
                          by_cases c806 : 0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c807 : b0 + b2 + b4 + b6 + b8 < 0 + a0
                          swap
                          · -- branch
                            by_cases c808 : 0 < a2
                            swap
                            · omega
                            by_cases c809 : 0 < b10
                            swap
                            · omega
                            by_cases c810 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c811 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                            swap
                            · -- branch
                              by_cases c812 : 0 < a8
                              swap
                              · omega
                              by_cases c813 : 0 < b10
                              swap
                              · omega
                              by_cases c814 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c815 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                              swap
                              · -- branch
                                by_cases c816 : 0 < a10
                                swap
                                · omega
                                by_cases c817 : 0 < b6
                                swap
                                · omega
                                by_cases c818 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c819 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f820 := pair_fact E (i := 10) (j := 6) rfl rfl c816 c817
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f820
                                omega
                              have f821 := pair_fact E (i := 8) (j := 10) rfl rfl c812 c813
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f821
                              omega
                            have f822 := pair_fact E (i := 2) (j := 10) rfl rfl c808 c809
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f822
                            omega
                          have f823 := pair_fact E (i := 0) (j := 10) rfl rfl c799 c800
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f823
                          omega
                        have f824 := pair_fact E (i := 2) (j := 4) rfl rfl c795 c796
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f824
                        omega
                      by_cases c825 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f826 := pair_fact E (i := 8) (j := 4) rfl rfl c787 c788
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f826
                      omega
                    have f827 := pair_fact E (i := 0) (j := 4) rfl rfl c738 c739
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f827
                    omega
                  by_cases c828 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c829 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                  swap
                  · omega
                  have f830 := pair_fact E (i := 8) (j := 8) rfl rfl c736 c737
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f830
                  omega
                by_cases c831 : a0 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c832 : b0 + b2 + b4 + b6 < a0 + a2
                swap
                · omega
                have f833 := pair_fact E (i := 2) (j := 8) rfl rfl c734 c735
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f833
                omega
              have f834 := pair_fact E (i := 2) (j := 6) rfl rfl c730 c731
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f834
              omega
            by_cases c835 : 0 < a0 + a2
            swap
            · omega
            have f836 := pair_fact E (i := 2) (j := 0) rfl rfl c727 c728
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f836
            omega
          have f837 := pair_fact E (i := 0) (j := 2) rfl rfl c723 c724
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f837
          omega
        by_cases c838 : b0 < a0 + a2 + a4 + a6 + a8
        swap
        · omega
        have f839 := pair_fact E (i := 8) (j := 2) rfl rfl c715 c716
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f839
        omega
      by_cases c840 : 0 < a0 + a2 + a4 + a6 + a8
      swap
      · omega
      have f841 := pair_fact E (i := 8) (j := 0) rfl rfl c712 c713
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f841
      omega
    by_cases c842 : 0 < b0 + b2 + b4 + b6 + b8
    swap
    · omega
    by_cases c843 : b0 + b2 + b4 + b6 < 0 + a0
    swap
    · -- branch
      by_cases c844 : 0 < a0
      swap
      · omega
      by_cases c845 : 0 < b10
      swap
      · -- branch
        by_cases c846 : 0 < a2
        swap
        · -- branch
          by_cases c847 : 0 < a6
          swap
          · omega
          by_cases c848 : 0 < b2
          swap
          · omega
          by_cases c849 : a0 + a2 + a4 < b0 + b2
          swap
          · omega
          by_cases c850 : b0 < a0 + a2 + a4 + a6
          swap
          · omega
          have f851 := pair_fact E (i := 6) (j := 2) rfl rfl c847 c848
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f851
          omega
        by_cases c852 : 0 < b6
        swap
        · omega
        by_cases c853 : a0 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c854 : b0 + b2 + b4 < a0 + a2
        swap
        · -- branch
          by_cases c855 : 0 < a2
          swap
          · omega
          by_cases c856 : 0 < b8
          swap
          · omega
          by_cases c857 : a0 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c858 : b0 + b2 + b4 + b6 < a0 + a2
          swap
          · -- branch
            by_cases c859 : 0 < a2
            swap
            · omega
            by_cases c860 : 0 < b10
            swap
            · -- branch
              by_cases c861 : 0 < a0
              swap
              · omega
              by_cases c862 : 0 < b2
              swap
              · omega
              by_cases c863 : 0 < b0 + b2
              swap
              · omega
              by_cases c864 : b0 < 0 + a0
              swap
              · -- branch
                by_cases c865 : 0 < a0
                swap
                · omega
                by_cases c866 : 0 < b4
                swap
                · -- branch
                  by_cases c867 : 0 < a2
                  swap
                  · omega
                  by_cases c868 : 0 < b4
                  swap
                  · -- branch
                    by_cases c869 : 0 < a4
                    swap
                    · omega
                    by_cases c870 : 0 < b4
                    swap
                    · -- branch
                      by_cases c871 : 0 < a4
                      swap
                      · omega
                      by_cases c872 : 0 < b8
                      swap
                      · omega
                      by_cases c873 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c874 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                      swap
                      · -- branch
                        by_cases c875 : 0 < a4
                        swap
                        · omega
                        by_cases c876 : 0 < b10
                        swap
                        · -- branch
                          by_cases c877 : 0 < a2
                          swap
                          · omega
                          by_cases c878 : 0 < b0
                          swap
                          · omega
                          by_cases c879 : a0 < 0 + b0
                          swap
                          · -- branch
                            by_cases c880 : 0 < a2
                            swap
                            · omega
                            by_cases c881 : 0 < b2
                            swap
                            · omega
                            by_cases c882 : a0 < b0 + b2
                            swap
                            · omega
                            by_cases c883 : b0 < a0 + a2
                            swap
                            · omega
                            have f884 := pair_fact E (i := 2) (j := 2) rfl rfl c880 c881
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f884
                            by_cases c885 : 0 < a4
                            swap
                            · omega
                            by_cases c886 : 0 < b0
                            swap
                            · omega
                            by_cases c887 : a0 + a2 < 0 + b0
                            swap
                            · -- branch
                              by_cases c888 : 0 < a4
                              swap
                              · omega
                              by_cases c889 : 0 < b2
                              swap
                              · omega
                              by_cases c890 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c891 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f892 := pair_fact E (i := 4) (j := 2) rfl rfl c888 c889
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f892
                              by_cases c893 : 0 < a4
                              swap
                              · omega
                              by_cases c894 : 0 < b6
                              swap
                              · omega
                              by_cases c895 : a0 + a2 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c896 : b0 + b2 + b4 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c897 : 0 < a6
                                swap
                                · omega
                                by_cases c898 : 0 < b0
                                swap
                                · omega
                                by_cases c899 : a0 + a2 + a4 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c900 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c901 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c902 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c903 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c904 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c905 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c906 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f907 := pair_fact E (i := 6) (j := 6) rfl rfl c903 c904
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f907
                                    omega
                                  by_cases c908 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f909 := pair_fact E (i := 6) (j := 2) rfl rfl c900 c901
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f909
                                  omega
                                by_cases c910 : 0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f911 := pair_fact E (i := 6) (j := 0) rfl rfl c897 c898
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f911
                                omega
                              have f912 := pair_fact E (i := 4) (j := 6) rfl rfl c893 c894
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f912
                              omega
                            by_cases c913 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f914 := pair_fact E (i := 4) (j := 0) rfl rfl c885 c886
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f914
                            omega
                          by_cases c915 : 0 < a0 + a2
                          swap
                          · omega
                          have f916 := pair_fact E (i := 2) (j := 0) rfl rfl c877 c878
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f916
                          by_cases c917 : 0 < a2
                          swap
                          · omega
                          by_cases c918 : 0 < b2
                          swap
                          · omega
                          by_cases c919 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c920 : b0 < a0 + a2
                          swap
                          · -- branch
                            by_cases c921 : 0 < a6
                            swap
                            · omega
                            by_cases c922 : 0 < b2
                            swap
                            · omega
                            by_cases c923 : a0 + a2 + a4 < b0 + b2
                            swap
                            · omega
                            by_cases c924 : b0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f925 := pair_fact E (i := 6) (j := 2) rfl rfl c921 c922
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f925
                            omega
                          have f926 := pair_fact E (i := 2) (j := 2) rfl rfl c917 c918
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f926
                          omega
                        by_cases c927 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c928 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                        swap
                        · omega
                        have f929 := pair_fact E (i := 4) (j := 10) rfl rfl c875 c876
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f929
                        omega
                      have f930 := pair_fact E (i := 4) (j := 8) rfl rfl c871 c872
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f930
                      omega
                    by_cases c931 : a0 + a2 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c932 : b0 + b2 < a0 + a2 + a4
                    swap
                    · omega
                    have f933 := pair_fact E (i := 4) (j := 4) rfl rfl c869 c870
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f933
                    omega
                  by_cases c934 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c935 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f936 := pair_fact E (i := 2) (j := 4) rfl rfl c867 c868
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f936
                  omega
                by_cases c937 : 0 < b0 + b2 + b4
                swap
                · omega
                by_cases c938 : b0 + b2 < 0 + a0
                swap
                · -- branch
                  by_cases c939 : 0 < a2
                  swap
                  · omega
                  by_cases c940 : 0 < b0
                  swap
                  · omega
                  by_cases c941 : a0 < 0 + b0
                  swap
                  · -- branch
                    by_cases c942 : 0 < a2
                    swap
                    · omega
                    by_cases c943 : 0 < b2
                    swap
                    · omega
                    by_cases c944 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c945 : b0 < a0 + a2
                    swap
                    · omega
                    have f946 := pair_fact E (i := 2) (j := 2) rfl rfl c942 c943
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f946
                    by_cases c947 : 0 < a10
                    swap
                    · omega
                    by_cases c948 : 0 < b0
                    swap
                    · omega
                    by_cases c949 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                    swap
                    · -- branch
                      by_cases c950 : 0 < a10
                      swap
                      · omega
                      by_cases c951 : 0 < b2
                      swap
                      · omega
                      by_cases c952 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                      swap
                      · -- branch
                        by_cases c953 : 0 < a10
                        swap
                        · omega
                        by_cases c954 : 0 < b4
                        swap
                        · omega
                        by_cases c955 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                        swap
                        · -- branch
                          by_cases c956 : 0 < a10
                          swap
                          · omega
                          by_cases c957 : 0 < b8
                          swap
                          · omega
                          by_cases c958 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c959 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                          swap
                          · omega
                          have f960 := pair_fact E (i := 10) (j := 8) rfl rfl c956 c957
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f960
                          by_cases c961 : 0 < a10
                          swap
                          · omega
                          by_cases c962 : 0 < b10
                          swap
                          · -- branch
                            by_cases c963 : 0 < a2
                            swap
                            · omega
                            by_cases c964 : 0 < b4
                            swap
                            · omega
                            by_cases c965 : a0 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c966 : b0 + b2 < a0 + a2
                            swap
                            · -- branch
                              by_cases c967 : 0 < a4
                              swap
                              · -- branch
                                by_cases c968 : 0 < a6
                                swap
                                · omega
                                by_cases c969 : 0 < b2
                                swap
                                · omega
                                by_cases c970 : a0 + a2 + a4 < b0 + b2
                                swap
                                · omega
                                by_cases c971 : b0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f972 := pair_fact E (i := 6) (j := 2) rfl rfl c968 c969
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f972
                                omega
                              by_cases c973 : 0 < b0
                              swap
                              · omega
                              by_cases c974 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c975 : 0 < a4
                                swap
                                · omega
                                by_cases c976 : 0 < b2
                                swap
                                · omega
                                by_cases c977 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c978 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f979 := pair_fact E (i := 4) (j := 2) rfl rfl c975 c976
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f979
                                by_cases c980 : 0 < a4
                                swap
                                · omega
                                by_cases c981 : 0 < b4
                                swap
                                · omega
                                by_cases c982 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c983 : b0 + b2 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c984 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c985 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c986 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c987 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c988 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c989 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c990 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c991 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c992 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c993 : 0 < b10
                                      swap
                                      · -- branch
                                        by_cases c994 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c995 : 0 < b0
                                        swap
                                        · omega
                                        by_cases c996 : a0 + a2 + a4 < 0 + b0
                                        swap
                                        · -- branch
                                          by_cases c997 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c998 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c999 : a0 + a2 + a4 < b0 + b2
                                          swap
                                          · -- branch
                                            by_cases c1000 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c1001 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c1002 : a0 + a2 + a4 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c1003 : b0 + b2 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f1004 := pair_fact E (i := 6) (j := 4) rfl rfl c1000 c1001
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1004
                                            omega
                                          by_cases c1005 : b0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f1006 := pair_fact E (i := 6) (j := 2) rfl rfl c997 c998
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1006
                                          omega
                                        by_cases c1007 : 0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f1008 := pair_fact E (i := 6) (j := 0) rfl rfl c994 c995
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1008
                                        omega
                                      by_cases c1009 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c1010 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f1011 := pair_fact E (i := 4) (j := 10) rfl rfl c992 c993
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1011
                                      omega
                                    have f1012 := pair_fact E (i := 4) (j := 8) rfl rfl c988 c989
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1012
                                    omega
                                  have f1013 := pair_fact E (i := 4) (j := 6) rfl rfl c984 c985
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1013
                                  omega
                                have f1014 := pair_fact E (i := 4) (j := 4) rfl rfl c980 c981
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1014
                                omega
                              by_cases c1015 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f1016 := pair_fact E (i := 4) (j := 0) rfl rfl c967 c973
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1016
                              omega
                            have f1017 := pair_fact E (i := 2) (j := 4) rfl rfl c963 c964
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1017
                            by_cases c1018 : 0 < a10
                            swap
                            · omega
                            by_cases c1019 : 0 < b6
                            swap
                            · omega
                            by_cases c1020 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                            swap
                            · -- branch
                              by_cases c1021 : 0 < a6
                              swap
                              · omega
                              by_cases c1022 : 0 < b6
                              swap
                              · omega
                              by_cases c1023 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c1024 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f1025 := pair_fact E (i := 6) (j := 6) rfl rfl c1021 c1022
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1025
                              omega
                            by_cases c1026 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f1027 := pair_fact E (i := 10) (j := 6) rfl rfl c1018 c1019
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1027
                            omega
                          by_cases c1028 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c1029 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8 + a10
                          swap
                          · omega
                          have f1030 := pair_fact E (i := 10) (j := 10) rfl rfl c961 c962
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1030
                          omega
                        by_cases c1031 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                        swap
                        · omega
                        have f1032 := pair_fact E (i := 10) (j := 4) rfl rfl c953 c954
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1032
                        omega
                      by_cases c1033 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f1034 := pair_fact E (i := 10) (j := 2) rfl rfl c950 c951
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1034
                      omega
                    by_cases c1035 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                    swap
                    · omega
                    have f1036 := pair_fact E (i := 10) (j := 0) rfl rfl c947 c948
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1036
                    omega
                  by_cases c1037 : 0 < a0 + a2
                  swap
                  · omega
                  have f1038 := pair_fact E (i := 2) (j := 0) rfl rfl c939 c940
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1038
                  by_cases c1039 : 0 < a2
                  swap
                  · omega
                  by_cases c1040 : 0 < b2
                  swap
                  · omega
                  by_cases c1041 : a0 < b0 + b2
                  swap
                  · omega
                  by_cases c1042 : b0 < a0 + a2
                  swap
                  · -- branch
                    by_cases c1043 : 0 < a6
                    swap
                    · omega
                    by_cases c1044 : 0 < b2
                    swap
                    · omega
                    by_cases c1045 : a0 + a2 + a4 < b0 + b2
                    swap
                    · omega
                    by_cases c1046 : b0 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f1047 := pair_fact E (i := 6) (j := 2) rfl rfl c1043 c1044
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1047
                    omega
                  have f1048 := pair_fact E (i := 2) (j := 2) rfl rfl c1039 c1040
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1048
                  omega
                have f1049 := pair_fact E (i := 0) (j := 4) rfl rfl c865 c866
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1049
                omega
              have f1050 := pair_fact E (i := 0) (j := 2) rfl rfl c861 c862
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1050
              by_cases c1051 : 0 < a2
              swap
              · omega
              by_cases c1052 : 0 < b2
              swap
              · omega
              by_cases c1053 : a0 < b0 + b2
              swap
              · omega
              by_cases c1054 : b0 < a0 + a2
              swap
              · omega
              have f1055 := pair_fact E (i := 2) (j := 2) rfl rfl c1051 c1052
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1055
              omega
            by_cases c1056 : a0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c1057 : b0 + b2 + b4 + b6 + b8 < a0 + a2
            swap
            · omega
            have f1058 := pair_fact E (i := 2) (j := 10) rfl rfl c859 c860
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1058
            omega
          have f1059 := pair_fact E (i := 2) (j := 8) rfl rfl c855 c856
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1059
          omega
        have f1060 := pair_fact E (i := 2) (j := 6) rfl rfl c846 c852
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1060
        omega
      by_cases c1061 : 0 < b0 + b2 + b4 + b6 + b8 + b10
      swap
      · omega
      by_cases c1062 : b0 + b2 + b4 + b6 + b8 < 0 + a0
      swap
      · -- branch
        by_cases c1063 : 0 < a2
        swap
        · -- branch
          by_cases c1064 : 0 < a6
          swap
          · omega
          by_cases c1065 : 0 < b2
          swap
          · omega
          by_cases c1066 : a0 + a2 + a4 < b0 + b2
          swap
          · omega
          by_cases c1067 : b0 < a0 + a2 + a4 + a6
          swap
          · omega
          have f1068 := pair_fact E (i := 6) (j := 2) rfl rfl c1064 c1065
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1068
          omega
        by_cases c1069 : 0 < b6
        swap
        · omega
        by_cases c1070 : a0 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c1071 : b0 + b2 + b4 < a0 + a2
        swap
        · -- branch
          by_cases c1072 : 0 < a2
          swap
          · omega
          by_cases c1073 : 0 < b8
          swap
          · omega
          by_cases c1074 : a0 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c1075 : b0 + b2 + b4 + b6 < a0 + a2
          swap
          · -- branch
            by_cases c1076 : 0 < a2
            swap
            · omega
            by_cases c1077 : 0 < b10
            swap
            · omega
            by_cases c1078 : a0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c1079 : b0 + b2 + b4 + b6 + b8 < a0 + a2
            swap
            · -- branch
              by_cases c1080 : 0 < a0
              swap
              · omega
              by_cases c1081 : 0 < b2
              swap
              · omega
              by_cases c1082 : 0 < b0 + b2
              swap
              · omega
              by_cases c1083 : b0 < 0 + a0
              swap
              · -- branch
                by_cases c1084 : 0 < a0
                swap
                · omega
                by_cases c1085 : 0 < b4
                swap
                · -- branch
                  by_cases c1086 : 0 < a2
                  swap
                  · omega
                  by_cases c1087 : 0 < b4
                  swap
                  · -- branch
                    by_cases c1088 : 0 < a4
                    swap
                    · omega
                    by_cases c1089 : 0 < b4
                    swap
                    · -- branch
                      by_cases c1090 : 0 < a4
                      swap
                      · omega
                      by_cases c1091 : 0 < b8
                      swap
                      · omega
                      by_cases c1092 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c1093 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                      swap
                      · -- branch
                        by_cases c1094 : 0 < a4
                        swap
                        · omega
                        by_cases c1095 : 0 < b10
                        swap
                        · omega
                        by_cases c1096 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c1097 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                        swap
                        · -- branch
                          by_cases c1098 : 0 < a2
                          swap
                          · omega
                          by_cases c1099 : 0 < b0
                          swap
                          · omega
                          by_cases c1100 : a0 < 0 + b0
                          swap
                          · -- branch
                            by_cases c1101 : 0 < a2
                            swap
                            · omega
                            by_cases c1102 : 0 < b2
                            swap
                            · omega
                            by_cases c1103 : a0 < b0 + b2
                            swap
                            · omega
                            by_cases c1104 : b0 < a0 + a2
                            swap
                            · omega
                            have f1105 := pair_fact E (i := 2) (j := 2) rfl rfl c1101 c1102
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1105
                            by_cases c1106 : 0 < a4
                            swap
                            · omega
                            by_cases c1107 : 0 < b0
                            swap
                            · omega
                            by_cases c1108 : a0 + a2 < 0 + b0
                            swap
                            · -- branch
                              by_cases c1109 : 0 < a4
                              swap
                              · omega
                              by_cases c1110 : 0 < b2
                              swap
                              · omega
                              by_cases c1111 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c1112 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f1113 := pair_fact E (i := 4) (j := 2) rfl rfl c1109 c1110
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1113
                              by_cases c1114 : 0 < a4
                              swap
                              · omega
                              by_cases c1115 : 0 < b6
                              swap
                              · omega
                              by_cases c1116 : a0 + a2 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c1117 : b0 + b2 + b4 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c1118 : 0 < a6
                                swap
                                · omega
                                by_cases c1119 : 0 < b0
                                swap
                                · omega
                                by_cases c1120 : a0 + a2 + a4 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c1121 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1122 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c1123 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c1124 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c1125 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c1126 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c1127 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f1128 := pair_fact E (i := 6) (j := 6) rfl rfl c1124 c1125
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1128
                                    omega
                                  by_cases c1129 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1130 := pair_fact E (i := 6) (j := 2) rfl rfl c1121 c1122
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1130
                                  omega
                                by_cases c1131 : 0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f1132 := pair_fact E (i := 6) (j := 0) rfl rfl c1118 c1119
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1132
                                omega
                              have f1133 := pair_fact E (i := 4) (j := 6) rfl rfl c1114 c1115
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1133
                              omega
                            by_cases c1134 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f1135 := pair_fact E (i := 4) (j := 0) rfl rfl c1106 c1107
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1135
                            omega
                          by_cases c1136 : 0 < a0 + a2
                          swap
                          · omega
                          have f1137 := pair_fact E (i := 2) (j := 0) rfl rfl c1098 c1099
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1137
                          by_cases c1138 : 0 < a2
                          swap
                          · omega
                          by_cases c1139 : 0 < b2
                          swap
                          · omega
                          by_cases c1140 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c1141 : b0 < a0 + a2
                          swap
                          · -- branch
                            by_cases c1142 : 0 < a6
                            swap
                            · omega
                            by_cases c1143 : 0 < b2
                            swap
                            · omega
                            by_cases c1144 : a0 + a2 + a4 < b0 + b2
                            swap
                            · omega
                            by_cases c1145 : b0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f1146 := pair_fact E (i := 6) (j := 2) rfl rfl c1142 c1143
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1146
                            omega
                          have f1147 := pair_fact E (i := 2) (j := 2) rfl rfl c1138 c1139
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1147
                          omega
                        have f1148 := pair_fact E (i := 4) (j := 10) rfl rfl c1094 c1095
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1148
                        omega
                      have f1149 := pair_fact E (i := 4) (j := 8) rfl rfl c1090 c1091
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1149
                      omega
                    by_cases c1150 : a0 + a2 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c1151 : b0 + b2 < a0 + a2 + a4
                    swap
                    · omega
                    have f1152 := pair_fact E (i := 4) (j := 4) rfl rfl c1088 c1089
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1152
                    omega
                  by_cases c1153 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c1154 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f1155 := pair_fact E (i := 2) (j := 4) rfl rfl c1086 c1087
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1155
                  omega
                by_cases c1156 : 0 < b0 + b2 + b4
                swap
                · omega
                by_cases c1157 : b0 + b2 < 0 + a0
                swap
                · -- branch
                  by_cases c1158 : 0 < a2
                  swap
                  · omega
                  by_cases c1159 : 0 < b0
                  swap
                  · omega
                  by_cases c1160 : a0 < 0 + b0
                  swap
                  · -- branch
                    by_cases c1161 : 0 < a2
                    swap
                    · omega
                    by_cases c1162 : 0 < b2
                    swap
                    · omega
                    by_cases c1163 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c1164 : b0 < a0 + a2
                    swap
                    · omega
                    have f1165 := pair_fact E (i := 2) (j := 2) rfl rfl c1161 c1162
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1165
                    by_cases c1166 : 0 < a2
                    swap
                    · omega
                    by_cases c1167 : 0 < b4
                    swap
                    · omega
                    by_cases c1168 : a0 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c1169 : b0 + b2 < a0 + a2
                    swap
                    · -- branch
                      by_cases c1170 : 0 < a4
                      swap
                      · -- branch
                        by_cases c1171 : 0 < a6
                        swap
                        · omega
                        by_cases c1172 : 0 < b2
                        swap
                        · omega
                        by_cases c1173 : a0 + a2 + a4 < b0 + b2
                        swap
                        · omega
                        by_cases c1174 : b0 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f1175 := pair_fact E (i := 6) (j := 2) rfl rfl c1171 c1172
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1175
                        omega
                      by_cases c1176 : 0 < b0
                      swap
                      · omega
                      by_cases c1177 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c1178 : 0 < a4
                        swap
                        · omega
                        by_cases c1179 : 0 < b2
                        swap
                        · omega
                        by_cases c1180 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c1181 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f1182 := pair_fact E (i := 4) (j := 2) rfl rfl c1178 c1179
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1182
                        by_cases c1183 : 0 < a4
                        swap
                        · omega
                        by_cases c1184 : 0 < b4
                        swap
                        · omega
                        by_cases c1185 : a0 + a2 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c1186 : b0 + b2 < a0 + a2 + a4
                        swap
                        · -- branch
                          by_cases c1187 : 0 < a4
                          swap
                          · omega
                          by_cases c1188 : 0 < b6
                          swap
                          · omega
                          by_cases c1189 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c1190 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · -- branch
                            by_cases c1191 : 0 < a4
                            swap
                            · omega
                            by_cases c1192 : 0 < b8
                            swap
                            · omega
                            by_cases c1193 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1194 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c1195 : 0 < a4
                              swap
                              · omega
                              by_cases c1196 : 0 < b10
                              swap
                              · omega
                              by_cases c1197 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c1198 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c1199 : 0 < a6
                                swap
                                · omega
                                by_cases c1200 : 0 < b0
                                swap
                                · omega
                                by_cases c1201 : a0 + a2 + a4 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c1202 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1203 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c1204 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c1205 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c1206 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c1207 : a0 + a2 + a4 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c1208 : b0 + b2 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f1209 := pair_fact E (i := 6) (j := 4) rfl rfl c1205 c1206
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1209
                                    omega
                                  by_cases c1210 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1211 := pair_fact E (i := 6) (j := 2) rfl rfl c1202 c1203
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1211
                                  omega
                                by_cases c1212 : 0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f1213 := pair_fact E (i := 6) (j := 0) rfl rfl c1199 c1200
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1213
                                omega
                              have f1214 := pair_fact E (i := 4) (j := 10) rfl rfl c1195 c1196
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1214
                              omega
                            have f1215 := pair_fact E (i := 4) (j := 8) rfl rfl c1191 c1192
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1215
                            omega
                          have f1216 := pair_fact E (i := 4) (j := 6) rfl rfl c1187 c1188
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1216
                          omega
                        have f1217 := pair_fact E (i := 4) (j := 4) rfl rfl c1183 c1184
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1217
                        omega
                      by_cases c1218 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f1219 := pair_fact E (i := 4) (j := 0) rfl rfl c1170 c1176
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1219
                      omega
                    have f1220 := pair_fact E (i := 2) (j := 4) rfl rfl c1166 c1167
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1220
                    by_cases c1221 : 0 < a4
                    swap
                    · -- branch
                      by_cases c1222 : 0 < a4
                      swap
                      · -- branch
                        by_cases c1223 : 0 < a4
                        swap
                        · -- branch
                          by_cases c1224 : 0 < a4
                          swap
                          · -- branch
                            by_cases c1225 : 0 < a4
                            swap
                            · -- branch
                              by_cases c1226 : 0 < a4
                              swap
                              · -- branch
                                by_cases c1227 : 0 < a6
                                swap
                                · omega
                                by_cases c1228 : 0 < b0
                                swap
                                · omega
                                by_cases c1229 : a0 + a2 + a4 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c1230 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1231 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c1232 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c1233 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c1234 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c1235 : a0 + a2 + a4 < b0 + b2 + b4
                                    swap
                                    · -- branch
                                      by_cases c1236 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c1237 : 0 < b6
                                      swap
                                      · omega
                                      by_cases c1238 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                      swap
                                      · omega
                                      by_cases c1239 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f1240 := pair_fact E (i := 6) (j := 6) rfl rfl c1236 c1237
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1240
                                      omega
                                    by_cases c1241 : b0 + b2 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f1242 := pair_fact E (i := 6) (j := 4) rfl rfl c1233 c1234
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1242
                                    omega
                                  by_cases c1243 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1244 := pair_fact E (i := 6) (j := 2) rfl rfl c1230 c1231
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1244
                                  omega
                                by_cases c1245 : 0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f1246 := pair_fact E (i := 6) (j := 0) rfl rfl c1227 c1228
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1246
                                omega
                              by_cases c1247 : 0 < b10
                              swap
                              · omega
                              by_cases c1248 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c1249 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · omega
                              have f1250 := pair_fact E (i := 4) (j := 10) rfl rfl c1226 c1247
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1250
                              omega
                            by_cases c1251 : 0 < b8
                            swap
                            · omega
                            by_cases c1252 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1253 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · omega
                            have f1254 := pair_fact E (i := 4) (j := 8) rfl rfl c1225 c1251
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1254
                            omega
                          by_cases c1255 : 0 < b6
                          swap
                          · omega
                          by_cases c1256 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c1257 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · omega
                          have f1258 := pair_fact E (i := 4) (j := 6) rfl rfl c1224 c1255
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1258
                          omega
                        by_cases c1259 : 0 < b4
                        swap
                        · omega
                        by_cases c1260 : a0 + a2 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c1261 : b0 + b2 < a0 + a2 + a4
                        swap
                        · omega
                        have f1262 := pair_fact E (i := 4) (j := 4) rfl rfl c1223 c1259
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1262
                        omega
                      by_cases c1263 : 0 < b2
                      swap
                      · omega
                      by_cases c1264 : a0 + a2 < b0 + b2
                      swap
                      · omega
                      by_cases c1265 : b0 < a0 + a2 + a4
                      swap
                      · omega
                      have f1266 := pair_fact E (i := 4) (j := 2) rfl rfl c1222 c1263
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1266
                      omega
                    by_cases c1267 : 0 < b0
                    swap
                    · omega
                    by_cases c1268 : a0 + a2 < 0 + b0
                    swap
                    · -- branch
                      by_cases c1269 : 0 < a4
                      swap
                      · omega
                      by_cases c1270 : 0 < b2
                      swap
                      · omega
                      by_cases c1271 : a0 + a2 < b0 + b2
                      swap
                      · -- branch
                        by_cases c1272 : 0 < a4
                        swap
                        · omega
                        by_cases c1273 : 0 < b4
                        swap
                        · omega
                        by_cases c1274 : a0 + a2 < b0 + b2 + b4
                        swap
                        · -- branch
                          by_cases c1275 : 0 < a4
                          swap
                          · omega
                          by_cases c1276 : 0 < b6
                          swap
                          · omega
                          by_cases c1277 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c1278 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · omega
                          have f1279 := pair_fact E (i := 4) (j := 6) rfl rfl c1275 c1276
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1279
                          omega
                        by_cases c1280 : b0 + b2 < a0 + a2 + a4
                        swap
                        · omega
                        have f1281 := pair_fact E (i := 4) (j := 4) rfl rfl c1272 c1273
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1281
                        omega
                      by_cases c1282 : b0 < a0 + a2 + a4
                      swap
                      · omega
                      have f1283 := pair_fact E (i := 4) (j := 2) rfl rfl c1269 c1270
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1283
                      omega
                    by_cases c1284 : 0 < a0 + a2 + a4
                    swap
                    · omega
                    have f1285 := pair_fact E (i := 4) (j := 0) rfl rfl c1221 c1267
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1285
                    omega
                  by_cases c1286 : 0 < a0 + a2
                  swap
                  · omega
                  have f1287 := pair_fact E (i := 2) (j := 0) rfl rfl c1158 c1159
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1287
                  by_cases c1288 : 0 < a2
                  swap
                  · omega
                  by_cases c1289 : 0 < b2
                  swap
                  · omega
                  by_cases c1290 : a0 < b0 + b2
                  swap
                  · omega
                  by_cases c1291 : b0 < a0 + a2
                  swap
                  · -- branch
                    by_cases c1292 : 0 < a6
                    swap
                    · omega
                    by_cases c1293 : 0 < b2
                    swap
                    · omega
                    by_cases c1294 : a0 + a2 + a4 < b0 + b2
                    swap
                    · omega
                    by_cases c1295 : b0 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f1296 := pair_fact E (i := 6) (j := 2) rfl rfl c1292 c1293
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1296
                    omega
                  have f1297 := pair_fact E (i := 2) (j := 2) rfl rfl c1288 c1289
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1297
                  omega
                have f1298 := pair_fact E (i := 0) (j := 4) rfl rfl c1084 c1085
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1298
                omega
              have f1299 := pair_fact E (i := 0) (j := 2) rfl rfl c1080 c1081
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1299
              by_cases c1300 : 0 < a2
              swap
              · omega
              by_cases c1301 : 0 < b2
              swap
              · omega
              by_cases c1302 : a0 < b0 + b2
              swap
              · omega
              by_cases c1303 : b0 < a0 + a2
              swap
              · omega
              have f1304 := pair_fact E (i := 2) (j := 2) rfl rfl c1300 c1301
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1304
              omega
            have f1305 := pair_fact E (i := 2) (j := 10) rfl rfl c1076 c1077
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1305
            omega
          have f1306 := pair_fact E (i := 2) (j := 8) rfl rfl c1072 c1073
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1306
          omega
        have f1307 := pair_fact E (i := 2) (j := 6) rfl rfl c1063 c1069
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1307
        omega
      have f1308 := pair_fact E (i := 0) (j := 10) rfl rfl c844 c845
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1308
      omega
    have f1309 := pair_fact E (i := 0) (j := 8) rfl rfl c710 c711
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1309
    omega
  have f1310 := pair_fact E (i := 0) (j := 6) rfl rfl c641 c642
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1310
  omega

end Blocks
