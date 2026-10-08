import LeanProofs.ShuffleBlocks.Basic

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Blocks

set_option maxHeartbeats 0 in
/-- Cut inside run 1 of `V`: no splitting of this rotation gives two equal copies. -/
theorem V_cut01 (L l m v k a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9 a10 b10 : Nat)
    (hl : 1 ≤ l) (hm : m = 2 * v + 1) (hL : 9 * l ≤ L) (hk : k ≤ m)
    (e0 : a0 + b0 = (m - k))
    (e1 : a1 + b1 = 5 * l)
    (e2 : a2 + b2 = 2 * m)
    (e3 : a3 + b3 = L)
    (e4 : a4 + b4 = m)
    (e5 : a5 + b5 = 2 * l)
    (e6 : a6 + b6 = m)
    (e7 : a7 + b7 = l)
    (e8 : a8 + b8 = 3 * m)
    (e9 : a9 + b9 = L)
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
                                      by_cases c19 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c20 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c21 : a0 + a2 + a4 + a6 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c22 : b0 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f23 := pair_fact E (i := 8) (j := 2) rfl rfl c19 c20
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f23
                                      by_cases c24 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c25 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c26 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c27 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f28 := pair_fact E (i := 8) (j := 4) rfl rfl c24 c25
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f28
                                      omega
                                    by_cases c29 : 0 < b10
                                    swap
                                    · omega
                                    by_cases c30 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c31 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f32 := pair_fact E (i := 4) (j := 10) rfl rfl c18 c29
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f32
                                    omega
                                  by_cases c33 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c34 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c35 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f36 := pair_fact E (i := 4) (j := 8) rfl rfl c17 c33
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f36
                                  omega
                                by_cases c37 : 0 < b6
                                swap
                                · omega
                                by_cases c38 : a0 + a2 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c39 : b0 + b2 + b4 < a0 + a2 + a4
                                swap
                                · omega
                                have f40 := pair_fact E (i := 4) (j := 6) rfl rfl c16 c37
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f40
                                omega
                              by_cases c41 : 0 < b4
                              swap
                              · omega
                              by_cases c42 : a0 + a2 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c43 : b0 + b2 < a0 + a2 + a4
                              swap
                              · omega
                              have f44 := pair_fact E (i := 4) (j := 4) rfl rfl c15 c41
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f44
                              omega
                            by_cases c45 : 0 < b2
                            swap
                            · omega
                            by_cases c46 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c47 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f48 := pair_fact E (i := 4) (j := 2) rfl rfl c14 c45
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f48
                            omega
                          by_cases c49 : 0 < b0
                          swap
                          · -- branch
                            by_cases c50 : 0 < a4
                            swap
                            · omega
                            by_cases c51 : 0 < b2
                            swap
                            · omega
                            by_cases c52 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c53 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f54 := pair_fact E (i := 4) (j := 2) rfl rfl c50 c51
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f54
                            by_cases c55 : 0 < a8
                            swap
                            · omega
                            by_cases c56 : 0 < b0
                            swap
                            · -- branch
                              by_cases c57 : 0 < a8
                              swap
                              · omega
                              by_cases c58 : 0 < b4
                              swap
                              · -- branch
                                by_cases c59 : 0 < a4
                                swap
                                · omega
                                by_cases c60 : 0 < b4
                                swap
                                · -- branch
                                  by_cases c61 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c62 : 0 < b6
                                  swap
                                  · -- branch
                                    by_cases c63 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c64 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c65 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c66 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f67 := pair_fact E (i := 8) (j := 8) rfl rfl c63 c64
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f67
                                    omega
                                  by_cases c68 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c69 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f70 := pair_fact E (i := 8) (j := 6) rfl rfl c61 c62
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f70
                                  omega
                                by_cases c71 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c72 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f73 := pair_fact E (i := 4) (j := 4) rfl rfl c59 c60
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f73
                                omega
                              by_cases c74 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c75 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f76 := pair_fact E (i := 8) (j := 4) rfl rfl c57 c58
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f76
                              omega
                            by_cases c77 : a0 + a2 + a4 + a6 < 0 + b0
                            swap
                            · omega
                            by_cases c78 : 0 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f79 := pair_fact E (i := 8) (j := 0) rfl rfl c55 c56
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f79
                            omega
                          by_cases c80 : a0 + a2 < 0 + b0
                          swap
                          · omega
                          by_cases c81 : 0 < a0 + a2 + a4
                          swap
                          · omega
                          have f82 := pair_fact E (i := 4) (j := 0) rfl rfl c13 c49
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f82
                          omega
                        by_cases c83 : 0 < b10
                        swap
                        · omega
                        by_cases c84 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c85 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                        swap
                        · omega
                        have f86 := pair_fact E (i := 2) (j := 10) rfl rfl c12 c83
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f86
                        omega
                      by_cases c87 : 0 < b8
                      swap
                      · omega
                      by_cases c88 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c89 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · omega
                      have f90 := pair_fact E (i := 2) (j := 8) rfl rfl c11 c87
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f90
                      omega
                    by_cases c91 : 0 < b6
                    swap
                    · omega
                    by_cases c92 : a0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c93 : b0 + b2 + b4 < a0 + a2
                    swap
                    · omega
                    have f94 := pair_fact E (i := 2) (j := 6) rfl rfl c10 c91
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f94
                    omega
                  by_cases c95 : 0 < b4
                  swap
                  · omega
                  by_cases c96 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c97 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f98 := pair_fact E (i := 2) (j := 4) rfl rfl c9 c95
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f98
                  omega
                by_cases c99 : 0 < b2
                swap
                · omega
                by_cases c100 : a0 < b0 + b2
                swap
                · omega
                by_cases c101 : b0 < a0 + a2
                swap
                · omega
                have f102 := pair_fact E (i := 2) (j := 2) rfl rfl c8 c99
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f102
                omega
              by_cases c103 : 0 < b0
              swap
              · -- branch
                by_cases c104 : 0 < a2
                swap
                · omega
                by_cases c105 : 0 < b2
                swap
                · -- branch
                  by_cases c106 : 0 < a2
                  swap
                  · omega
                  by_cases c107 : 0 < b4
                  swap
                  · -- branch
                    by_cases c108 : 0 < a2
                    swap
                    · omega
                    by_cases c109 : 0 < b8
                    swap
                    · omega
                    by_cases c110 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c111 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · omega
                    have f112 := pair_fact E (i := 2) (j := 8) rfl rfl c108 c109
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f112
                    by_cases c113 : 0 < a4
                    swap
                    · omega
                    by_cases c114 : 0 < b8
                    swap
                    · omega
                    by_cases c115 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c116 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                    swap
                    · omega
                    have f117 := pair_fact E (i := 4) (j := 8) rfl rfl c113 c114
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f117
                    omega
                  by_cases c118 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c119 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f120 := pair_fact E (i := 2) (j := 4) rfl rfl c106 c107
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f120
                  by_cases c121 : 0 < a4
                  swap
                  · -- branch
                    by_cases c122 : 0 < a4
                    swap
                    · -- branch
                      by_cases c123 : 0 < a4
                      swap
                      · -- branch
                        by_cases c124 : 0 < a4
                        swap
                        · -- branch
                          by_cases c125 : 0 < a4
                          swap
                          · -- branch
                            by_cases c126 : 0 < a4
                            swap
                            · -- branch
                              by_cases c127 : 0 < a6
                              swap
                              · -- branch
                                by_cases c128 : 0 < a8
                                swap
                                · omega
                                by_cases c129 : 0 < b8
                                swap
                                · omega
                                by_cases c130 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                swap
                                · omega
                                by_cases c131 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f132 := pair_fact E (i := 8) (j := 8) rfl rfl c128 c129
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f132
                                omega
                              by_cases c133 : 0 < b8
                              swap
                              · omega
                              by_cases c134 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c135 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f136 := pair_fact E (i := 6) (j := 8) rfl rfl c127 c133
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
                            have f140 := pair_fact E (i := 4) (j := 10) rfl rfl c126 c137
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f140
                            omega
                          by_cases c141 : 0 < b6
                          swap
                          · omega
                          by_cases c142 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c143 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · omega
                          have f144 := pair_fact E (i := 4) (j := 6) rfl rfl c125 c141
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f144
                          omega
                        by_cases c145 : 0 < b4
                        swap
                        · omega
                        by_cases c146 : a0 + a2 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c147 : b0 + b2 < a0 + a2 + a4
                        swap
                        · omega
                        have f148 := pair_fact E (i := 4) (j := 4) rfl rfl c124 c145
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f148
                        omega
                      by_cases c149 : 0 < b2
                      swap
                      · omega
                      by_cases c150 : a0 + a2 < b0 + b2
                      swap
                      · omega
                      by_cases c151 : b0 < a0 + a2 + a4
                      swap
                      · omega
                      have f152 := pair_fact E (i := 4) (j := 2) rfl rfl c123 c149
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f152
                      omega
                    by_cases c153 : 0 < b0
                    swap
                    · omega
                    by_cases c154 : a0 + a2 < 0 + b0
                    swap
                    · omega
                    by_cases c155 : 0 < a0 + a2 + a4
                    swap
                    · omega
                    have f156 := pair_fact E (i := 4) (j := 0) rfl rfl c122 c153
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f156
                    omega
                  by_cases c157 : 0 < b8
                  swap
                  · omega
                  by_cases c158 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c159 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                  swap
                  · omega
                  have f160 := pair_fact E (i := 4) (j := 8) rfl rfl c121 c157
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f160
                  omega
                by_cases c161 : a0 < b0 + b2
                swap
                · omega
                by_cases c162 : b0 < a0 + a2
                swap
                · omega
                have f163 := pair_fact E (i := 2) (j := 2) rfl rfl c104 c105
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f163
                by_cases c164 : 0 < a2
                swap
                · omega
                by_cases c165 : 0 < b6
                swap
                · -- branch
                  by_cases c166 : 0 < a2
                  swap
                  · omega
                  by_cases c167 : 0 < b8
                  swap
                  · omega
                  by_cases c168 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c169 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · -- branch
                    by_cases c170 : 0 < a6
                    swap
                    · omega
                    by_cases c171 : 0 < b0
                    swap
                    · -- branch
                      by_cases c172 : 0 < a6
                      swap
                      · omega
                      by_cases c173 : 0 < b2
                      swap
                      · omega
                      by_cases c174 : a0 + a2 + a4 < b0 + b2
                      swap
                      · -- branch
                        by_cases c175 : 0 < a6
                        swap
                        · omega
                        by_cases c176 : 0 < b6
                        swap
                        · -- branch
                          by_cases c177 : 0 < a2
                          swap
                          · omega
                          by_cases c178 : 0 < b10
                          swap
                          · -- branch
                            by_cases c179 : 0 < a6
                            swap
                            · omega
                            by_cases c180 : 0 < b10
                            swap
                            · -- branch
                              by_cases c181 : 0 < a10
                              swap
                              · omega
                              by_cases c182 : 0 < b0
                              swap
                              · -- branch
                                by_cases c183 : 0 < a10
                                swap
                                · omega
                                by_cases c184 : 0 < b2
                                swap
                                · omega
                                by_cases c185 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                                swap
                                · -- branch
                                  by_cases c186 : 0 < a10
                                  swap
                                  · omega
                                  by_cases c187 : 0 < b6
                                  swap
                                  · -- branch
                                    by_cases c188 : 0 < a10
                                    swap
                                    · omega
                                    by_cases c189 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c190 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c191 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                    swap
                                    · omega
                                    have f192 := pair_fact E (i := 10) (j := 8) rfl rfl c188 c189
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f192
                                    by_cases c193 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c194 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c195 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c196 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
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
                                    have f202 := pair_fact E (i := 6) (j := 8) rfl rfl c193 c194
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f202
                                    omega
                                  by_cases c203 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c204 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                  swap
                                  · omega
                                  have f205 := pair_fact E (i := 10) (j := 6) rfl rfl c186 c187
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f205
                                  omega
                                by_cases c206 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f207 := pair_fact E (i := 10) (j := 2) rfl rfl c183 c184
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f207
                                omega
                              by_cases c208 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                              swap
                              · omega
                              by_cases c209 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                              swap
                              · omega
                              have f210 := pair_fact E (i := 10) (j := 0) rfl rfl c181 c182
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f210
                              omega
                            by_cases c211 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c212 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f213 := pair_fact E (i := 6) (j := 10) rfl rfl c179 c180
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f213
                            omega
                          by_cases c214 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c215 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · -- branch
                            by_cases c216 : 0 < a6
                            swap
                            · omega
                            by_cases c217 : 0 < b10
                            swap
                            · omega
                            by_cases c218 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c219 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                            swap
                            · -- branch
                              by_cases c220 : 0 < a8
                              swap
                              · omega
                              by_cases c221 : 0 < b0
                              swap
                              · -- branch
                                by_cases c222 : 0 < a8
                                swap
                                · omega
                                by_cases c223 : 0 < b2
                                swap
                                · omega
                                by_cases c224 : a0 + a2 + a4 + a6 < b0 + b2
                                swap
                                · -- branch
                                  by_cases c225 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c226 : 0 < b6
                                  swap
                                  · -- branch
                                    by_cases c227 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c228 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c229 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c230 : 0 < a4
                                          swap
                                          · -- branch
                                            by_cases c231 : 0 < a4
                                            swap
                                            · -- branch
                                              by_cases c232 : 0 < a4
                                              swap
                                              · -- branch
                                                by_cases c233 : 0 < a6
                                                swap
                                                · omega
                                                by_cases c234 : 0 < b4
                                                swap
                                                · omega
                                                by_cases c235 : a0 + a2 + a4 < b0 + b2 + b4
                                                swap
                                                · omega
                                                by_cases c236 : b0 + b2 < a0 + a2 + a4 + a6
                                                swap
                                                · omega
                                                have f237 := pair_fact E (i := 6) (j := 4) rfl rfl c233 c234
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f237
                                                by_cases c238 : 0 < a2
                                                swap
                                                · omega
                                                by_cases c239 : 0 < b4
                                                swap
                                                · omega
                                                by_cases c240 : a0 < b0 + b2 + b4
                                                swap
                                                · omega
                                                by_cases c241 : b0 + b2 < a0 + a2
                                                swap
                                                · -- branch
                                                  by_cases c242 : 0 < a6
                                                  swap
                                                  · omega
                                                  by_cases c243 : 0 < b8
                                                  swap
                                                  · omega
                                                  by_cases c244 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                                  swap
                                                  · omega
                                                  by_cases c245 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                                  swap
                                                  · -- branch
                                                    by_cases c246 : 0 < a8
                                                    swap
                                                    · omega
                                                    by_cases c247 : 0 < b4
                                                    swap
                                                    · omega
                                                    by_cases c248 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                                    swap
                                                    · -- branch
                                                      by_cases c249 : 0 < a8
                                                      swap
                                                      · omega
                                                      by_cases c250 : 0 < b8
                                                      swap
                                                      · omega
                                                      by_cases c251 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                                      swap
                                                      · omega
                                                      by_cases c252 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                                      swap
                                                      · omega
                                                      have f253 := pair_fact E (i := 8) (j := 8) rfl rfl c249 c250
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f253
                                                      by_cases c254 : 0 < a8
                                                      swap
                                                      · omega
                                                      by_cases c255 : 0 < b10
                                                      swap
                                                      · omega
                                                      by_cases c256 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                                      swap
                                                      · omega
                                                      by_cases c257 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                                      swap
                                                      · -- branch
                                                        by_cases c258 : 0 < a10
                                                        swap
                                                        · omega
                                                        by_cases c259 : 0 < b8
                                                        swap
                                                        · omega
                                                        by_cases c260 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                                        swap
                                                        · omega
                                                        by_cases c261 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                                        swap
                                                        · omega
                                                        have f262 := pair_fact E (i := 10) (j := 8) rfl rfl c258 c259
                                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f262
                                                        omega
                                                      have f263 := pair_fact E (i := 8) (j := 10) rfl rfl c254 c255
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f263
                                                      omega
                                                    by_cases c264 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                                    swap
                                                    · omega
                                                    have f265 := pair_fact E (i := 8) (j := 4) rfl rfl c246 c247
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f265
                                                    omega
                                                  have f266 := pair_fact E (i := 6) (j := 8) rfl rfl c242 c243
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f266
                                                  omega
                                                have f267 := pair_fact E (i := 2) (j := 4) rfl rfl c238 c239
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f267
                                                omega
                                              by_cases c268 : 0 < b10
                                              swap
                                              · omega
                                              by_cases c269 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                              swap
                                              · omega
                                              by_cases c270 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                              swap
                                              · omega
                                              have f271 := pair_fact E (i := 4) (j := 10) rfl rfl c232 c268
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f271
                                              omega
                                            by_cases c272 : 0 < b8
                                            swap
                                            · omega
                                            by_cases c273 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                            swap
                                            · omega
                                            by_cases c274 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                            swap
                                            · omega
                                            have f275 := pair_fact E (i := 4) (j := 8) rfl rfl c231 c272
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f275
                                            omega
                                          by_cases c276 : 0 < b6
                                          swap
                                          · omega
                                          by_cases c277 : a0 + a2 < b0 + b2 + b4 + b6
                                          swap
                                          · omega
                                          by_cases c278 : b0 + b2 + b4 < a0 + a2 + a4
                                          swap
                                          · omega
                                          have f279 := pair_fact E (i := 4) (j := 6) rfl rfl c230 c276
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f279
                                          omega
                                        by_cases c280 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c281 : a0 + a2 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c282 : b0 + b2 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f283 := pair_fact E (i := 4) (j := 4) rfl rfl c229 c280
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f283
                                        omega
                                      by_cases c284 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c285 : a0 + a2 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c286 : b0 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f287 := pair_fact E (i := 4) (j := 2) rfl rfl c228 c284
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f287
                                      omega
                                    by_cases c288 : 0 < b0
                                    swap
                                    · -- branch
                                      by_cases c289 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c290 : 0 < b6
                                      swap
                                      · -- branch
                                        by_cases c291 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c292 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c293 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c294 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · -- branch
                                          by_cases c295 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c296 : 0 < b8
                                          swap
                                          · omega
                                          by_cases c297 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                          swap
                                          · omega
                                          by_cases c298 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f299 := pair_fact E (i := 6) (j := 8) rfl rfl c295 c296
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f299
                                          by_cases c300 : 0 < a4
                                          swap
                                          · omega
                                          by_cases c301 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c302 : a0 + a2 < b0 + b2
                                          swap
                                          · -- branch
                                            by_cases c303 : 0 < a8
                                            swap
                                            · omega
                                            by_cases c304 : 0 < b10
                                            swap
                                            · omega
                                            by_cases c305 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                            swap
                                            · omega
                                            by_cases c306 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · -- branch
                                              by_cases c307 : 0 < a10
                                              swap
                                              · omega
                                              by_cases c308 : 0 < b8
                                              swap
                                              · omega
                                              by_cases c309 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                              swap
                                              · omega
                                              by_cases c310 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                              swap
                                              · omega
                                              have f311 := pair_fact E (i := 10) (j := 8) rfl rfl c307 c308
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f311
                                              omega
                                            have f312 := pair_fact E (i := 8) (j := 10) rfl rfl c303 c304
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f312
                                            omega
                                          by_cases c313 : b0 < a0 + a2 + a4
                                          swap
                                          · omega
                                          have f314 := pair_fact E (i := 4) (j := 2) rfl rfl c300 c301
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f314
                                          omega
                                        have f315 := pair_fact E (i := 4) (j := 10) rfl rfl c291 c292
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f315
                                        omega
                                      by_cases c316 : a0 + a2 < b0 + b2 + b4 + b6
                                      swap
                                      · omega
                                      by_cases c317 : b0 + b2 + b4 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f318 := pair_fact E (i := 4) (j := 6) rfl rfl c289 c290
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f318
                                      omega
                                    by_cases c319 : a0 + a2 < 0 + b0
                                    swap
                                    · omega
                                    by_cases c320 : 0 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f321 := pair_fact E (i := 4) (j := 0) rfl rfl c227 c288
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f321
                                    omega
                                  by_cases c322 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c323 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f324 := pair_fact E (i := 8) (j := 6) rfl rfl c225 c226
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f324
                                  omega
                                by_cases c325 : b0 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f326 := pair_fact E (i := 8) (j := 2) rfl rfl c222 c223
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f326
                                omega
                              by_cases c327 : a0 + a2 + a4 + a6 < 0 + b0
                              swap
                              · omega
                              by_cases c328 : 0 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f329 := pair_fact E (i := 8) (j := 0) rfl rfl c220 c221
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f329
                              omega
                            have f330 := pair_fact E (i := 6) (j := 10) rfl rfl c216 c217
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f330
                            omega
                          have f331 := pair_fact E (i := 2) (j := 10) rfl rfl c177 c178
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f331
                          omega
                        by_cases c332 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c333 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f334 := pair_fact E (i := 6) (j := 6) rfl rfl c175 c176
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f334
                        omega
                      by_cases c335 : b0 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f336 := pair_fact E (i := 6) (j := 2) rfl rfl c172 c173
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f336
                      omega
                    by_cases c337 : a0 + a2 + a4 < 0 + b0
                    swap
                    · omega
                    by_cases c338 : 0 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f339 := pair_fact E (i := 6) (j := 0) rfl rfl c170 c171
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f339
                    omega
                  have f340 := pair_fact E (i := 2) (j := 8) rfl rfl c166 c167
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f340
                  omega
                by_cases c341 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c342 : b0 + b2 + b4 < a0 + a2
                swap
                · -- branch
                  by_cases c343 : 0 < a8
                  swap
                  · omega
                  by_cases c344 : 0 < b0
                  swap
                  · -- branch
                    by_cases c345 : 0 < a8
                    swap
                    · omega
                    by_cases c346 : 0 < b2
                    swap
                    · omega
                    by_cases c347 : a0 + a2 + a4 + a6 < b0 + b2
                    swap
                    · -- branch
                      by_cases c348 : 0 < a2
                      swap
                      · omega
                      by_cases c349 : 0 < b8
                      swap
                      · -- branch
                        by_cases c350 : 0 < a2
                        swap
                        · omega
                        by_cases c351 : 0 < b4
                        swap
                        · omega
                        by_cases c352 : a0 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c353 : b0 + b2 < a0 + a2
                        swap
                        · -- branch
                          by_cases c354 : 0 < a2
                          swap
                          · omega
                          by_cases c355 : 0 < b10
                          swap
                          · omega
                          by_cases c356 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c357 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · -- branch
                            by_cases c358 : 0 < a4
                            swap
                            · -- branch
                              by_cases c359 : 0 < a4
                              swap
                              · -- branch
                                by_cases c360 : 0 < a4
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
                                        by_cases c364 : 0 < a6
                                        swap
                                        · -- branch
                                          by_cases c365 : 0 < a6
                                          swap
                                          · -- branch
                                            by_cases c366 : 0 < a6
                                            swap
                                            · -- branch
                                              by_cases c367 : 0 < a6
                                              swap
                                              · -- branch
                                                by_cases c368 : 0 < a6
                                                swap
                                                · -- branch
                                                  by_cases c369 : 0 < a6
                                                  swap
                                                  · -- branch
                                                    by_cases c370 : 0 < a8
                                                    swap
                                                    · omega
                                                    by_cases c371 : 0 < b4
                                                    swap
                                                    · omega
                                                    by_cases c372 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                                    swap
                                                    · omega
                                                    by_cases c373 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                                    swap
                                                    · omega
                                                    have f374 := pair_fact E (i := 8) (j := 4) rfl rfl c370 c371
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f374
                                                    by_cases c375 : 0 < a8
                                                    swap
                                                    · omega
                                                    by_cases c376 : 0 < b10
                                                    swap
                                                    · omega
                                                    by_cases c377 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                                    swap
                                                    · omega
                                                    by_cases c378 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                                    swap
                                                    · omega
                                                    have f379 := pair_fact E (i := 8) (j := 10) rfl rfl c375 c376
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f379
                                                    omega
                                                  by_cases c380 : 0 < b10
                                                  swap
                                                  · omega
                                                  by_cases c381 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                                  swap
                                                  · omega
                                                  by_cases c382 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                                  swap
                                                  · omega
                                                  have f383 := pair_fact E (i := 6) (j := 10) rfl rfl c369 c380
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f383
                                                  omega
                                                by_cases c384 : 0 < b8
                                                swap
                                                · omega
                                                by_cases c385 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                                swap
                                                · omega
                                                by_cases c386 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                                swap
                                                · omega
                                                have f387 := pair_fact E (i := 6) (j := 8) rfl rfl c368 c384
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f387
                                                omega
                                              by_cases c388 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c389 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c390 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f391 := pair_fact E (i := 6) (j := 6) rfl rfl c367 c388
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f391
                                              omega
                                            by_cases c392 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c393 : a0 + a2 + a4 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c394 : b0 + b2 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f395 := pair_fact E (i := 6) (j := 4) rfl rfl c366 c392
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f395
                                            omega
                                          by_cases c396 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c397 : a0 + a2 + a4 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c398 : b0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f399 := pair_fact E (i := 6) (j := 2) rfl rfl c365 c396
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f399
                                          omega
                                        by_cases c400 : 0 < b0
                                        swap
                                        · omega
                                        by_cases c401 : a0 + a2 + a4 < 0 + b0
                                        swap
                                        · omega
                                        by_cases c402 : 0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f403 := pair_fact E (i := 6) (j := 0) rfl rfl c364 c400
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f403
                                        omega
                                      by_cases c404 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c405 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c406 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f407 := pair_fact E (i := 4) (j := 10) rfl rfl c363 c404
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f407
                                      omega
                                    by_cases c408 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c409 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c410 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f411 := pair_fact E (i := 4) (j := 8) rfl rfl c362 c408
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f411
                                    omega
                                  by_cases c412 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c413 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c414 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f415 := pair_fact E (i := 4) (j := 6) rfl rfl c361 c412
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f415
                                  omega
                                by_cases c416 : 0 < b4
                                swap
                                · omega
                                by_cases c417 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c418 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f419 := pair_fact E (i := 4) (j := 4) rfl rfl c360 c416
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f419
                                omega
                              by_cases c420 : 0 < b2
                              swap
                              · omega
                              by_cases c421 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c422 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f423 := pair_fact E (i := 4) (j := 2) rfl rfl c359 c420
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f423
                              omega
                            by_cases c424 : 0 < b0
                            swap
                            · omega
                            by_cases c425 : a0 + a2 < 0 + b0
                            swap
                            · omega
                            by_cases c426 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f427 := pair_fact E (i := 4) (j := 0) rfl rfl c358 c424
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f427
                            omega
                          have f428 := pair_fact E (i := 2) (j := 10) rfl rfl c354 c355
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f428
                          omega
                        have f429 := pair_fact E (i := 2) (j := 4) rfl rfl c350 c351
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f429
                        omega
                      by_cases c430 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c431 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · -- branch
                        by_cases c432 : 0 < a2
                        swap
                        · omega
                        by_cases c433 : 0 < b10
                        swap
                        · -- branch
                          by_cases c434 : 0 < a8
                          swap
                          · omega
                          by_cases c435 : 0 < b10
                          swap
                          · -- branch
                            by_cases c436 : 0 < a10
                            swap
                            · omega
                            by_cases c437 : 0 < b0
                            swap
                            · -- branch
                              by_cases c438 : 0 < a10
                              swap
                              · omega
                              by_cases c439 : 0 < b2
                              swap
                              · omega
                              by_cases c440 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                              swap
                              · -- branch
                                by_cases c441 : 0 < a10
                                swap
                                · omega
                                by_cases c442 : 0 < b6
                                swap
                                · omega
                                by_cases c443 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                swap
                                · -- branch
                                  by_cases c444 : 0 < a10
                                  swap
                                  · omega
                                  by_cases c445 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c446 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c447 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                  swap
                                  · omega
                                  have f448 := pair_fact E (i := 10) (j := 8) rfl rfl c444 c445
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f448
                                  by_cases c449 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c450 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c451 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                  swap
                                  · -- branch
                                    by_cases c452 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c453 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c454 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c455 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f456 := pair_fact E (i := 8) (j := 8) rfl rfl c452 c453
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f456
                                    omega
                                  by_cases c457 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f458 := pair_fact E (i := 8) (j := 6) rfl rfl c449 c450
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f458
                                  omega
                                by_cases c459 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f460 := pair_fact E (i := 10) (j := 6) rfl rfl c441 c442
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f460
                                omega
                              by_cases c461 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                              swap
                              · omega
                              have f462 := pair_fact E (i := 10) (j := 2) rfl rfl c438 c439
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f462
                              omega
                            by_cases c463 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                            swap
                            · omega
                            by_cases c464 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f465 := pair_fact E (i := 10) (j := 0) rfl rfl c436 c437
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f465
                            omega
                          by_cases c466 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c467 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f468 := pair_fact E (i := 8) (j := 10) rfl rfl c434 c435
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f468
                          omega
                        by_cases c469 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c470 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                        swap
                        · -- branch
                          by_cases c471 : 0 < a8
                          swap
                          · omega
                          by_cases c472 : 0 < b8
                          swap
                          · omega
                          by_cases c473 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c474 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f475 := pair_fact E (i := 8) (j := 8) rfl rfl c471 c472
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f475
                          by_cases c476 : 0 < a8
                          swap
                          · omega
                          by_cases c477 : 0 < b10
                          swap
                          · omega
                          by_cases c478 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c479 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                          swap
                          · -- branch
                            by_cases c480 : 0 < a10
                            swap
                            · omega
                            by_cases c481 : 0 < b8
                            swap
                            · omega
                            by_cases c482 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c483 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f484 := pair_fact E (i := 10) (j := 8) rfl rfl c480 c481
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f484
                            omega
                          have f485 := pair_fact E (i := 8) (j := 10) rfl rfl c476 c477
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f485
                          omega
                        have f486 := pair_fact E (i := 2) (j := 10) rfl rfl c432 c433
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f486
                        omega
                      have f487 := pair_fact E (i := 2) (j := 8) rfl rfl c348 c349
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f487
                      omega
                    by_cases c488 : b0 < a0 + a2 + a4 + a6 + a8
                    swap
                    · omega
                    have f489 := pair_fact E (i := 8) (j := 2) rfl rfl c345 c346
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f489
                    omega
                  by_cases c490 : a0 + a2 + a4 + a6 < 0 + b0
                  swap
                  · omega
                  by_cases c491 : 0 < a0 + a2 + a4 + a6 + a8
                  swap
                  · omega
                  have f492 := pair_fact E (i := 8) (j := 0) rfl rfl c343 c344
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f492
                  omega
                have f493 := pair_fact E (i := 2) (j := 6) rfl rfl c164 c165
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f493
                omega
              by_cases c494 : a0 < 0 + b0
              swap
              · omega
              by_cases c495 : 0 < a0 + a2
              swap
              · omega
              have f496 := pair_fact E (i := 2) (j := 0) rfl rfl c7 c103
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f496
              by_cases c497 : 0 < a2
              swap
              · omega
              by_cases c498 : 0 < b2
              swap
              · -- branch
                by_cases c499 : 0 < a2
                swap
                · omega
                by_cases c500 : 0 < b4
                swap
                · -- branch
                  by_cases c501 : 0 < a2
                  swap
                  · omega
                  by_cases c502 : 0 < b6
                  swap
                  · -- branch
                    by_cases c503 : 0 < a2
                    swap
                    · omega
                    by_cases c504 : 0 < b8
                    swap
                    · omega
                    by_cases c505 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c506 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · omega
                    have f507 := pair_fact E (i := 2) (j := 8) rfl rfl c503 c504
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f507
                    omega
                  by_cases c508 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c509 : b0 + b2 + b4 < a0 + a2
                  swap
                  · omega
                  have f510 := pair_fact E (i := 2) (j := 6) rfl rfl c501 c502
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f510
                  omega
                by_cases c511 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c512 : b0 + b2 < a0 + a2
                swap
                · omega
                have f513 := pair_fact E (i := 2) (j := 4) rfl rfl c499 c500
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f513
                omega
              by_cases c514 : a0 < b0 + b2
              swap
              · omega
              by_cases c515 : b0 < a0 + a2
              swap
              · -- branch
                by_cases c516 : 0 < a8
                swap
                · omega
                by_cases c517 : 0 < b0
                swap
                · omega
                by_cases c518 : a0 + a2 + a4 + a6 < 0 + b0
                swap
                · -- branch
                  by_cases c519 : 0 < a2
                  swap
                  · omega
                  by_cases c520 : 0 < b4
                  swap
                  · -- branch
                    by_cases c521 : 0 < a2
                    swap
                    · omega
                    by_cases c522 : 0 < b8
                    swap
                    · omega
                    by_cases c523 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c524 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · -- branch
                      by_cases c525 : 0 < a4
                      swap
                      · omega
                      by_cases c526 : 0 < b0
                      swap
                      · omega
                      by_cases c527 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c528 : 0 < a4
                        swap
                        · omega
                        by_cases c529 : 0 < b2
                        swap
                        · omega
                        by_cases c530 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c531 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f532 := pair_fact E (i := 4) (j := 2) rfl rfl c528 c529
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f532
                        by_cases c533 : 0 < a8
                        swap
                        · omega
                        by_cases c534 : 0 < b8
                        swap
                        · omega
                        by_cases c535 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c536 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f537 := pair_fact E (i := 8) (j := 8) rfl rfl c533 c534
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f537
                        omega
                      by_cases c538 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f539 := pair_fact E (i := 4) (j := 0) rfl rfl c525 c526
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f539
                      omega
                    have f540 := pair_fact E (i := 2) (j := 8) rfl rfl c521 c522
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f540
                    omega
                  by_cases c541 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c542 : b0 + b2 < a0 + a2
                  swap
                  · -- branch
                    by_cases c543 : 0 < a2
                    swap
                    · omega
                    by_cases c544 : 0 < b6
                    swap
                    · -- branch
                      by_cases c545 : 0 < a2
                      swap
                      · omega
                      by_cases c546 : 0 < b8
                      swap
                      · omega
                      by_cases c547 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c548 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · -- branch
                        by_cases c549 : 0 < a6
                        swap
                        · omega
                        by_cases c550 : 0 < b0
                        swap
                        · omega
                        by_cases c551 : a0 + a2 + a4 < 0 + b0
                        swap
                        · -- branch
                          by_cases c552 : 0 < a6
                          swap
                          · omega
                          by_cases c553 : 0 < b2
                          swap
                          · omega
                          by_cases c554 : a0 + a2 + a4 < b0 + b2
                          swap
                          · omega
                          by_cases c555 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f556 := pair_fact E (i := 6) (j := 2) rfl rfl c552 c553
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f556
                          by_cases c557 : 0 < a8
                          swap
                          · omega
                          by_cases c558 : 0 < b8
                          swap
                          · omega
                          by_cases c559 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c560 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f561 := pair_fact E (i := 8) (j := 8) rfl rfl c557 c558
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f561
                          omega
                        by_cases c562 : 0 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f563 := pair_fact E (i := 6) (j := 0) rfl rfl c549 c550
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f563
                        omega
                      have f564 := pair_fact E (i := 2) (j := 8) rfl rfl c545 c546
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f564
                      omega
                    by_cases c565 : a0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c566 : b0 + b2 + b4 < a0 + a2
                    swap
                    · -- branch
                      by_cases c567 : 0 < a2
                      swap
                      · omega
                      by_cases c568 : 0 < b8
                      swap
                      · -- branch
                        by_cases c569 : 0 < a8
                        swap
                        · omega
                        by_cases c570 : 0 < b2
                        swap
                        · omega
                        by_cases c571 : a0 + a2 + a4 + a6 < b0 + b2
                        swap
                        · omega
                        by_cases c572 : b0 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f573 := pair_fact E (i := 8) (j := 2) rfl rfl c569 c570
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f573
                        by_cases c574 : 0 < a8
                        swap
                        · omega
                        by_cases c575 : 0 < b4
                        swap
                        · omega
                        by_cases c576 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c577 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f578 := pair_fact E (i := 8) (j := 4) rfl rfl c574 c575
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f578
                        omega
                      by_cases c579 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c580 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · -- branch
                        by_cases c581 : 0 < a2
                        swap
                        · omega
                        by_cases c582 : 0 < b10
                        swap
                        · -- branch
                          by_cases c583 : 0 < a8
                          swap
                          · omega
                          by_cases c584 : 0 < b10
                          swap
                          · -- branch
                            by_cases c585 : 0 < a4
                            swap
                            · -- branch
                              by_cases c586 : 0 < a4
                              swap
                              · -- branch
                                by_cases c587 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c588 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c589 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c590 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c591 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c592 : 0 < b0
                                        swap
                                        · omega
                                        by_cases c593 : a0 + a2 + a4 < 0 + b0
                                        swap
                                        · -- branch
                                          by_cases c594 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c595 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c596 : a0 + a2 + a4 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c597 : b0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f598 := pair_fact E (i := 6) (j := 2) rfl rfl c594 c595
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f598
                                          by_cases c599 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c600 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c601 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c602 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f603 := pair_fact E (i := 8) (j := 4) rfl rfl c599 c600
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f603
                                          omega
                                        by_cases c604 : 0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f605 := pair_fact E (i := 6) (j := 0) rfl rfl c591 c592
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f605
                                        omega
                                      by_cases c606 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c607 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c608 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f609 := pair_fact E (i := 4) (j := 10) rfl rfl c590 c606
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f609
                                      omega
                                    by_cases c610 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c611 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c612 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f613 := pair_fact E (i := 4) (j := 8) rfl rfl c589 c610
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f613
                                    omega
                                  by_cases c614 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c615 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c616 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f617 := pair_fact E (i := 4) (j := 6) rfl rfl c588 c614
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f617
                                  omega
                                by_cases c618 : 0 < b4
                                swap
                                · omega
                                by_cases c619 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c620 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f621 := pair_fact E (i := 4) (j := 4) rfl rfl c587 c618
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f621
                                omega
                              by_cases c622 : 0 < b2
                              swap
                              · omega
                              by_cases c623 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c624 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f625 := pair_fact E (i := 4) (j := 2) rfl rfl c586 c622
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f625
                              omega
                            by_cases c626 : 0 < b0
                            swap
                            · omega
                            by_cases c627 : a0 + a2 < 0 + b0
                            swap
                            · -- branch
                              by_cases c628 : 0 < a4
                              swap
                              · omega
                              by_cases c629 : 0 < b2
                              swap
                              · omega
                              by_cases c630 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c631 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f632 := pair_fact E (i := 4) (j := 2) rfl rfl c628 c629
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f632
                              by_cases c633 : 0 < a4
                              swap
                              · omega
                              by_cases c634 : 0 < b4
                              swap
                              · omega
                              by_cases c635 : a0 + a2 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c636 : b0 + b2 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c637 : 0 < a4
                                swap
                                · omega
                                by_cases c638 : 0 < b6
                                swap
                                · omega
                                by_cases c639 : a0 + a2 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c640 : b0 + b2 + b4 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c641 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c642 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c643 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c644 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c645 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c646 : 0 < b10
                                    swap
                                    · -- branch
                                      by_cases c647 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c648 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c649 : a0 + a2 + a4 + a6 < b0 + b2 + b4
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
                                        omega
                                      by_cases c655 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f656 := pair_fact E (i := 8) (j := 4) rfl rfl c647 c648
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f656
                                      omega
                                    by_cases c657 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c658 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f659 := pair_fact E (i := 4) (j := 10) rfl rfl c645 c646
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f659
                                    omega
                                  have f660 := pair_fact E (i := 4) (j := 8) rfl rfl c641 c642
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f660
                                  omega
                                have f661 := pair_fact E (i := 4) (j := 6) rfl rfl c637 c638
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f661
                                omega
                              have f662 := pair_fact E (i := 4) (j := 4) rfl rfl c633 c634
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f662
                              omega
                            by_cases c663 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f664 := pair_fact E (i := 4) (j := 0) rfl rfl c585 c626
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f664
                            omega
                          by_cases c665 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c666 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f667 := pair_fact E (i := 8) (j := 10) rfl rfl c583 c584
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f667
                          omega
                        by_cases c668 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c669 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                        swap
                        · -- branch
                          by_cases c670 : 0 < a8
                          swap
                          · omega
                          by_cases c671 : 0 < b10
                          swap
                          · omega
                          by_cases c672 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c673 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                          swap
                          · -- branch
                            by_cases c674 : 0 < a10
                            swap
                            · omega
                            by_cases c675 : 0 < b0
                            swap
                            · omega
                            by_cases c676 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                            swap
                            · -- branch
                              by_cases c677 : 0 < a10
                              swap
                              · omega
                              by_cases c678 : 0 < b2
                              swap
                              · omega
                              by_cases c679 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                              swap
                              · -- branch
                                by_cases c680 : 0 < a10
                                swap
                                · omega
                                by_cases c681 : 0 < b4
                                swap
                                · omega
                                by_cases c682 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                swap
                                · -- branch
                                  by_cases c683 : 0 < a10
                                  swap
                                  · omega
                                  by_cases c684 : 0 < b10
                                  swap
                                  · omega
                                  by_cases c685 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8 + b10
                                  swap
                                  · omega
                                  by_cases c686 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8 + a10
                                  swap
                                  · omega
                                  have f687 := pair_fact E (i := 10) (j := 10) rfl rfl c683 c684
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f687
                                  by_cases c688 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c689 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c690 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c691 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c692 : 0 < a4
                                          swap
                                          · -- branch
                                            by_cases c693 : 0 < a4
                                            swap
                                            · -- branch
                                              by_cases c694 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c695 : 0 < b0
                                              swap
                                              · omega
                                              by_cases c696 : a0 + a2 + a4 < 0 + b0
                                              swap
                                              · -- branch
                                                by_cases c697 : 0 < a6
                                                swap
                                                · omega
                                                by_cases c698 : 0 < b2
                                                swap
                                                · omega
                                                by_cases c699 : a0 + a2 + a4 < b0 + b2
                                                swap
                                                · omega
                                                by_cases c700 : b0 < a0 + a2 + a4 + a6
                                                swap
                                                · omega
                                                have f701 := pair_fact E (i := 6) (j := 2) rfl rfl c697 c698
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f701
                                                by_cases c702 : 0 < a8
                                                swap
                                                · omega
                                                by_cases c703 : 0 < b4
                                                swap
                                                · omega
                                                by_cases c704 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                                swap
                                                · omega
                                                by_cases c705 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                                swap
                                                · omega
                                                have f706 := pair_fact E (i := 8) (j := 4) rfl rfl c702 c703
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f706
                                                omega
                                              by_cases c707 : 0 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f708 := pair_fact E (i := 6) (j := 0) rfl rfl c694 c695
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f708
                                              omega
                                            by_cases c709 : 0 < b10
                                            swap
                                            · omega
                                            by_cases c710 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                            swap
                                            · omega
                                            by_cases c711 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                            swap
                                            · omega
                                            have f712 := pair_fact E (i := 4) (j := 10) rfl rfl c693 c709
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f712
                                            omega
                                          by_cases c713 : 0 < b8
                                          swap
                                          · omega
                                          by_cases c714 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                          swap
                                          · omega
                                          by_cases c715 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                          swap
                                          · omega
                                          have f716 := pair_fact E (i := 4) (j := 8) rfl rfl c692 c713
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f716
                                          omega
                                        by_cases c717 : 0 < b6
                                        swap
                                        · omega
                                        by_cases c718 : a0 + a2 < b0 + b2 + b4 + b6
                                        swap
                                        · omega
                                        by_cases c719 : b0 + b2 + b4 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f720 := pair_fact E (i := 4) (j := 6) rfl rfl c691 c717
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f720
                                        omega
                                      by_cases c721 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c722 : a0 + a2 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c723 : b0 + b2 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f724 := pair_fact E (i := 4) (j := 4) rfl rfl c690 c721
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f724
                                      omega
                                    by_cases c725 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c726 : a0 + a2 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c727 : b0 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f728 := pair_fact E (i := 4) (j := 2) rfl rfl c689 c725
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f728
                                    omega
                                  by_cases c729 : 0 < b0
                                  swap
                                  · omega
                                  by_cases c730 : a0 + a2 < 0 + b0
                                  swap
                                  · -- branch
                                    by_cases c731 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c732 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c733 : a0 + a2 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c734 : b0 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f735 := pair_fact E (i := 4) (j := 2) rfl rfl c731 c732
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f735
                                    by_cases c736 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c737 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c738 : a0 + a2 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c739 : b0 + b2 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c740 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c741 : 0 < b6
                                      swap
                                      · omega
                                      by_cases c742 : a0 + a2 < b0 + b2 + b4 + b6
                                      swap
                                      · omega
                                      by_cases c743 : b0 + b2 + b4 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c744 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c745 : 0 < b8
                                        swap
                                        · omega
                                        by_cases c746 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                        swap
                                        · omega
                                        by_cases c747 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                        swap
                                        · -- branch
                                          by_cases c748 : 0 < a4
                                          swap
                                          · omega
                                          by_cases c749 : 0 < b10
                                          swap
                                          · omega
                                          by_cases c750 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                          swap
                                          · omega
                                          by_cases c751 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                          swap
                                          · -- branch
                                            by_cases c752 : 0 < a8
                                            swap
                                            · omega
                                            by_cases c753 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c754 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                            swap
                                            · -- branch
                                              by_cases c755 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c756 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c757 : a0 + a2 + a4 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c758 : b0 + b2 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f759 := pair_fact E (i := 6) (j := 4) rfl rfl c755 c756
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f759
                                              omega
                                            by_cases c760 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f761 := pair_fact E (i := 8) (j := 4) rfl rfl c752 c753
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f761
                                            omega
                                          have f762 := pair_fact E (i := 4) (j := 10) rfl rfl c748 c749
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f762
                                          omega
                                        have f763 := pair_fact E (i := 4) (j := 8) rfl rfl c744 c745
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f763
                                        omega
                                      have f764 := pair_fact E (i := 4) (j := 6) rfl rfl c740 c741
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f764
                                      omega
                                    have f765 := pair_fact E (i := 4) (j := 4) rfl rfl c736 c737
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f765
                                    omega
                                  by_cases c766 : 0 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f767 := pair_fact E (i := 4) (j := 0) rfl rfl c688 c729
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f767
                                  omega
                                by_cases c768 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f769 := pair_fact E (i := 10) (j := 4) rfl rfl c680 c681
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f769
                                omega
                              by_cases c770 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                              swap
                              · omega
                              have f771 := pair_fact E (i := 10) (j := 2) rfl rfl c677 c678
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f771
                              omega
                            by_cases c772 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f773 := pair_fact E (i := 10) (j := 0) rfl rfl c674 c675
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f773
                            omega
                          have f774 := pair_fact E (i := 8) (j := 10) rfl rfl c670 c671
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f774
                          omega
                        have f775 := pair_fact E (i := 2) (j := 10) rfl rfl c581 c582
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f775
                        omega
                      have f776 := pair_fact E (i := 2) (j := 8) rfl rfl c567 c568
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f776
                      omega
                    have f777 := pair_fact E (i := 2) (j := 6) rfl rfl c543 c544
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f777
                    omega
                  have f778 := pair_fact E (i := 2) (j := 4) rfl rfl c519 c520
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f778
                  omega
                by_cases c779 : 0 < a0 + a2 + a4 + a6 + a8
                swap
                · omega
                have f780 := pair_fact E (i := 8) (j := 0) rfl rfl c516 c517
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f780
                omega
              have f781 := pair_fact E (i := 2) (j := 2) rfl rfl c497 c498
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f781
              omega
            by_cases c782 : 0 < b10
            swap
            · omega
            by_cases c783 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c784 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · omega
            have f785 := pair_fact E (i := 0) (j := 10) rfl rfl c6 c782
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f785
            omega
          by_cases c786 : 0 < b8
          swap
          · omega
          by_cases c787 : 0 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c788 : b0 + b2 + b4 + b6 < 0 + a0
          swap
          · omega
          have f789 := pair_fact E (i := 0) (j := 8) rfl rfl c5 c786
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f789
          omega
        by_cases c790 : 0 < b6
        swap
        · omega
        by_cases c791 : 0 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c792 : b0 + b2 + b4 < 0 + a0
        swap
        · omega
        have f793 := pair_fact E (i := 0) (j := 6) rfl rfl c4 c790
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f793
        omega
      by_cases c794 : 0 < b4
      swap
      · omega
      by_cases c795 : 0 < b0 + b2 + b4
      swap
      · omega
      by_cases c796 : b0 + b2 < 0 + a0
      swap
      · omega
      have f797 := pair_fact E (i := 0) (j := 4) rfl rfl c3 c794
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f797
      omega
    by_cases c798 : 0 < b2
    swap
    · omega
    by_cases c799 : 0 < b0 + b2
    swap
    · omega
    by_cases c800 : b0 < 0 + a0
    swap
    · omega
    have f801 := pair_fact E (i := 0) (j := 2) rfl rfl c2 c798
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f801
    omega
  by_cases c802 : 0 < b0
  swap
  · -- branch
    by_cases c803 : 0 < a0
    swap
    · omega
    by_cases c804 : 0 < b2
    swap
    · -- branch
      by_cases c805 : 0 < a0
      swap
      · omega
      by_cases c806 : 0 < b4
      swap
      · -- branch
        by_cases c807 : 0 < a0
        swap
        · omega
        by_cases c808 : 0 < b6
        swap
        · omega
        by_cases c809 : 0 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c810 : b0 + b2 + b4 < 0 + a0
        swap
        · omega
        have f811 := pair_fact E (i := 0) (j := 6) rfl rfl c807 c808
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f811
        omega
      by_cases c812 : 0 < b0 + b2 + b4
      swap
      · omega
      by_cases c813 : b0 + b2 < 0 + a0
      swap
      · omega
      have f814 := pair_fact E (i := 0) (j := 4) rfl rfl c805 c806
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f814
      omega
    by_cases c815 : 0 < b0 + b2
    swap
    · omega
    by_cases c816 : b0 < 0 + a0
    swap
    · omega
    have f817 := pair_fact E (i := 0) (j := 2) rfl rfl c803 c804
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f817
    by_cases c818 : 0 < a0
    swap
    · omega
    by_cases c819 : 0 < b4
    swap
    · -- branch
      by_cases c820 : 0 < a0
      swap
      · omega
      by_cases c821 : 0 < b8
      swap
      · omega
      by_cases c822 : 0 < b0 + b2 + b4 + b6 + b8
      swap
      · omega
      by_cases c823 : b0 + b2 + b4 + b6 < 0 + a0
      swap
      · -- branch
        by_cases c824 : 0 < a4
        swap
        · omega
        by_cases c825 : 0 < b0
        swap
        · -- branch
          by_cases c826 : 0 < a4
          swap
          · omega
          by_cases c827 : 0 < b2
          swap
          · omega
          by_cases c828 : a0 + a2 < b0 + b2
          swap
          · -- branch
            by_cases c829 : 0 < a2
            swap
            · omega
            by_cases c830 : 0 < b0
            swap
            · -- branch
              by_cases c831 : 0 < a2
              swap
              · omega
              by_cases c832 : 0 < b2
              swap
              · omega
              by_cases c833 : a0 < b0 + b2
              swap
              · -- branch
                by_cases c834 : 0 < a2
                swap
                · omega
                by_cases c835 : 0 < b4
                swap
                · -- branch
                  by_cases c836 : 0 < a4
                  swap
                  · omega
                  by_cases c837 : 0 < b4
                  swap
                  · -- branch
                    by_cases c838 : 0 < a4
                    swap
                    · omega
                    by_cases c839 : 0 < b8
                    swap
                    · omega
                    by_cases c840 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c841 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                    swap
                    · omega
                    have f842 := pair_fact E (i := 4) (j := 8) rfl rfl c838 c839
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f842
                    by_cases c843 : 0 < a2
                    swap
                    · omega
                    by_cases c844 : 0 < b8
                    swap
                    · omega
                    by_cases c845 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c846 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · -- branch
                      by_cases c847 : 0 < a2
                      swap
                      · omega
                      by_cases c848 : 0 < b6
                      swap
                      · omega
                      by_cases c849 : a0 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c850 : b0 + b2 + b4 < a0 + a2
                      swap
                      · omega
                      have f851 := pair_fact E (i := 2) (j := 6) rfl rfl c847 c848
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f851
                      omega
                    have f852 := pair_fact E (i := 2) (j := 8) rfl rfl c843 c844
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f852
                    omega
                  by_cases c853 : a0 + a2 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c854 : b0 + b2 < a0 + a2 + a4
                  swap
                  · omega
                  have f855 := pair_fact E (i := 4) (j := 4) rfl rfl c836 c837
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f855
                  omega
                by_cases c856 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c857 : b0 + b2 < a0 + a2
                swap
                · omega
                have f858 := pair_fact E (i := 2) (j := 4) rfl rfl c834 c835
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f858
                omega
              by_cases c859 : b0 < a0 + a2
              swap
              · omega
              have f860 := pair_fact E (i := 2) (j := 2) rfl rfl c831 c832
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f860
              omega
            by_cases c861 : a0 < 0 + b0
            swap
            · omega
            by_cases c862 : 0 < a0 + a2
            swap
            · omega
            have f863 := pair_fact E (i := 2) (j := 0) rfl rfl c829 c830
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f863
            omega
          by_cases c864 : b0 < a0 + a2 + a4
          swap
          · omega
          have f865 := pair_fact E (i := 4) (j := 2) rfl rfl c826 c827
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f865
          omega
        by_cases c866 : a0 + a2 < 0 + b0
        swap
        · omega
        by_cases c867 : 0 < a0 + a2 + a4
        swap
        · omega
        have f868 := pair_fact E (i := 4) (j := 0) rfl rfl c824 c825
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f868
        omega
      have f869 := pair_fact E (i := 0) (j := 8) rfl rfl c820 c821
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f869
      omega
    by_cases c870 : 0 < b0 + b2 + b4
    swap
    · omega
    by_cases c871 : b0 + b2 < 0 + a0
    swap
    · -- branch
      by_cases c872 : 0 < a0
      swap
      · omega
      by_cases c873 : 0 < b6
      swap
      · -- branch
        by_cases c874 : 0 < a0
        swap
        · omega
        by_cases c875 : 0 < b8
        swap
        · omega
        by_cases c876 : 0 < b0 + b2 + b4 + b6 + b8
        swap
        · omega
        by_cases c877 : b0 + b2 + b4 + b6 < 0 + a0
        swap
        · -- branch
          by_cases c878 : 0 < a6
          swap
          · omega
          by_cases c879 : 0 < b0
          swap
          · -- branch
            by_cases c880 : 0 < a6
            swap
            · omega
            by_cases c881 : 0 < b2
            swap
            · omega
            by_cases c882 : a0 + a2 + a4 < b0 + b2
            swap
            · -- branch
              by_cases c883 : 0 < a2
              swap
              · omega
              by_cases c884 : 0 < b0
              swap
              · -- branch
                by_cases c885 : 0 < a2
                swap
                · omega
                by_cases c886 : 0 < b2
                swap
                · omega
                by_cases c887 : a0 < b0 + b2
                swap
                · -- branch
                  by_cases c888 : 0 < a2
                  swap
                  · omega
                  by_cases c889 : 0 < b4
                  swap
                  · omega
                  by_cases c890 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c891 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f892 := pair_fact E (i := 2) (j := 4) rfl rfl c888 c889
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f892
                  by_cases c893 : 0 < a6
                  swap
                  · omega
                  by_cases c894 : 0 < b8
                  swap
                  · omega
                  by_cases c895 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c896 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                  swap
                  · omega
                  have f897 := pair_fact E (i := 6) (j := 8) rfl rfl c893 c894
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f897
                  omega
                by_cases c898 : b0 < a0 + a2
                swap
                · omega
                have f899 := pair_fact E (i := 2) (j := 2) rfl rfl c885 c886
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f899
                omega
              by_cases c900 : a0 < 0 + b0
              swap
              · omega
              by_cases c901 : 0 < a0 + a2
              swap
              · omega
              have f902 := pair_fact E (i := 2) (j := 0) rfl rfl c883 c884
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f902
              omega
            by_cases c903 : b0 < a0 + a2 + a4 + a6
            swap
            · omega
            have f904 := pair_fact E (i := 6) (j := 2) rfl rfl c880 c881
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f904
            omega
          by_cases c905 : a0 + a2 + a4 < 0 + b0
          swap
          · omega
          by_cases c906 : 0 < a0 + a2 + a4 + a6
          swap
          · omega
          have f907 := pair_fact E (i := 6) (j := 0) rfl rfl c878 c879
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f907
          omega
        have f908 := pair_fact E (i := 0) (j := 8) rfl rfl c874 c875
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f908
        omega
      by_cases c909 : 0 < b0 + b2 + b4 + b6
      swap
      · omega
      by_cases c910 : b0 + b2 + b4 < 0 + a0
      swap
      · -- branch
        by_cases c911 : 0 < a0
        swap
        · omega
        by_cases c912 : 0 < b8
        swap
        · -- branch
          by_cases c913 : 0 < a8
          swap
          · omega
          by_cases c914 : 0 < b2
          swap
          · omega
          by_cases c915 : a0 + a2 + a4 + a6 < b0 + b2
          swap
          · omega
          by_cases c916 : b0 < a0 + a2 + a4 + a6 + a8
          swap
          · omega
          have f917 := pair_fact E (i := 8) (j := 2) rfl rfl c913 c914
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f917
          omega
        by_cases c918 : 0 < b0 + b2 + b4 + b6 + b8
        swap
        · omega
        by_cases c919 : b0 + b2 + b4 + b6 < 0 + a0
        swap
        · -- branch
          by_cases c920 : 0 < a0
          swap
          · omega
          by_cases c921 : 0 < b10
          swap
          · -- branch
            by_cases c922 : 0 < a10
            swap
            · -- branch
              by_cases c923 : 0 < a8
              swap
              · omega
              by_cases c924 : 0 < b0
              swap
              · -- branch
                by_cases c925 : 0 < a8
                swap
                · omega
                by_cases c926 : 0 < b2
                swap
                · omega
                by_cases c927 : a0 + a2 + a4 + a6 < b0 + b2
                swap
                · -- branch
                  by_cases c928 : 0 < a8
                  swap
                  · omega
                  by_cases c929 : 0 < b8
                  swap
                  · omega
                  by_cases c930 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c931 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                  swap
                  · omega
                  have f932 := pair_fact E (i := 8) (j := 8) rfl rfl c928 c929
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f932
                  by_cases c933 : 0 < a8
                  swap
                  · omega
                  by_cases c934 : 0 < b10
                  swap
                  · -- branch
                    by_cases c935 : 0 < a10
                    swap
                    · -- branch
                      by_cases c936 : 0 < a10
                      swap
                      · -- branch
                        by_cases c937 : 0 < a10
                        swap
                        · -- branch
                          by_cases c938 : 0 < a10
                          swap
                          · -- branch
                            by_cases c939 : 0 < a10
                            swap
                            · -- branch
                              by_cases c940 : 0 < a2
                              swap
                              · -- branch
                                by_cases c941 : 0 < a4
                                swap
                                · omega
                                by_cases c942 : 0 < b2
                                swap
                                · omega
                                by_cases c943 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c944 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f945 := pair_fact E (i := 4) (j := 2) rfl rfl c941 c942
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f945
                                omega
                              by_cases c946 : 0 < b0
                              swap
                              · -- branch
                                by_cases c947 : 0 < a2
                                swap
                                · omega
                                by_cases c948 : 0 < b2
                                swap
                                · omega
                                by_cases c949 : a0 < b0 + b2
                                swap
                                · -- branch
                                  by_cases c950 : 0 < a2
                                  swap
                                  · omega
                                  by_cases c951 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c952 : a0 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c953 : b0 + b2 < a0 + a2
                                  swap
                                  · omega
                                  have f954 := pair_fact E (i := 2) (j := 4) rfl rfl c950 c951
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f954
                                  omega
                                by_cases c955 : b0 < a0 + a2
                                swap
                                · omega
                                have f956 := pair_fact E (i := 2) (j := 2) rfl rfl c947 c948
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f956
                                omega
                              by_cases c957 : a0 < 0 + b0
                              swap
                              · omega
                              by_cases c958 : 0 < a0 + a2
                              swap
                              · omega
                              have f959 := pair_fact E (i := 2) (j := 0) rfl rfl c940 c946
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f959
                              omega
                            by_cases c960 : 0 < b10
                            swap
                            · omega
                            by_cases c961 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c962 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f963 := pair_fact E (i := 10) (j := 10) rfl rfl c939 c960
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f963
                            omega
                          by_cases c964 : 0 < b6
                          swap
                          · omega
                          by_cases c965 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c966 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                          swap
                          · omega
                          have f967 := pair_fact E (i := 10) (j := 6) rfl rfl c938 c964
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f967
                          omega
                        by_cases c968 : 0 < b4
                        swap
                        · omega
                        by_cases c969 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c970 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                        swap
                        · omega
                        have f971 := pair_fact E (i := 10) (j := 4) rfl rfl c937 c968
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f971
                        omega
                      by_cases c972 : 0 < b2
                      swap
                      · omega
                      by_cases c973 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                      swap
                      · omega
                      by_cases c974 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f975 := pair_fact E (i := 10) (j := 2) rfl rfl c936 c972
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f975
                      omega
                    by_cases c976 : 0 < b0
                    swap
                    · omega
                    by_cases c977 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                    swap
                    · omega
                    by_cases c978 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                    swap
                    · omega
                    have f979 := pair_fact E (i := 10) (j := 0) rfl rfl c935 c976
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f979
                    omega
                  by_cases c980 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c981 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                  swap
                  · omega
                  have f982 := pair_fact E (i := 8) (j := 10) rfl rfl c933 c934
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f982
                  omega
                by_cases c983 : b0 < a0 + a2 + a4 + a6 + a8
                swap
                · omega
                have f984 := pair_fact E (i := 8) (j := 2) rfl rfl c925 c926
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f984
                omega
              by_cases c985 : a0 + a2 + a4 + a6 < 0 + b0
              swap
              · omega
              by_cases c986 : 0 < a0 + a2 + a4 + a6 + a8
              swap
              · omega
              have f987 := pair_fact E (i := 8) (j := 0) rfl rfl c923 c924
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f987
              omega
            by_cases c988 : 0 < b8
            swap
            · omega
            by_cases c989 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
            swap
            · omega
            by_cases c990 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
            swap
            · omega
            have f991 := pair_fact E (i := 10) (j := 8) rfl rfl c922 c988
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f991
            omega
          by_cases c992 : 0 < b0 + b2 + b4 + b6 + b8 + b10
          swap
          · omega
          by_cases c993 : b0 + b2 + b4 + b6 + b8 < 0 + a0
          swap
          · -- branch
            by_cases c994 : 0 < a2
            swap
            · -- branch
              by_cases c995 : 0 < a2
              swap
              · -- branch
                by_cases c996 : 0 < a2
                swap
                · -- branch
                  by_cases c997 : 0 < a2
                  swap
                  · -- branch
                    by_cases c998 : 0 < a2
                    swap
                    · -- branch
                      by_cases c999 : 0 < a2
                      swap
                      · -- branch
                        by_cases c1000 : 0 < a4
                        swap
                        · -- branch
                          by_cases c1001 : 0 < a6
                          swap
                          · omega
                          by_cases c1002 : 0 < b2
                          swap
                          · omega
                          by_cases c1003 : a0 + a2 + a4 < b0 + b2
                          swap
                          · omega
                          by_cases c1004 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f1005 := pair_fact E (i := 6) (j := 2) rfl rfl c1001 c1002
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1005
                          omega
                        by_cases c1006 : 0 < b2
                        swap
                        · omega
                        by_cases c1007 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c1008 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f1009 := pair_fact E (i := 4) (j := 2) rfl rfl c1000 c1006
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1009
                        omega
                      by_cases c1010 : 0 < b10
                      swap
                      · omega
                      by_cases c1011 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                      swap
                      · omega
                      by_cases c1012 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                      swap
                      · omega
                      have f1013 := pair_fact E (i := 2) (j := 10) rfl rfl c999 c1010
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1013
                      omega
                    by_cases c1014 : 0 < b8
                    swap
                    · omega
                    by_cases c1015 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c1016 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · omega
                    have f1017 := pair_fact E (i := 2) (j := 8) rfl rfl c998 c1014
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1017
                    omega
                  by_cases c1018 : 0 < b6
                  swap
                  · omega
                  by_cases c1019 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c1020 : b0 + b2 + b4 < a0 + a2
                  swap
                  · omega
                  have f1021 := pair_fact E (i := 2) (j := 6) rfl rfl c997 c1018
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1021
                  omega
                by_cases c1022 : 0 < b4
                swap
                · omega
                by_cases c1023 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c1024 : b0 + b2 < a0 + a2
                swap
                · omega
                have f1025 := pair_fact E (i := 2) (j := 4) rfl rfl c996 c1022
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1025
                omega
              by_cases c1026 : 0 < b2
              swap
              · omega
              by_cases c1027 : a0 < b0 + b2
              swap
              · omega
              by_cases c1028 : b0 < a0 + a2
              swap
              · omega
              have f1029 := pair_fact E (i := 2) (j := 2) rfl rfl c995 c1026
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1029
              omega
            by_cases c1030 : 0 < b0
            swap
            · -- branch
              by_cases c1031 : 0 < a2
              swap
              · omega
              by_cases c1032 : 0 < b2
              swap
              · omega
              by_cases c1033 : a0 < b0 + b2
              swap
              · -- branch
                by_cases c1034 : 0 < a2
                swap
                · omega
                by_cases c1035 : 0 < b4
                swap
                · omega
                by_cases c1036 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c1037 : b0 + b2 < a0 + a2
                swap
                · omega
                have f1038 := pair_fact E (i := 2) (j := 4) rfl rfl c1034 c1035
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1038
                by_cases c1039 : 0 < a2
                swap
                · omega
                by_cases c1040 : 0 < b6
                swap
                · omega
                by_cases c1041 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c1042 : b0 + b2 + b4 < a0 + a2
                swap
                · omega
                have f1043 := pair_fact E (i := 2) (j := 6) rfl rfl c1039 c1040
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1043
                by_cases c1044 : 0 < a2
                swap
                · omega
                by_cases c1045 : 0 < b10
                swap
                · omega
                by_cases c1046 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                swap
                · omega
                by_cases c1047 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                swap
                · -- branch
                  by_cases c1048 : 0 < a2
                  swap
                  · omega
                  by_cases c1049 : 0 < b8
                  swap
                  · omega
                  by_cases c1050 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c1051 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · -- branch
                    by_cases c1052 : 0 < a8
                    swap
                    · omega
                    by_cases c1053 : 0 < b8
                    swap
                    · omega
                    by_cases c1054 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c1055 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                    swap
                    · omega
                    have f1056 := pair_fact E (i := 8) (j := 8) rfl rfl c1052 c1053
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1056
                    omega
                  have f1057 := pair_fact E (i := 2) (j := 8) rfl rfl c1048 c1049
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1057
                  by_cases c1058 : 0 < a4
                  swap
                  · -- branch
                    by_cases c1059 : 0 < a6
                    swap
                    · omega
                    by_cases c1060 : 0 < b8
                    swap
                    · omega
                    by_cases c1061 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c1062 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f1063 := pair_fact E (i := 6) (j := 8) rfl rfl c1059 c1060
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1063
                    omega
                  by_cases c1064 : 0 < b8
                  swap
                  · omega
                  by_cases c1065 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c1066 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                  swap
                  · omega
                  have f1067 := pair_fact E (i := 4) (j := 8) rfl rfl c1058 c1064
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1067
                  omega
                have f1068 := pair_fact E (i := 2) (j := 10) rfl rfl c1044 c1045
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1068
                omega
              by_cases c1069 : b0 < a0 + a2
              swap
              · omega
              have f1070 := pair_fact E (i := 2) (j := 2) rfl rfl c1031 c1032
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1070
              omega
            by_cases c1071 : a0 < 0 + b0
            swap
            · omega
            by_cases c1072 : 0 < a0 + a2
            swap
            · omega
            have f1073 := pair_fact E (i := 2) (j := 0) rfl rfl c994 c1030
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1073
            omega
          have f1074 := pair_fact E (i := 0) (j := 10) rfl rfl c920 c921
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1074
          omega
        have f1075 := pair_fact E (i := 0) (j := 8) rfl rfl c911 c912
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1075
        omega
      have f1076 := pair_fact E (i := 0) (j := 6) rfl rfl c872 c873
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1076
      omega
    have f1077 := pair_fact E (i := 0) (j := 4) rfl rfl c818 c819
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1077
    omega
  by_cases c1078 : 0 < 0 + b0
  swap
  · omega
  by_cases c1079 : 0 < 0 + a0
  swap
  · omega
  have f1080 := pair_fact E (i := 0) (j := 0) rfl rfl c1 c802
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1080
  by_cases c1081 : 0 < a0
  swap
  · omega
  by_cases c1082 : 0 < b4
  swap
  · -- branch
    by_cases c1083 : 0 < a0
    swap
    · omega
    by_cases c1084 : 0 < b8
    swap
    · omega
    by_cases c1085 : 0 < b0 + b2 + b4 + b6 + b8
    swap
    · omega
    by_cases c1086 : b0 + b2 + b4 + b6 < 0 + a0
    swap
    · -- branch
      by_cases c1087 : 0 < a4
      swap
      · omega
      by_cases c1088 : 0 < b0
      swap
      · omega
      by_cases c1089 : a0 + a2 < 0 + b0
      swap
      · -- branch
        by_cases c1090 : 0 < a4
        swap
        · omega
        by_cases c1091 : 0 < b4
        swap
        · -- branch
          by_cases c1092 : 0 < a0
          swap
          · omega
          by_cases c1093 : 0 < b6
          swap
          · -- branch
            by_cases c1094 : 0 < a4
            swap
            · omega
            by_cases c1095 : 0 < b6
            swap
            · -- branch
              by_cases c1096 : 0 < a6
              swap
              · omega
              by_cases c1097 : 0 < b0
              swap
              · omega
              by_cases c1098 : a0 + a2 + a4 < 0 + b0
              swap
              · -- branch
                by_cases c1099 : 0 < a6
                swap
                · omega
                by_cases c1100 : 0 < b4
                swap
                · -- branch
                  by_cases c1101 : 0 < a6
                  swap
                  · omega
                  by_cases c1102 : 0 < b6
                  swap
                  · -- branch
                    by_cases c1103 : 0 < a0
                    swap
                    · omega
                    by_cases c1104 : 0 < b2
                    swap
                    · omega
                    by_cases c1105 : 0 < b0 + b2
                    swap
                    · omega
                    by_cases c1106 : b0 < 0 + a0
                    swap
                    · -- branch
                      by_cases c1107 : 0 < a0
                      swap
                      · omega
                      by_cases c1108 : 0 < b10
                      swap
                      · -- branch
                        by_cases c1109 : 0 < a4
                        swap
                        · omega
                        by_cases c1110 : 0 < b10
                        swap
                        · -- branch
                          by_cases c1111 : 0 < a6
                          swap
                          · omega
                          by_cases c1112 : 0 < b10
                          swap
                          · -- branch
                            by_cases c1113 : 0 < a2
                            swap
                            · -- branch
                              by_cases c1114 : 0 < a2
                              swap
                              · -- branch
                                by_cases c1115 : 0 < a2
                                swap
                                · -- branch
                                  by_cases c1116 : 0 < a2
                                  swap
                                  · -- branch
                                    by_cases c1117 : 0 < a2
                                    swap
                                    · -- branch
                                      by_cases c1118 : 0 < a2
                                      swap
                                      · -- branch
                                        by_cases c1119 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c1120 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c1121 : a0 + a2 < b0 + b2
                                        swap
                                        · omega
                                        by_cases c1122 : b0 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f1123 := pair_fact E (i := 4) (j := 2) rfl rfl c1119 c1120
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1123
                                        by_cases c1124 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c1125 : 0 < b8
                                        swap
                                        · omega
                                        by_cases c1126 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                        swap
                                        · omega
                                        by_cases c1127 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f1128 := pair_fact E (i := 8) (j := 8) rfl rfl c1124 c1125
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1128
                                        omega
                                      by_cases c1129 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c1130 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c1131 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                                      swap
                                      · omega
                                      have f1132 := pair_fact E (i := 2) (j := 10) rfl rfl c1118 c1129
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1132
                                      omega
                                    by_cases c1133 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c1134 : a0 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c1135 : b0 + b2 + b4 + b6 < a0 + a2
                                    swap
                                    · omega
                                    have f1136 := pair_fact E (i := 2) (j := 8) rfl rfl c1117 c1133
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1136
                                    omega
                                  by_cases c1137 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c1138 : a0 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c1139 : b0 + b2 + b4 < a0 + a2
                                  swap
                                  · omega
                                  have f1140 := pair_fact E (i := 2) (j := 6) rfl rfl c1116 c1137
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1140
                                  omega
                                by_cases c1141 : 0 < b2
                                swap
                                · omega
                                by_cases c1142 : a0 < b0 + b2
                                swap
                                · omega
                                by_cases c1143 : b0 < a0 + a2
                                swap
                                · omega
                                have f1144 := pair_fact E (i := 2) (j := 2) rfl rfl c1115 c1141
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1144
                                omega
                              by_cases c1145 : 0 < b0
                              swap
                              · omega
                              by_cases c1146 : a0 < 0 + b0
                              swap
                              · omega
                              by_cases c1147 : 0 < a0 + a2
                              swap
                              · omega
                              have f1148 := pair_fact E (i := 2) (j := 0) rfl rfl c1114 c1145
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1148
                              omega
                            by_cases c1149 : 0 < b4
                            swap
                            · -- branch
                              by_cases c1150 : 0 < a2
                              swap
                              · omega
                              by_cases c1151 : 0 < b6
                              swap
                              · -- branch
                                by_cases c1152 : 0 < a2
                                swap
                                · omega
                                by_cases c1153 : 0 < b10
                                swap
                                · -- branch
                                  by_cases c1154 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1155 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c1156 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c1157 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1158 := pair_fact E (i := 6) (j := 8) rfl rfl c1154 c1155
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1158
                                  by_cases c1159 : 0 < a2
                                  swap
                                  · omega
                                  by_cases c1160 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c1161 : a0 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c1162 : b0 + b2 + b4 + b6 < a0 + a2
                                  swap
                                  · -- branch
                                    by_cases c1163 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1164 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c1165 : a0 + a2 < b0 + b2
                                    swap
                                    · -- branch
                                      by_cases c1166 : 0 < a10
                                      swap
                                      · omega
                                      by_cases c1167 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c1168 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c1169 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                      swap
                                      · omega
                                      have f1170 := pair_fact E (i := 10) (j := 8) rfl rfl c1166 c1167
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1170
                                      omega
                                    by_cases c1171 : b0 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f1172 := pair_fact E (i := 4) (j := 2) rfl rfl c1163 c1164
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1172
                                    omega
                                  have f1173 := pair_fact E (i := 2) (j := 8) rfl rfl c1159 c1160
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1173
                                  omega
                                by_cases c1174 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c1175 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                                swap
                                · omega
                                have f1176 := pair_fact E (i := 2) (j := 10) rfl rfl c1152 c1153
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1176
                                omega
                              by_cases c1177 : a0 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c1178 : b0 + b2 + b4 < a0 + a2
                              swap
                              · omega
                              have f1179 := pair_fact E (i := 2) (j := 6) rfl rfl c1150 c1151
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1179
                              omega
                            by_cases c1180 : a0 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c1181 : b0 + b2 < a0 + a2
                            swap
                            · omega
                            have f1182 := pair_fact E (i := 2) (j := 4) rfl rfl c1113 c1149
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1182
                            omega
                          by_cases c1183 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c1184 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f1185 := pair_fact E (i := 6) (j := 10) rfl rfl c1111 c1112
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1185
                          omega
                        by_cases c1186 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c1187 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                        swap
                        · omega
                        have f1188 := pair_fact E (i := 4) (j := 10) rfl rfl c1109 c1110
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1188
                        omega
                      by_cases c1189 : 0 < b0 + b2 + b4 + b6 + b8 + b10
                      swap
                      · omega
                      by_cases c1190 : b0 + b2 + b4 + b6 + b8 < 0 + a0
                      swap
                      · -- branch
                        by_cases c1191 : 0 < a4
                        swap
                        · omega
                        by_cases c1192 : 0 < b10
                        swap
                        · omega
                        by_cases c1193 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c1194 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                        swap
                        · -- branch
                          by_cases c1195 : 0 < a2
                          swap
                          · -- branch
                            by_cases c1196 : 0 < a2
                            swap
                            · -- branch
                              by_cases c1197 : 0 < a2
                              swap
                              · -- branch
                                by_cases c1198 : 0 < a2
                                swap
                                · -- branch
                                  by_cases c1199 : 0 < a2
                                  swap
                                  · -- branch
                                    by_cases c1200 : 0 < a2
                                    swap
                                    · -- branch
                                      by_cases c1201 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c1202 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c1203 : a0 + a2 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c1204 : b0 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f1205 := pair_fact E (i := 4) (j := 2) rfl rfl c1201 c1202
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1205
                                      by_cases c1206 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c1207 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c1208 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c1209 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f1210 := pair_fact E (i := 8) (j := 8) rfl rfl c1206 c1207
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1210
                                      omega
                                    by_cases c1211 : 0 < b10
                                    swap
                                    · omega
                                    by_cases c1212 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c1213 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                                    swap
                                    · omega
                                    have f1214 := pair_fact E (i := 2) (j := 10) rfl rfl c1200 c1211
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1214
                                    omega
                                  by_cases c1215 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c1216 : a0 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c1217 : b0 + b2 + b4 + b6 < a0 + a2
                                  swap
                                  · omega
                                  have f1218 := pair_fact E (i := 2) (j := 8) rfl rfl c1199 c1215
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1218
                                  omega
                                by_cases c1219 : 0 < b6
                                swap
                                · omega
                                by_cases c1220 : a0 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c1221 : b0 + b2 + b4 < a0 + a2
                                swap
                                · omega
                                have f1222 := pair_fact E (i := 2) (j := 6) rfl rfl c1198 c1219
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1222
                                omega
                              by_cases c1223 : 0 < b2
                              swap
                              · omega
                              by_cases c1224 : a0 < b0 + b2
                              swap
                              · omega
                              by_cases c1225 : b0 < a0 + a2
                              swap
                              · omega
                              have f1226 := pair_fact E (i := 2) (j := 2) rfl rfl c1197 c1223
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1226
                              omega
                            by_cases c1227 : 0 < b0
                            swap
                            · omega
                            by_cases c1228 : a0 < 0 + b0
                            swap
                            · omega
                            by_cases c1229 : 0 < a0 + a2
                            swap
                            · omega
                            have f1230 := pair_fact E (i := 2) (j := 0) rfl rfl c1196 c1227
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1230
                            omega
                          by_cases c1231 : 0 < b4
                          swap
                          · -- branch
                            by_cases c1232 : 0 < a2
                            swap
                            · omega
                            by_cases c1233 : 0 < b6
                            swap
                            · -- branch
                              by_cases c1234 : 0 < a2
                              swap
                              · omega
                              by_cases c1235 : 0 < b10
                              swap
                              · omega
                              by_cases c1236 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c1237 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                              swap
                              · -- branch
                                by_cases c1238 : 0 < a6
                                swap
                                · omega
                                by_cases c1239 : 0 < b8
                                swap
                                · omega
                                by_cases c1240 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                swap
                                · omega
                                by_cases c1241 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f1242 := pair_fact E (i := 6) (j := 8) rfl rfl c1238 c1239
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1242
                                by_cases c1243 : 0 < a2
                                swap
                                · omega
                                by_cases c1244 : 0 < b8
                                swap
                                · omega
                                by_cases c1245 : a0 < b0 + b2 + b4 + b6 + b8
                                swap
                                · omega
                                by_cases c1246 : b0 + b2 + b4 + b6 < a0 + a2
                                swap
                                · -- branch
                                  by_cases c1247 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c1248 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c1249 : a0 + a2 < b0 + b2
                                  swap
                                  · -- branch
                                    by_cases c1250 : 0 < a2
                                    swap
                                    · omega
                                    by_cases c1251 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c1252 : a0 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c1253 : b0 < a0 + a2
                                    swap
                                    · omega
                                    have f1254 := pair_fact E (i := 2) (j := 2) rfl rfl c1250 c1251
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1254
                                    by_cases c1255 : 0 < a2
                                    swap
                                    · omega
                                    by_cases c1256 : 0 < b0
                                    swap
                                    · omega
                                    by_cases c1257 : a0 < 0 + b0
                                    swap
                                    · -- branch
                                      by_cases c1258 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c1259 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c1260 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c1261 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f1262 := pair_fact E (i := 4) (j := 8) rfl rfl c1258 c1259
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1262
                                      by_cases c1263 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c1264 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c1265 : a0 + a2 + a4 < b0 + b2
                                      swap
                                      · -- branch
                                        by_cases c1266 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c1267 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c1268 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c1269 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                        swap
                                        · -- branch
                                          by_cases c1270 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c1271 : 0 < b0
                                          swap
                                          · omega
                                          by_cases c1272 : a0 + a2 + a4 + a6 < 0 + b0
                                          swap
                                          · -- branch
                                            by_cases c1273 : 0 < a8
                                            swap
                                            · omega
                                            by_cases c1274 : 0 < b2
                                            swap
                                            · omega
                                            by_cases c1275 : a0 + a2 + a4 + a6 < b0 + b2
                                            swap
                                            · -- branch
                                              by_cases c1276 : 0 < a8
                                              swap
                                              · omega
                                              by_cases c1277 : 0 < b4
                                              swap
                                              · -- branch
                                                by_cases c1278 : 0 < a8
                                                swap
                                                · omega
                                                by_cases c1279 : 0 < b6
                                                swap
                                                · -- branch
                                                  by_cases c1280 : 0 < a8
                                                  swap
                                                  · omega
                                                  by_cases c1281 : 0 < b8
                                                  swap
                                                  · omega
                                                  by_cases c1282 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                                  swap
                                                  · omega
                                                  by_cases c1283 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · omega
                                                  have f1284 := pair_fact E (i := 8) (j := 8) rfl rfl c1280 c1281
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1284
                                                  by_cases c1285 : 0 < a8
                                                  swap
                                                  · omega
                                                  by_cases c1286 : 0 < b10
                                                  swap
                                                  · omega
                                                  by_cases c1287 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                                  swap
                                                  · omega
                                                  by_cases c1288 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · -- branch
                                                    by_cases c1289 : 0 < a10
                                                    swap
                                                    · omega
                                                    by_cases c1290 : 0 < b8
                                                    swap
                                                    · omega
                                                    by_cases c1291 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                                    swap
                                                    · omega
                                                    by_cases c1292 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                                    swap
                                                    · omega
                                                    have f1293 := pair_fact E (i := 10) (j := 8) rfl rfl c1289 c1290
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1293
                                                    omega
                                                  have f1294 := pair_fact E (i := 8) (j := 10) rfl rfl c1285 c1286
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1294
                                                  omega
                                                by_cases c1295 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                swap
                                                · omega
                                                by_cases c1296 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                swap
                                                · omega
                                                have f1297 := pair_fact E (i := 8) (j := 6) rfl rfl c1278 c1279
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1297
                                                omega
                                              by_cases c1298 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c1299 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                              swap
                                              · omega
                                              have f1300 := pair_fact E (i := 8) (j := 4) rfl rfl c1276 c1277
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1300
                                              omega
                                            by_cases c1301 : b0 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f1302 := pair_fact E (i := 8) (j := 2) rfl rfl c1273 c1274
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1302
                                            omega
                                          by_cases c1303 : 0 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f1304 := pair_fact E (i := 8) (j := 0) rfl rfl c1270 c1271
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1304
                                          omega
                                        have f1305 := pair_fact E (i := 6) (j := 10) rfl rfl c1266 c1267
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1305
                                        omega
                                      by_cases c1306 : b0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f1307 := pair_fact E (i := 6) (j := 2) rfl rfl c1263 c1264
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1307
                                      omega
                                    by_cases c1308 : 0 < a0 + a2
                                    swap
                                    · omega
                                    have f1309 := pair_fact E (i := 2) (j := 0) rfl rfl c1255 c1256
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1309
                                    omega
                                  by_cases c1310 : b0 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f1311 := pair_fact E (i := 4) (j := 2) rfl rfl c1247 c1248
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1311
                                  omega
                                have f1312 := pair_fact E (i := 2) (j := 8) rfl rfl c1243 c1244
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1312
                                omega
                              have f1313 := pair_fact E (i := 2) (j := 10) rfl rfl c1234 c1235
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1313
                              omega
                            by_cases c1314 : a0 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c1315 : b0 + b2 + b4 < a0 + a2
                            swap
                            · omega
                            have f1316 := pair_fact E (i := 2) (j := 6) rfl rfl c1232 c1233
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1316
                            omega
                          by_cases c1317 : a0 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1318 : b0 + b2 < a0 + a2
                          swap
                          · omega
                          have f1319 := pair_fact E (i := 2) (j := 4) rfl rfl c1195 c1231
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1319
                          omega
                        have f1320 := pair_fact E (i := 4) (j := 10) rfl rfl c1191 c1192
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1320
                        omega
                      have f1321 := pair_fact E (i := 0) (j := 10) rfl rfl c1107 c1108
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1321
                      omega
                    have f1322 := pair_fact E (i := 0) (j := 2) rfl rfl c1103 c1104
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1322
                    by_cases c1323 : 0 < a2
                    swap
                    · -- branch
                      by_cases c1324 : 0 < a4
                      swap
                      · omega
                      by_cases c1325 : 0 < b2
                      swap
                      · omega
                      by_cases c1326 : a0 + a2 < b0 + b2
                      swap
                      · omega
                      by_cases c1327 : b0 < a0 + a2 + a4
                      swap
                      · omega
                      have f1328 := pair_fact E (i := 4) (j := 2) rfl rfl c1324 c1325
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1328
                      omega
                    by_cases c1329 : 0 < b2
                    swap
                    · omega
                    by_cases c1330 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c1331 : b0 < a0 + a2
                    swap
                    · omega
                    have f1332 := pair_fact E (i := 2) (j := 2) rfl rfl c1323 c1329
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1332
                    omega
                  by_cases c1333 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c1334 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                  swap
                  · omega
                  have f1335 := pair_fact E (i := 6) (j := 6) rfl rfl c1101 c1102
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1335
                  omega
                by_cases c1336 : a0 + a2 + a4 < b0 + b2 + b4
                swap
                · omega
                by_cases c1337 : b0 + b2 < a0 + a2 + a4 + a6
                swap
                · omega
                have f1338 := pair_fact E (i := 6) (j := 4) rfl rfl c1099 c1100
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1338
                omega
              by_cases c1339 : 0 < a0 + a2 + a4 + a6
              swap
              · omega
              have f1340 := pair_fact E (i := 6) (j := 0) rfl rfl c1096 c1097
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1340
              omega
            by_cases c1341 : a0 + a2 < b0 + b2 + b4 + b6
            swap
            · omega
            by_cases c1342 : b0 + b2 + b4 < a0 + a2 + a4
            swap
            · omega
            have f1343 := pair_fact E (i := 4) (j := 6) rfl rfl c1094 c1095
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
            by_cases c1347 : 0 < b10
            swap
            · -- branch
              by_cases c1348 : 0 < a4
              swap
              · omega
              by_cases c1349 : 0 < b10
              swap
              · -- branch
                by_cases c1350 : 0 < a2
                swap
                · -- branch
                  by_cases c1351 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1352 : 0 < a2
                    swap
                    · -- branch
                      by_cases c1353 : 0 < a2
                      swap
                      · -- branch
                        by_cases c1354 : 0 < a2
                        swap
                        · -- branch
                          by_cases c1355 : 0 < a2
                          swap
                          · -- branch
                            by_cases c1356 : 0 < a4
                            swap
                            · omega
                            by_cases c1357 : 0 < b2
                            swap
                            · omega
                            by_cases c1358 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c1359 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f1360 := pair_fact E (i := 4) (j := 2) rfl rfl c1356 c1357
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1360
                            by_cases c1361 : 0 < a8
                            swap
                            · omega
                            by_cases c1362 : 0 < b8
                            swap
                            · omega
                            by_cases c1363 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1364 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f1365 := pair_fact E (i := 8) (j := 8) rfl rfl c1361 c1362
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1365
                            omega
                          by_cases c1366 : 0 < b10
                          swap
                          · omega
                          by_cases c1367 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c1368 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · omega
                          have f1369 := pair_fact E (i := 2) (j := 10) rfl rfl c1355 c1366
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1369
                          omega
                        by_cases c1370 : 0 < b8
                        swap
                        · omega
                        by_cases c1371 : a0 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1372 : b0 + b2 + b4 + b6 < a0 + a2
                        swap
                        · omega
                        have f1373 := pair_fact E (i := 2) (j := 8) rfl rfl c1354 c1370
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1373
                        omega
                      by_cases c1374 : 0 < b6
                      swap
                      · omega
                      by_cases c1375 : a0 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c1376 : b0 + b2 + b4 < a0 + a2
                      swap
                      · omega
                      have f1377 := pair_fact E (i := 2) (j := 6) rfl rfl c1353 c1374
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1377
                      omega
                    by_cases c1378 : 0 < b2
                    swap
                    · omega
                    by_cases c1379 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c1380 : b0 < a0 + a2
                    swap
                    · omega
                    have f1381 := pair_fact E (i := 2) (j := 2) rfl rfl c1352 c1378
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1381
                    omega
                  by_cases c1382 : 0 < b0
                  swap
                  · omega
                  by_cases c1383 : a0 < 0 + b0
                  swap
                  · omega
                  by_cases c1384 : 0 < a0 + a2
                  swap
                  · omega
                  have f1385 := pair_fact E (i := 2) (j := 0) rfl rfl c1351 c1382
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1385
                  omega
                by_cases c1386 : 0 < b4
                swap
                · -- branch
                  by_cases c1387 : 0 < a2
                  swap
                  · omega
                  by_cases c1388 : 0 < b10
                  swap
                  · -- branch
                    by_cases c1389 : 0 < a2
                    swap
                    · omega
                    by_cases c1390 : 0 < b0
                    swap
                    · omega
                    by_cases c1391 : a0 < 0 + b0
                    swap
                    · -- branch
                      by_cases c1392 : 0 < a2
                      swap
                      · omega
                      by_cases c1393 : 0 < b6
                      swap
                      · omega
                      by_cases c1394 : a0 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c1395 : b0 + b2 + b4 < a0 + a2
                      swap
                      · -- branch
                        by_cases c1396 : 0 < a2
                        swap
                        · omega
                        by_cases c1397 : 0 < b2
                        swap
                        · omega
                        by_cases c1398 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c1399 : b0 < a0 + a2
                        swap
                        · omega
                        have f1400 := pair_fact E (i := 2) (j := 2) rfl rfl c1396 c1397
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1400
                        by_cases c1401 : 0 < a0
                        swap
                        · omega
                        by_cases c1402 : 0 < b2
                        swap
                        · omega
                        by_cases c1403 : 0 < b0 + b2
                        swap
                        · omega
                        by_cases c1404 : b0 < 0 + a0
                        swap
                        · -- branch
                          by_cases c1405 : 0 < a2
                          swap
                          · omega
                          by_cases c1406 : 0 < b8
                          swap
                          · omega
                          by_cases c1407 : a0 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c1408 : b0 + b2 + b4 + b6 < a0 + a2
                          swap
                          · -- branch
                            by_cases c1409 : 0 < a8
                            swap
                            · omega
                            by_cases c1410 : 0 < b0
                            swap
                            · omega
                            by_cases c1411 : a0 + a2 + a4 + a6 < 0 + b0
                            swap
                            · -- branch
                              by_cases c1412 : 0 < a8
                              swap
                              · omega
                              by_cases c1413 : 0 < b2
                              swap
                              · omega
                              by_cases c1414 : a0 + a2 + a4 + a6 < b0 + b2
                              swap
                              · -- branch
                                by_cases c1415 : 0 < a8
                                swap
                                · omega
                                by_cases c1416 : 0 < b4
                                swap
                                · -- branch
                                  by_cases c1417 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c1418 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c1419 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c1420 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f1421 := pair_fact E (i := 8) (j := 8) rfl rfl c1417 c1418
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1421
                                  by_cases c1422 : 0 < a10
                                  swap
                                  · omega
                                  by_cases c1423 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c1424 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c1425 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                  swap
                                  · omega
                                  have f1426 := pair_fact E (i := 10) (j := 8) rfl rfl c1422 c1423
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1426
                                  omega
                                by_cases c1427 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c1428 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f1429 := pair_fact E (i := 8) (j := 4) rfl rfl c1415 c1416
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1429
                                omega
                              by_cases c1430 : b0 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f1431 := pair_fact E (i := 8) (j := 2) rfl rfl c1412 c1413
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1431
                              omega
                            by_cases c1432 : 0 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f1433 := pair_fact E (i := 8) (j := 0) rfl rfl c1409 c1410
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1433
                            omega
                          have f1434 := pair_fact E (i := 2) (j := 8) rfl rfl c1405 c1406
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1434
                          omega
                        have f1435 := pair_fact E (i := 0) (j := 2) rfl rfl c1401 c1402
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1435
                        omega
                      have f1436 := pair_fact E (i := 2) (j := 6) rfl rfl c1392 c1393
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1436
                      by_cases c1437 : 0 < a4
                      swap
                      · omega
                      by_cases c1438 : 0 < b8
                      swap
                      · omega
                      by_cases c1439 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c1440 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                      swap
                      · omega
                      have f1441 := pair_fact E (i := 4) (j := 8) rfl rfl c1437 c1438
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1441
                      omega
                    by_cases c1442 : 0 < a0 + a2
                    swap
                    · omega
                    have f1443 := pair_fact E (i := 2) (j := 0) rfl rfl c1389 c1390
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1443
                    by_cases c1444 : 0 < a2
                    swap
                    · omega
                    by_cases c1445 : 0 < b6
                    swap
                    · omega
                    by_cases c1446 : a0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c1447 : b0 + b2 + b4 < a0 + a2
                    swap
                    · -- branch
                      by_cases c1448 : 0 < a0
                      swap
                      · omega
                      by_cases c1449 : 0 < b2
                      swap
                      · omega
                      by_cases c1450 : 0 < b0 + b2
                      swap
                      · omega
                      by_cases c1451 : b0 < 0 + a0
                      swap
                      · -- branch
                        by_cases c1452 : 0 < a2
                        swap
                        · omega
                        by_cases c1453 : 0 < b2
                        swap
                        · omega
                        by_cases c1454 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c1455 : b0 < a0 + a2
                        swap
                        · -- branch
                          by_cases c1456 : 0 < a2
                          swap
                          · omega
                          by_cases c1457 : 0 < b8
                          swap
                          · omega
                          by_cases c1458 : a0 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c1459 : b0 + b2 + b4 + b6 < a0 + a2
                          swap
                          · -- branch
                            by_cases c1460 : 0 < a4
                            swap
                            · omega
                            by_cases c1461 : 0 < b2
                            swap
                            · omega
                            by_cases c1462 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c1463 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f1464 := pair_fact E (i := 4) (j := 2) rfl rfl c1460 c1461
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1464
                            by_cases c1465 : 0 < a8
                            swap
                            · omega
                            by_cases c1466 : 0 < b8
                            swap
                            · omega
                            by_cases c1467 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1468 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f1469 := pair_fact E (i := 8) (j := 8) rfl rfl c1465 c1466
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1469
                            omega
                          have f1470 := pair_fact E (i := 2) (j := 8) rfl rfl c1456 c1457
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1470
                          omega
                        have f1471 := pair_fact E (i := 2) (j := 2) rfl rfl c1452 c1453
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1471
                        omega
                      have f1472 := pair_fact E (i := 0) (j := 2) rfl rfl c1448 c1449
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1472
                      omega
                    have f1473 := pair_fact E (i := 2) (j := 6) rfl rfl c1444 c1445
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1473
                    omega
                  by_cases c1474 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c1475 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                  swap
                  · omega
                  have f1476 := pair_fact E (i := 2) (j := 10) rfl rfl c1387 c1388
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1476
                  omega
                by_cases c1477 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c1478 : b0 + b2 < a0 + a2
                swap
                · omega
                have f1479 := pair_fact E (i := 2) (j := 4) rfl rfl c1350 c1386
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1479
                omega
              by_cases c1480 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c1481 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
              swap
              · omega
              have f1482 := pair_fact E (i := 4) (j := 10) rfl rfl c1348 c1349
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1482
              omega
            by_cases c1483 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c1484 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · -- branch
              by_cases c1485 : 0 < a4
              swap
              · omega
              by_cases c1486 : 0 < b10
              swap
              · omega
              by_cases c1487 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c1488 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
              swap
              · -- branch
                by_cases c1489 : 0 < a2
                swap
                · -- branch
                  by_cases c1490 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1491 : 0 < a2
                    swap
                    · -- branch
                      by_cases c1492 : 0 < a2
                      swap
                      · -- branch
                        by_cases c1493 : 0 < a2
                        swap
                        · -- branch
                          by_cases c1494 : 0 < a2
                          swap
                          · -- branch
                            by_cases c1495 : 0 < a4
                            swap
                            · omega
                            by_cases c1496 : 0 < b2
                            swap
                            · omega
                            by_cases c1497 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c1498 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f1499 := pair_fact E (i := 4) (j := 2) rfl rfl c1495 c1496
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1499
                            by_cases c1500 : 0 < a8
                            swap
                            · omega
                            by_cases c1501 : 0 < b8
                            swap
                            · omega
                            by_cases c1502 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1503 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f1504 := pair_fact E (i := 8) (j := 8) rfl rfl c1500 c1501
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1504
                            omega
                          by_cases c1505 : 0 < b10
                          swap
                          · omega
                          by_cases c1506 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c1507 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · omega
                          have f1508 := pair_fact E (i := 2) (j := 10) rfl rfl c1494 c1505
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1508
                          omega
                        by_cases c1509 : 0 < b8
                        swap
                        · omega
                        by_cases c1510 : a0 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1511 : b0 + b2 + b4 + b6 < a0 + a2
                        swap
                        · omega
                        have f1512 := pair_fact E (i := 2) (j := 8) rfl rfl c1493 c1509
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1512
                        omega
                      by_cases c1513 : 0 < b6
                      swap
                      · omega
                      by_cases c1514 : a0 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c1515 : b0 + b2 + b4 < a0 + a2
                      swap
                      · omega
                      have f1516 := pair_fact E (i := 2) (j := 6) rfl rfl c1492 c1513
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1516
                      omega
                    by_cases c1517 : 0 < b2
                    swap
                    · omega
                    by_cases c1518 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c1519 : b0 < a0 + a2
                    swap
                    · omega
                    have f1520 := pair_fact E (i := 2) (j := 2) rfl rfl c1491 c1517
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1520
                    omega
                  by_cases c1521 : 0 < b0
                  swap
                  · omega
                  by_cases c1522 : a0 < 0 + b0
                  swap
                  · omega
                  by_cases c1523 : 0 < a0 + a2
                  swap
                  · omega
                  have f1524 := pair_fact E (i := 2) (j := 0) rfl rfl c1490 c1521
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1524
                  omega
                by_cases c1525 : 0 < b4
                swap
                · -- branch
                  by_cases c1526 : 0 < a2
                  swap
                  · omega
                  by_cases c1527 : 0 < b10
                  swap
                  · omega
                  by_cases c1528 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c1529 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                  swap
                  · -- branch
                    by_cases c1530 : 0 < a2
                    swap
                    · omega
                    by_cases c1531 : 0 < b0
                    swap
                    · omega
                    by_cases c1532 : a0 < 0 + b0
                    swap
                    · -- branch
                      by_cases c1533 : 0 < a2
                      swap
                      · omega
                      by_cases c1534 : 0 < b6
                      swap
                      · omega
                      by_cases c1535 : a0 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c1536 : b0 + b2 + b4 < a0 + a2
                      swap
                      · -- branch
                        by_cases c1537 : 0 < a2
                        swap
                        · omega
                        by_cases c1538 : 0 < b2
                        swap
                        · omega
                        by_cases c1539 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c1540 : b0 < a0 + a2
                        swap
                        · omega
                        have f1541 := pair_fact E (i := 2) (j := 2) rfl rfl c1537 c1538
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1541
                        by_cases c1542 : 0 < a0
                        swap
                        · omega
                        by_cases c1543 : 0 < b2
                        swap
                        · omega
                        by_cases c1544 : 0 < b0 + b2
                        swap
                        · omega
                        by_cases c1545 : b0 < 0 + a0
                        swap
                        · -- branch
                          by_cases c1546 : 0 < a2
                          swap
                          · omega
                          by_cases c1547 : 0 < b8
                          swap
                          · omega
                          by_cases c1548 : a0 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c1549 : b0 + b2 + b4 + b6 < a0 + a2
                          swap
                          · -- branch
                            by_cases c1550 : 0 < a8
                            swap
                            · omega
                            by_cases c1551 : 0 < b0
                            swap
                            · omega
                            by_cases c1552 : a0 + a2 + a4 + a6 < 0 + b0
                            swap
                            · -- branch
                              by_cases c1553 : 0 < a8
                              swap
                              · omega
                              by_cases c1554 : 0 < b2
                              swap
                              · omega
                              by_cases c1555 : a0 + a2 + a4 + a6 < b0 + b2
                              swap
                              · -- branch
                                by_cases c1556 : 0 < a8
                                swap
                                · omega
                                by_cases c1557 : 0 < b4
                                swap
                                · -- branch
                                  by_cases c1558 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c1559 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c1560 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c1561 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f1562 := pair_fact E (i := 8) (j := 8) rfl rfl c1558 c1559
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1562
                                  by_cases c1563 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c1564 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c1565 : a0 + a2 < b0 + b2
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
                                    by_cases c1572 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c1573 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c1574 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c1575 : 0 < a6
                                      swap
                                      · -- branch
                                        by_cases c1576 : 0 < a6
                                        swap
                                        · -- branch
                                          by_cases c1577 : 0 < a6
                                          swap
                                          · -- branch
                                            by_cases c1578 : 0 < a6
                                            swap
                                            · -- branch
                                              by_cases c1579 : 0 < a6
                                              swap
                                              · -- branch
                                                by_cases c1580 : 0 < a6
                                                swap
                                                · -- branch
                                                  by_cases c1581 : 0 < a8
                                                  swap
                                                  · omega
                                                  by_cases c1582 : 0 < b6
                                                  swap
                                                  · omega
                                                  by_cases c1583 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                  swap
                                                  · -- branch
                                                    by_cases c1584 : 0 < a8
                                                    swap
                                                    · omega
                                                    by_cases c1585 : 0 < b10
                                                    swap
                                                    · omega
                                                    by_cases c1586 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                                    swap
                                                    · omega
                                                    by_cases c1587 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                                    swap
                                                    · -- branch
                                                      by_cases c1588 : 0 < a10
                                                      swap
                                                      · omega
                                                      by_cases c1589 : 0 < b8
                                                      swap
                                                      · omega
                                                      by_cases c1590 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                                      swap
                                                      · omega
                                                      by_cases c1591 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                                      swap
                                                      · omega
                                                      have f1592 := pair_fact E (i := 10) (j := 8) rfl rfl c1588 c1589
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1592
                                                      omega
                                                    have f1593 := pair_fact E (i := 8) (j := 10) rfl rfl c1584 c1585
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1593
                                                    omega
                                                  by_cases c1594 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · omega
                                                  have f1595 := pair_fact E (i := 8) (j := 6) rfl rfl c1581 c1582
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1595
                                                  omega
                                                by_cases c1596 : 0 < b10
                                                swap
                                                · omega
                                                by_cases c1597 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                                swap
                                                · omega
                                                by_cases c1598 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                                swap
                                                · omega
                                                have f1599 := pair_fact E (i := 6) (j := 10) rfl rfl c1580 c1596
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1599
                                                omega
                                              by_cases c1600 : 0 < b8
                                              swap
                                              · omega
                                              by_cases c1601 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                              swap
                                              · omega
                                              by_cases c1602 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f1603 := pair_fact E (i := 6) (j := 8) rfl rfl c1579 c1600
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1603
                                              omega
                                            by_cases c1604 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c1605 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c1606 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f1607 := pair_fact E (i := 6) (j := 6) rfl rfl c1578 c1604
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1607
                                            omega
                                          by_cases c1608 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c1609 : a0 + a2 + a4 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c1610 : b0 + b2 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f1611 := pair_fact E (i := 6) (j := 4) rfl rfl c1577 c1608
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1611
                                          omega
                                        by_cases c1612 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c1613 : a0 + a2 + a4 < b0 + b2
                                        swap
                                        · omega
                                        by_cases c1614 : b0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f1615 := pair_fact E (i := 6) (j := 2) rfl rfl c1576 c1612
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1615
                                        omega
                                      by_cases c1616 : 0 < b0
                                      swap
                                      · omega
                                      by_cases c1617 : a0 + a2 + a4 < 0 + b0
                                      swap
                                      · omega
                                      by_cases c1618 : 0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f1619 := pair_fact E (i := 6) (j := 0) rfl rfl c1575 c1616
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1619
                                      omega
                                    have f1620 := pair_fact E (i := 4) (j := 8) rfl rfl c1571 c1572
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1620
                                    omega
                                  by_cases c1621 : b0 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f1622 := pair_fact E (i := 4) (j := 2) rfl rfl c1563 c1564
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1622
                                  omega
                                by_cases c1623 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c1624 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f1625 := pair_fact E (i := 8) (j := 4) rfl rfl c1556 c1557
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1625
                                omega
                              by_cases c1626 : b0 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f1627 := pair_fact E (i := 8) (j := 2) rfl rfl c1553 c1554
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1627
                              omega
                            by_cases c1628 : 0 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f1629 := pair_fact E (i := 8) (j := 0) rfl rfl c1550 c1551
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1629
                            omega
                          have f1630 := pair_fact E (i := 2) (j := 8) rfl rfl c1546 c1547
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1630
                          omega
                        have f1631 := pair_fact E (i := 0) (j := 2) rfl rfl c1542 c1543
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1631
                        omega
                      have f1632 := pair_fact E (i := 2) (j := 6) rfl rfl c1533 c1534
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1632
                      by_cases c1633 : 0 < a4
                      swap
                      · omega
                      by_cases c1634 : 0 < b8
                      swap
                      · omega
                      by_cases c1635 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c1636 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                      swap
                      · omega
                      have f1637 := pair_fact E (i := 4) (j := 8) rfl rfl c1633 c1634
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1637
                      omega
                    by_cases c1638 : 0 < a0 + a2
                    swap
                    · omega
                    have f1639 := pair_fact E (i := 2) (j := 0) rfl rfl c1530 c1531
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1639
                    by_cases c1640 : 0 < a2
                    swap
                    · omega
                    by_cases c1641 : 0 < b6
                    swap
                    · omega
                    by_cases c1642 : a0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c1643 : b0 + b2 + b4 < a0 + a2
                    swap
                    · -- branch
                      by_cases c1644 : 0 < a0
                      swap
                      · omega
                      by_cases c1645 : 0 < b2
                      swap
                      · omega
                      by_cases c1646 : 0 < b0 + b2
                      swap
                      · omega
                      by_cases c1647 : b0 < 0 + a0
                      swap
                      · -- branch
                        by_cases c1648 : 0 < a2
                        swap
                        · omega
                        by_cases c1649 : 0 < b2
                        swap
                        · omega
                        by_cases c1650 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c1651 : b0 < a0 + a2
                        swap
                        · -- branch
                          by_cases c1652 : 0 < a2
                          swap
                          · omega
                          by_cases c1653 : 0 < b8
                          swap
                          · omega
                          by_cases c1654 : a0 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c1655 : b0 + b2 + b4 + b6 < a0 + a2
                          swap
                          · -- branch
                            by_cases c1656 : 0 < a4
                            swap
                            · omega
                            by_cases c1657 : 0 < b2
                            swap
                            · omega
                            by_cases c1658 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c1659 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f1660 := pair_fact E (i := 4) (j := 2) rfl rfl c1656 c1657
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1660
                            by_cases c1661 : 0 < a8
                            swap
                            · omega
                            by_cases c1662 : 0 < b8
                            swap
                            · omega
                            by_cases c1663 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1664 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f1665 := pair_fact E (i := 8) (j := 8) rfl rfl c1661 c1662
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1665
                            omega
                          have f1666 := pair_fact E (i := 2) (j := 8) rfl rfl c1652 c1653
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1666
                          omega
                        have f1667 := pair_fact E (i := 2) (j := 2) rfl rfl c1648 c1649
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1667
                        omega
                      have f1668 := pair_fact E (i := 0) (j := 2) rfl rfl c1644 c1645
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1668
                      omega
                    have f1669 := pair_fact E (i := 2) (j := 6) rfl rfl c1640 c1641
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1669
                    omega
                  have f1670 := pair_fact E (i := 2) (j := 10) rfl rfl c1526 c1527
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1670
                  omega
                by_cases c1671 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c1672 : b0 + b2 < a0 + a2
                swap
                · omega
                have f1673 := pair_fact E (i := 2) (j := 4) rfl rfl c1489 c1525
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1673
                omega
              have f1674 := pair_fact E (i := 4) (j := 10) rfl rfl c1485 c1486
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1674
              omega
            have f1675 := pair_fact E (i := 0) (j := 10) rfl rfl c1346 c1347
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1675
            omega
          have f1676 := pair_fact E (i := 0) (j := 6) rfl rfl c1092 c1093
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1676
          omega
        by_cases c1677 : a0 + a2 < b0 + b2 + b4
        swap
        · omega
        by_cases c1678 : b0 + b2 < a0 + a2 + a4
        swap
        · omega
        have f1679 := pair_fact E (i := 4) (j := 4) rfl rfl c1090 c1091
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1679
        omega
      by_cases c1680 : 0 < a0 + a2 + a4
      swap
      · omega
      have f1681 := pair_fact E (i := 4) (j := 0) rfl rfl c1087 c1088
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1681
      omega
    have f1682 := pair_fact E (i := 0) (j := 8) rfl rfl c1083 c1084
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1682
    omega
  by_cases c1683 : 0 < b0 + b2 + b4
  swap
  · omega
  by_cases c1684 : b0 + b2 < 0 + a0
  swap
  · -- branch
    by_cases c1685 : 0 < a0
    swap
    · omega
    by_cases c1686 : 0 < b6
    swap
    · -- branch
      by_cases c1687 : 0 < a0
      swap
      · omega
      by_cases c1688 : 0 < b8
      swap
      · omega
      by_cases c1689 : 0 < b0 + b2 + b4 + b6 + b8
      swap
      · omega
      by_cases c1690 : b0 + b2 + b4 + b6 < 0 + a0
      swap
      · -- branch
        by_cases c1691 : 0 < a6
        swap
        · omega
        by_cases c1692 : 0 < b0
        swap
        · omega
        by_cases c1693 : a0 + a2 + a4 < 0 + b0
        swap
        · -- branch
          by_cases c1694 : 0 < a6
          swap
          · omega
          by_cases c1695 : 0 < b6
          swap
          · -- branch
            by_cases c1696 : 0 < a0
            swap
            · omega
            by_cases c1697 : 0 < b10
            swap
            · -- branch
              by_cases c1698 : 0 < a6
              swap
              · omega
              by_cases c1699 : 0 < b10
              swap
              · -- branch
                by_cases c1700 : 0 < a2
                swap
                · -- branch
                  by_cases c1701 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1702 : 0 < a2
                    swap
                    · -- branch
                      by_cases c1703 : 0 < a2
                      swap
                      · -- branch
                        by_cases c1704 : 0 < a2
                        swap
                        · -- branch
                          by_cases c1705 : 0 < a2
                          swap
                          · -- branch
                            by_cases c1706 : 0 < a6
                            swap
                            · omega
                            by_cases c1707 : 0 < b2
                            swap
                            · omega
                            by_cases c1708 : a0 + a2 + a4 < b0 + b2
                            swap
                            · omega
                            by_cases c1709 : b0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f1710 := pair_fact E (i := 6) (j := 2) rfl rfl c1706 c1707
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1710
                            by_cases c1711 : 0 < a8
                            swap
                            · omega
                            by_cases c1712 : 0 < b8
                            swap
                            · omega
                            by_cases c1713 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1714 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f1715 := pair_fact E (i := 8) (j := 8) rfl rfl c1711 c1712
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1715
                            omega
                          by_cases c1716 : 0 < b10
                          swap
                          · omega
                          by_cases c1717 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c1718 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · omega
                          have f1719 := pair_fact E (i := 2) (j := 10) rfl rfl c1705 c1716
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1719
                          omega
                        by_cases c1720 : 0 < b8
                        swap
                        · omega
                        by_cases c1721 : a0 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1722 : b0 + b2 + b4 + b6 < a0 + a2
                        swap
                        · omega
                        have f1723 := pair_fact E (i := 2) (j := 8) rfl rfl c1704 c1720
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1723
                        omega
                      by_cases c1724 : 0 < b4
                      swap
                      · omega
                      by_cases c1725 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c1726 : b0 + b2 < a0 + a2
                      swap
                      · omega
                      have f1727 := pair_fact E (i := 2) (j := 4) rfl rfl c1703 c1724
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1727
                      omega
                    by_cases c1728 : 0 < b2
                    swap
                    · omega
                    by_cases c1729 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c1730 : b0 < a0 + a2
                    swap
                    · omega
                    have f1731 := pair_fact E (i := 2) (j := 2) rfl rfl c1702 c1728
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1731
                    omega
                  by_cases c1732 : 0 < b0
                  swap
                  · omega
                  by_cases c1733 : a0 < 0 + b0
                  swap
                  · omega
                  by_cases c1734 : 0 < a0 + a2
                  swap
                  · omega
                  have f1735 := pair_fact E (i := 2) (j := 0) rfl rfl c1701 c1732
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1735
                  omega
                by_cases c1736 : 0 < b6
                swap
                · -- branch
                  by_cases c1737 : 0 < a2
                  swap
                  · omega
                  by_cases c1738 : 0 < b10
                  swap
                  · -- branch
                    by_cases c1739 : 0 < a2
                    swap
                    · omega
                    by_cases c1740 : 0 < b0
                    swap
                    · omega
                    by_cases c1741 : a0 < 0 + b0
                    swap
                    · -- branch
                      by_cases c1742 : 0 < a2
                      swap
                      · omega
                      by_cases c1743 : 0 < b4
                      swap
                      · omega
                      by_cases c1744 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c1745 : b0 + b2 < a0 + a2
                      swap
                      · -- branch
                        by_cases c1746 : 0 < a2
                        swap
                        · omega
                        by_cases c1747 : 0 < b2
                        swap
                        · omega
                        by_cases c1748 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c1749 : b0 < a0 + a2
                        swap
                        · omega
                        have f1750 := pair_fact E (i := 2) (j := 2) rfl rfl c1746 c1747
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1750
                        by_cases c1751 : 0 < a0
                        swap
                        · omega
                        by_cases c1752 : 0 < b2
                        swap
                        · omega
                        by_cases c1753 : 0 < b0 + b2
                        swap
                        · omega
                        by_cases c1754 : b0 < 0 + a0
                        swap
                        · -- branch
                          by_cases c1755 : 0 < a2
                          swap
                          · omega
                          by_cases c1756 : 0 < b8
                          swap
                          · omega
                          by_cases c1757 : a0 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c1758 : b0 + b2 + b4 + b6 < a0 + a2
                          swap
                          · -- branch
                            by_cases c1759 : 0 < a6
                            swap
                            · omega
                            by_cases c1760 : 0 < b2
                            swap
                            · omega
                            by_cases c1761 : a0 + a2 + a4 < b0 + b2
                            swap
                            · -- branch
                              by_cases c1762 : 0 < a8
                              swap
                              · omega
                              by_cases c1763 : 0 < b0
                              swap
                              · omega
                              by_cases c1764 : a0 + a2 + a4 + a6 < 0 + b0
                              swap
                              · -- branch
                                by_cases c1765 : 0 < a8
                                swap
                                · omega
                                by_cases c1766 : 0 < b2
                                swap
                                · omega
                                by_cases c1767 : a0 + a2 + a4 + a6 < b0 + b2
                                swap
                                · -- branch
                                  by_cases c1768 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c1769 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c1770 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                  swap
                                  · -- branch
                                    by_cases c1771 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c1772 : 0 < b6
                                    swap
                                    · -- branch
                                      by_cases c1773 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c1774 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c1775 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c1776 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f1777 := pair_fact E (i := 8) (j := 8) rfl rfl c1773 c1774
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1777
                                      by_cases c1778 : 0 < a10
                                      swap
                                      · omega
                                      by_cases c1779 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c1780 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c1781 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                      swap
                                      · omega
                                      have f1782 := pair_fact E (i := 10) (j := 8) rfl rfl c1778 c1779
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1782
                                      omega
                                    by_cases c1783 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c1784 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f1785 := pair_fact E (i := 8) (j := 6) rfl rfl c1771 c1772
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1785
                                    omega
                                  by_cases c1786 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f1787 := pair_fact E (i := 8) (j := 4) rfl rfl c1768 c1769
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1787
                                  omega
                                by_cases c1788 : b0 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f1789 := pair_fact E (i := 8) (j := 2) rfl rfl c1765 c1766
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1789
                                omega
                              by_cases c1790 : 0 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f1791 := pair_fact E (i := 8) (j := 0) rfl rfl c1762 c1763
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1791
                              omega
                            by_cases c1792 : b0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f1793 := pair_fact E (i := 6) (j := 2) rfl rfl c1759 c1760
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1793
                            omega
                          have f1794 := pair_fact E (i := 2) (j := 8) rfl rfl c1755 c1756
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1794
                          omega
                        have f1795 := pair_fact E (i := 0) (j := 2) rfl rfl c1751 c1752
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1795
                        omega
                      have f1796 := pair_fact E (i := 2) (j := 4) rfl rfl c1742 c1743
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1796
                      by_cases c1797 : 0 < a6
                      swap
                      · omega
                      by_cases c1798 : 0 < b8
                      swap
                      · omega
                      by_cases c1799 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c1800 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f1801 := pair_fact E (i := 6) (j := 8) rfl rfl c1797 c1798
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1801
                      omega
                    by_cases c1802 : 0 < a0 + a2
                    swap
                    · omega
                    have f1803 := pair_fact E (i := 2) (j := 0) rfl rfl c1739 c1740
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1803
                    by_cases c1804 : 0 < a2
                    swap
                    · omega
                    by_cases c1805 : 0 < b4
                    swap
                    · omega
                    by_cases c1806 : a0 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c1807 : b0 + b2 < a0 + a2
                    swap
                    · -- branch
                      by_cases c1808 : 0 < a0
                      swap
                      · omega
                      by_cases c1809 : 0 < b2
                      swap
                      · omega
                      by_cases c1810 : 0 < b0 + b2
                      swap
                      · omega
                      by_cases c1811 : b0 < 0 + a0
                      swap
                      · -- branch
                        by_cases c1812 : 0 < a2
                        swap
                        · omega
                        by_cases c1813 : 0 < b2
                        swap
                        · omega
                        by_cases c1814 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c1815 : b0 < a0 + a2
                        swap
                        · -- branch
                          by_cases c1816 : 0 < a2
                          swap
                          · omega
                          by_cases c1817 : 0 < b8
                          swap
                          · omega
                          by_cases c1818 : a0 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c1819 : b0 + b2 + b4 + b6 < a0 + a2
                          swap
                          · -- branch
                            by_cases c1820 : 0 < a6
                            swap
                            · omega
                            by_cases c1821 : 0 < b2
                            swap
                            · omega
                            by_cases c1822 : a0 + a2 + a4 < b0 + b2
                            swap
                            · omega
                            by_cases c1823 : b0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f1824 := pair_fact E (i := 6) (j := 2) rfl rfl c1820 c1821
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1824
                            by_cases c1825 : 0 < a8
                            swap
                            · omega
                            by_cases c1826 : 0 < b8
                            swap
                            · omega
                            by_cases c1827 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1828 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f1829 := pair_fact E (i := 8) (j := 8) rfl rfl c1825 c1826
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1829
                            omega
                          have f1830 := pair_fact E (i := 2) (j := 8) rfl rfl c1816 c1817
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1830
                          omega
                        have f1831 := pair_fact E (i := 2) (j := 2) rfl rfl c1812 c1813
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1831
                        omega
                      have f1832 := pair_fact E (i := 0) (j := 2) rfl rfl c1808 c1809
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1832
                      omega
                    have f1833 := pair_fact E (i := 2) (j := 4) rfl rfl c1804 c1805
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1833
                    omega
                  by_cases c1834 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c1835 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                  swap
                  · omega
                  have f1836 := pair_fact E (i := 2) (j := 10) rfl rfl c1737 c1738
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1836
                  omega
                by_cases c1837 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c1838 : b0 + b2 + b4 < a0 + a2
                swap
                · omega
                have f1839 := pair_fact E (i := 2) (j := 6) rfl rfl c1700 c1736
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1839
                omega
              by_cases c1840 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c1841 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
              swap
              · omega
              have f1842 := pair_fact E (i := 6) (j := 10) rfl rfl c1698 c1699
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1842
              omega
            by_cases c1843 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c1844 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · -- branch
              by_cases c1845 : 0 < a2
              swap
              · -- branch
                by_cases c1846 : 0 < a2
                swap
                · -- branch
                  by_cases c1847 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1848 : 0 < a2
                    swap
                    · -- branch
                      by_cases c1849 : 0 < a2
                      swap
                      · -- branch
                        by_cases c1850 : 0 < a2
                        swap
                        · -- branch
                          by_cases c1851 : 0 < a6
                          swap
                          · omega
                          by_cases c1852 : 0 < b2
                          swap
                          · omega
                          by_cases c1853 : a0 + a2 + a4 < b0 + b2
                          swap
                          · omega
                          by_cases c1854 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f1855 := pair_fact E (i := 6) (j := 2) rfl rfl c1851 c1852
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1855
                          by_cases c1856 : 0 < a8
                          swap
                          · omega
                          by_cases c1857 : 0 < b8
                          swap
                          · omega
                          by_cases c1858 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c1859 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f1860 := pair_fact E (i := 8) (j := 8) rfl rfl c1856 c1857
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1860
                          omega
                        by_cases c1861 : 0 < b10
                        swap
                        · omega
                        by_cases c1862 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c1863 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                        swap
                        · omega
                        have f1864 := pair_fact E (i := 2) (j := 10) rfl rfl c1850 c1861
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1864
                        omega
                      by_cases c1865 : 0 < b8
                      swap
                      · omega
                      by_cases c1866 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c1867 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · omega
                      have f1868 := pair_fact E (i := 2) (j := 8) rfl rfl c1849 c1865
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1868
                      omega
                    by_cases c1869 : 0 < b4
                    swap
                    · omega
                    by_cases c1870 : a0 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c1871 : b0 + b2 < a0 + a2
                    swap
                    · omega
                    have f1872 := pair_fact E (i := 2) (j := 4) rfl rfl c1848 c1869
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1872
                    omega
                  by_cases c1873 : 0 < b2
                  swap
                  · omega
                  by_cases c1874 : a0 < b0 + b2
                  swap
                  · omega
                  by_cases c1875 : b0 < a0 + a2
                  swap
                  · omega
                  have f1876 := pair_fact E (i := 2) (j := 2) rfl rfl c1847 c1873
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1876
                  omega
                by_cases c1877 : 0 < b0
                swap
                · omega
                by_cases c1878 : a0 < 0 + b0
                swap
                · omega
                by_cases c1879 : 0 < a0 + a2
                swap
                · omega
                have f1880 := pair_fact E (i := 2) (j := 0) rfl rfl c1846 c1877
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1880
                omega
              by_cases c1881 : 0 < b6
              swap
              · -- branch
                by_cases c1882 : 0 < a2
                swap
                · omega
                by_cases c1883 : 0 < b10
                swap
                · omega
                by_cases c1884 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                swap
                · omega
                by_cases c1885 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                swap
                · -- branch
                  by_cases c1886 : 0 < a2
                  swap
                  · omega
                  by_cases c1887 : 0 < b0
                  swap
                  · omega
                  by_cases c1888 : a0 < 0 + b0
                  swap
                  · -- branch
                    by_cases c1889 : 0 < a2
                    swap
                    · omega
                    by_cases c1890 : 0 < b4
                    swap
                    · omega
                    by_cases c1891 : a0 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c1892 : b0 + b2 < a0 + a2
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
                      · omega
                      have f1897 := pair_fact E (i := 2) (j := 2) rfl rfl c1893 c1894
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1897
                      by_cases c1898 : 0 < a0
                      swap
                      · omega
                      by_cases c1899 : 0 < b2
                      swap
                      · omega
                      by_cases c1900 : 0 < b0 + b2
                      swap
                      · omega
                      by_cases c1901 : b0 < 0 + a0
                      swap
                      · -- branch
                        by_cases c1902 : 0 < a2
                        swap
                        · omega
                        by_cases c1903 : 0 < b8
                        swap
                        · omega
                        by_cases c1904 : a0 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1905 : b0 + b2 + b4 + b6 < a0 + a2
                        swap
                        · -- branch
                          by_cases c1906 : 0 < a6
                          swap
                          · omega
                          by_cases c1907 : 0 < b2
                          swap
                          · omega
                          by_cases c1908 : a0 + a2 + a4 < b0 + b2
                          swap
                          · -- branch
                            by_cases c1909 : 0 < a6
                            swap
                            · omega
                            by_cases c1910 : 0 < b10
                            swap
                            · omega
                            by_cases c1911 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c1912 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                            swap
                            · -- branch
                              by_cases c1913 : 0 < a8
                              swap
                              · omega
                              by_cases c1914 : 0 < b0
                              swap
                              · omega
                              by_cases c1915 : a0 + a2 + a4 + a6 < 0 + b0
                              swap
                              · -- branch
                                by_cases c1916 : 0 < a8
                                swap
                                · omega
                                by_cases c1917 : 0 < b2
                                swap
                                · omega
                                by_cases c1918 : a0 + a2 + a4 + a6 < b0 + b2
                                swap
                                · -- branch
                                  by_cases c1919 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c1920 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c1921 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                  swap
                                  · -- branch
                                    by_cases c1922 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c1923 : 0 < b6
                                    swap
                                    · -- branch
                                      by_cases c1924 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c1925 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c1926 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c1927 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f1928 := pair_fact E (i := 8) (j := 8) rfl rfl c1924 c1925
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1928
                                      by_cases c1929 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c1930 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c1931 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c1932 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · -- branch
                                        by_cases c1933 : 0 < a10
                                        swap
                                        · omega
                                        by_cases c1934 : 0 < b8
                                        swap
                                        · omega
                                        by_cases c1935 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                        swap
                                        · omega
                                        by_cases c1936 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                        swap
                                        · omega
                                        have f1937 := pair_fact E (i := 10) (j := 8) rfl rfl c1933 c1934
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1937
                                        omega
                                      have f1938 := pair_fact E (i := 8) (j := 10) rfl rfl c1929 c1930
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1938
                                      omega
                                    by_cases c1939 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c1940 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f1941 := pair_fact E (i := 8) (j := 6) rfl rfl c1922 c1923
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1941
                                    omega
                                  by_cases c1942 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f1943 := pair_fact E (i := 8) (j := 4) rfl rfl c1919 c1920
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1943
                                  omega
                                by_cases c1944 : b0 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f1945 := pair_fact E (i := 8) (j := 2) rfl rfl c1916 c1917
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1945
                                omega
                              by_cases c1946 : 0 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f1947 := pair_fact E (i := 8) (j := 0) rfl rfl c1913 c1914
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1947
                              omega
                            have f1948 := pair_fact E (i := 6) (j := 10) rfl rfl c1909 c1910
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1948
                            omega
                          by_cases c1949 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f1950 := pair_fact E (i := 6) (j := 2) rfl rfl c1906 c1907
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1950
                          omega
                        have f1951 := pair_fact E (i := 2) (j := 8) rfl rfl c1902 c1903
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1951
                        omega
                      have f1952 := pair_fact E (i := 0) (j := 2) rfl rfl c1898 c1899
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1952
                      omega
                    have f1953 := pair_fact E (i := 2) (j := 4) rfl rfl c1889 c1890
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1953
                    by_cases c1954 : 0 < a6
                    swap
                    · omega
                    by_cases c1955 : 0 < b8
                    swap
                    · omega
                    by_cases c1956 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c1957 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f1958 := pair_fact E (i := 6) (j := 8) rfl rfl c1954 c1955
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1958
                    omega
                  by_cases c1959 : 0 < a0 + a2
                  swap
                  · omega
                  have f1960 := pair_fact E (i := 2) (j := 0) rfl rfl c1886 c1887
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1960
                  by_cases c1961 : 0 < a2
                  swap
                  · omega
                  by_cases c1962 : 0 < b4
                  swap
                  · omega
                  by_cases c1963 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c1964 : b0 + b2 < a0 + a2
                  swap
                  · -- branch
                    by_cases c1965 : 0 < a0
                    swap
                    · omega
                    by_cases c1966 : 0 < b2
                    swap
                    · omega
                    by_cases c1967 : 0 < b0 + b2
                    swap
                    · omega
                    by_cases c1968 : b0 < 0 + a0
                    swap
                    · -- branch
                      by_cases c1969 : 0 < a2
                      swap
                      · omega
                      by_cases c1970 : 0 < b2
                      swap
                      · omega
                      by_cases c1971 : a0 < b0 + b2
                      swap
                      · omega
                      by_cases c1972 : b0 < a0 + a2
                      swap
                      · -- branch
                        by_cases c1973 : 0 < a2
                        swap
                        · omega
                        by_cases c1974 : 0 < b8
                        swap
                        · omega
                        by_cases c1975 : a0 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1976 : b0 + b2 + b4 + b6 < a0 + a2
                        swap
                        · -- branch
                          by_cases c1977 : 0 < a6
                          swap
                          · omega
                          by_cases c1978 : 0 < b2
                          swap
                          · omega
                          by_cases c1979 : a0 + a2 + a4 < b0 + b2
                          swap
                          · omega
                          by_cases c1980 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f1981 := pair_fact E (i := 6) (j := 2) rfl rfl c1977 c1978
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1981
                          by_cases c1982 : 0 < a8
                          swap
                          · omega
                          by_cases c1983 : 0 < b8
                          swap
                          · omega
                          by_cases c1984 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c1985 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f1986 := pair_fact E (i := 8) (j := 8) rfl rfl c1982 c1983
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1986
                          omega
                        have f1987 := pair_fact E (i := 2) (j := 8) rfl rfl c1973 c1974
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1987
                        omega
                      have f1988 := pair_fact E (i := 2) (j := 2) rfl rfl c1969 c1970
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1988
                      omega
                    have f1989 := pair_fact E (i := 0) (j := 2) rfl rfl c1965 c1966
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1989
                    omega
                  have f1990 := pair_fact E (i := 2) (j := 4) rfl rfl c1961 c1962
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1990
                  omega
                have f1991 := pair_fact E (i := 2) (j := 10) rfl rfl c1882 c1883
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1991
                omega
              by_cases c1992 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c1993 : b0 + b2 + b4 < a0 + a2
              swap
              · omega
              have f1994 := pair_fact E (i := 2) (j := 6) rfl rfl c1845 c1881
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1994
              omega
            have f1995 := pair_fact E (i := 0) (j := 10) rfl rfl c1696 c1697
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1995
            omega
          by_cases c1996 : a0 + a2 + a4 < b0 + b2 + b4 + b6
          swap
          · omega
          by_cases c1997 : b0 + b2 + b4 < a0 + a2 + a4 + a6
          swap
          · omega
          have f1998 := pair_fact E (i := 6) (j := 6) rfl rfl c1694 c1695
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1998
          omega
        by_cases c1999 : 0 < a0 + a2 + a4 + a6
        swap
        · omega
        have f2000 := pair_fact E (i := 6) (j := 0) rfl rfl c1691 c1692
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2000
        omega
      have f2001 := pair_fact E (i := 0) (j := 8) rfl rfl c1687 c1688
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2001
      omega
    by_cases c2002 : 0 < b0 + b2 + b4 + b6
    swap
    · omega
    by_cases c2003 : b0 + b2 + b4 < 0 + a0
    swap
    · -- branch
      by_cases c2004 : 0 < a0
      swap
      · omega
      by_cases c2005 : 0 < b8
      swap
      · -- branch
        by_cases c2006 : 0 < a8
        swap
        · omega
        by_cases c2007 : 0 < b0
        swap
        · omega
        by_cases c2008 : a0 + a2 + a4 + a6 < 0 + b0
        swap
        · -- branch
          by_cases c2009 : 0 < a8
          swap
          · omega
          by_cases c2010 : 0 < b2
          swap
          · omega
          by_cases c2011 : a0 + a2 + a4 + a6 < b0 + b2
          swap
          · omega
          by_cases c2012 : b0 < a0 + a2 + a4 + a6 + a8
          swap
          · omega
          have f2013 := pair_fact E (i := 8) (j := 2) rfl rfl c2009 c2010
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2013
          by_cases c2014 : 0 < a8
          swap
          · omega
          by_cases c2015 : 0 < b4
          swap
          · omega
          by_cases c2016 : a0 + a2 + a4 + a6 < b0 + b2 + b4
          swap
          · omega
          by_cases c2017 : b0 + b2 < a0 + a2 + a4 + a6 + a8
          swap
          · omega
          have f2018 := pair_fact E (i := 8) (j := 4) rfl rfl c2014 c2015
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2018
          omega
        by_cases c2019 : 0 < a0 + a2 + a4 + a6 + a8
        swap
        · omega
        have f2020 := pair_fact E (i := 8) (j := 0) rfl rfl c2006 c2007
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2020
        omega
      by_cases c2021 : 0 < b0 + b2 + b4 + b6 + b8
      swap
      · omega
      by_cases c2022 : b0 + b2 + b4 + b6 < 0 + a0
      swap
      · -- branch
        by_cases c2023 : 0 < a0
        swap
        · omega
        by_cases c2024 : 0 < b10
        swap
        · -- branch
          by_cases c2025 : 0 < a2
          swap
          · -- branch
            by_cases c2026 : 0 < a2
            swap
            · -- branch
              by_cases c2027 : 0 < a2
              swap
              · -- branch
                by_cases c2028 : 0 < a2
                swap
                · -- branch
                  by_cases c2029 : 0 < a2
                  swap
                  · -- branch
                    by_cases c2030 : 0 < a2
                    swap
                    · -- branch
                      by_cases c2031 : 0 < a8
                      swap
                      · omega
                      by_cases c2032 : 0 < b0
                      swap
                      · omega
                      by_cases c2033 : a0 + a2 + a4 + a6 < 0 + b0
                      swap
                      · -- branch
                        by_cases c2034 : 0 < a8
                        swap
                        · omega
                        by_cases c2035 : 0 < b10
                        swap
                        · -- branch
                          by_cases c2036 : 0 < a0
                          swap
                          · omega
                          by_cases c2037 : 0 < b2
                          swap
                          · omega
                          by_cases c2038 : 0 < b0 + b2
                          swap
                          · omega
                          by_cases c2039 : b0 < 0 + a0
                          swap
                          · -- branch
                            by_cases c2040 : 0 < a8
                            swap
                            · omega
                            by_cases c2041 : 0 < b2
                            swap
                            · omega
                            by_cases c2042 : a0 + a2 + a4 + a6 < b0 + b2
                            swap
                            · omega
                            by_cases c2043 : b0 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f2044 := pair_fact E (i := 8) (j := 2) rfl rfl c2040 c2041
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2044
                            by_cases c2045 : 0 < a8
                            swap
                            · omega
                            by_cases c2046 : 0 < b4
                            swap
                            · omega
                            by_cases c2047 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c2048 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f2049 := pair_fact E (i := 8) (j := 4) rfl rfl c2045 c2046
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2049
                            omega
                          have f2050 := pair_fact E (i := 0) (j := 2) rfl rfl c2036 c2037
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2050
                          by_cases c2051 : 0 < a4
                          swap
                          · -- branch
                            by_cases c2052 : 0 < a6
                            swap
                            · omega
                            by_cases c2053 : 0 < b2
                            swap
                            · omega
                            by_cases c2054 : a0 + a2 + a4 < b0 + b2
                            swap
                            · omega
                            by_cases c2055 : b0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f2056 := pair_fact E (i := 6) (j := 2) rfl rfl c2052 c2053
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2056
                            omega
                          by_cases c2057 : 0 < b2
                          swap
                          · omega
                          by_cases c2058 : a0 + a2 < b0 + b2
                          swap
                          · omega
                          by_cases c2059 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f2060 := pair_fact E (i := 4) (j := 2) rfl rfl c2051 c2057
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2060
                          omega
                        by_cases c2061 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c2062 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f2063 := pair_fact E (i := 8) (j := 10) rfl rfl c2034 c2035
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2063
                        omega
                      by_cases c2064 : 0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f2065 := pair_fact E (i := 8) (j := 0) rfl rfl c2031 c2032
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2065
                      omega
                    by_cases c2066 : 0 < b8
                    swap
                    · omega
                    by_cases c2067 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c2068 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · omega
                    have f2069 := pair_fact E (i := 2) (j := 8) rfl rfl c2030 c2066
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2069
                    omega
                  by_cases c2070 : 0 < b6
                  swap
                  · omega
                  by_cases c2071 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c2072 : b0 + b2 + b4 < a0 + a2
                  swap
                  · omega
                  have f2073 := pair_fact E (i := 2) (j := 6) rfl rfl c2029 c2070
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2073
                  omega
                by_cases c2074 : 0 < b4
                swap
                · omega
                by_cases c2075 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c2076 : b0 + b2 < a0 + a2
                swap
                · omega
                have f2077 := pair_fact E (i := 2) (j := 4) rfl rfl c2028 c2074
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2077
                omega
              by_cases c2078 : 0 < b2
              swap
              · omega
              by_cases c2079 : a0 < b0 + b2
              swap
              · omega
              by_cases c2080 : b0 < a0 + a2
              swap
              · omega
              have f2081 := pair_fact E (i := 2) (j := 2) rfl rfl c2027 c2078
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2081
              omega
            by_cases c2082 : 0 < b0
            swap
            · omega
            by_cases c2083 : a0 < 0 + b0
            swap
            · omega
            by_cases c2084 : 0 < a0 + a2
            swap
            · omega
            have f2085 := pair_fact E (i := 2) (j := 0) rfl rfl c2026 c2082
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2085
            omega
          by_cases c2086 : 0 < b10
          swap
          · -- branch
            by_cases c2087 : 0 < a2
            swap
            · omega
            by_cases c2088 : 0 < b0
            swap
            · omega
            by_cases c2089 : a0 < 0 + b0
            swap
            · -- branch
              by_cases c2090 : 0 < a2
              swap
              · omega
              by_cases c2091 : 0 < b4
              swap
              · omega
              by_cases c2092 : a0 < b0 + b2 + b4
              swap
              · omega
              by_cases c2093 : b0 + b2 < a0 + a2
              swap
              · -- branch
                by_cases c2094 : 0 < a2
                swap
                · omega
                by_cases c2095 : 0 < b2
                swap
                · omega
                by_cases c2096 : a0 < b0 + b2
                swap
                · omega
                by_cases c2097 : b0 < a0 + a2
                swap
                · omega
                have f2098 := pair_fact E (i := 2) (j := 2) rfl rfl c2094 c2095
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2098
                by_cases c2099 : 0 < a0
                swap
                · omega
                by_cases c2100 : 0 < b2
                swap
                · omega
                by_cases c2101 : 0 < b0 + b2
                swap
                · omega
                by_cases c2102 : b0 < 0 + a0
                swap
                · -- branch
                  by_cases c2103 : 0 < a2
                  swap
                  · omega
                  by_cases c2104 : 0 < b6
                  swap
                  · omega
                  by_cases c2105 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c2106 : b0 + b2 + b4 < a0 + a2
                  swap
                  · -- branch
                    by_cases c2107 : 0 < a2
                    swap
                    · omega
                    by_cases c2108 : 0 < b8
                    swap
                    · omega
                    by_cases c2109 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c2110 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · -- branch
                      by_cases c2111 : 0 < a8
                      swap
                      · omega
                      by_cases c2112 : 0 < b0
                      swap
                      · omega
                      by_cases c2113 : a0 + a2 + a4 + a6 < 0 + b0
                      swap
                      · -- branch
                        by_cases c2114 : 0 < a8
                        swap
                        · omega
                        by_cases c2115 : 0 < b2
                        swap
                        · omega
                        by_cases c2116 : a0 + a2 + a4 + a6 < b0 + b2
                        swap
                        · -- branch
                          by_cases c2117 : 0 < a8
                          swap
                          · omega
                          by_cases c2118 : 0 < b8
                          swap
                          · omega
                          by_cases c2119 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c2120 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f2121 := pair_fact E (i := 8) (j := 8) rfl rfl c2117 c2118
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2121
                          by_cases c2122 : 0 < a10
                          swap
                          · omega
                          by_cases c2123 : 0 < b8
                          swap
                          · omega
                          by_cases c2124 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c2125 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                          swap
                          · omega
                          have f2126 := pair_fact E (i := 10) (j := 8) rfl rfl c2122 c2123
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2126
                          omega
                        by_cases c2127 : b0 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f2128 := pair_fact E (i := 8) (j := 2) rfl rfl c2114 c2115
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2128
                        omega
                      by_cases c2129 : 0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f2130 := pair_fact E (i := 8) (j := 0) rfl rfl c2111 c2112
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2130
                      omega
                    have f2131 := pair_fact E (i := 2) (j := 8) rfl rfl c2107 c2108
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2131
                    omega
                  have f2132 := pair_fact E (i := 2) (j := 6) rfl rfl c2103 c2104
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2132
                  omega
                have f2133 := pair_fact E (i := 0) (j := 2) rfl rfl c2099 c2100
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2133
                omega
              have f2134 := pair_fact E (i := 2) (j := 4) rfl rfl c2090 c2091
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2134
              by_cases c2135 : 0 < a8
              swap
              · -- branch
                by_cases c2136 : 0 < a4
                swap
                · omega
                by_cases c2137 : 0 < b8
                swap
                · omega
                by_cases c2138 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c2139 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                swap
                · omega
                have f2140 := pair_fact E (i := 4) (j := 8) rfl rfl c2136 c2137
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2140
                omega
              by_cases c2141 : 0 < b8
              swap
              · omega
              by_cases c2142 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
              swap
              · omega
              by_cases c2143 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
              swap
              · omega
              have f2144 := pair_fact E (i := 8) (j := 8) rfl rfl c2135 c2141
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2144
              omega
            by_cases c2145 : 0 < a0 + a2
            swap
            · omega
            have f2146 := pair_fact E (i := 2) (j := 0) rfl rfl c2087 c2088
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2146
            by_cases c2147 : 0 < a2
            swap
            · omega
            by_cases c2148 : 0 < b4
            swap
            · omega
            by_cases c2149 : a0 < b0 + b2 + b4
            swap
            · omega
            by_cases c2150 : b0 + b2 < a0 + a2
            swap
            · -- branch
              by_cases c2151 : 0 < a0
              swap
              · omega
              by_cases c2152 : 0 < b2
              swap
              · omega
              by_cases c2153 : 0 < b0 + b2
              swap
              · omega
              by_cases c2154 : b0 < 0 + a0
              swap
              · -- branch
                by_cases c2155 : 0 < a2
                swap
                · omega
                by_cases c2156 : 0 < b2
                swap
                · omega
                by_cases c2157 : a0 < b0 + b2
                swap
                · omega
                by_cases c2158 : b0 < a0 + a2
                swap
                · -- branch
                  by_cases c2159 : 0 < a2
                  swap
                  · omega
                  by_cases c2160 : 0 < b6
                  swap
                  · omega
                  by_cases c2161 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c2162 : b0 + b2 + b4 < a0 + a2
                  swap
                  · -- branch
                    by_cases c2163 : 0 < a2
                    swap
                    · omega
                    by_cases c2164 : 0 < b8
                    swap
                    · omega
                    by_cases c2165 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c2166 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · -- branch
                      by_cases c2167 : 0 < a8
                      swap
                      · omega
                      by_cases c2168 : 0 < b0
                      swap
                      · omega
                      by_cases c2169 : a0 + a2 + a4 + a6 < 0 + b0
                      swap
                      · -- branch
                        by_cases c2170 : 0 < a8
                        swap
                        · omega
                        by_cases c2171 : 0 < b10
                        swap
                        · -- branch
                          by_cases c2172 : 0 < a4
                          swap
                          · -- branch
                            by_cases c2173 : 0 < a4
                            swap
                            · -- branch
                              by_cases c2174 : 0 < a4
                              swap
                              · -- branch
                                by_cases c2175 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c2176 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c2177 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c2178 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c2179 : 0 < b0
                                      swap
                                      · omega
                                      by_cases c2180 : a0 + a2 + a4 < 0 + b0
                                      swap
                                      · -- branch
                                        by_cases c2181 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c2182 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c2183 : a0 + a2 + a4 < b0 + b2
                                        swap
                                        · omega
                                        by_cases c2184 : b0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f2185 := pair_fact E (i := 6) (j := 2) rfl rfl c2181 c2182
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2185
                                        by_cases c2186 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c2187 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c2188 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c2189 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f2190 := pair_fact E (i := 8) (j := 4) rfl rfl c2186 c2187
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2190
                                        omega
                                      by_cases c2191 : 0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f2192 := pair_fact E (i := 6) (j := 0) rfl rfl c2178 c2179
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2192
                                      omega
                                    by_cases c2193 : 0 < b10
                                    swap
                                    · omega
                                    by_cases c2194 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c2195 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f2196 := pair_fact E (i := 4) (j := 10) rfl rfl c2177 c2193
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2196
                                    omega
                                  by_cases c2197 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c2198 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c2199 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f2200 := pair_fact E (i := 4) (j := 8) rfl rfl c2176 c2197
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2200
                                  omega
                                by_cases c2201 : 0 < b6
                                swap
                                · omega
                                by_cases c2202 : a0 + a2 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c2203 : b0 + b2 + b4 < a0 + a2 + a4
                                swap
                                · omega
                                have f2204 := pair_fact E (i := 4) (j := 6) rfl rfl c2175 c2201
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2204
                                omega
                              by_cases c2205 : 0 < b4
                              swap
                              · omega
                              by_cases c2206 : a0 + a2 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c2207 : b0 + b2 < a0 + a2 + a4
                              swap
                              · omega
                              have f2208 := pair_fact E (i := 4) (j := 4) rfl rfl c2174 c2205
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2208
                              omega
                            by_cases c2209 : 0 < b2
                            swap
                            · omega
                            by_cases c2210 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c2211 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f2212 := pair_fact E (i := 4) (j := 2) rfl rfl c2173 c2209
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2212
                            omega
                          by_cases c2213 : 0 < b0
                          swap
                          · omega
                          by_cases c2214 : a0 + a2 < 0 + b0
                          swap
                          · -- branch
                            by_cases c2215 : 0 < a4
                            swap
                            · omega
                            by_cases c2216 : 0 < b2
                            swap
                            · omega
                            by_cases c2217 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c2218 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f2219 := pair_fact E (i := 4) (j := 2) rfl rfl c2215 c2216
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2219
                            by_cases c2220 : 0 < a4
                            swap
                            · omega
                            by_cases c2221 : 0 < b4
                            swap
                            · omega
                            by_cases c2222 : a0 + a2 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c2223 : b0 + b2 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c2224 : 0 < a4
                              swap
                              · omega
                              by_cases c2225 : 0 < b6
                              swap
                              · omega
                              by_cases c2226 : a0 + a2 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c2227 : b0 + b2 + b4 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c2228 : 0 < a4
                                swap
                                · omega
                                by_cases c2229 : 0 < b8
                                swap
                                · omega
                                by_cases c2230 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                swap
                                · omega
                                by_cases c2231 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c2232 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c2233 : 0 < b10
                                  swap
                                  · -- branch
                                    by_cases c2234 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c2235 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c2236 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                    swap
                                    · -- branch
                                      by_cases c2237 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c2238 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c2239 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c2240 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f2241 := pair_fact E (i := 6) (j := 4) rfl rfl c2237 c2238
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2241
                                      omega
                                    by_cases c2242 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f2243 := pair_fact E (i := 8) (j := 4) rfl rfl c2234 c2235
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2243
                                    omega
                                  by_cases c2244 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                  swap
                                  · omega
                                  by_cases c2245 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f2246 := pair_fact E (i := 4) (j := 10) rfl rfl c2232 c2233
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2246
                                  omega
                                have f2247 := pair_fact E (i := 4) (j := 8) rfl rfl c2228 c2229
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2247
                                omega
                              have f2248 := pair_fact E (i := 4) (j := 6) rfl rfl c2224 c2225
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2248
                              omega
                            have f2249 := pair_fact E (i := 4) (j := 4) rfl rfl c2220 c2221
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2249
                            omega
                          by_cases c2250 : 0 < a0 + a2 + a4
                          swap
                          · omega
                          have f2251 := pair_fact E (i := 4) (j := 0) rfl rfl c2172 c2213
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2251
                          omega
                        by_cases c2252 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c2253 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f2254 := pair_fact E (i := 8) (j := 10) rfl rfl c2170 c2171
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2254
                        omega
                      by_cases c2255 : 0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f2256 := pair_fact E (i := 8) (j := 0) rfl rfl c2167 c2168
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2256
                      omega
                    have f2257 := pair_fact E (i := 2) (j := 8) rfl rfl c2163 c2164
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2257
                    omega
                  have f2258 := pair_fact E (i := 2) (j := 6) rfl rfl c2159 c2160
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2258
                  omega
                have f2259 := pair_fact E (i := 2) (j := 2) rfl rfl c2155 c2156
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2259
                omega
              have f2260 := pair_fact E (i := 0) (j := 2) rfl rfl c2151 c2152
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2260
              omega
            have f2261 := pair_fact E (i := 2) (j := 4) rfl rfl c2147 c2148
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2261
            omega
          by_cases c2262 : a0 < b0 + b2 + b4 + b6 + b8 + b10
          swap
          · omega
          by_cases c2263 : b0 + b2 + b4 + b6 + b8 < a0 + a2
          swap
          · omega
          have f2264 := pair_fact E (i := 2) (j := 10) rfl rfl c2025 c2086
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2264
          omega
        by_cases c2265 : 0 < b0 + b2 + b4 + b6 + b8 + b10
        swap
        · omega
        by_cases c2266 : b0 + b2 + b4 + b6 + b8 < 0 + a0
        swap
        · -- branch
          by_cases c2267 : 0 < a2
          swap
          · -- branch
            by_cases c2268 : 0 < a2
            swap
            · -- branch
              by_cases c2269 : 0 < a2
              swap
              · -- branch
                by_cases c2270 : 0 < a2
                swap
                · -- branch
                  by_cases c2271 : 0 < a2
                  swap
                  · -- branch
                    by_cases c2272 : 0 < a2
                    swap
                    · -- branch
                      by_cases c2273 : 0 < a8
                      swap
                      · omega
                      by_cases c2274 : 0 < b0
                      swap
                      · omega
                      by_cases c2275 : a0 + a2 + a4 + a6 < 0 + b0
                      swap
                      · -- branch
                        by_cases c2276 : 0 < a0
                        swap
                        · omega
                        by_cases c2277 : 0 < b2
                        swap
                        · omega
                        by_cases c2278 : 0 < b0 + b2
                        swap
                        · omega
                        by_cases c2279 : b0 < 0 + a0
                        swap
                        · -- branch
                          by_cases c2280 : 0 < a8
                          swap
                          · omega
                          by_cases c2281 : 0 < b2
                          swap
                          · omega
                          by_cases c2282 : a0 + a2 + a4 + a6 < b0 + b2
                          swap
                          · omega
                          by_cases c2283 : b0 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f2284 := pair_fact E (i := 8) (j := 2) rfl rfl c2280 c2281
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2284
                          by_cases c2285 : 0 < a8
                          swap
                          · omega
                          by_cases c2286 : 0 < b4
                          swap
                          · omega
                          by_cases c2287 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c2288 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f2289 := pair_fact E (i := 8) (j := 4) rfl rfl c2285 c2286
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2289
                          omega
                        have f2290 := pair_fact E (i := 0) (j := 2) rfl rfl c2276 c2277
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2290
                        by_cases c2291 : 0 < a4
                        swap
                        · -- branch
                          by_cases c2292 : 0 < a6
                          swap
                          · omega
                          by_cases c2293 : 0 < b2
                          swap
                          · omega
                          by_cases c2294 : a0 + a2 + a4 < b0 + b2
                          swap
                          · omega
                          by_cases c2295 : b0 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f2296 := pair_fact E (i := 6) (j := 2) rfl rfl c2292 c2293
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2296
                          omega
                        by_cases c2297 : 0 < b2
                        swap
                        · omega
                        by_cases c2298 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c2299 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f2300 := pair_fact E (i := 4) (j := 2) rfl rfl c2291 c2297
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2300
                        omega
                      by_cases c2301 : 0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f2302 := pair_fact E (i := 8) (j := 0) rfl rfl c2273 c2274
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2302
                      omega
                    by_cases c2303 : 0 < b8
                    swap
                    · omega
                    by_cases c2304 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c2305 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · omega
                    have f2306 := pair_fact E (i := 2) (j := 8) rfl rfl c2272 c2303
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2306
                    omega
                  by_cases c2307 : 0 < b6
                  swap
                  · omega
                  by_cases c2308 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c2309 : b0 + b2 + b4 < a0 + a2
                  swap
                  · omega
                  have f2310 := pair_fact E (i := 2) (j := 6) rfl rfl c2271 c2307
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2310
                  omega
                by_cases c2311 : 0 < b4
                swap
                · omega
                by_cases c2312 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c2313 : b0 + b2 < a0 + a2
                swap
                · omega
                have f2314 := pair_fact E (i := 2) (j := 4) rfl rfl c2270 c2311
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2314
                omega
              by_cases c2315 : 0 < b2
              swap
              · omega
              by_cases c2316 : a0 < b0 + b2
              swap
              · omega
              by_cases c2317 : b0 < a0 + a2
              swap
              · omega
              have f2318 := pair_fact E (i := 2) (j := 2) rfl rfl c2269 c2315
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2318
              omega
            by_cases c2319 : 0 < b0
            swap
            · omega
            by_cases c2320 : a0 < 0 + b0
            swap
            · omega
            by_cases c2321 : 0 < a0 + a2
            swap
            · omega
            have f2322 := pair_fact E (i := 2) (j := 0) rfl rfl c2268 c2319
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2322
            omega
          by_cases c2323 : 0 < b10
          swap
          · omega
          by_cases c2324 : a0 < b0 + b2 + b4 + b6 + b8 + b10
          swap
          · omega
          by_cases c2325 : b0 + b2 + b4 + b6 + b8 < a0 + a2
          swap
          · -- branch
            by_cases c2326 : 0 < a2
            swap
            · omega
            by_cases c2327 : 0 < b0
            swap
            · omega
            by_cases c2328 : a0 < 0 + b0
            swap
            · -- branch
              by_cases c2329 : 0 < a2
              swap
              · omega
              by_cases c2330 : 0 < b4
              swap
              · omega
              by_cases c2331 : a0 < b0 + b2 + b4
              swap
              · omega
              by_cases c2332 : b0 + b2 < a0 + a2
              swap
              · -- branch
                by_cases c2333 : 0 < a2
                swap
                · omega
                by_cases c2334 : 0 < b2
                swap
                · omega
                by_cases c2335 : a0 < b0 + b2
                swap
                · omega
                by_cases c2336 : b0 < a0 + a2
                swap
                · omega
                have f2337 := pair_fact E (i := 2) (j := 2) rfl rfl c2333 c2334
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2337
                by_cases c2338 : 0 < a0
                swap
                · omega
                by_cases c2339 : 0 < b2
                swap
                · omega
                by_cases c2340 : 0 < b0 + b2
                swap
                · omega
                by_cases c2341 : b0 < 0 + a0
                swap
                · -- branch
                  by_cases c2342 : 0 < a2
                  swap
                  · omega
                  by_cases c2343 : 0 < b6
                  swap
                  · omega
                  by_cases c2344 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c2345 : b0 + b2 + b4 < a0 + a2
                  swap
                  · -- branch
                    by_cases c2346 : 0 < a2
                    swap
                    · omega
                    by_cases c2347 : 0 < b8
                    swap
                    · omega
                    by_cases c2348 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c2349 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · -- branch
                      by_cases c2350 : 0 < a8
                      swap
                      · omega
                      by_cases c2351 : 0 < b0
                      swap
                      · omega
                      by_cases c2352 : a0 + a2 + a4 + a6 < 0 + b0
                      swap
                      · -- branch
                        by_cases c2353 : 0 < a8
                        swap
                        · omega
                        by_cases c2354 : 0 < b2
                        swap
                        · omega
                        by_cases c2355 : a0 + a2 + a4 + a6 < b0 + b2
                        swap
                        · -- branch
                          by_cases c2356 : 0 < a8
                          swap
                          · omega
                          by_cases c2357 : 0 < b8
                          swap
                          · omega
                          by_cases c2358 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c2359 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f2360 := pair_fact E (i := 8) (j := 8) rfl rfl c2356 c2357
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2360
                          by_cases c2361 : 0 < a8
                          swap
                          · omega
                          by_cases c2362 : 0 < b10
                          swap
                          · omega
                          by_cases c2363 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c2364 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                          swap
                          · -- branch
                            by_cases c2365 : 0 < a10
                            swap
                            · omega
                            by_cases c2366 : 0 < b8
                            swap
                            · omega
                            by_cases c2367 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c2368 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f2369 := pair_fact E (i := 10) (j := 8) rfl rfl c2365 c2366
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2369
                            omega
                          have f2370 := pair_fact E (i := 8) (j := 10) rfl rfl c2361 c2362
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2370
                          omega
                        by_cases c2371 : b0 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f2372 := pair_fact E (i := 8) (j := 2) rfl rfl c2353 c2354
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2372
                        omega
                      by_cases c2373 : 0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f2374 := pair_fact E (i := 8) (j := 0) rfl rfl c2350 c2351
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2374
                      omega
                    have f2375 := pair_fact E (i := 2) (j := 8) rfl rfl c2346 c2347
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2375
                    omega
                  have f2376 := pair_fact E (i := 2) (j := 6) rfl rfl c2342 c2343
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2376
                  omega
                have f2377 := pair_fact E (i := 0) (j := 2) rfl rfl c2338 c2339
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2377
                omega
              have f2378 := pair_fact E (i := 2) (j := 4) rfl rfl c2329 c2330
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2378
              by_cases c2379 : 0 < a2
              swap
              · omega
              by_cases c2380 : 0 < b6
              swap
              · omega
              by_cases c2381 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c2382 : b0 + b2 + b4 < a0 + a2
              swap
              · -- branch
                by_cases c2383 : 0 < a8
                swap
                · omega
                by_cases c2384 : 0 < b8
                swap
                · omega
                by_cases c2385 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c2386 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                swap
                · omega
                have f2387 := pair_fact E (i := 8) (j := 8) rfl rfl c2383 c2384
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2387
                omega
              have f2388 := pair_fact E (i := 2) (j := 6) rfl rfl c2379 c2380
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2388
              by_cases c2389 : 0 < a2
              swap
              · omega
              by_cases c2390 : 0 < b2
              swap
              · -- branch
                by_cases c2391 : 0 < a0
                swap
                · omega
                by_cases c2392 : 0 < b2
                swap
                · -- branch
                  by_cases c2393 : 0 < a4
                  swap
                  · -- branch
                    by_cases c2394 : 0 < a8
                    swap
                    · omega
                    by_cases c2395 : 0 < b8
                    swap
                    · omega
                    by_cases c2396 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c2397 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                    swap
                    · omega
                    have f2398 := pair_fact E (i := 8) (j := 8) rfl rfl c2394 c2395
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2398
                    omega
                  by_cases c2399 : 0 < b8
                  swap
                  · omega
                  by_cases c2400 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c2401 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                  swap
                  · omega
                  have f2402 := pair_fact E (i := 4) (j := 8) rfl rfl c2393 c2399
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2402
                  omega
                by_cases c2403 : 0 < b0 + b2
                swap
                · omega
                by_cases c2404 : b0 < 0 + a0
                swap
                · omega
                have f2405 := pair_fact E (i := 0) (j := 2) rfl rfl c2391 c2392
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2405
                omega
              by_cases c2406 : a0 < b0 + b2
              swap
              · -- branch
                by_cases c2407 : 0 < a0
                swap
                · omega
                by_cases c2408 : 0 < b2
                swap
                · omega
                by_cases c2409 : 0 < b0 + b2
                swap
                · omega
                by_cases c2410 : b0 < 0 + a0
                swap
                · omega
                have f2411 := pair_fact E (i := 0) (j := 2) rfl rfl c2407 c2408
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2411
                by_cases c2412 : 0 < a2
                swap
                · omega
                by_cases c2413 : 0 < b8
                swap
                · omega
                by_cases c2414 : a0 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c2415 : b0 + b2 + b4 + b6 < a0 + a2
                swap
                · -- branch
                  by_cases c2416 : 0 < a8
                  swap
                  · omega
                  by_cases c2417 : 0 < b8
                  swap
                  · omega
                  by_cases c2418 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c2419 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                  swap
                  · omega
                  have f2420 := pair_fact E (i := 8) (j := 8) rfl rfl c2416 c2417
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2420
                  omega
                have f2421 := pair_fact E (i := 2) (j := 8) rfl rfl c2412 c2413
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2421
                by_cases c2422 : 0 < a4
                swap
                · -- branch
                  by_cases c2423 : 0 < a6
                  swap
                  · omega
                  by_cases c2424 : 0 < b8
                  swap
                  · omega
                  by_cases c2425 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c2426 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                  swap
                  · omega
                  have f2427 := pair_fact E (i := 6) (j := 8) rfl rfl c2423 c2424
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2427
                  omega
                by_cases c2428 : 0 < b8
                swap
                · omega
                by_cases c2429 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c2430 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                swap
                · omega
                have f2431 := pair_fact E (i := 4) (j := 8) rfl rfl c2422 c2428
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2431
                omega
              by_cases c2432 : b0 < a0 + a2
              swap
              · omega
              have f2433 := pair_fact E (i := 2) (j := 2) rfl rfl c2389 c2390
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2433
              omega
            by_cases c2434 : 0 < a0 + a2
            swap
            · omega
            have f2435 := pair_fact E (i := 2) (j := 0) rfl rfl c2326 c2327
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2435
            by_cases c2436 : 0 < a2
            swap
            · omega
            by_cases c2437 : 0 < b4
            swap
            · omega
            by_cases c2438 : a0 < b0 + b2 + b4
            swap
            · omega
            by_cases c2439 : b0 + b2 < a0 + a2
            swap
            · -- branch
              by_cases c2440 : 0 < a0
              swap
              · omega
              by_cases c2441 : 0 < b2
              swap
              · omega
              by_cases c2442 : 0 < b0 + b2
              swap
              · omega
              by_cases c2443 : b0 < 0 + a0
              swap
              · -- branch
                by_cases c2444 : 0 < a2
                swap
                · omega
                by_cases c2445 : 0 < b2
                swap
                · omega
                by_cases c2446 : a0 < b0 + b2
                swap
                · omega
                by_cases c2447 : b0 < a0 + a2
                swap
                · -- branch
                  by_cases c2448 : 0 < a2
                  swap
                  · omega
                  by_cases c2449 : 0 < b6
                  swap
                  · omega
                  by_cases c2450 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c2451 : b0 + b2 + b4 < a0 + a2
                  swap
                  · -- branch
                    by_cases c2452 : 0 < a2
                    swap
                    · omega
                    by_cases c2453 : 0 < b8
                    swap
                    · omega
                    by_cases c2454 : a0 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c2455 : b0 + b2 + b4 + b6 < a0 + a2
                    swap
                    · -- branch
                      by_cases c2456 : 0 < a8
                      swap
                      · omega
                      by_cases c2457 : 0 < b0
                      swap
                      · omega
                      by_cases c2458 : a0 + a2 + a4 + a6 < 0 + b0
                      swap
                      · -- branch
                        by_cases c2459 : 0 < a8
                        swap
                        · omega
                        by_cases c2460 : 0 < b10
                        swap
                        · omega
                        by_cases c2461 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c2462 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                        swap
                        · -- branch
                          by_cases c2463 : 0 < a10
                          swap
                          · omega
                          by_cases c2464 : 0 < b0
                          swap
                          · omega
                          by_cases c2465 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                          swap
                          · -- branch
                            by_cases c2466 : 0 < a10
                            swap
                            · omega
                            by_cases c2467 : 0 < b2
                            swap
                            · omega
                            by_cases c2468 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                            swap
                            · -- branch
                              by_cases c2469 : 0 < a10
                              swap
                              · omega
                              by_cases c2470 : 0 < b4
                              swap
                              · omega
                              by_cases c2471 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                              swap
                              · -- branch
                                by_cases c2472 : 0 < a10
                                swap
                                · omega
                                by_cases c2473 : 0 < b10
                                swap
                                · omega
                                by_cases c2474 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c2475 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f2476 := pair_fact E (i := 10) (j := 10) rfl rfl c2472 c2473
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2476
                                by_cases c2477 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c2478 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c2479 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c2480 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c2481 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c2482 : 0 < a4
                                          swap
                                          · -- branch
                                            by_cases c2483 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c2484 : 0 < b0
                                            swap
                                            · omega
                                            by_cases c2485 : a0 + a2 + a4 < 0 + b0
                                            swap
                                            · -- branch
                                              by_cases c2486 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c2487 : 0 < b2
                                              swap
                                              · omega
                                              by_cases c2488 : a0 + a2 + a4 < b0 + b2
                                              swap
                                              · omega
                                              by_cases c2489 : b0 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f2490 := pair_fact E (i := 6) (j := 2) rfl rfl c2486 c2487
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2490
                                              by_cases c2491 : 0 < a8
                                              swap
                                              · omega
                                              by_cases c2492 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c2493 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c2494 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                              swap
                                              · omega
                                              have f2495 := pair_fact E (i := 8) (j := 4) rfl rfl c2491 c2492
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2495
                                              omega
                                            by_cases c2496 : 0 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f2497 := pair_fact E (i := 6) (j := 0) rfl rfl c2483 c2484
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2497
                                            omega
                                          by_cases c2498 : 0 < b10
                                          swap
                                          · omega
                                          by_cases c2499 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                          swap
                                          · omega
                                          by_cases c2500 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                          swap
                                          · omega
                                          have f2501 := pair_fact E (i := 4) (j := 10) rfl rfl c2482 c2498
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2501
                                          omega
                                        by_cases c2502 : 0 < b8
                                        swap
                                        · omega
                                        by_cases c2503 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                        swap
                                        · omega
                                        by_cases c2504 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f2505 := pair_fact E (i := 4) (j := 8) rfl rfl c2481 c2502
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2505
                                        omega
                                      by_cases c2506 : 0 < b6
                                      swap
                                      · omega
                                      by_cases c2507 : a0 + a2 < b0 + b2 + b4 + b6
                                      swap
                                      · omega
                                      by_cases c2508 : b0 + b2 + b4 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f2509 := pair_fact E (i := 4) (j := 6) rfl rfl c2480 c2506
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2509
                                      omega
                                    by_cases c2510 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c2511 : a0 + a2 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c2512 : b0 + b2 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f2513 := pair_fact E (i := 4) (j := 4) rfl rfl c2479 c2510
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2513
                                    omega
                                  by_cases c2514 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c2515 : a0 + a2 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c2516 : b0 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f2517 := pair_fact E (i := 4) (j := 2) rfl rfl c2478 c2514
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2517
                                  omega
                                by_cases c2518 : 0 < b0
                                swap
                                · omega
                                by_cases c2519 : a0 + a2 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c2520 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c2521 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c2522 : a0 + a2 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c2523 : b0 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f2524 := pair_fact E (i := 4) (j := 2) rfl rfl c2520 c2521
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2524
                                  by_cases c2525 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c2526 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c2527 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c2528 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c2529 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c2530 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c2531 : a0 + a2 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c2532 : b0 + b2 + b4 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c2533 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c2534 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c2535 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c2536 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c2537 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c2538 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c2539 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c2540 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · -- branch
                                          by_cases c2541 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c2542 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c2543 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                          swap
                                          · -- branch
                                            by_cases c2544 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c2545 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c2546 : a0 + a2 + a4 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c2547 : b0 + b2 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f2548 := pair_fact E (i := 6) (j := 4) rfl rfl c2544 c2545
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2548
                                            omega
                                          by_cases c2549 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f2550 := pair_fact E (i := 8) (j := 4) rfl rfl c2541 c2542
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2550
                                          omega
                                        have f2551 := pair_fact E (i := 4) (j := 10) rfl rfl c2537 c2538
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2551
                                        omega
                                      have f2552 := pair_fact E (i := 4) (j := 8) rfl rfl c2533 c2534
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2552
                                      omega
                                    have f2553 := pair_fact E (i := 4) (j := 6) rfl rfl c2529 c2530
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2553
                                    omega
                                  have f2554 := pair_fact E (i := 4) (j := 4) rfl rfl c2525 c2526
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2554
                                  omega
                                by_cases c2555 : 0 < a0 + a2 + a4
                                swap
                                · omega
                                have f2556 := pair_fact E (i := 4) (j := 0) rfl rfl c2477 c2518
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2556
                                omega
                              by_cases c2557 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                              swap
                              · omega
                              have f2558 := pair_fact E (i := 10) (j := 4) rfl rfl c2469 c2470
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2558
                              omega
                            by_cases c2559 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f2560 := pair_fact E (i := 10) (j := 2) rfl rfl c2466 c2467
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2560
                            omega
                          by_cases c2561 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                          swap
                          · omega
                          have f2562 := pair_fact E (i := 10) (j := 0) rfl rfl c2463 c2464
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2562
                          omega
                        have f2563 := pair_fact E (i := 8) (j := 10) rfl rfl c2459 c2460
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2563
                        omega
                      by_cases c2564 : 0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f2565 := pair_fact E (i := 8) (j := 0) rfl rfl c2456 c2457
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2565
                      omega
                    have f2566 := pair_fact E (i := 2) (j := 8) rfl rfl c2452 c2453
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2566
                    omega
                  have f2567 := pair_fact E (i := 2) (j := 6) rfl rfl c2448 c2449
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2567
                  omega
                have f2568 := pair_fact E (i := 2) (j := 2) rfl rfl c2444 c2445
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2568
                omega
              have f2569 := pair_fact E (i := 0) (j := 2) rfl rfl c2440 c2441
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2569
              omega
            have f2570 := pair_fact E (i := 2) (j := 4) rfl rfl c2436 c2437
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2570
            omega
          have f2571 := pair_fact E (i := 2) (j := 10) rfl rfl c2267 c2323
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2571
          omega
        have f2572 := pair_fact E (i := 0) (j := 10) rfl rfl c2023 c2024
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2572
        omega
      have f2573 := pair_fact E (i := 0) (j := 8) rfl rfl c2004 c2005
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2573
      omega
    have f2574 := pair_fact E (i := 0) (j := 6) rfl rfl c1685 c1686
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2574
    omega
  have f2575 := pair_fact E (i := 0) (j := 4) rfl rfl c1081 c1082
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2575
  omega

end Blocks
