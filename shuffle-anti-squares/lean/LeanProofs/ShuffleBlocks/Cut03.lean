import LeanProofs.ShuffleBlocks.Basic

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Blocks

set_option maxHeartbeats 0 in
/-- Cut inside run 3 of `V`: no splitting of this rotation gives two equal copies. -/
theorem V_cut03 (L l m v k a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9 a10 b10 : Nat)
    (hl : 1 ≤ l) (hm : m = 2 * v + 1) (hL : 9 * l ≤ L) (hk : k ≤ 2 * m)
    (e0 : a0 + b0 = (2 * m - k))
    (e1 : a1 + b1 = L)
    (e2 : a2 + b2 = m)
    (e3 : a3 + b3 = 2 * l)
    (e4 : a4 + b4 = m)
    (e5 : a5 + b5 = l)
    (e6 : a6 + b6 = 3 * m)
    (e7 : a7 + b7 = L)
    (e8 : a8 + b8 = m)
    (e9 : a9 + b9 = 5 * l)
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
                          by_cases c13 : 0 < a8
                          swap
                          · -- branch
                            by_cases c14 : 0 < a8
                            swap
                            · -- branch
                              by_cases c15 : 0 < a8
                              swap
                              · -- branch
                                by_cases c16 : 0 < a8
                                swap
                                · -- branch
                                  by_cases c17 : 0 < a8
                                  swap
                                  · -- branch
                                    by_cases c18 : 0 < a8
                                    swap
                                    · -- branch
                                      by_cases c19 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c20 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c21 : 0 < a4
                                          swap
                                          · -- branch
                                            by_cases c22 : 0 < a4
                                            swap
                                            · -- branch
                                              by_cases c23 : 0 < a4
                                              swap
                                              · -- branch
                                                by_cases c24 : 0 < a4
                                                swap
                                                · -- branch
                                                  by_cases c25 : 0 < a6
                                                  swap
                                                  · omega
                                                  by_cases c26 : 0 < b2
                                                  swap
                                                  · omega
                                                  by_cases c27 : a0 + a2 + a4 < b0 + b2
                                                  swap
                                                  · omega
                                                  by_cases c28 : b0 < a0 + a2 + a4 + a6
                                                  swap
                                                  · omega
                                                  have f29 := pair_fact E (i := 6) (j := 2) rfl rfl c25 c26
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f29
                                                  by_cases c30 : 0 < a6
                                                  swap
                                                  · omega
                                                  by_cases c31 : 0 < b0
                                                  swap
                                                  · -- branch
                                                    by_cases c32 : 0 < a6
                                                    swap
                                                    · omega
                                                    by_cases c33 : 0 < b4
                                                    swap
                                                    · omega
                                                    by_cases c34 : a0 + a2 + a4 < b0 + b2 + b4
                                                    swap
                                                    · omega
                                                    by_cases c35 : b0 + b2 < a0 + a2 + a4 + a6
                                                    swap
                                                    · omega
                                                    have f36 := pair_fact E (i := 6) (j := 4) rfl rfl c32 c33
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f36
                                                    by_cases c37 : 0 < a6
                                                    swap
                                                    · omega
                                                    by_cases c38 : 0 < b8
                                                    swap
                                                    · omega
                                                    by_cases c39 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                                    swap
                                                    · omega
                                                    by_cases c40 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                                    swap
                                                    · -- branch
                                                      by_cases c41 : 0 < a10
                                                      swap
                                                      · omega
                                                      by_cases c42 : 0 < b6
                                                      swap
                                                      · omega
                                                      by_cases c43 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                                      swap
                                                      · omega
                                                      by_cases c44 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                                      swap
                                                      · omega
                                                      have f45 := pair_fact E (i := 10) (j := 6) rfl rfl c41 c42
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f45
                                                      omega
                                                    have f46 := pair_fact E (i := 6) (j := 8) rfl rfl c37 c38
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f46
                                                    omega
                                                  by_cases c47 : a0 + a2 + a4 < 0 + b0
                                                  swap
                                                  · omega
                                                  by_cases c48 : 0 < a0 + a2 + a4 + a6
                                                  swap
                                                  · omega
                                                  have f49 := pair_fact E (i := 6) (j := 0) rfl rfl c30 c31
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f49
                                                  omega
                                                by_cases c50 : 0 < b10
                                                swap
                                                · omega
                                                by_cases c51 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                                swap
                                                · omega
                                                by_cases c52 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                                swap
                                                · omega
                                                have f53 := pair_fact E (i := 4) (j := 10) rfl rfl c24 c50
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f53
                                                omega
                                              by_cases c54 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c55 : a0 + a2 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c56 : b0 + b2 + b4 < a0 + a2 + a4
                                              swap
                                              · omega
                                              have f57 := pair_fact E (i := 4) (j := 6) rfl rfl c23 c54
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f57
                                              omega
                                            by_cases c58 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c59 : a0 + a2 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c60 : b0 + b2 < a0 + a2 + a4
                                            swap
                                            · omega
                                            have f61 := pair_fact E (i := 4) (j := 4) rfl rfl c22 c58
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f61
                                            omega
                                          by_cases c62 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c63 : a0 + a2 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c64 : b0 < a0 + a2 + a4
                                          swap
                                          · omega
                                          have f65 := pair_fact E (i := 4) (j := 2) rfl rfl c21 c62
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f65
                                          omega
                                        by_cases c66 : 0 < b0
                                        swap
                                        · omega
                                        by_cases c67 : a0 + a2 < 0 + b0
                                        swap
                                        · omega
                                        by_cases c68 : 0 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f69 := pair_fact E (i := 4) (j := 0) rfl rfl c20 c66
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f69
                                        omega
                                      by_cases c70 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c71 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c72 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c73 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c74 : 0 < b0
                                        swap
                                        · -- branch
                                          by_cases c75 : 0 < a4
                                          swap
                                          · omega
                                          by_cases c76 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c77 : a0 + a2 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c78 : b0 < a0 + a2 + a4
                                          swap
                                          · omega
                                          have f79 := pair_fact E (i := 4) (j := 2) rfl rfl c75 c76
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f79
                                          by_cases c80 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c81 : 0 < b0
                                          swap
                                          · -- branch
                                            by_cases c82 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c83 : 0 < b8
                                            swap
                                            · omega
                                            by_cases c84 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                            swap
                                            · omega
                                            by_cases c85 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                            swap
                                            · -- branch
                                              by_cases c86 : 0 < a10
                                              swap
                                              · omega
                                              by_cases c87 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c88 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c89 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                              swap
                                              · omega
                                              have f90 := pair_fact E (i := 10) (j := 6) rfl rfl c86 c87
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f90
                                              omega
                                            have f91 := pair_fact E (i := 6) (j := 8) rfl rfl c82 c83
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f91
                                            omega
                                          by_cases c92 : a0 + a2 + a4 < 0 + b0
                                          swap
                                          · omega
                                          by_cases c93 : 0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f94 := pair_fact E (i := 6) (j := 0) rfl rfl c80 c81
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f94
                                          omega
                                        by_cases c95 : a0 + a2 < 0 + b0
                                        swap
                                        · omega
                                        by_cases c96 : 0 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f97 := pair_fact E (i := 4) (j := 0) rfl rfl c73 c74
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f97
                                        by_cases c98 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c99 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c100 : a0 + a2 + a4 < b0 + b2
                                        swap
                                        · omega
                                        by_cases c101 : b0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f102 := pair_fact E (i := 6) (j := 2) rfl rfl c98 c99
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f102
                                        omega
                                      have f103 := pair_fact E (i := 4) (j := 8) rfl rfl c19 c70
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f103
                                      omega
                                    by_cases c104 : 0 < b10
                                    swap
                                    · omega
                                    by_cases c105 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c106 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f107 := pair_fact E (i := 8) (j := 10) rfl rfl c18 c104
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f107
                                    omega
                                  by_cases c108 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c109 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c110 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f111 := pair_fact E (i := 8) (j := 8) rfl rfl c17 c108
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f111
                                  omega
                                by_cases c112 : 0 < b6
                                swap
                                · omega
                                by_cases c113 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c114 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f115 := pair_fact E (i := 8) (j := 6) rfl rfl c16 c112
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f115
                                omega
                              by_cases c116 : 0 < b4
                              swap
                              · omega
                              by_cases c117 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c118 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f119 := pair_fact E (i := 8) (j := 4) rfl rfl c15 c116
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f119
                              omega
                            by_cases c120 : 0 < b0
                            swap
                            · omega
                            by_cases c121 : a0 + a2 + a4 + a6 < 0 + b0
                            swap
                            · omega
                            by_cases c122 : 0 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f123 := pair_fact E (i := 8) (j := 0) rfl rfl c14 c120
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f123
                            omega
                          by_cases c124 : 0 < b2
                          swap
                          · omega
                          by_cases c125 : a0 + a2 + a4 + a6 < b0 + b2
                          swap
                          · -- branch
                            by_cases c126 : 0 < a8
                            swap
                            · omega
                            by_cases c127 : 0 < b0
                            swap
                            · -- branch
                              by_cases c128 : 0 < a4
                              swap
                              · -- branch
                                by_cases c129 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c130 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c131 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c132 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c133 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c134 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c135 : 0 < b0
                                          swap
                                          · -- branch
                                            by_cases c136 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c137 : 0 < b2
                                            swap
                                            · omega
                                            by_cases c138 : a0 + a2 + a4 < b0 + b2
                                            swap
                                            · omega
                                            by_cases c139 : b0 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f140 := pair_fact E (i := 6) (j := 2) rfl rfl c136 c137
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f140
                                            by_cases c141 : 0 < a8
                                            swap
                                            · omega
                                            by_cases c142 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c143 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                            swap
                                            · -- branch
                                              by_cases c144 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c145 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c146 : a0 + a2 + a4 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c147 : b0 + b2 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f148 := pair_fact E (i := 6) (j := 4) rfl rfl c144 c145
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f148
                                              by_cases c149 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c150 : 0 < b10
                                              swap
                                              · omega
                                              by_cases c151 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                              swap
                                              · omega
                                              by_cases c152 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                              swap
                                              · -- branch
                                                by_cases c153 : 0 < a8
                                                swap
                                                · omega
                                                by_cases c154 : 0 < b6
                                                swap
                                                · omega
                                                by_cases c155 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                swap
                                                · -- branch
                                                  by_cases c156 : 0 < a6
                                                  swap
                                                  · omega
                                                  by_cases c157 : 0 < b8
                                                  swap
                                                  · omega
                                                  by_cases c158 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                                  swap
                                                  · omega
                                                  by_cases c159 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                                  swap
                                                  · omega
                                                  have f160 := pair_fact E (i := 6) (j := 8) rfl rfl c156 c157
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f160
                                                  omega
                                                by_cases c161 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                swap
                                                · omega
                                                have f162 := pair_fact E (i := 8) (j := 6) rfl rfl c153 c154
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f162
                                                omega
                                              have f163 := pair_fact E (i := 6) (j := 10) rfl rfl c149 c150
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f163
                                              omega
                                            by_cases c164 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f165 := pair_fact E (i := 8) (j := 4) rfl rfl c141 c142
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f165
                                            omega
                                          by_cases c166 : a0 + a2 + a4 < 0 + b0
                                          swap
                                          · omega
                                          by_cases c167 : 0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f168 := pair_fact E (i := 6) (j := 0) rfl rfl c134 c135
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f168
                                          omega
                                        by_cases c169 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c170 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c171 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f172 := pair_fact E (i := 4) (j := 10) rfl rfl c133 c169
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f172
                                        omega
                                      by_cases c173 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c174 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c175 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f176 := pair_fact E (i := 4) (j := 8) rfl rfl c132 c173
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f176
                                      omega
                                    by_cases c177 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c178 : a0 + a2 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c179 : b0 + b2 + b4 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f180 := pair_fact E (i := 4) (j := 6) rfl rfl c131 c177
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f180
                                    omega
                                  by_cases c181 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c182 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c183 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f184 := pair_fact E (i := 4) (j := 4) rfl rfl c130 c181
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f184
                                  omega
                                by_cases c185 : 0 < b2
                                swap
                                · omega
                                by_cases c186 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c187 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f188 := pair_fact E (i := 4) (j := 2) rfl rfl c129 c185
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f188
                                omega
                              by_cases c189 : 0 < b0
                              swap
                              · -- branch
                                by_cases c190 : 0 < a4
                                swap
                                · omega
                                by_cases c191 : 0 < b2
                                swap
                                · omega
                                by_cases c192 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c193 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f194 := pair_fact E (i := 4) (j := 2) rfl rfl c190 c191
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f194
                                by_cases c195 : 0 < a4
                                swap
                                · omega
                                by_cases c196 : 0 < b4
                                swap
                                · -- branch
                                  by_cases c197 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c198 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c199 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c200 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c201 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c202 : 0 < b4
                                    swap
                                    · -- branch
                                      by_cases c203 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c204 : 0 < b6
                                      swap
                                      · omega
                                      by_cases c205 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                      swap
                                      · -- branch
                                        by_cases c206 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c207 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c208 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c209 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · -- branch
                                          by_cases c210 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c211 : 0 < b0
                                          swap
                                          · -- branch
                                            by_cases c212 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c213 : 0 < b2
                                            swap
                                            · omega
                                            by_cases c214 : a0 + a2 + a4 < b0 + b2
                                            swap
                                            · -- branch
                                              by_cases c215 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c216 : 0 < b4
                                              swap
                                              · -- branch
                                                by_cases c217 : 0 < a6
                                                swap
                                                · omega
                                                by_cases c218 : 0 < b6
                                                swap
                                                · omega
                                                by_cases c219 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                                swap
                                                · omega
                                                by_cases c220 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                                swap
                                                · omega
                                                have f221 := pair_fact E (i := 6) (j := 6) rfl rfl c217 c218
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f221
                                                by_cases c222 : 0 < a6
                                                swap
                                                · omega
                                                by_cases c223 : 0 < b8
                                                swap
                                                · -- branch
                                                  by_cases c224 : 0 < a6
                                                  swap
                                                  · omega
                                                  by_cases c225 : 0 < b10
                                                  swap
                                                  · omega
                                                  by_cases c226 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                                  swap
                                                  · omega
                                                  by_cases c227 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                                  swap
                                                  · omega
                                                  have f228 := pair_fact E (i := 6) (j := 10) rfl rfl c224 c225
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f228
                                                  omega
                                                by_cases c229 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                                swap
                                                · omega
                                                by_cases c230 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                                swap
                                                · omega
                                                have f231 := pair_fact E (i := 6) (j := 8) rfl rfl c222 c223
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f231
                                                omega
                                              by_cases c232 : a0 + a2 + a4 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c233 : b0 + b2 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f234 := pair_fact E (i := 6) (j := 4) rfl rfl c215 c216
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f234
                                              omega
                                            by_cases c235 : b0 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f236 := pair_fact E (i := 6) (j := 2) rfl rfl c212 c213
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f236
                                            omega
                                          by_cases c237 : a0 + a2 + a4 < 0 + b0
                                          swap
                                          · omega
                                          by_cases c238 : 0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f239 := pair_fact E (i := 6) (j := 0) rfl rfl c210 c211
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f239
                                          omega
                                        have f240 := pair_fact E (i := 4) (j := 10) rfl rfl c206 c207
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f240
                                        omega
                                      by_cases c241 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f242 := pair_fact E (i := 8) (j := 6) rfl rfl c203 c204
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f242
                                      omega
                                    by_cases c243 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c244 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f245 := pair_fact E (i := 8) (j := 4) rfl rfl c201 c202
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f245
                                    omega
                                  have f246 := pair_fact E (i := 4) (j := 6) rfl rfl c197 c198
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f246
                                  omega
                                by_cases c247 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c248 : b0 + b2 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c249 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c250 : 0 < b0
                                  swap
                                  · -- branch
                                    by_cases c251 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c252 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c253 : a0 + a2 + a4 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c254 : b0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f255 := pair_fact E (i := 6) (j := 2) rfl rfl c251 c252
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f255
                                    by_cases c256 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c257 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c258 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                    swap
                                    · -- branch
                                      by_cases c259 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c260 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c261 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c262 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f263 := pair_fact E (i := 6) (j := 4) rfl rfl c259 c260
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f263
                                      by_cases c264 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c265 : 0 < b6
                                      swap
                                      · -- branch
                                        by_cases c266 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c267 : 0 < b8
                                        swap
                                        · omega
                                        by_cases c268 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                        swap
                                        · omega
                                        by_cases c269 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f270 := pair_fact E (i := 6) (j := 8) rfl rfl c266 c267
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f270
                                        omega
                                      by_cases c271 : a0 + a2 < b0 + b2 + b4 + b6
                                      swap
                                      · omega
                                      by_cases c272 : b0 + b2 + b4 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c273 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c274 : 0 < b6
                                        swap
                                        · omega
                                        by_cases c275 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                        swap
                                        · omega
                                        by_cases c276 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                        swap
                                        · -- branch
                                          by_cases c277 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c278 : 0 < b6
                                          swap
                                          · omega
                                          by_cases c279 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                          swap
                                          · omega
                                          by_cases c280 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f281 := pair_fact E (i := 8) (j := 6) rfl rfl c277 c278
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f281
                                          omega
                                        have f282 := pair_fact E (i := 6) (j := 6) rfl rfl c273 c274
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f282
                                        omega
                                      have f283 := pair_fact E (i := 4) (j := 6) rfl rfl c264 c265
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f283
                                      omega
                                    by_cases c284 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f285 := pair_fact E (i := 8) (j := 4) rfl rfl c256 c257
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f285
                                    omega
                                  by_cases c286 : a0 + a2 + a4 < 0 + b0
                                  swap
                                  · omega
                                  by_cases c287 : 0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f288 := pair_fact E (i := 6) (j := 0) rfl rfl c249 c250
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f288
                                  omega
                                have f289 := pair_fact E (i := 4) (j := 4) rfl rfl c195 c196
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f289
                                omega
                              by_cases c290 : a0 + a2 < 0 + b0
                              swap
                              · omega
                              by_cases c291 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f292 := pair_fact E (i := 4) (j := 0) rfl rfl c128 c189
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f292
                              omega
                            by_cases c293 : a0 + a2 + a4 + a6 < 0 + b0
                            swap
                            · -- branch
                              by_cases c294 : 0 < a6
                              swap
                              · omega
                              by_cases c295 : 0 < b2
                              swap
                              · omega
                              by_cases c296 : a0 + a2 + a4 < b0 + b2
                              swap
                              · omega
                              by_cases c297 : b0 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f298 := pair_fact E (i := 6) (j := 2) rfl rfl c294 c295
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f298
                              by_cases c299 : 0 < a4
                              swap
                              · -- branch
                                by_cases c300 : 0 < a6
                                swap
                                · omega
                                by_cases c301 : 0 < b0
                                swap
                                · omega
                                by_cases c302 : a0 + a2 + a4 < 0 + b0
                                swap
                                · omega
                                by_cases c303 : 0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f304 := pair_fact E (i := 6) (j := 0) rfl rfl c300 c301
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f304
                                omega
                              by_cases c305 : 0 < b0
                              swap
                              · omega
                              by_cases c306 : a0 + a2 < 0 + b0
                              swap
                              · omega
                              by_cases c307 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f308 := pair_fact E (i := 4) (j := 0) rfl rfl c299 c305
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f308
                              omega
                            by_cases c309 : 0 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f310 := pair_fact E (i := 8) (j := 0) rfl rfl c126 c127
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f310
                            omega
                          by_cases c311 : b0 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f312 := pair_fact E (i := 8) (j := 2) rfl rfl c13 c124
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f312
                          omega
                        by_cases c313 : 0 < b10
                        swap
                        · omega
                        by_cases c314 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c315 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                        swap
                        · omega
                        have f316 := pair_fact E (i := 2) (j := 10) rfl rfl c12 c313
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f316
                        omega
                      by_cases c317 : 0 < b8
                      swap
                      · omega
                      by_cases c318 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c319 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · omega
                      have f320 := pair_fact E (i := 2) (j := 8) rfl rfl c11 c317
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f320
                      omega
                    by_cases c321 : 0 < b6
                    swap
                    · omega
                    by_cases c322 : a0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c323 : b0 + b2 + b4 < a0 + a2
                    swap
                    · omega
                    have f324 := pair_fact E (i := 2) (j := 6) rfl rfl c10 c321
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f324
                    omega
                  by_cases c325 : 0 < b4
                  swap
                  · omega
                  by_cases c326 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c327 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f328 := pair_fact E (i := 2) (j := 4) rfl rfl c9 c325
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f328
                  omega
                by_cases c329 : 0 < b2
                swap
                · omega
                by_cases c330 : a0 < b0 + b2
                swap
                · omega
                by_cases c331 : b0 < a0 + a2
                swap
                · omega
                have f332 := pair_fact E (i := 2) (j := 2) rfl rfl c8 c329
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f332
                omega
              by_cases c333 : 0 < b0
              swap
              · -- branch
                by_cases c334 : 0 < a2
                swap
                · omega
                by_cases c335 : 0 < b2
                swap
                · -- branch
                  by_cases c336 : 0 < a2
                  swap
                  · omega
                  by_cases c337 : 0 < b4
                  swap
                  · -- branch
                    by_cases c338 : 0 < a2
                    swap
                    · omega
                    by_cases c339 : 0 < b6
                    swap
                    · omega
                    by_cases c340 : a0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c341 : b0 + b2 + b4 < a0 + a2
                    swap
                    · omega
                    have f342 := pair_fact E (i := 2) (j := 6) rfl rfl c338 c339
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f342
                    by_cases c343 : 0 < a4
                    swap
                    · omega
                    by_cases c344 : 0 < b0
                    swap
                    · -- branch
                      by_cases c345 : 0 < a4
                      swap
                      · omega
                      by_cases c346 : 0 < b2
                      swap
                      · -- branch
                        by_cases c347 : 0 < a4
                        swap
                        · omega
                        by_cases c348 : 0 < b4
                        swap
                        · -- branch
                          by_cases c349 : 0 < a2
                          swap
                          · omega
                          by_cases c350 : 0 < b8
                          swap
                          · -- branch
                            by_cases c351 : 0 < a2
                            swap
                            · omega
                            by_cases c352 : 0 < b10
                            swap
                            · omega
                            by_cases c353 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c354 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                            swap
                            · -- branch
                              by_cases c355 : 0 < a4
                              swap
                              · omega
                              by_cases c356 : 0 < b6
                              swap
                              · omega
                              by_cases c357 : a0 + a2 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c358 : b0 + b2 + b4 < a0 + a2 + a4
                              swap
                              · omega
                              have f359 := pair_fact E (i := 4) (j := 6) rfl rfl c355 c356
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f359
                              by_cases c360 : 0 < a4
                              swap
                              · omega
                              by_cases c361 : 0 < b8
                              swap
                              · -- branch
                                by_cases c362 : 0 < a4
                                swap
                                · omega
                                by_cases c363 : 0 < b10
                                swap
                                · omega
                                by_cases c364 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c365 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c366 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c367 : 0 < b0
                                  swap
                                  · -- branch
                                    by_cases c368 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c369 : 0 < b2
                                    swap
                                    · -- branch
                                      by_cases c370 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c371 : 0 < b4
                                      swap
                                      · -- branch
                                        by_cases c372 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c373 : 0 < b6
                                        swap
                                        · omega
                                        by_cases c374 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                        swap
                                        · -- branch
                                          by_cases c375 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c376 : 0 < b10
                                          swap
                                          · omega
                                          by_cases c377 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                          swap
                                          · omega
                                          by_cases c378 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f379 := pair_fact E (i := 6) (j := 10) rfl rfl c375 c376
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f379
                                          omega
                                        by_cases c380 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f381 := pair_fact E (i := 8) (j := 6) rfl rfl c372 c373
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f381
                                        omega
                                      by_cases c382 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c383 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f384 := pair_fact E (i := 8) (j := 4) rfl rfl c370 c371
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f384
                                      omega
                                    by_cases c385 : a0 + a2 + a4 + a6 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c386 : b0 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f387 := pair_fact E (i := 8) (j := 2) rfl rfl c368 c369
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f387
                                    omega
                                  by_cases c388 : a0 + a2 + a4 + a6 < 0 + b0
                                  swap
                                  · omega
                                  by_cases c389 : 0 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f390 := pair_fact E (i := 8) (j := 0) rfl rfl c366 c367
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f390
                                  omega
                                have f391 := pair_fact E (i := 4) (j := 10) rfl rfl c362 c363
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f391
                                omega
                              by_cases c392 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c393 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · omega
                              have f394 := pair_fact E (i := 4) (j := 8) rfl rfl c360 c361
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f394
                              omega
                            have f395 := pair_fact E (i := 2) (j := 10) rfl rfl c351 c352
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f395
                            omega
                          by_cases c396 : a0 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c397 : b0 + b2 + b4 + b6 < a0 + a2
                          swap
                          · -- branch
                            by_cases c398 : 0 < a4
                            swap
                            · omega
                            by_cases c399 : 0 < b8
                            swap
                            · omega
                            by_cases c400 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c401 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c402 : 0 < a4
                              swap
                              · omega
                              by_cases c403 : 0 < b6
                              swap
                              · omega
                              by_cases c404 : a0 + a2 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c405 : b0 + b2 + b4 < a0 + a2 + a4
                              swap
                              · omega
                              have f406 := pair_fact E (i := 4) (j := 6) rfl rfl c402 c403
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f406
                              by_cases c407 : 0 < a10
                              swap
                              · omega
                              by_cases c408 : 0 < b0
                              swap
                              · -- branch
                                by_cases c409 : 0 < a10
                                swap
                                · omega
                                by_cases c410 : 0 < b2
                                swap
                                · -- branch
                                  by_cases c411 : 0 < a10
                                  swap
                                  · omega
                                  by_cases c412 : 0 < b4
                                  swap
                                  · -- branch
                                    by_cases c413 : 0 < a10
                                    swap
                                    · omega
                                    by_cases c414 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c415 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                    swap
                                    · -- branch
                                      by_cases c416 : 0 < a2
                                      swap
                                      · omega
                                      by_cases c417 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c418 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c419 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                                      swap
                                      · -- branch
                                        by_cases c420 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c421 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c422 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c423 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · -- branch
                                          by_cases c424 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c425 : 0 < b0
                                          swap
                                          · -- branch
                                            by_cases c426 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c427 : 0 < b2
                                            swap
                                            · -- branch
                                              by_cases c428 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c429 : 0 < b4
                                              swap
                                              · -- branch
                                                by_cases c430 : 0 < a6
                                                swap
                                                · omega
                                                by_cases c431 : 0 < b8
                                                swap
                                                · omega
                                                by_cases c432 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                                swap
                                                · omega
                                                by_cases c433 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                                swap
                                                · -- branch
                                                  by_cases c434 : 0 < a8
                                                  swap
                                                  · omega
                                                  by_cases c435 : 0 < b6
                                                  swap
                                                  · omega
                                                  by_cases c436 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                  swap
                                                  · omega
                                                  by_cases c437 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · omega
                                                  have f438 := pair_fact E (i := 8) (j := 6) rfl rfl c434 c435
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f438
                                                  omega
                                                have f439 := pair_fact E (i := 6) (j := 8) rfl rfl c430 c431
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f439
                                                omega
                                              by_cases c440 : a0 + a2 + a4 < b0 + b2 + b4
                                              swap
                                              · omega
                                              by_cases c441 : b0 + b2 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f442 := pair_fact E (i := 6) (j := 4) rfl rfl c428 c429
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f442
                                              omega
                                            by_cases c443 : a0 + a2 + a4 < b0 + b2
                                            swap
                                            · omega
                                            by_cases c444 : b0 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f445 := pair_fact E (i := 6) (j := 2) rfl rfl c426 c427
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f445
                                            omega
                                          by_cases c446 : a0 + a2 + a4 < 0 + b0
                                          swap
                                          · omega
                                          by_cases c447 : 0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f448 := pair_fact E (i := 6) (j := 0) rfl rfl c424 c425
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f448
                                          omega
                                        have f449 := pair_fact E (i := 4) (j := 10) rfl rfl c420 c421
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f449
                                        omega
                                      have f450 := pair_fact E (i := 2) (j := 10) rfl rfl c416 c417
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f450
                                      omega
                                    by_cases c451 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                    swap
                                    · omega
                                    have f452 := pair_fact E (i := 10) (j := 6) rfl rfl c413 c414
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f452
                                    omega
                                  by_cases c453 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c454 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                  swap
                                  · omega
                                  have f455 := pair_fact E (i := 10) (j := 4) rfl rfl c411 c412
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f455
                                  omega
                                by_cases c456 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                                swap
                                · omega
                                by_cases c457 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f458 := pair_fact E (i := 10) (j := 2) rfl rfl c409 c410
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f458
                                omega
                              by_cases c459 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                              swap
                              · omega
                              by_cases c460 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                              swap
                              · omega
                              have f461 := pair_fact E (i := 10) (j := 0) rfl rfl c407 c408
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f461
                              omega
                            have f462 := pair_fact E (i := 4) (j := 8) rfl rfl c398 c399
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f462
                            omega
                          have f463 := pair_fact E (i := 2) (j := 8) rfl rfl c349 c350
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f463
                          omega
                        by_cases c464 : a0 + a2 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c465 : b0 + b2 < a0 + a2 + a4
                        swap
                        · omega
                        have f466 := pair_fact E (i := 4) (j := 4) rfl rfl c347 c348
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f466
                        omega
                      by_cases c467 : a0 + a2 < b0 + b2
                      swap
                      · omega
                      by_cases c468 : b0 < a0 + a2 + a4
                      swap
                      · omega
                      have f469 := pair_fact E (i := 4) (j := 2) rfl rfl c345 c346
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f469
                      omega
                    by_cases c470 : a0 + a2 < 0 + b0
                    swap
                    · omega
                    by_cases c471 : 0 < a0 + a2 + a4
                    swap
                    · omega
                    have f472 := pair_fact E (i := 4) (j := 0) rfl rfl c343 c344
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f472
                    omega
                  by_cases c473 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c474 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f475 := pair_fact E (i := 2) (j := 4) rfl rfl c336 c337
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f475
                  by_cases c476 : 0 < a2
                  swap
                  · omega
                  by_cases c477 : 0 < b8
                  swap
                  · -- branch
                    by_cases c478 : 0 < a8
                    swap
                    · omega
                    by_cases c479 : 0 < b0
                    swap
                    · -- branch
                      by_cases c480 : 0 < a8
                      swap
                      · omega
                      by_cases c481 : 0 < b2
                      swap
                      · -- branch
                        by_cases c482 : 0 < a8
                        swap
                        · omega
                        by_cases c483 : 0 < b4
                        swap
                        · omega
                        by_cases c484 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                        swap
                        · -- branch
                          by_cases c485 : 0 < a8
                          swap
                          · omega
                          by_cases c486 : 0 < b6
                          swap
                          · omega
                          by_cases c487 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                          swap
                          · -- branch
                            by_cases c488 : 0 < a6
                            swap
                            · omega
                            by_cases c489 : 0 < b10
                            swap
                            · omega
                            by_cases c490 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c491 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f492 := pair_fact E (i := 6) (j := 10) rfl rfl c488 c489
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f492
                            omega
                          by_cases c493 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f494 := pair_fact E (i := 8) (j := 6) rfl rfl c485 c486
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f494
                          omega
                        by_cases c495 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f496 := pair_fact E (i := 8) (j := 4) rfl rfl c482 c483
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f496
                        omega
                      by_cases c497 : a0 + a2 + a4 + a6 < b0 + b2
                      swap
                      · omega
                      by_cases c498 : b0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f499 := pair_fact E (i := 8) (j := 2) rfl rfl c480 c481
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f499
                      omega
                    by_cases c500 : a0 + a2 + a4 + a6 < 0 + b0
                    swap
                    · omega
                    by_cases c501 : 0 < a0 + a2 + a4 + a6 + a8
                    swap
                    · omega
                    have f502 := pair_fact E (i := 8) (j := 0) rfl rfl c478 c479
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f502
                    omega
                  by_cases c503 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c504 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · -- branch
                    by_cases c505 : 0 < a2
                    swap
                    · omega
                    by_cases c506 : 0 < b10
                    swap
                    · -- branch
                      by_cases c507 : 0 < a10
                      swap
                      · omega
                      by_cases c508 : 0 < b6
                      swap
                      · omega
                      by_cases c509 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c510 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f511 := pair_fact E (i := 10) (j := 6) rfl rfl c507 c508
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f511
                      omega
                    by_cases c512 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c513 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · -- branch
                      by_cases c514 : 0 < a4
                      swap
                      · -- branch
                        by_cases c515 : 0 < a4
                        swap
                        · -- branch
                          by_cases c516 : 0 < a4
                          swap
                          · -- branch
                            by_cases c517 : 0 < a4
                            swap
                            · -- branch
                              by_cases c518 : 0 < a4
                              swap
                              · -- branch
                                by_cases c519 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c520 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c521 : 0 < b0
                                  swap
                                  · -- branch
                                    by_cases c522 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c523 : 0 < b2
                                    swap
                                    · -- branch
                                      by_cases c524 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c525 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c526 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · -- branch
                                        by_cases c527 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c528 : 0 < b8
                                        swap
                                        · omega
                                        by_cases c529 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                        swap
                                        · omega
                                        by_cases c530 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                        swap
                                        · -- branch
                                          by_cases c531 : 0 < a2
                                          swap
                                          · omega
                                          by_cases c532 : 0 < b6
                                          swap
                                          · omega
                                          by_cases c533 : a0 < b0 + b2 + b4 + b6
                                          swap
                                          · omega
                                          by_cases c534 : b0 + b2 + b4 < a0 + a2
                                          swap
                                          · -- branch
                                            by_cases c535 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c536 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c537 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c538 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f539 := pair_fact E (i := 6) (j := 6) rfl rfl c535 c536
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f539
                                            by_cases c540 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c541 : 0 < b10
                                            swap
                                            · omega
                                            by_cases c542 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                            swap
                                            · omega
                                            by_cases c543 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                            swap
                                            · -- branch
                                              by_cases c544 : 0 < a8
                                              swap
                                              · -- branch
                                                by_cases c545 : 0 < a10
                                                swap
                                                · omega
                                                by_cases c546 : 0 < b6
                                                swap
                                                · omega
                                                by_cases c547 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                                swap
                                                · omega
                                                by_cases c548 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                                swap
                                                · omega
                                                have f549 := pair_fact E (i := 10) (j := 6) rfl rfl c545 c546
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f549
                                                omega
                                              by_cases c550 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c551 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c552 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                              swap
                                              · omega
                                              have f553 := pair_fact E (i := 8) (j := 6) rfl rfl c544 c550
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f553
                                              omega
                                            have f554 := pair_fact E (i := 6) (j := 10) rfl rfl c540 c541
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f554
                                            omega
                                          have f555 := pair_fact E (i := 2) (j := 6) rfl rfl c531 c532
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f555
                                          omega
                                        have f556 := pair_fact E (i := 6) (j := 8) rfl rfl c527 c528
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f556
                                        omega
                                      by_cases c557 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f558 := pair_fact E (i := 6) (j := 4) rfl rfl c524 c525
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f558
                                      omega
                                    by_cases c559 : a0 + a2 + a4 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c560 : b0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f561 := pair_fact E (i := 6) (j := 2) rfl rfl c522 c523
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f561
                                    omega
                                  by_cases c562 : a0 + a2 + a4 < 0 + b0
                                  swap
                                  · omega
                                  by_cases c563 : 0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f564 := pair_fact E (i := 6) (j := 0) rfl rfl c520 c521
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f564
                                  omega
                                by_cases c565 : 0 < b10
                                swap
                                · omega
                                by_cases c566 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c567 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                swap
                                · omega
                                have f568 := pair_fact E (i := 4) (j := 10) rfl rfl c519 c565
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f568
                                omega
                              by_cases c569 : 0 < b8
                              swap
                              · omega
                              by_cases c570 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c571 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · omega
                              have f572 := pair_fact E (i := 4) (j := 8) rfl rfl c518 c569
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f572
                              omega
                            by_cases c573 : 0 < b6
                            swap
                            · omega
                            by_cases c574 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c575 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · omega
                            have f576 := pair_fact E (i := 4) (j := 6) rfl rfl c517 c573
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f576
                            omega
                          by_cases c577 : 0 < b4
                          swap
                          · omega
                          by_cases c578 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c579 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f580 := pair_fact E (i := 4) (j := 4) rfl rfl c516 c577
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f580
                          omega
                        by_cases c581 : 0 < b2
                        swap
                        · omega
                        by_cases c582 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c583 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f584 := pair_fact E (i := 4) (j := 2) rfl rfl c515 c581
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f584
                        omega
                      by_cases c585 : 0 < b0
                      swap
                      · -- branch
                        by_cases c586 : 0 < a2
                        swap
                        · omega
                        by_cases c587 : 0 < b6
                        swap
                        · omega
                        by_cases c588 : a0 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c589 : b0 + b2 + b4 < a0 + a2
                        swap
                        · omega
                        have f590 := pair_fact E (i := 2) (j := 6) rfl rfl c586 c587
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f590
                        by_cases c591 : 0 < a4
                        swap
                        · omega
                        by_cases c592 : 0 < b2
                        swap
                        · -- branch
                          by_cases c593 : 0 < a4
                          swap
                          · omega
                          by_cases c594 : 0 < b4
                          swap
                          · omega
                          by_cases c595 : a0 + a2 < b0 + b2 + b4
                          swap
                          · -- branch
                            by_cases c596 : 0 < a4
                            swap
                            · omega
                            by_cases c597 : 0 < b8
                            swap
                            · omega
                            by_cases c598 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c599 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c600 : 0 < a4
                              swap
                              · omega
                              by_cases c601 : 0 < b6
                              swap
                              · omega
                              by_cases c602 : a0 + a2 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c603 : b0 + b2 + b4 < a0 + a2 + a4
                              swap
                              · omega
                              have f604 := pair_fact E (i := 4) (j := 6) rfl rfl c600 c601
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f604
                              by_cases c605 : 0 < a4
                              swap
                              · omega
                              by_cases c606 : 0 < b10
                              swap
                              · omega
                              by_cases c607 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c608 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c609 : 0 < a6
                                swap
                                · -- branch
                                  by_cases c610 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c611 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c612 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c613 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f614 := pair_fact E (i := 8) (j := 6) rfl rfl c610 c611
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f614
                                  omega
                                by_cases c615 : 0 < b0
                                swap
                                · -- branch
                                  by_cases c616 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c617 : 0 < b2
                                  swap
                                  · -- branch
                                    by_cases c618 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c619 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c620 : a0 + a2 + a4 < b0 + b2 + b4
                                    swap
                                    · -- branch
                                      by_cases c621 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c622 : 0 < b6
                                      swap
                                      · omega
                                      by_cases c623 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                      swap
                                      · -- branch
                                        by_cases c624 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c625 : 0 < b8
                                        swap
                                        · omega
                                        by_cases c626 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                        swap
                                        · omega
                                        by_cases c627 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f628 := pair_fact E (i := 6) (j := 8) rfl rfl c624 c625
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f628
                                        omega
                                      by_cases c629 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f630 := pair_fact E (i := 6) (j := 6) rfl rfl c621 c622
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f630
                                      omega
                                    by_cases c631 : b0 + b2 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f632 := pair_fact E (i := 6) (j := 4) rfl rfl c618 c619
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f632
                                    omega
                                  by_cases c633 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c634 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f635 := pair_fact E (i := 6) (j := 2) rfl rfl c616 c617
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f635
                                  omega
                                by_cases c636 : a0 + a2 + a4 < 0 + b0
                                swap
                                · omega
                                by_cases c637 : 0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f638 := pair_fact E (i := 6) (j := 0) rfl rfl c609 c615
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f638
                                omega
                              have f639 := pair_fact E (i := 4) (j := 10) rfl rfl c605 c606
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f639
                              omega
                            have f640 := pair_fact E (i := 4) (j := 8) rfl rfl c596 c597
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f640
                            omega
                          by_cases c641 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f642 := pair_fact E (i := 4) (j := 4) rfl rfl c593 c594
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f642
                          omega
                        by_cases c643 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c644 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f645 := pair_fact E (i := 4) (j := 2) rfl rfl c591 c592
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f645
                        omega
                      by_cases c646 : a0 + a2 < 0 + b0
                      swap
                      · omega
                      by_cases c647 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f648 := pair_fact E (i := 4) (j := 0) rfl rfl c514 c585
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f648
                      omega
                    have f649 := pair_fact E (i := 2) (j := 10) rfl rfl c505 c506
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f649
                    omega
                  have f650 := pair_fact E (i := 2) (j := 8) rfl rfl c476 c477
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f650
                  omega
                by_cases c651 : a0 < b0 + b2
                swap
                · omega
                by_cases c652 : b0 < a0 + a2
                swap
                · omega
                have f653 := pair_fact E (i := 2) (j := 2) rfl rfl c334 c335
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f653
                by_cases c654 : 0 < a2
                swap
                · omega
                by_cases c655 : 0 < b8
                swap
                · -- branch
                  by_cases c656 : 0 < a8
                  swap
                  · omega
                  by_cases c657 : 0 < b0
                  swap
                  · -- branch
                    by_cases c658 : 0 < a8
                    swap
                    · omega
                    by_cases c659 : 0 < b2
                    swap
                    · omega
                    by_cases c660 : a0 + a2 + a4 + a6 < b0 + b2
                    swap
                    · -- branch
                      by_cases c661 : 0 < a8
                      swap
                      · omega
                      by_cases c662 : 0 < b6
                      swap
                      · omega
                      by_cases c663 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                      swap
                      · -- branch
                        by_cases c664 : 0 < a6
                        swap
                        · omega
                        by_cases c665 : 0 < b10
                        swap
                        · omega
                        by_cases c666 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c667 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f668 := pair_fact E (i := 6) (j := 10) rfl rfl c664 c665
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f668
                        omega
                      by_cases c669 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f670 := pair_fact E (i := 8) (j := 6) rfl rfl c661 c662
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f670
                      omega
                    by_cases c671 : b0 < a0 + a2 + a4 + a6 + a8
                    swap
                    · omega
                    have f672 := pair_fact E (i := 8) (j := 2) rfl rfl c658 c659
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f672
                    omega
                  by_cases c673 : a0 + a2 + a4 + a6 < 0 + b0
                  swap
                  · omega
                  by_cases c674 : 0 < a0 + a2 + a4 + a6 + a8
                  swap
                  · omega
                  have f675 := pair_fact E (i := 8) (j := 0) rfl rfl c656 c657
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f675
                  omega
                by_cases c676 : a0 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c677 : b0 + b2 + b4 + b6 < a0 + a2
                swap
                · -- branch
                  by_cases c678 : 0 < a2
                  swap
                  · omega
                  by_cases c679 : 0 < b10
                  swap
                  · -- branch
                    by_cases c680 : 0 < a10
                    swap
                    · omega
                    by_cases c681 : 0 < b6
                    swap
                    · omega
                    by_cases c682 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c683 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                    swap
                    · omega
                    have f684 := pair_fact E (i := 10) (j := 6) rfl rfl c680 c681
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f684
                    omega
                  by_cases c685 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c686 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                  swap
                  · -- branch
                    by_cases c687 : 0 < a4
                    swap
                    · -- branch
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
                                by_cases c693 : 0 < a6
                                swap
                                · omega
                                by_cases c694 : 0 < b0
                                swap
                                · -- branch
                                  by_cases c695 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c696 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c697 : a0 + a2 + a4 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c698 : b0 + b2 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f699 := pair_fact E (i := 6) (j := 4) rfl rfl c695 c696
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f699
                                  by_cases c700 : 0 < a2
                                  swap
                                  · omega
                                  by_cases c701 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c702 : a0 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c703 : b0 + b2 < a0 + a2
                                  swap
                                  · -- branch
                                    by_cases c704 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c705 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c706 : a0 + a2 + a4 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c707 : b0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f708 := pair_fact E (i := 6) (j := 2) rfl rfl c704 c705
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f708
                                    omega
                                  have f709 := pair_fact E (i := 2) (j := 4) rfl rfl c700 c701
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f709
                                  omega
                                by_cases c710 : a0 + a2 + a4 < 0 + b0
                                swap
                                · omega
                                by_cases c711 : 0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f712 := pair_fact E (i := 6) (j := 0) rfl rfl c693 c694
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f712
                                omega
                              by_cases c713 : 0 < b10
                              swap
                              · omega
                              by_cases c714 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c715 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · omega
                              have f716 := pair_fact E (i := 4) (j := 10) rfl rfl c692 c713
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f716
                              omega
                            by_cases c717 : 0 < b8
                            swap
                            · omega
                            by_cases c718 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c719 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · omega
                            have f720 := pair_fact E (i := 4) (j := 8) rfl rfl c691 c717
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f720
                            omega
                          by_cases c721 : 0 < b6
                          swap
                          · omega
                          by_cases c722 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c723 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · omega
                          have f724 := pair_fact E (i := 4) (j := 6) rfl rfl c690 c721
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f724
                          omega
                        by_cases c725 : 0 < b4
                        swap
                        · omega
                        by_cases c726 : a0 + a2 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c727 : b0 + b2 < a0 + a2 + a4
                        swap
                        · omega
                        have f728 := pair_fact E (i := 4) (j := 4) rfl rfl c689 c725
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f728
                        omega
                      by_cases c729 : 0 < b2
                      swap
                      · omega
                      by_cases c730 : a0 + a2 < b0 + b2
                      swap
                      · omega
                      by_cases c731 : b0 < a0 + a2 + a4
                      swap
                      · omega
                      have f732 := pair_fact E (i := 4) (j := 2) rfl rfl c688 c729
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f732
                      omega
                    by_cases c733 : 0 < b0
                    swap
                    · -- branch
                      by_cases c734 : 0 < a4
                      swap
                      · omega
                      by_cases c735 : 0 < b8
                      swap
                      · omega
                      by_cases c736 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c737 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                      swap
                      · -- branch
                        by_cases c738 : 0 < a4
                        swap
                        · omega
                        by_cases c739 : 0 < b10
                        swap
                        · omega
                        by_cases c740 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c741 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                        swap
                        · -- branch
                          by_cases c742 : 0 < a4
                          swap
                          · omega
                          by_cases c743 : 0 < b2
                          swap
                          · omega
                          by_cases c744 : a0 + a2 < b0 + b2
                          swap
                          · -- branch
                            by_cases c745 : 0 < a2
                            swap
                            · omega
                            by_cases c746 : 0 < b4
                            swap
                            · -- branch
                              by_cases c747 : 0 < a2
                              swap
                              · omega
                              by_cases c748 : 0 < b6
                              swap
                              · omega
                              by_cases c749 : a0 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c750 : b0 + b2 + b4 < a0 + a2
                              swap
                              · omega
                              have f751 := pair_fact E (i := 2) (j := 6) rfl rfl c747 c748
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f751
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
                              · omega
                              have f756 := pair_fact E (i := 4) (j := 6) rfl rfl c752 c753
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f756
                              omega
                            by_cases c757 : a0 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c758 : b0 + b2 < a0 + a2
                            swap
                            · omega
                            have f759 := pair_fact E (i := 2) (j := 4) rfl rfl c745 c746
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f759
                            by_cases c760 : 0 < a4
                            swap
                            · omega
                            by_cases c761 : 0 < b4
                            swap
                            · omega
                            by_cases c762 : a0 + a2 < b0 + b2 + b4
                            swap
                            · -- branch
                              by_cases c763 : 0 < a4
                              swap
                              · omega
                              by_cases c764 : 0 < b6
                              swap
                              · omega
                              by_cases c765 : a0 + a2 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c766 : b0 + b2 + b4 < a0 + a2 + a4
                              swap
                              · omega
                              have f767 := pair_fact E (i := 4) (j := 6) rfl rfl c763 c764
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f767
                              omega
                            by_cases c768 : b0 + b2 < a0 + a2 + a4
                            swap
                            · omega
                            have f769 := pair_fact E (i := 4) (j := 4) rfl rfl c760 c761
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f769
                            omega
                          by_cases c770 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f771 := pair_fact E (i := 4) (j := 2) rfl rfl c742 c743
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f771
                          by_cases c772 : 0 < a2
                          swap
                          · omega
                          by_cases c773 : 0 < b4
                          swap
                          · -- branch
                            by_cases c774 : 0 < a4
                            swap
                            · omega
                            by_cases c775 : 0 < b6
                            swap
                            · omega
                            by_cases c776 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c777 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · omega
                            have f778 := pair_fact E (i := 4) (j := 6) rfl rfl c774 c775
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f778
                            omega
                          by_cases c779 : a0 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c780 : b0 + b2 < a0 + a2
                          swap
                          · -- branch
                            by_cases c781 : 0 < a4
                            swap
                            · omega
                            by_cases c782 : 0 < b4
                            swap
                            · omega
                            by_cases c783 : a0 + a2 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c784 : b0 + b2 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c785 : 0 < a6
                              swap
                              · omega
                              by_cases c786 : 0 < b4
                              swap
                              · omega
                              by_cases c787 : a0 + a2 + a4 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c788 : b0 + b2 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f789 := pair_fact E (i := 6) (j := 4) rfl rfl c785 c786
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f789
                              omega
                            have f790 := pair_fact E (i := 4) (j := 4) rfl rfl c781 c782
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f790
                            omega
                          have f791 := pair_fact E (i := 2) (j := 4) rfl rfl c772 c773
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f791
                          omega
                        have f792 := pair_fact E (i := 4) (j := 10) rfl rfl c738 c739
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f792
                        omega
                      have f793 := pair_fact E (i := 4) (j := 8) rfl rfl c734 c735
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f793
                      omega
                    by_cases c794 : a0 + a2 < 0 + b0
                    swap
                    · omega
                    by_cases c795 : 0 < a0 + a2 + a4
                    swap
                    · omega
                    have f796 := pair_fact E (i := 4) (j := 0) rfl rfl c687 c733
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f796
                    omega
                  have f797 := pair_fact E (i := 2) (j := 10) rfl rfl c678 c679
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f797
                  omega
                have f798 := pair_fact E (i := 2) (j := 8) rfl rfl c654 c655
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f798
                omega
              by_cases c799 : a0 < 0 + b0
              swap
              · omega
              by_cases c800 : 0 < a0 + a2
              swap
              · omega
              have f801 := pair_fact E (i := 2) (j := 0) rfl rfl c7 c333
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f801
              by_cases c802 : 0 < a2
              swap
              · omega
              by_cases c803 : 0 < b2
              swap
              · -- branch
                by_cases c804 : 0 < a2
                swap
                · omega
                by_cases c805 : 0 < b4
                swap
                · -- branch
                  by_cases c806 : 0 < a2
                  swap
                  · omega
                  by_cases c807 : 0 < b6
                  swap
                  · omega
                  by_cases c808 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c809 : b0 + b2 + b4 < a0 + a2
                  swap
                  · -- branch
                    by_cases c810 : 0 < a4
                    swap
                    · omega
                    by_cases c811 : 0 < b2
                    swap
                    · -- branch
                      by_cases c812 : 0 < a4
                      swap
                      · omega
                      by_cases c813 : 0 < b4
                      swap
                      · -- branch
                        by_cases c814 : 0 < a4
                        swap
                        · omega
                        by_cases c815 : 0 < b6
                        swap
                        · omega
                        by_cases c816 : a0 + a2 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c817 : b0 + b2 + b4 < a0 + a2 + a4
                        swap
                        · -- branch
                          by_cases c818 : 0 < a6
                          swap
                          · omega
                          by_cases c819 : 0 < b6
                          swap
                          · omega
                          by_cases c820 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c821 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f822 := pair_fact E (i := 6) (j := 6) rfl rfl c818 c819
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f822
                          omega
                        have f823 := pair_fact E (i := 4) (j := 6) rfl rfl c814 c815
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f823
                        omega
                      by_cases c824 : a0 + a2 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c825 : b0 + b2 < a0 + a2 + a4
                      swap
                      · omega
                      have f826 := pair_fact E (i := 4) (j := 4) rfl rfl c812 c813
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f826
                      omega
                    by_cases c827 : a0 + a2 < b0 + b2
                    swap
                    · omega
                    by_cases c828 : b0 < a0 + a2 + a4
                    swap
                    · omega
                    have f829 := pair_fact E (i := 4) (j := 2) rfl rfl c810 c811
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f829
                    omega
                  have f830 := pair_fact E (i := 2) (j := 6) rfl rfl c806 c807
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f830
                  omega
                by_cases c831 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c832 : b0 + b2 < a0 + a2
                swap
                · -- branch
                  by_cases c833 : 0 < a6
                  swap
                  · omega
                  by_cases c834 : 0 < b2
                  swap
                  · -- branch
                    by_cases c835 : 0 < a6
                    swap
                    · omega
                    by_cases c836 : 0 < b4
                    swap
                    · omega
                    by_cases c837 : a0 + a2 + a4 < b0 + b2 + b4
                    swap
                    · -- branch
                      by_cases c838 : 0 < a4
                      swap
                      · omega
                      by_cases c839 : 0 < b4
                      swap
                      · omega
                      by_cases c840 : a0 + a2 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c841 : b0 + b2 < a0 + a2 + a4
                      swap
                      · omega
                      have f842 := pair_fact E (i := 4) (j := 4) rfl rfl c838 c839
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f842
                      omega
                    by_cases c843 : b0 + b2 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f844 := pair_fact E (i := 6) (j := 4) rfl rfl c835 c836
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f844
                    omega
                  by_cases c845 : a0 + a2 + a4 < b0 + b2
                  swap
                  · omega
                  by_cases c846 : b0 < a0 + a2 + a4 + a6
                  swap
                  · omega
                  have f847 := pair_fact E (i := 6) (j := 2) rfl rfl c833 c834
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f847
                  omega
                have f848 := pair_fact E (i := 2) (j := 4) rfl rfl c804 c805
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f848
                omega
              by_cases c849 : a0 < b0 + b2
              swap
              · omega
              by_cases c850 : b0 < a0 + a2
              swap
              · -- branch
                by_cases c851 : 0 < a2
                swap
                · omega
                by_cases c852 : 0 < b4
                swap
                · -- branch
                  by_cases c853 : 0 < a2
                  swap
                  · omega
                  by_cases c854 : 0 < b6
                  swap
                  · omega
                  by_cases c855 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c856 : b0 + b2 + b4 < a0 + a2
                  swap
                  · -- branch
                    by_cases c857 : 0 < a4
                    swap
                    · omega
                    by_cases c858 : 0 < b2
                    swap
                    · omega
                    by_cases c859 : a0 + a2 < b0 + b2
                    swap
                    · omega
                    by_cases c860 : b0 < a0 + a2 + a4
                    swap
                    · -- branch
                      by_cases c861 : 0 < a6
                      swap
                      · omega
                      by_cases c862 : 0 < b2
                      swap
                      · omega
                      by_cases c863 : a0 + a2 + a4 < b0 + b2
                      swap
                      · omega
                      by_cases c864 : b0 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f865 := pair_fact E (i := 6) (j := 2) rfl rfl c861 c862
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f865
                      omega
                    have f866 := pair_fact E (i := 4) (j := 2) rfl rfl c857 c858
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f866
                    omega
                  have f867 := pair_fact E (i := 2) (j := 6) rfl rfl c853 c854
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f867
                  omega
                by_cases c868 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c869 : b0 + b2 < a0 + a2
                swap
                · -- branch
                  by_cases c870 : 0 < a6
                  swap
                  · omega
                  by_cases c871 : 0 < b2
                  swap
                  · omega
                  by_cases c872 : a0 + a2 + a4 < b0 + b2
                  swap
                  · -- branch
                    by_cases c873 : 0 < a4
                    swap
                    · omega
                    by_cases c874 : 0 < b2
                    swap
                    · omega
                    by_cases c875 : a0 + a2 < b0 + b2
                    swap
                    · omega
                    by_cases c876 : b0 < a0 + a2 + a4
                    swap
                    · omega
                    have f877 := pair_fact E (i := 4) (j := 2) rfl rfl c873 c874
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f877
                    omega
                  by_cases c878 : b0 < a0 + a2 + a4 + a6
                  swap
                  · omega
                  have f879 := pair_fact E (i := 6) (j := 2) rfl rfl c870 c871
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f879
                  omega
                have f880 := pair_fact E (i := 2) (j := 4) rfl rfl c851 c852
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f880
                omega
              have f881 := pair_fact E (i := 2) (j := 2) rfl rfl c802 c803
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f881
              omega
            by_cases c882 : 0 < b10
            swap
            · omega
            by_cases c883 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c884 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · omega
            have f885 := pair_fact E (i := 0) (j := 10) rfl rfl c6 c882
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f885
            omega
          by_cases c886 : 0 < b8
          swap
          · omega
          by_cases c887 : 0 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c888 : b0 + b2 + b4 + b6 < 0 + a0
          swap
          · omega
          have f889 := pair_fact E (i := 0) (j := 8) rfl rfl c5 c886
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f889
          omega
        by_cases c890 : 0 < b6
        swap
        · omega
        by_cases c891 : 0 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c892 : b0 + b2 + b4 < 0 + a0
        swap
        · omega
        have f893 := pair_fact E (i := 0) (j := 6) rfl rfl c4 c890
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f893
        omega
      by_cases c894 : 0 < b4
      swap
      · omega
      by_cases c895 : 0 < b0 + b2 + b4
      swap
      · omega
      by_cases c896 : b0 + b2 < 0 + a0
      swap
      · omega
      have f897 := pair_fact E (i := 0) (j := 4) rfl rfl c3 c894
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f897
      omega
    by_cases c898 : 0 < b2
    swap
    · omega
    by_cases c899 : 0 < b0 + b2
    swap
    · omega
    by_cases c900 : b0 < 0 + a0
    swap
    · omega
    have f901 := pair_fact E (i := 0) (j := 2) rfl rfl c2 c898
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f901
    omega
  by_cases c902 : 0 < b0
  swap
  · -- branch
    by_cases c903 : 0 < a0
    swap
    · omega
    by_cases c904 : 0 < b2
    swap
    · -- branch
      by_cases c905 : 0 < a2
      swap
      · omega
      by_cases c906 : 0 < b0
      swap
      · -- branch
        by_cases c907 : 0 < a2
        swap
        · omega
        by_cases c908 : 0 < b2
        swap
        · -- branch
          by_cases c909 : 0 < a2
          swap
          · omega
          by_cases c910 : 0 < b6
          swap
          · omega
          by_cases c911 : a0 < b0 + b2 + b4 + b6
          swap
          · omega
          by_cases c912 : b0 + b2 + b4 < a0 + a2
          swap
          · omega
          have f913 := pair_fact E (i := 2) (j := 6) rfl rfl c909 c910
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f913
          by_cases c914 : 0 < a0
          swap
          · omega
          by_cases c915 : 0 < b4
          swap
          · -- branch
            by_cases c916 : 0 < a0
            swap
            · omega
            by_cases c917 : 0 < b6
            swap
            · omega
            by_cases c918 : 0 < b0 + b2 + b4 + b6
            swap
            · omega
            by_cases c919 : b0 + b2 + b4 < 0 + a0
            swap
            · omega
            have f920 := pair_fact E (i := 0) (j := 6) rfl rfl c916 c917
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f920
            omega
          by_cases c921 : 0 < b0 + b2 + b4
          swap
          · omega
          by_cases c922 : b0 + b2 < 0 + a0
          swap
          · omega
          have f923 := pair_fact E (i := 0) (j := 4) rfl rfl c914 c915
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f923
          omega
        by_cases c924 : a0 < b0 + b2
        swap
        · omega
        by_cases c925 : b0 < a0 + a2
        swap
        · omega
        have f926 := pair_fact E (i := 2) (j := 2) rfl rfl c907 c908
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f926
        omega
      by_cases c927 : a0 < 0 + b0
      swap
      · omega
      by_cases c928 : 0 < a0 + a2
      swap
      · omega
      have f929 := pair_fact E (i := 2) (j := 0) rfl rfl c905 c906
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f929
      omega
    by_cases c930 : 0 < b0 + b2
    swap
    · omega
    by_cases c931 : b0 < 0 + a0
    swap
    · omega
    have f932 := pair_fact E (i := 0) (j := 2) rfl rfl c903 c904
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f932
    by_cases c933 : 0 < a0
    swap
    · omega
    by_cases c934 : 0 < b8
    swap
    · -- branch
      by_cases c935 : 0 < a8
      swap
      · omega
      by_cases c936 : 0 < b0
      swap
      · -- branch
        by_cases c937 : 0 < a8
        swap
        · omega
        by_cases c938 : 0 < b2
        swap
        · omega
        by_cases c939 : a0 + a2 + a4 + a6 < b0 + b2
        swap
        · -- branch
          by_cases c940 : 0 < a8
          swap
          · omega
          by_cases c941 : 0 < b6
          swap
          · omega
          by_cases c942 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
          swap
          · -- branch
            by_cases c943 : 0 < a6
            swap
            · omega
            by_cases c944 : 0 < b6
            swap
            · omega
            by_cases c945 : a0 + a2 + a4 < b0 + b2 + b4 + b6
            swap
            · omega
            by_cases c946 : b0 + b2 + b4 < a0 + a2 + a4 + a6
            swap
            · omega
            have f947 := pair_fact E (i := 6) (j := 6) rfl rfl c943 c944
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f947
            omega
          by_cases c948 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
          swap
          · omega
          have f949 := pair_fact E (i := 8) (j := 6) rfl rfl c940 c941
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f949
          omega
        by_cases c950 : b0 < a0 + a2 + a4 + a6 + a8
        swap
        · omega
        have f951 := pair_fact E (i := 8) (j := 2) rfl rfl c937 c938
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f951
        omega
      by_cases c952 : a0 + a2 + a4 + a6 < 0 + b0
      swap
      · omega
      by_cases c953 : 0 < a0 + a2 + a4 + a6 + a8
      swap
      · omega
      have f954 := pair_fact E (i := 8) (j := 0) rfl rfl c935 c936
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f954
      omega
    by_cases c955 : 0 < b0 + b2 + b4 + b6 + b8
    swap
    · omega
    by_cases c956 : b0 + b2 + b4 + b6 < 0 + a0
    swap
    · -- branch
      by_cases c957 : 0 < a0
      swap
      · omega
      by_cases c958 : 0 < b10
      swap
      · -- branch
        by_cases c959 : 0 < a10
        swap
        · -- branch
          by_cases c960 : 0 < a2
          swap
          · -- branch
            by_cases c961 : 0 < a2
            swap
            · -- branch
              by_cases c962 : 0 < a2
              swap
              · -- branch
                by_cases c963 : 0 < a2
                swap
                · -- branch
                  by_cases c964 : 0 < a2
                  swap
                  · -- branch
                    by_cases c965 : 0 < a2
                    swap
                    · -- branch
                      by_cases c966 : 0 < a4
                      swap
                      · -- branch
                        by_cases c967 : 0 < a6
                        swap
                        · omega
                        by_cases c968 : 0 < b6
                        swap
                        · omega
                        by_cases c969 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c970 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f971 := pair_fact E (i := 6) (j := 6) rfl rfl c967 c968
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f971
                        omega
                      by_cases c972 : 0 < b6
                      swap
                      · omega
                      by_cases c973 : a0 + a2 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c974 : b0 + b2 + b4 < a0 + a2 + a4
                      swap
                      · omega
                      have f975 := pair_fact E (i := 4) (j := 6) rfl rfl c966 c972
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f975
                      omega
                    by_cases c976 : 0 < b10
                    swap
                    · omega
                    by_cases c977 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c978 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · omega
                    have f979 := pair_fact E (i := 2) (j := 10) rfl rfl c965 c976
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f979
                    omega
                  by_cases c980 : 0 < b8
                  swap
                  · omega
                  by_cases c981 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c982 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · omega
                  have f983 := pair_fact E (i := 2) (j := 8) rfl rfl c964 c980
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f983
                  omega
                by_cases c984 : 0 < b4
                swap
                · omega
                by_cases c985 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c986 : b0 + b2 < a0 + a2
                swap
                · omega
                have f987 := pair_fact E (i := 2) (j := 4) rfl rfl c963 c984
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f987
                omega
              by_cases c988 : 0 < b2
              swap
              · omega
              by_cases c989 : a0 < b0 + b2
              swap
              · omega
              by_cases c990 : b0 < a0 + a2
              swap
              · omega
              have f991 := pair_fact E (i := 2) (j := 2) rfl rfl c962 c988
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f991
              omega
            by_cases c992 : 0 < b0
            swap
            · omega
            by_cases c993 : a0 < 0 + b0
            swap
            · omega
            by_cases c994 : 0 < a0 + a2
            swap
            · omega
            have f995 := pair_fact E (i := 2) (j := 0) rfl rfl c961 c992
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f995
            omega
          by_cases c996 : 0 < b6
          swap
          · omega
          by_cases c997 : a0 < b0 + b2 + b4 + b6
          swap
          · omega
          by_cases c998 : b0 + b2 + b4 < a0 + a2
          swap
          · omega
          have f999 := pair_fact E (i := 2) (j := 6) rfl rfl c960 c996
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f999
          omega
        by_cases c1000 : 0 < b8
        swap
        · omega
        by_cases c1001 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
        swap
        · omega
        by_cases c1002 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
        swap
        · omega
        have f1003 := pair_fact E (i := 10) (j := 8) rfl rfl c959 c1000
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1003
        omega
      by_cases c1004 : 0 < b0 + b2 + b4 + b6 + b8 + b10
      swap
      · omega
      by_cases c1005 : b0 + b2 + b4 + b6 + b8 < 0 + a0
      swap
      · -- branch
        by_cases c1006 : 0 < a2
        swap
        · -- branch
          by_cases c1007 : 0 < a2
          swap
          · -- branch
            by_cases c1008 : 0 < a2
            swap
            · -- branch
              by_cases c1009 : 0 < a2
              swap
              · -- branch
                by_cases c1010 : 0 < a2
                swap
                · -- branch
                  by_cases c1011 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1012 : 0 < a6
                    swap
                    · omega
                    by_cases c1013 : 0 < b0
                    swap
                    · -- branch
                      by_cases c1014 : 0 < a6
                      swap
                      · omega
                      by_cases c1015 : 0 < b2
                      swap
                      · omega
                      by_cases c1016 : a0 + a2 + a4 < b0 + b2
                      swap
                      · -- branch
                        by_cases c1017 : 0 < a6
                        swap
                        · omega
                        by_cases c1018 : 0 < b10
                        swap
                        · omega
                        by_cases c1019 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c1020 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
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
                        have f1026 := pair_fact E (i := 6) (j := 10) rfl rfl c1017 c1018
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1026
                        omega
                      by_cases c1027 : b0 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f1028 := pair_fact E (i := 6) (j := 2) rfl rfl c1014 c1015
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1028
                      omega
                    by_cases c1029 : a0 + a2 + a4 < 0 + b0
                    swap
                    · omega
                    by_cases c1030 : 0 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f1031 := pair_fact E (i := 6) (j := 0) rfl rfl c1012 c1013
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1031
                    omega
                  by_cases c1032 : 0 < b10
                  swap
                  · omega
                  by_cases c1033 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c1034 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                  swap
                  · omega
                  have f1035 := pair_fact E (i := 2) (j := 10) rfl rfl c1011 c1032
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1035
                  omega
                by_cases c1036 : 0 < b8
                swap
                · omega
                by_cases c1037 : a0 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c1038 : b0 + b2 + b4 + b6 < a0 + a2
                swap
                · omega
                have f1039 := pair_fact E (i := 2) (j := 8) rfl rfl c1010 c1036
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1039
                omega
              by_cases c1040 : 0 < b6
              swap
              · omega
              by_cases c1041 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c1042 : b0 + b2 + b4 < a0 + a2
              swap
              · omega
              have f1043 := pair_fact E (i := 2) (j := 6) rfl rfl c1009 c1040
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1043
              omega
            by_cases c1044 : 0 < b4
            swap
            · omega
            by_cases c1045 : a0 < b0 + b2 + b4
            swap
            · omega
            by_cases c1046 : b0 + b2 < a0 + a2
            swap
            · omega
            have f1047 := pair_fact E (i := 2) (j := 4) rfl rfl c1008 c1044
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1047
            omega
          by_cases c1048 : 0 < b2
          swap
          · omega
          by_cases c1049 : a0 < b0 + b2
          swap
          · omega
          by_cases c1050 : b0 < a0 + a2
          swap
          · omega
          have f1051 := pair_fact E (i := 2) (j := 2) rfl rfl c1007 c1048
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1051
          omega
        by_cases c1052 : 0 < b0
        swap
        · -- branch
          by_cases c1053 : 0 < a2
          swap
          · omega
          by_cases c1054 : 0 < b2
          swap
          · omega
          by_cases c1055 : a0 < b0 + b2
          swap
          · -- branch
            by_cases c1056 : 0 < a2
            swap
            · omega
            by_cases c1057 : 0 < b8
            swap
            · omega
            by_cases c1058 : a0 < b0 + b2 + b4 + b6 + b8
            swap
            · omega
            by_cases c1059 : b0 + b2 + b4 + b6 < a0 + a2
            swap
            · -- branch
              by_cases c1060 : 0 < a2
              swap
              · omega
              by_cases c1061 : 0 < b10
              swap
              · omega
              by_cases c1062 : a0 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c1063 : b0 + b2 + b4 + b6 + b8 < a0 + a2
              swap
              · -- branch
                by_cases c1064 : 0 < a2
                swap
                · omega
                by_cases c1065 : 0 < b4
                swap
                · -- branch
                  by_cases c1066 : 0 < a2
                  swap
                  · omega
                  by_cases c1067 : 0 < b6
                  swap
                  · omega
                  by_cases c1068 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c1069 : b0 + b2 + b4 < a0 + a2
                  swap
                  · omega
                  have f1070 := pair_fact E (i := 2) (j := 6) rfl rfl c1066 c1067
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1070
                  omega
                by_cases c1071 : a0 < b0 + b2 + b4
                swap
                · -- branch
                  by_cases c1072 : 0 < a2
                  swap
                  · omega
                  by_cases c1073 : 0 < b6
                  swap
                  · omega
                  by_cases c1074 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c1075 : b0 + b2 + b4 < a0 + a2
                  swap
                  · omega
                  have f1076 := pair_fact E (i := 2) (j := 6) rfl rfl c1072 c1073
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1076
                  omega
                by_cases c1077 : b0 + b2 < a0 + a2
                swap
                · omega
                have f1078 := pair_fact E (i := 2) (j := 4) rfl rfl c1064 c1065
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1078
                omega
              have f1079 := pair_fact E (i := 2) (j := 10) rfl rfl c1060 c1061
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1079
              omega
            have f1080 := pair_fact E (i := 2) (j := 8) rfl rfl c1056 c1057
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1080
            omega
          by_cases c1081 : b0 < a0 + a2
          swap
          · omega
          have f1082 := pair_fact E (i := 2) (j := 2) rfl rfl c1053 c1054
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1082
          omega
        by_cases c1083 : a0 < 0 + b0
        swap
        · omega
        by_cases c1084 : 0 < a0 + a2
        swap
        · omega
        have f1085 := pair_fact E (i := 2) (j := 0) rfl rfl c1006 c1052
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1085
        omega
      have f1086 := pair_fact E (i := 0) (j := 10) rfl rfl c957 c958
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1086
      omega
    have f1087 := pair_fact E (i := 0) (j := 8) rfl rfl c933 c934
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1087
    omega
  by_cases c1088 : 0 < 0 + b0
  swap
  · omega
  by_cases c1089 : 0 < 0 + a0
  swap
  · omega
  have f1090 := pair_fact E (i := 0) (j := 0) rfl rfl c1 c902
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1090
  by_cases c1091 : 0 < a0
  swap
  · omega
  by_cases c1092 : 0 < b8
  swap
  · -- branch
    by_cases c1093 : 0 < a8
    swap
    · omega
    by_cases c1094 : 0 < b0
    swap
    · omega
    by_cases c1095 : a0 + a2 + a4 + a6 < 0 + b0
    swap
    · -- branch
      by_cases c1096 : 0 < a8
      swap
      · omega
      by_cases c1097 : 0 < b8
      swap
      · -- branch
        by_cases c1098 : 0 < a0
        swap
        · omega
        by_cases c1099 : 0 < b6
        swap
        · omega
        by_cases c1100 : 0 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c1101 : b0 + b2 + b4 < 0 + a0
        swap
        · -- branch
          by_cases c1102 : 0 < a0
          swap
          · omega
          by_cases c1103 : 0 < b10
          swap
          · -- branch
            by_cases c1104 : 0 < a8
            swap
            · omega
            by_cases c1105 : 0 < b6
            swap
            · omega
            by_cases c1106 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
            swap
            · omega
            by_cases c1107 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
            swap
            · omega
            have f1108 := pair_fact E (i := 8) (j := 6) rfl rfl c1104 c1105
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1108
            by_cases c1109 : 0 < a8
            swap
            · omega
            by_cases c1110 : 0 < b10
            swap
            · -- branch
              by_cases c1111 : 0 < a10
              swap
              · -- branch
                by_cases c1112 : 0 < a10
                swap
                · -- branch
                  by_cases c1113 : 0 < a10
                  swap
                  · -- branch
                    by_cases c1114 : 0 < a10
                    swap
                    · -- branch
                      by_cases c1115 : 0 < a10
                      swap
                      · -- branch
                        by_cases c1116 : 0 < a10
                        swap
                        · -- branch
                          by_cases c1117 : 0 < a0
                          swap
                          · omega
                          by_cases c1118 : 0 < b2
                          swap
                          · -- branch
                            by_cases c1119 : 0 < a2
                            swap
                            · omega
                            by_cases c1120 : 0 < b2
                            swap
                            · -- branch
                              by_cases c1121 : 0 < a2
                              swap
                              · omega
                              by_cases c1122 : 0 < b6
                              swap
                              · omega
                              by_cases c1123 : a0 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c1124 : b0 + b2 + b4 < a0 + a2
                              swap
                              · -- branch
                                by_cases c1125 : 0 < a6
                                swap
                                · omega
                                by_cases c1126 : 0 < b6
                                swap
                                · omega
                                by_cases c1127 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c1128 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f1129 := pair_fact E (i := 6) (j := 6) rfl rfl c1125 c1126
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1129
                                omega
                              have f1130 := pair_fact E (i := 2) (j := 6) rfl rfl c1121 c1122
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1130
                              omega
                            by_cases c1131 : a0 < b0 + b2
                            swap
                            · omega
                            by_cases c1132 : b0 < a0 + a2
                            swap
                            · omega
                            have f1133 := pair_fact E (i := 2) (j := 2) rfl rfl c1119 c1120
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1133
                            omega
                          by_cases c1134 : 0 < b0 + b2
                          swap
                          · omega
                          by_cases c1135 : b0 < 0 + a0
                          swap
                          · -- branch
                            by_cases c1136 : 0 < a6
                            swap
                            · omega
                            by_cases c1137 : 0 < b0
                            swap
                            · omega
                            by_cases c1138 : a0 + a2 + a4 < 0 + b0
                            swap
                            · -- branch
                              by_cases c1139 : 0 < a6
                              swap
                              · omega
                              by_cases c1140 : 0 < b2
                              swap
                              · omega
                              by_cases c1141 : a0 + a2 + a4 < b0 + b2
                              swap
                              · -- branch
                                by_cases c1142 : 0 < a6
                                swap
                                · omega
                                by_cases c1143 : 0 < b6
                                swap
                                · omega
                                by_cases c1144 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c1145 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f1146 := pair_fact E (i := 6) (j := 6) rfl rfl c1142 c1143
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1146
                                omega
                              by_cases c1147 : b0 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f1148 := pair_fact E (i := 6) (j := 2) rfl rfl c1139 c1140
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1148
                              omega
                            by_cases c1149 : 0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f1150 := pair_fact E (i := 6) (j := 0) rfl rfl c1136 c1137
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1150
                            omega
                          have f1151 := pair_fact E (i := 0) (j := 2) rfl rfl c1117 c1118
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1151
                          omega
                        by_cases c1152 : 0 < b10
                        swap
                        · omega
                        by_cases c1153 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c1154 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8 + a10
                        swap
                        · omega
                        have f1155 := pair_fact E (i := 10) (j := 10) rfl rfl c1116 c1152
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1155
                        omega
                      by_cases c1156 : 0 < b8
                      swap
                      · omega
                      by_cases c1157 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c1158 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f1159 := pair_fact E (i := 10) (j := 8) rfl rfl c1115 c1156
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1159
                      omega
                    by_cases c1160 : 0 < b4
                    swap
                    · omega
                    by_cases c1161 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c1162 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                    swap
                    · omega
                    have f1163 := pair_fact E (i := 10) (j := 4) rfl rfl c1114 c1160
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1163
                    omega
                  by_cases c1164 : 0 < b2
                  swap
                  · omega
                  by_cases c1165 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                  swap
                  · omega
                  by_cases c1166 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                  swap
                  · omega
                  have f1167 := pair_fact E (i := 10) (j := 2) rfl rfl c1113 c1164
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1167
                  omega
                by_cases c1168 : 0 < b0
                swap
                · omega
                by_cases c1169 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                swap
                · omega
                by_cases c1170 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                swap
                · omega
                have f1171 := pair_fact E (i := 10) (j := 0) rfl rfl c1112 c1168
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1171
                omega
              by_cases c1172 : 0 < b6
              swap
              · omega
              by_cases c1173 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c1174 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
              swap
              · omega
              have f1175 := pair_fact E (i := 10) (j := 6) rfl rfl c1111 c1172
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1175
              omega
            by_cases c1176 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c1177 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
            swap
            · omega
            have f1178 := pair_fact E (i := 8) (j := 10) rfl rfl c1109 c1110
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1178
            omega
          by_cases c1179 : 0 < b0 + b2 + b4 + b6 + b8 + b10
          swap
          · omega
          by_cases c1180 : b0 + b2 + b4 + b6 + b8 < 0 + a0
          swap
          · -- branch
            by_cases c1181 : 0 < a2
            swap
            · -- branch
              by_cases c1182 : 0 < a2
              swap
              · -- branch
                by_cases c1183 : 0 < a2
                swap
                · -- branch
                  by_cases c1184 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1185 : 0 < a2
                    swap
                    · -- branch
                      by_cases c1186 : 0 < a2
                      swap
                      · -- branch
                        by_cases c1187 : 0 < a6
                        swap
                        · omega
                        by_cases c1188 : 0 < b8
                        swap
                        · -- branch
                          by_cases c1189 : 0 < a6
                          swap
                          · omega
                          by_cases c1190 : 0 < b10
                          swap
                          · omega
                          by_cases c1191 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c1192 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                          swap
                          · -- branch
                            by_cases c1193 : 0 < a8
                            swap
                            · omega
                            by_cases c1194 : 0 < b2
                            swap
                            · omega
                            by_cases c1195 : a0 + a2 + a4 + a6 < b0 + b2
                            swap
                            · -- branch
                              by_cases c1196 : 0 < a0
                              swap
                              · omega
                              by_cases c1197 : 0 < b2
                              swap
                              · omega
                              by_cases c1198 : 0 < b0 + b2
                              swap
                              · omega
                              by_cases c1199 : b0 < 0 + a0
                              swap
                              · -- branch
                                by_cases c1200 : 0 < a0
                                swap
                                · omega
                                by_cases c1201 : 0 < b4
                                swap
                                · -- branch
                                  by_cases c1202 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c1203 : 0 < b4
                                  swap
                                  · -- branch
                                    by_cases c1204 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1205 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c1206 : a0 + a2 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c1207 : b0 + b2 + b4 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c1208 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c1209 : 0 < b8
                                      swap
                                      · -- branch
                                        by_cases c1210 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c1211 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c1212 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c1213 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · -- branch
                                          by_cases c1214 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c1215 : 0 < b4
                                          swap
                                          · -- branch
                                            by_cases c1216 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c1217 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c1218 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c1219 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f1220 := pair_fact E (i := 6) (j := 6) rfl rfl c1216 c1217
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1220
                                            by_cases c1221 : 0 < a4
                                            swap
                                            · omega
                                            by_cases c1222 : 0 < b0
                                            swap
                                            · omega
                                            by_cases c1223 : a0 + a2 < 0 + b0
                                            swap
                                            · -- branch
                                              by_cases c1224 : 0 < a8
                                              swap
                                              · omega
                                              by_cases c1225 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c1226 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c1227 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                              swap
                                              · omega
                                              have f1228 := pair_fact E (i := 8) (j := 6) rfl rfl c1224 c1225
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1228
                                              omega
                                            by_cases c1229 : 0 < a0 + a2 + a4
                                            swap
                                            · omega
                                            have f1230 := pair_fact E (i := 4) (j := 0) rfl rfl c1221 c1222
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1230
                                            omega
                                          by_cases c1231 : a0 + a2 + a4 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c1232 : b0 + b2 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f1233 := pair_fact E (i := 6) (j := 4) rfl rfl c1214 c1215
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1233
                                          omega
                                        have f1234 := pair_fact E (i := 4) (j := 10) rfl rfl c1210 c1211
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1234
                                        omega
                                      by_cases c1235 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c1236 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f1237 := pair_fact E (i := 4) (j := 8) rfl rfl c1208 c1209
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1237
                                      omega
                                    have f1238 := pair_fact E (i := 4) (j := 6) rfl rfl c1204 c1205
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1238
                                    omega
                                  by_cases c1239 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c1240 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f1241 := pair_fact E (i := 4) (j := 4) rfl rfl c1202 c1203
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1241
                                  omega
                                by_cases c1242 : 0 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c1243 : b0 + b2 < 0 + a0
                                swap
                                · -- branch
                                  by_cases c1244 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1245 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c1246 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c1247 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1248 := pair_fact E (i := 6) (j := 2) rfl rfl c1244 c1245
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1248
                                  by_cases c1249 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1250 : 0 < b0
                                  swap
                                  · omega
                                  by_cases c1251 : a0 + a2 + a4 < 0 + b0
                                  swap
                                  · -- branch
                                    by_cases c1252 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c1253 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c1254 : a0 + a2 + a4 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c1255 : b0 + b2 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f1256 := pair_fact E (i := 6) (j := 4) rfl rfl c1252 c1253
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1256
                                    by_cases c1257 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c1258 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c1259 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                    swap
                                    · -- branch
                                      by_cases c1260 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c1261 : 0 < b6
                                      swap
                                      · omega
                                      by_cases c1262 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                      swap
                                      · -- branch
                                        by_cases c1263 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c1264 : 0 < b0
                                        swap
                                        · omega
                                        by_cases c1265 : a0 + a2 < 0 + b0
                                        swap
                                        · omega
                                        by_cases c1266 : 0 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f1267 := pair_fact E (i := 4) (j := 0) rfl rfl c1263 c1264
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1267
                                        omega
                                      by_cases c1268 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f1269 := pair_fact E (i := 8) (j := 6) rfl rfl c1260 c1261
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1269
                                      omega
                                    by_cases c1270 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f1271 := pair_fact E (i := 8) (j := 4) rfl rfl c1257 c1258
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1271
                                    omega
                                  by_cases c1272 : 0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1273 := pair_fact E (i := 6) (j := 0) rfl rfl c1249 c1250
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1273
                                  omega
                                have f1274 := pair_fact E (i := 0) (j := 4) rfl rfl c1200 c1201
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1274
                                omega
                              have f1275 := pair_fact E (i := 0) (j := 2) rfl rfl c1196 c1197
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1275
                              by_cases c1276 : 0 < a6
                              swap
                              · omega
                              by_cases c1277 : 0 < b0
                              swap
                              · omega
                              by_cases c1278 : a0 + a2 + a4 < 0 + b0
                              swap
                              · -- branch
                                by_cases c1279 : 0 < a6
                                swap
                                · omega
                                by_cases c1280 : 0 < b2
                                swap
                                · omega
                                by_cases c1281 : a0 + a2 + a4 < b0 + b2
                                swap
                                · -- branch
                                  by_cases c1282 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1283 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c1284 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c1285 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1286 := pair_fact E (i := 6) (j := 6) rfl rfl c1282 c1283
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1286
                                  omega
                                by_cases c1287 : b0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f1288 := pair_fact E (i := 6) (j := 2) rfl rfl c1279 c1280
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1288
                                omega
                              by_cases c1289 : 0 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f1290 := pair_fact E (i := 6) (j := 0) rfl rfl c1276 c1277
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1290
                              omega
                            by_cases c1291 : b0 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f1292 := pair_fact E (i := 8) (j := 2) rfl rfl c1193 c1194
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1292
                            omega
                          have f1293 := pair_fact E (i := 6) (j := 10) rfl rfl c1189 c1190
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1293
                          omega
                        by_cases c1294 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1295 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f1296 := pair_fact E (i := 6) (j := 8) rfl rfl c1187 c1188
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1296
                        omega
                      by_cases c1297 : 0 < b10
                      swap
                      · omega
                      by_cases c1298 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                      swap
                      · omega
                      by_cases c1299 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                      swap
                      · omega
                      have f1300 := pair_fact E (i := 2) (j := 10) rfl rfl c1186 c1297
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1300
                      omega
                    by_cases c1301 : 0 < b6
                    swap
                    · omega
                    by_cases c1302 : a0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c1303 : b0 + b2 + b4 < a0 + a2
                    swap
                    · omega
                    have f1304 := pair_fact E (i := 2) (j := 6) rfl rfl c1185 c1301
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1304
                    omega
                  by_cases c1305 : 0 < b4
                  swap
                  · omega
                  by_cases c1306 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c1307 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f1308 := pair_fact E (i := 2) (j := 4) rfl rfl c1184 c1305
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1308
                  omega
                by_cases c1309 : 0 < b2
                swap
                · omega
                by_cases c1310 : a0 < b0 + b2
                swap
                · omega
                by_cases c1311 : b0 < a0 + a2
                swap
                · omega
                have f1312 := pair_fact E (i := 2) (j := 2) rfl rfl c1183 c1309
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1312
                omega
              by_cases c1313 : 0 < b0
              swap
              · omega
              by_cases c1314 : a0 < 0 + b0
              swap
              · omega
              by_cases c1315 : 0 < a0 + a2
              swap
              · omega
              have f1316 := pair_fact E (i := 2) (j := 0) rfl rfl c1182 c1313
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1316
              omega
            by_cases c1317 : 0 < b8
            swap
            · -- branch
              by_cases c1318 : 0 < a2
              swap
              · omega
              by_cases c1319 : 0 < b10
              swap
              · omega
              by_cases c1320 : a0 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c1321 : b0 + b2 + b4 + b6 + b8 < a0 + a2
              swap
              · -- branch
                by_cases c1322 : 0 < a2
                swap
                · omega
                by_cases c1323 : 0 < b0
                swap
                · omega
                by_cases c1324 : a0 < 0 + b0
                swap
                · -- branch
                  by_cases c1325 : 0 < a2
                  swap
                  · omega
                  by_cases c1326 : 0 < b6
                  swap
                  · omega
                  by_cases c1327 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c1328 : b0 + b2 + b4 < a0 + a2
                  swap
                  · -- branch
                    by_cases c1329 : 0 < a4
                    swap
                    · -- branch
                      by_cases c1330 : 0 < a4
                      swap
                      · -- branch
                        by_cases c1331 : 0 < a4
                        swap
                        · -- branch
                          by_cases c1332 : 0 < a4
                          swap
                          · -- branch
                            by_cases c1333 : 0 < a4
                            swap
                            · -- branch
                              by_cases c1334 : 0 < a4
                              swap
                              · -- branch
                                by_cases c1335 : 0 < a6
                                swap
                                · omega
                                by_cases c1336 : 0 < b0
                                swap
                                · omega
                                by_cases c1337 : a0 + a2 + a4 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c1338 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1339 : 0 < b8
                                  swap
                                  · -- branch
                                    by_cases c1340 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c1341 : 0 < b10
                                    swap
                                    · omega
                                    by_cases c1342 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c1343 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                    swap
                                    · -- branch
                                      by_cases c1344 : 0 < a0
                                      swap
                                      · omega
                                      by_cases c1345 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c1346 : 0 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c1347 : b0 + b2 < 0 + a0
                                      swap
                                      · -- branch
                                        by_cases c1348 : 0 < a2
                                        swap
                                        · omega
                                        by_cases c1349 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c1350 : a0 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c1351 : b0 + b2 < a0 + a2
                                        swap
                                        · -- branch
                                          by_cases c1352 : 0 < a2
                                          swap
                                          · omega
                                          by_cases c1353 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c1354 : a0 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c1355 : b0 < a0 + a2
                                          swap
                                          · omega
                                          have f1356 := pair_fact E (i := 2) (j := 2) rfl rfl c1352 c1353
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1356
                                          by_cases c1357 : 0 < a0
                                          swap
                                          · omega
                                          by_cases c1358 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c1359 : 0 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c1360 : b0 < 0 + a0
                                          swap
                                          · -- branch
                                            by_cases c1361 : 0 < a8
                                            swap
                                            · omega
                                            by_cases c1362 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c1363 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c1364 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f1365 := pair_fact E (i := 8) (j := 6) rfl rfl c1361 c1362
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1365
                                            omega
                                          have f1366 := pair_fact E (i := 0) (j := 2) rfl rfl c1357 c1358
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1366
                                          omega
                                        have f1367 := pair_fact E (i := 2) (j := 4) rfl rfl c1348 c1349
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1367
                                        by_cases c1368 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c1369 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c1370 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                        swap
                                        · -- branch
                                          by_cases c1371 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c1372 : 0 < b6
                                          swap
                                          · omega
                                          by_cases c1373 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                          swap
                                          · -- branch
                                            by_cases c1374 : 0 < a0
                                            swap
                                            · omega
                                            by_cases c1375 : 0 < b2
                                            swap
                                            · omega
                                            by_cases c1376 : 0 < b0 + b2
                                            swap
                                            · omega
                                            by_cases c1377 : b0 < 0 + a0
                                            swap
                                            · omega
                                            have f1378 := pair_fact E (i := 0) (j := 2) rfl rfl c1374 c1375
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1378
                                            omega
                                          by_cases c1379 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f1380 := pair_fact E (i := 8) (j := 6) rfl rfl c1371 c1372
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1380
                                          omega
                                        by_cases c1381 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f1382 := pair_fact E (i := 8) (j := 4) rfl rfl c1368 c1369
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1382
                                        omega
                                      have f1383 := pair_fact E (i := 0) (j := 4) rfl rfl c1344 c1345
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1383
                                      by_cases c1384 : 0 < a2
                                      swap
                                      · omega
                                      by_cases c1385 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c1386 : a0 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c1387 : b0 + b2 < a0 + a2
                                      swap
                                      · omega
                                      have f1388 := pair_fact E (i := 2) (j := 4) rfl rfl c1384 c1385
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1388
                                      omega
                                    have f1389 := pair_fact E (i := 6) (j := 10) rfl rfl c1340 c1341
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1389
                                    omega
                                  by_cases c1390 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c1391 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1392 := pair_fact E (i := 6) (j := 8) rfl rfl c1338 c1339
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1392
                                  omega
                                by_cases c1393 : 0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f1394 := pair_fact E (i := 6) (j := 0) rfl rfl c1335 c1336
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1394
                                omega
                              by_cases c1395 : 0 < b10
                              swap
                              · omega
                              by_cases c1396 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c1397 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · omega
                              have f1398 := pair_fact E (i := 4) (j := 10) rfl rfl c1334 c1395
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1398
                              omega
                            by_cases c1399 : 0 < b8
                            swap
                            · omega
                            by_cases c1400 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1401 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · omega
                            have f1402 := pair_fact E (i := 4) (j := 8) rfl rfl c1333 c1399
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1402
                            omega
                          by_cases c1403 : 0 < b6
                          swap
                          · omega
                          by_cases c1404 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c1405 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · omega
                          have f1406 := pair_fact E (i := 4) (j := 6) rfl rfl c1332 c1403
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1406
                          omega
                        by_cases c1407 : 0 < b4
                        swap
                        · omega
                        by_cases c1408 : a0 + a2 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c1409 : b0 + b2 < a0 + a2 + a4
                        swap
                        · omega
                        have f1410 := pair_fact E (i := 4) (j := 4) rfl rfl c1331 c1407
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1410
                        omega
                      by_cases c1411 : 0 < b2
                      swap
                      · omega
                      by_cases c1412 : a0 + a2 < b0 + b2
                      swap
                      · omega
                      by_cases c1413 : b0 < a0 + a2 + a4
                      swap
                      · omega
                      have f1414 := pair_fact E (i := 4) (j := 2) rfl rfl c1330 c1411
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1414
                      omega
                    by_cases c1415 : 0 < b0
                    swap
                    · omega
                    by_cases c1416 : a0 + a2 < 0 + b0
                    swap
                    · -- branch
                      by_cases c1417 : 0 < a4
                      swap
                      · omega
                      by_cases c1418 : 0 < b8
                      swap
                      · -- branch
                        by_cases c1419 : 0 < a4
                        swap
                        · omega
                        by_cases c1420 : 0 < b10
                        swap
                        · omega
                        by_cases c1421 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c1422 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                        swap
                        · -- branch
                          by_cases c1423 : 0 < a8
                          swap
                          · omega
                          by_cases c1424 : 0 < b2
                          swap
                          · omega
                          by_cases c1425 : a0 + a2 + a4 + a6 < b0 + b2
                          swap
                          · -- branch
                            by_cases c1426 : 0 < a0
                            swap
                            · omega
                            by_cases c1427 : 0 < b2
                            swap
                            · omega
                            by_cases c1428 : 0 < b0 + b2
                            swap
                            · omega
                            by_cases c1429 : b0 < 0 + a0
                            swap
                            · -- branch
                              by_cases c1430 : 0 < a2
                              swap
                              · omega
                              by_cases c1431 : 0 < b2
                              swap
                              · omega
                              by_cases c1432 : a0 < b0 + b2
                              swap
                              · omega
                              by_cases c1433 : b0 < a0 + a2
                              swap
                              · omega
                              have f1434 := pair_fact E (i := 2) (j := 2) rfl rfl c1430 c1431
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1434
                              by_cases c1435 : 0 < a8
                              swap
                              · omega
                              by_cases c1436 : 0 < b6
                              swap
                              · omega
                              by_cases c1437 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                              swap
                              · -- branch
                                by_cases c1438 : 0 < a6
                                swap
                                · omega
                                by_cases c1439 : 0 < b10
                                swap
                                · omega
                                by_cases c1440 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c1441 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f1442 := pair_fact E (i := 6) (j := 10) rfl rfl c1438 c1439
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1442
                                omega
                              by_cases c1443 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f1444 := pair_fact E (i := 8) (j := 6) rfl rfl c1435 c1436
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1444
                              omega
                            have f1445 := pair_fact E (i := 0) (j := 2) rfl rfl c1426 c1427
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1445
                            by_cases c1446 : 0 < a2
                            swap
                            · omega
                            by_cases c1447 : 0 < b2
                            swap
                            · omega
                            by_cases c1448 : a0 < b0 + b2
                            swap
                            · -- branch
                              by_cases c1449 : 0 < a2
                              swap
                              · omega
                              by_cases c1450 : 0 < b4
                              swap
                              · omega
                              by_cases c1451 : a0 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c1452 : b0 + b2 < a0 + a2
                              swap
                              · omega
                              have f1453 := pair_fact E (i := 2) (j := 4) rfl rfl c1449 c1450
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1453
                              omega
                            by_cases c1454 : b0 < a0 + a2
                            swap
                            · omega
                            have f1455 := pair_fact E (i := 2) (j := 2) rfl rfl c1446 c1447
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1455
                            omega
                          by_cases c1456 : b0 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f1457 := pair_fact E (i := 8) (j := 2) rfl rfl c1423 c1424
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1457
                          omega
                        have f1458 := pair_fact E (i := 4) (j := 10) rfl rfl c1419 c1420
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1458
                        omega
                      by_cases c1459 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c1460 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                      swap
                      · omega
                      have f1461 := pair_fact E (i := 4) (j := 8) rfl rfl c1417 c1418
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1461
                      omega
                    by_cases c1462 : 0 < a0 + a2 + a4
                    swap
                    · omega
                    have f1463 := pair_fact E (i := 4) (j := 0) rfl rfl c1329 c1415
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1463
                    omega
                  have f1464 := pair_fact E (i := 2) (j := 6) rfl rfl c1325 c1326
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1464
                  by_cases c1465 : 0 < a8
                  swap
                  · omega
                  by_cases c1466 : 0 < b6
                  swap
                  · omega
                  by_cases c1467 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                  swap
                  · -- branch
                    by_cases c1468 : 0 < a6
                    swap
                    · omega
                    by_cases c1469 : 0 < b0
                    swap
                    · omega
                    by_cases c1470 : a0 + a2 + a4 < 0 + b0
                    swap
                    · -- branch
                      by_cases c1471 : 0 < a6
                      swap
                      · omega
                      by_cases c1472 : 0 < b6
                      swap
                      · omega
                      by_cases c1473 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c1474 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f1475 := pair_fact E (i := 6) (j := 6) rfl rfl c1471 c1472
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1475
                      by_cases c1476 : 0 < a6
                      swap
                      · omega
                      by_cases c1477 : 0 < b8
                      swap
                      · -- branch
                        by_cases c1478 : 0 < a6
                        swap
                        · omega
                        by_cases c1479 : 0 < b10
                        swap
                        · omega
                        by_cases c1480 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c1481 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                        swap
                        · -- branch
                          by_cases c1482 : 0 < a0
                          swap
                          · omega
                          by_cases c1483 : 0 < b2
                          swap
                          · -- branch
                            by_cases c1484 : 0 < a0
                            swap
                            · omega
                            by_cases c1485 : 0 < b4
                            swap
                            · omega
                            by_cases c1486 : 0 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c1487 : b0 + b2 < 0 + a0
                            swap
                            · omega
                            have f1488 := pair_fact E (i := 0) (j := 4) rfl rfl c1484 c1485
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1488
                            omega
                          by_cases c1489 : 0 < b0 + b2
                          swap
                          · omega
                          by_cases c1490 : b0 < 0 + a0
                          swap
                          · omega
                          have f1491 := pair_fact E (i := 0) (j := 2) rfl rfl c1482 c1483
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1491
                          omega
                        have f1492 := pair_fact E (i := 6) (j := 10) rfl rfl c1478 c1479
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1492
                        omega
                      by_cases c1493 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c1494 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f1495 := pair_fact E (i := 6) (j := 8) rfl rfl c1476 c1477
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1495
                      omega
                    by_cases c1496 : 0 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f1497 := pair_fact E (i := 6) (j := 0) rfl rfl c1468 c1469
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1497
                    omega
                  by_cases c1498 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                  swap
                  · omega
                  have f1499 := pair_fact E (i := 8) (j := 6) rfl rfl c1465 c1466
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1499
                  omega
                by_cases c1500 : 0 < a0 + a2
                swap
                · omega
                have f1501 := pair_fact E (i := 2) (j := 0) rfl rfl c1322 c1323
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1501
                by_cases c1502 : 0 < a2
                swap
                · omega
                by_cases c1503 : 0 < b6
                swap
                · omega
                by_cases c1504 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c1505 : b0 + b2 + b4 < a0 + a2
                swap
                · -- branch
                  by_cases c1506 : 0 < a8
                  swap
                  · omega
                  by_cases c1507 : 0 < b10
                  swap
                  · omega
                  by_cases c1508 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c1509 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                  swap
                  · -- branch
                    by_cases c1510 : 0 < a8
                    swap
                    · omega
                    by_cases c1511 : 0 < b6
                    swap
                    · omega
                    by_cases c1512 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c1513 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                    swap
                    · omega
                    have f1514 := pair_fact E (i := 8) (j := 6) rfl rfl c1510 c1511
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1514
                    by_cases c1515 : 0 < a10
                    swap
                    · omega
                    by_cases c1516 : 0 < b0
                    swap
                    · omega
                    by_cases c1517 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                    swap
                    · -- branch
                      by_cases c1518 : 0 < a10
                      swap
                      · omega
                      by_cases c1519 : 0 < b6
                      swap
                      · omega
                      by_cases c1520 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                      swap
                      · -- branch
                        by_cases c1521 : 0 < a6
                        swap
                        · omega
                        by_cases c1522 : 0 < b0
                        swap
                        · omega
                        by_cases c1523 : a0 + a2 + a4 < 0 + b0
                        swap
                        · -- branch
                          by_cases c1524 : 0 < a6
                          swap
                          · omega
                          by_cases c1525 : 0 < b6
                          swap
                          · omega
                          by_cases c1526 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c1527 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f1528 := pair_fact E (i := 6) (j := 6) rfl rfl c1524 c1525
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1528
                          omega
                        by_cases c1529 : 0 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f1530 := pair_fact E (i := 6) (j := 0) rfl rfl c1521 c1522
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1530
                        omega
                      by_cases c1531 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f1532 := pair_fact E (i := 10) (j := 6) rfl rfl c1518 c1519
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1532
                      omega
                    by_cases c1533 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                    swap
                    · omega
                    have f1534 := pair_fact E (i := 10) (j := 0) rfl rfl c1515 c1516
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1534
                    omega
                  have f1535 := pair_fact E (i := 8) (j := 10) rfl rfl c1506 c1507
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1535
                  omega
                have f1536 := pair_fact E (i := 2) (j := 6) rfl rfl c1502 c1503
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1536
                omega
              have f1537 := pair_fact E (i := 2) (j := 10) rfl rfl c1318 c1319
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1537
              omega
            by_cases c1538 : a0 < b0 + b2 + b4 + b6 + b8
            swap
            · omega
            by_cases c1539 : b0 + b2 + b4 + b6 < a0 + a2
            swap
            · omega
            have f1540 := pair_fact E (i := 2) (j := 8) rfl rfl c1181 c1317
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1540
            omega
          have f1541 := pair_fact E (i := 0) (j := 10) rfl rfl c1102 c1103
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1541
          omega
        have f1542 := pair_fact E (i := 0) (j := 6) rfl rfl c1098 c1099
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1542
        by_cases c1543 : 0 < a2
        swap
        · -- branch
          by_cases c1544 : 0 < a4
          swap
          · omega
          by_cases c1545 : 0 < b6
          swap
          · omega
          by_cases c1546 : a0 + a2 < b0 + b2 + b4 + b6
          swap
          · omega
          by_cases c1547 : b0 + b2 + b4 < a0 + a2 + a4
          swap
          · omega
          have f1548 := pair_fact E (i := 4) (j := 6) rfl rfl c1544 c1545
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1548
          omega
        by_cases c1549 : 0 < b6
        swap
        · omega
        by_cases c1550 : a0 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c1551 : b0 + b2 + b4 < a0 + a2
        swap
        · omega
        have f1552 := pair_fact E (i := 2) (j := 6) rfl rfl c1543 c1549
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1552
        omega
      by_cases c1553 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
      swap
      · omega
      by_cases c1554 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
      swap
      · omega
      have f1555 := pair_fact E (i := 8) (j := 8) rfl rfl c1096 c1097
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1555
      omega
    by_cases c1556 : 0 < a0 + a2 + a4 + a6 + a8
    swap
    · omega
    have f1557 := pair_fact E (i := 8) (j := 0) rfl rfl c1093 c1094
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1557
    omega
  by_cases c1558 : 0 < b0 + b2 + b4 + b6 + b8
  swap
  · omega
  by_cases c1559 : b0 + b2 + b4 + b6 < 0 + a0
  swap
  · -- branch
    by_cases c1560 : 0 < a0
    swap
    · omega
    by_cases c1561 : 0 < b10
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
              by_cases c1566 : 0 < a2
              swap
              · -- branch
                by_cases c1567 : 0 < a2
                swap
                · -- branch
                  by_cases c1568 : 0 < a6
                  swap
                  · omega
                  by_cases c1569 : 0 < b10
                  swap
                  · -- branch
                    by_cases c1570 : 0 < a0
                    swap
                    · omega
                    by_cases c1571 : 0 < b2
                    swap
                    · omega
                    by_cases c1572 : 0 < b0 + b2
                    swap
                    · omega
                    by_cases c1573 : b0 < 0 + a0
                    swap
                    · -- branch
                      by_cases c1574 : 0 < a0
                      swap
                      · omega
                      by_cases c1575 : 0 < b4
                      swap
                      · -- branch
                        by_cases c1576 : 0 < a0
                        swap
                        · omega
                        by_cases c1577 : 0 < b6
                        swap
                        · omega
                        by_cases c1578 : 0 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c1579 : b0 + b2 + b4 < 0 + a0
                        swap
                        · -- branch
                          by_cases c1580 : 0 < a4
                          swap
                          · omega
                          by_cases c1581 : 0 < b4
                          swap
                          · -- branch
                            by_cases c1582 : 0 < a4
                            swap
                            · omega
                            by_cases c1583 : 0 < b6
                            swap
                            · omega
                            by_cases c1584 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c1585 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c1586 : 0 < a4
                              swap
                              · omega
                              by_cases c1587 : 0 < b8
                              swap
                              · omega
                              by_cases c1588 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c1589 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c1590 : 0 < a4
                                swap
                                · omega
                                by_cases c1591 : 0 < b10
                                swap
                                · -- branch
                                  by_cases c1592 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1593 : 0 < b4
                                  swap
                                  · -- branch
                                    by_cases c1594 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c1595 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c1596 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c1597 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f1598 := pair_fact E (i := 6) (j := 6) rfl rfl c1594 c1595
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1598
                                    by_cases c1599 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1600 : 0 < b0
                                    swap
                                    · omega
                                    by_cases c1601 : a0 + a2 < 0 + b0
                                    swap
                                    · -- branch
                                      by_cases c1602 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c1603 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c1604 : a0 + a2 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c1605 : b0 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f1606 := pair_fact E (i := 4) (j := 2) rfl rfl c1602 c1603
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1606
                                      by_cases c1607 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c1608 : 0 < b0
                                      swap
                                      · omega
                                      by_cases c1609 : a0 + a2 + a4 < 0 + b0
                                      swap
                                      · -- branch
                                        by_cases c1610 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c1611 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c1612 : a0 + a2 + a4 < b0 + b2
                                        swap
                                        · -- branch
                                          by_cases c1613 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c1614 : 0 < b8
                                          swap
                                          · omega
                                          by_cases c1615 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                          swap
                                          · omega
                                          by_cases c1616 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                          swap
                                          · -- branch
                                            by_cases c1617 : 0 < a8
                                            swap
                                            · -- branch
                                              by_cases c1618 : 0 < a10
                                              swap
                                              · omega
                                              by_cases c1619 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c1620 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c1621 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                              swap
                                              · omega
                                              have f1622 := pair_fact E (i := 10) (j := 6) rfl rfl c1618 c1619
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1622
                                              omega
                                            by_cases c1623 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c1624 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c1625 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f1626 := pair_fact E (i := 8) (j := 6) rfl rfl c1617 c1623
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1626
                                            omega
                                          have f1627 := pair_fact E (i := 6) (j := 8) rfl rfl c1613 c1614
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1627
                                          omega
                                        by_cases c1628 : b0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f1629 := pair_fact E (i := 6) (j := 2) rfl rfl c1610 c1611
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1629
                                        omega
                                      by_cases c1630 : 0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f1631 := pair_fact E (i := 6) (j := 0) rfl rfl c1607 c1608
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1631
                                      omega
                                    by_cases c1632 : 0 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f1633 := pair_fact E (i := 4) (j := 0) rfl rfl c1599 c1600
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1633
                                    omega
                                  by_cases c1634 : a0 + a2 + a4 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c1635 : b0 + b2 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f1636 := pair_fact E (i := 6) (j := 4) rfl rfl c1592 c1593
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1636
                                  omega
                                by_cases c1637 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c1638 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                swap
                                · omega
                                have f1639 := pair_fact E (i := 4) (j := 10) rfl rfl c1590 c1591
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1639
                                omega
                              have f1640 := pair_fact E (i := 4) (j := 8) rfl rfl c1586 c1587
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1640
                              omega
                            have f1641 := pair_fact E (i := 4) (j := 6) rfl rfl c1582 c1583
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1641
                            omega
                          by_cases c1642 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1643 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f1644 := pair_fact E (i := 4) (j := 4) rfl rfl c1580 c1581
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1644
                          omega
                        have f1645 := pair_fact E (i := 0) (j := 6) rfl rfl c1576 c1577
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1645
                        omega
                      by_cases c1646 : 0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c1647 : b0 + b2 < 0 + a0
                      swap
                      · -- branch
                        by_cases c1648 : 0 < a6
                        swap
                        · omega
                        by_cases c1649 : 0 < b2
                        swap
                        · omega
                        by_cases c1650 : a0 + a2 + a4 < b0 + b2
                        swap
                        · omega
                        by_cases c1651 : b0 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f1652 := pair_fact E (i := 6) (j := 2) rfl rfl c1648 c1649
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1652
                        by_cases c1653 : 0 < a6
                        swap
                        · omega
                        by_cases c1654 : 0 < b0
                        swap
                        · omega
                        by_cases c1655 : a0 + a2 + a4 < 0 + b0
                        swap
                        · -- branch
                          by_cases c1656 : 0 < a6
                          swap
                          · omega
                          by_cases c1657 : 0 < b4
                          swap
                          · omega
                          by_cases c1658 : a0 + a2 + a4 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1659 : b0 + b2 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f1660 := pair_fact E (i := 6) (j := 4) rfl rfl c1656 c1657
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1660
                          by_cases c1661 : 0 < a6
                          swap
                          · omega
                          by_cases c1662 : 0 < b8
                          swap
                          · omega
                          by_cases c1663 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c1664 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                          swap
                          · -- branch
                            by_cases c1665 : 0 < a0
                            swap
                            · omega
                            by_cases c1666 : 0 < b6
                            swap
                            · omega
                            by_cases c1667 : 0 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c1668 : b0 + b2 + b4 < 0 + a0
                            swap
                            · -- branch
                              by_cases c1669 : 0 < a4
                              swap
                              · -- branch
                                by_cases c1670 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c1671 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c1672 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c1673 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c1674 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c1675 : 0 < a8
                                          swap
                                          · -- branch
                                            by_cases c1676 : 0 < a10
                                            swap
                                            · omega
                                            by_cases c1677 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c1678 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c1679 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                            swap
                                            · omega
                                            have f1680 := pair_fact E (i := 10) (j := 6) rfl rfl c1676 c1677
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1680
                                            omega
                                          by_cases c1681 : 0 < b6
                                          swap
                                          · omega
                                          by_cases c1682 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                          swap
                                          · omega
                                          by_cases c1683 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f1684 := pair_fact E (i := 8) (j := 6) rfl rfl c1675 c1681
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1684
                                          omega
                                        by_cases c1685 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c1686 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c1687 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f1688 := pair_fact E (i := 4) (j := 10) rfl rfl c1674 c1685
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1688
                                        omega
                                      by_cases c1689 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c1690 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c1691 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f1692 := pair_fact E (i := 4) (j := 8) rfl rfl c1673 c1689
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1692
                                      omega
                                    by_cases c1693 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c1694 : a0 + a2 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c1695 : b0 + b2 + b4 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f1696 := pair_fact E (i := 4) (j := 6) rfl rfl c1672 c1693
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1696
                                    omega
                                  by_cases c1697 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c1698 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c1699 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f1700 := pair_fact E (i := 4) (j := 4) rfl rfl c1671 c1697
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1700
                                  omega
                                by_cases c1701 : 0 < b2
                                swap
                                · omega
                                by_cases c1702 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c1703 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f1704 := pair_fact E (i := 4) (j := 2) rfl rfl c1670 c1701
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1704
                                omega
                              by_cases c1705 : 0 < b0
                              swap
                              · omega
                              by_cases c1706 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c1707 : 0 < a4
                                swap
                                · omega
                                by_cases c1708 : 0 < b2
                                swap
                                · omega
                                by_cases c1709 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c1710 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f1711 := pair_fact E (i := 4) (j := 2) rfl rfl c1707 c1708
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1711
                                by_cases c1712 : 0 < a4
                                swap
                                · omega
                                by_cases c1713 : 0 < b4
                                swap
                                · omega
                                by_cases c1714 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c1715 : b0 + b2 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c1716 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c1717 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c1718 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c1719 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c1720 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1721 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c1722 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c1723 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c1724 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c1725 : 0 < b10
                                      swap
                                      · -- branch
                                        by_cases c1726 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c1727 : 0 < b6
                                        swap
                                        · omega
                                        by_cases c1728 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                        swap
                                        · omega
                                        by_cases c1729 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                        swap
                                        · -- branch
                                          by_cases c1730 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c1731 : 0 < b6
                                          swap
                                          · omega
                                          by_cases c1732 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                          swap
                                          · omega
                                          by_cases c1733 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f1734 := pair_fact E (i := 8) (j := 6) rfl rfl c1730 c1731
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1734
                                          omega
                                        have f1735 := pair_fact E (i := 6) (j := 6) rfl rfl c1726 c1727
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1735
                                        omega
                                      by_cases c1736 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c1737 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f1738 := pair_fact E (i := 4) (j := 10) rfl rfl c1724 c1725
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1738
                                      omega
                                    have f1739 := pair_fact E (i := 4) (j := 8) rfl rfl c1720 c1721
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1739
                                    omega
                                  have f1740 := pair_fact E (i := 4) (j := 6) rfl rfl c1716 c1717
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1740
                                  omega
                                have f1741 := pair_fact E (i := 4) (j := 4) rfl rfl c1712 c1713
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1741
                                omega
                              by_cases c1742 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f1743 := pair_fact E (i := 4) (j := 0) rfl rfl c1669 c1705
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1743
                              omega
                            have f1744 := pair_fact E (i := 0) (j := 6) rfl rfl c1665 c1666
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1744
                            omega
                          have f1745 := pair_fact E (i := 6) (j := 8) rfl rfl c1661 c1662
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1745
                          omega
                        by_cases c1746 : 0 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f1747 := pair_fact E (i := 6) (j := 0) rfl rfl c1653 c1654
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1747
                        omega
                      have f1748 := pair_fact E (i := 0) (j := 4) rfl rfl c1574 c1575
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1748
                      omega
                    have f1749 := pair_fact E (i := 0) (j := 2) rfl rfl c1570 c1571
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1749
                    by_cases c1750 : 0 < a6
                    swap
                    · omega
                    by_cases c1751 : 0 < b0
                    swap
                    · omega
                    by_cases c1752 : a0 + a2 + a4 < 0 + b0
                    swap
                    · -- branch
                      by_cases c1753 : 0 < a6
                      swap
                      · omega
                      by_cases c1754 : 0 < b2
                      swap
                      · omega
                      by_cases c1755 : a0 + a2 + a4 < b0 + b2
                      swap
                      · -- branch
                        by_cases c1756 : 0 < a6
                        swap
                        · omega
                        by_cases c1757 : 0 < b6
                        swap
                        · omega
                        by_cases c1758 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c1759 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f1760 := pair_fact E (i := 6) (j := 6) rfl rfl c1756 c1757
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1760
                        omega
                      by_cases c1761 : b0 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f1762 := pair_fact E (i := 6) (j := 2) rfl rfl c1753 c1754
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1762
                      omega
                    by_cases c1763 : 0 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f1764 := pair_fact E (i := 6) (j := 0) rfl rfl c1750 c1751
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1764
                    omega
                  by_cases c1765 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c1766 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                  swap
                  · omega
                  have f1767 := pair_fact E (i := 6) (j := 10) rfl rfl c1568 c1569
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1767
                  omega
                by_cases c1768 : 0 < b10
                swap
                · omega
                by_cases c1769 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                swap
                · omega
                by_cases c1770 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                swap
                · omega
                have f1771 := pair_fact E (i := 2) (j := 10) rfl rfl c1567 c1768
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1771
                omega
              by_cases c1772 : 0 < b6
              swap
              · omega
              by_cases c1773 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c1774 : b0 + b2 + b4 < a0 + a2
              swap
              · omega
              have f1775 := pair_fact E (i := 2) (j := 6) rfl rfl c1566 c1772
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1775
              omega
            by_cases c1776 : 0 < b4
            swap
            · omega
            by_cases c1777 : a0 < b0 + b2 + b4
            swap
            · omega
            by_cases c1778 : b0 + b2 < a0 + a2
            swap
            · omega
            have f1779 := pair_fact E (i := 2) (j := 4) rfl rfl c1565 c1776
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1779
            omega
          by_cases c1780 : 0 < b2
          swap
          · omega
          by_cases c1781 : a0 < b0 + b2
          swap
          · omega
          by_cases c1782 : b0 < a0 + a2
          swap
          · omega
          have f1783 := pair_fact E (i := 2) (j := 2) rfl rfl c1564 c1780
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1783
          omega
        by_cases c1784 : 0 < b0
        swap
        · omega
        by_cases c1785 : a0 < 0 + b0
        swap
        · omega
        by_cases c1786 : 0 < a0 + a2
        swap
        · omega
        have f1787 := pair_fact E (i := 2) (j := 0) rfl rfl c1563 c1784
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1787
        omega
      by_cases c1788 : 0 < b8
      swap
      · omega
      by_cases c1789 : a0 < b0 + b2 + b4 + b6 + b8
      swap
      · omega
      by_cases c1790 : b0 + b2 + b4 + b6 < a0 + a2
      swap
      · -- branch
        by_cases c1791 : 0 < a2
        swap
        · omega
        by_cases c1792 : 0 < b10
        swap
        · -- branch
          by_cases c1793 : 0 < a2
          swap
          · omega
          by_cases c1794 : 0 < b0
          swap
          · omega
          by_cases c1795 : a0 < 0 + b0
          swap
          · -- branch
            by_cases c1796 : 0 < a0
            swap
            · omega
            by_cases c1797 : 0 < b6
            swap
            · omega
            by_cases c1798 : 0 < b0 + b2 + b4 + b6
            swap
            · omega
            by_cases c1799 : b0 + b2 + b4 < 0 + a0
            swap
            · -- branch
              by_cases c1800 : 0 < a2
              swap
              · omega
              by_cases c1801 : 0 < b6
              swap
              · omega
              by_cases c1802 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c1803 : b0 + b2 + b4 < a0 + a2
              swap
              · -- branch
                by_cases c1804 : 0 < a4
                swap
                · -- branch
                  by_cases c1805 : 0 < a4
                  swap
                  · -- branch
                    by_cases c1806 : 0 < a4
                    swap
                    · -- branch
                      by_cases c1807 : 0 < a4
                      swap
                      · -- branch
                        by_cases c1808 : 0 < a4
                        swap
                        · -- branch
                          by_cases c1809 : 0 < a4
                          swap
                          · -- branch
                            by_cases c1810 : 0 < a6
                            swap
                            · omega
                            by_cases c1811 : 0 < b0
                            swap
                            · omega
                            by_cases c1812 : a0 + a2 + a4 < 0 + b0
                            swap
                            · -- branch
                              by_cases c1813 : 0 < a6
                              swap
                              · omega
                              by_cases c1814 : 0 < b10
                              swap
                              · -- branch
                                by_cases c1815 : 0 < a0
                                swap
                                · omega
                                by_cases c1816 : 0 < b4
                                swap
                                · omega
                                by_cases c1817 : 0 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c1818 : b0 + b2 < 0 + a0
                                swap
                                · -- branch
                                  by_cases c1819 : 0 < a2
                                  swap
                                  · omega
                                  by_cases c1820 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c1821 : a0 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c1822 : b0 + b2 < a0 + a2
                                  swap
                                  · -- branch
                                    by_cases c1823 : 0 < a2
                                    swap
                                    · omega
                                    by_cases c1824 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c1825 : a0 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c1826 : b0 < a0 + a2
                                    swap
                                    · omega
                                    have f1827 := pair_fact E (i := 2) (j := 2) rfl rfl c1823 c1824
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1827
                                    by_cases c1828 : 0 < a0
                                    swap
                                    · omega
                                    by_cases c1829 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c1830 : 0 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c1831 : b0 < 0 + a0
                                    swap
                                    · -- branch
                                      by_cases c1832 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c1833 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c1834 : a0 + a2 + a4 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c1835 : b0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f1836 := pair_fact E (i := 6) (j := 2) rfl rfl c1832 c1833
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1836
                                      by_cases c1837 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c1838 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c1839 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c1840 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f1841 := pair_fact E (i := 6) (j := 4) rfl rfl c1837 c1838
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1841
                                      omega
                                    have f1842 := pair_fact E (i := 0) (j := 2) rfl rfl c1828 c1829
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1842
                                    omega
                                  have f1843 := pair_fact E (i := 2) (j := 4) rfl rfl c1819 c1820
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1843
                                  by_cases c1844 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c1845 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c1846 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c1847 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                  swap
                                  · -- branch
                                    by_cases c1848 : 0 < a0
                                    swap
                                    · omega
                                    by_cases c1849 : 0 < b2
                                    swap
                                    · -- branch
                                      by_cases c1850 : 0 < a2
                                      swap
                                      · omega
                                      by_cases c1851 : 0 < b2
                                      swap
                                      · -- branch
                                        by_cases c1852 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c1853 : 0 < b2
                                        swap
                                        · -- branch
                                          by_cases c1854 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c1855 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c1856 : a0 + a2 + a4 < b0 + b2 + b4
                                          swap
                                          · -- branch
                                            by_cases c1857 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c1858 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c1859 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c1860 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f1861 := pair_fact E (i := 6) (j := 6) rfl rfl c1857 c1858
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1861
                                            by_cases c1862 : 0 < a8
                                            swap
                                            · -- branch
                                              by_cases c1863 : 0 < a10
                                              swap
                                              · omega
                                              by_cases c1864 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c1865 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c1866 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                              swap
                                              · omega
                                              have f1867 := pair_fact E (i := 10) (j := 6) rfl rfl c1863 c1864
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1867
                                              omega
                                            by_cases c1868 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c1869 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c1870 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f1871 := pair_fact E (i := 8) (j := 6) rfl rfl c1862 c1868
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1871
                                            omega
                                          by_cases c1872 : b0 + b2 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f1873 := pair_fact E (i := 6) (j := 4) rfl rfl c1854 c1855
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1873
                                          omega
                                        by_cases c1874 : a0 + a2 + a4 < b0 + b2
                                        swap
                                        · omega
                                        by_cases c1875 : b0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f1876 := pair_fact E (i := 6) (j := 2) rfl rfl c1852 c1853
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1876
                                        omega
                                      by_cases c1877 : a0 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c1878 : b0 < a0 + a2
                                      swap
                                      · omega
                                      have f1879 := pair_fact E (i := 2) (j := 2) rfl rfl c1850 c1851
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1879
                                      omega
                                    by_cases c1880 : 0 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c1881 : b0 < 0 + a0
                                    swap
                                    · -- branch
                                      by_cases c1882 : 0 < a2
                                      swap
                                      · omega
                                      by_cases c1883 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c1884 : a0 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c1885 : b0 < a0 + a2
                                      swap
                                      · omega
                                      have f1886 := pair_fact E (i := 2) (j := 2) rfl rfl c1882 c1883
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1886
                                      by_cases c1887 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c1888 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c1889 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c1890 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f1891 := pair_fact E (i := 6) (j := 4) rfl rfl c1887 c1888
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1891
                                      omega
                                    have f1892 := pair_fact E (i := 0) (j := 2) rfl rfl c1848 c1849
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1892
                                    omega
                                  have f1893 := pair_fact E (i := 6) (j := 8) rfl rfl c1844 c1845
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1893
                                  omega
                                have f1894 := pair_fact E (i := 0) (j := 4) rfl rfl c1815 c1816
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1894
                                by_cases c1895 : 0 < a2
                                swap
                                · omega
                                by_cases c1896 : 0 < b4
                                swap
                                · omega
                                by_cases c1897 : a0 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c1898 : b0 + b2 < a0 + a2
                                swap
                                · omega
                                have f1899 := pair_fact E (i := 2) (j := 4) rfl rfl c1895 c1896
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1899
                                omega
                              by_cases c1900 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c1901 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f1902 := pair_fact E (i := 6) (j := 10) rfl rfl c1813 c1814
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1902
                              omega
                            by_cases c1903 : 0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f1904 := pair_fact E (i := 6) (j := 0) rfl rfl c1810 c1811
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1904
                            omega
                          by_cases c1905 : 0 < b10
                          swap
                          · omega
                          by_cases c1906 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c1907 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                          swap
                          · omega
                          have f1908 := pair_fact E (i := 4) (j := 10) rfl rfl c1809 c1905
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1908
                          omega
                        by_cases c1909 : 0 < b8
                        swap
                        · omega
                        by_cases c1910 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1911 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                        swap
                        · omega
                        have f1912 := pair_fact E (i := 4) (j := 8) rfl rfl c1808 c1909
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1912
                        omega
                      by_cases c1913 : 0 < b6
                      swap
                      · omega
                      by_cases c1914 : a0 + a2 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c1915 : b0 + b2 + b4 < a0 + a2 + a4
                      swap
                      · omega
                      have f1916 := pair_fact E (i := 4) (j := 6) rfl rfl c1807 c1913
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1916
                      omega
                    by_cases c1917 : 0 < b4
                    swap
                    · omega
                    by_cases c1918 : a0 + a2 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c1919 : b0 + b2 < a0 + a2 + a4
                    swap
                    · omega
                    have f1920 := pair_fact E (i := 4) (j := 4) rfl rfl c1806 c1917
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1920
                    omega
                  by_cases c1921 : 0 < b2
                  swap
                  · omega
                  by_cases c1922 : a0 + a2 < b0 + b2
                  swap
                  · omega
                  by_cases c1923 : b0 < a0 + a2 + a4
                  swap
                  · omega
                  have f1924 := pair_fact E (i := 4) (j := 2) rfl rfl c1805 c1921
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1924
                  omega
                by_cases c1925 : 0 < b0
                swap
                · omega
                by_cases c1926 : a0 + a2 < 0 + b0
                swap
                · -- branch
                  by_cases c1927 : 0 < a4
                  swap
                  · omega
                  by_cases c1928 : 0 < b8
                  swap
                  · omega
                  by_cases c1929 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c1930 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                  swap
                  · -- branch
                    by_cases c1931 : 0 < a4
                    swap
                    · omega
                    by_cases c1932 : 0 < b10
                    swap
                    · -- branch
                      by_cases c1933 : 0 < a0
                      swap
                      · omega
                      by_cases c1934 : 0 < b2
                      swap
                      · omega
                      by_cases c1935 : 0 < b0 + b2
                      swap
                      · omega
                      by_cases c1936 : b0 < 0 + a0
                      swap
                      · -- branch
                        by_cases c1937 : 0 < a2
                        swap
                        · omega
                        by_cases c1938 : 0 < b2
                        swap
                        · omega
                        by_cases c1939 : a0 < b0 + b2
                        swap
                        · omega
                        by_cases c1940 : b0 < a0 + a2
                        swap
                        · omega
                        have f1941 := pair_fact E (i := 2) (j := 2) rfl rfl c1937 c1938
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1941
                        by_cases c1942 : 0 < a0
                        swap
                        · omega
                        by_cases c1943 : 0 < b4
                        swap
                        · -- branch
                          by_cases c1944 : 0 < a2
                          swap
                          · omega
                          by_cases c1945 : 0 < b4
                          swap
                          · -- branch
                            by_cases c1946 : 0 < a4
                            swap
                            · omega
                            by_cases c1947 : 0 < b2
                            swap
                            · omega
                            by_cases c1948 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c1949 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f1950 := pair_fact E (i := 4) (j := 2) rfl rfl c1946 c1947
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1950
                            by_cases c1951 : 0 < a4
                            swap
                            · omega
                            by_cases c1952 : 0 < b6
                            swap
                            · omega
                            by_cases c1953 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c1954 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · omega
                            have f1955 := pair_fact E (i := 4) (j := 6) rfl rfl c1951 c1952
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1955
                            omega
                          by_cases c1956 : a0 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1957 : b0 + b2 < a0 + a2
                          swap
                          · omega
                          have f1958 := pair_fact E (i := 2) (j := 4) rfl rfl c1944 c1945
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1958
                          omega
                        by_cases c1959 : 0 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c1960 : b0 + b2 < 0 + a0
                        swap
                        · -- branch
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
                            by_cases c1965 : 0 < a4
                            swap
                            · omega
                            by_cases c1966 : 0 < b2
                            swap
                            · omega
                            by_cases c1967 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c1968 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f1969 := pair_fact E (i := 4) (j := 2) rfl rfl c1965 c1966
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1969
                            by_cases c1970 : 0 < a4
                            swap
                            · omega
                            by_cases c1971 : 0 < b4
                            swap
                            · omega
                            by_cases c1972 : a0 + a2 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c1973 : b0 + b2 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c1974 : 0 < a6
                              swap
                              · omega
                              by_cases c1975 : 0 < b4
                              swap
                              · omega
                              by_cases c1976 : a0 + a2 + a4 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c1977 : b0 + b2 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f1978 := pair_fact E (i := 6) (j := 4) rfl rfl c1974 c1975
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1978
                              omega
                            have f1979 := pair_fact E (i := 4) (j := 4) rfl rfl c1970 c1971
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1979
                            omega
                          have f1980 := pair_fact E (i := 2) (j := 4) rfl rfl c1961 c1962
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1980
                          by_cases c1981 : 0 < a4
                          swap
                          · omega
                          by_cases c1982 : 0 < b2
                          swap
                          · omega
                          by_cases c1983 : a0 + a2 < b0 + b2
                          swap
                          · -- branch
                            by_cases c1984 : 0 < a4
                            swap
                            · omega
                            by_cases c1985 : 0 < b4
                            swap
                            · omega
                            by_cases c1986 : a0 + a2 < b0 + b2 + b4
                            swap
                            · -- branch
                              by_cases c1987 : 0 < a4
                              swap
                              · omega
                              by_cases c1988 : 0 < b6
                              swap
                              · omega
                              by_cases c1989 : a0 + a2 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c1990 : b0 + b2 + b4 < a0 + a2 + a4
                              swap
                              · omega
                              have f1991 := pair_fact E (i := 4) (j := 6) rfl rfl c1987 c1988
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1991
                              omega
                            by_cases c1992 : b0 + b2 < a0 + a2 + a4
                            swap
                            · omega
                            have f1993 := pair_fact E (i := 4) (j := 4) rfl rfl c1984 c1985
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1993
                            omega
                          by_cases c1994 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f1995 := pair_fact E (i := 4) (j := 2) rfl rfl c1981 c1982
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1995
                          omega
                        have f1996 := pair_fact E (i := 0) (j := 4) rfl rfl c1942 c1943
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1996
                        omega
                      have f1997 := pair_fact E (i := 0) (j := 2) rfl rfl c1933 c1934
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1997
                      by_cases c1998 : 0 < a2
                      swap
                      · omega
                      by_cases c1999 : 0 < b2
                      swap
                      · omega
                      by_cases c2000 : a0 < b0 + b2
                      swap
                      · -- branch
                        by_cases c2001 : 0 < a2
                        swap
                        · omega
                        by_cases c2002 : 0 < b4
                        swap
                        · omega
                        by_cases c2003 : a0 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c2004 : b0 + b2 < a0 + a2
                        swap
                        · omega
                        have f2005 := pair_fact E (i := 2) (j := 4) rfl rfl c2001 c2002
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2005
                        omega
                      by_cases c2006 : b0 < a0 + a2
                      swap
                      · omega
                      have f2007 := pair_fact E (i := 2) (j := 2) rfl rfl c1998 c1999
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2007
                      omega
                    by_cases c2008 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c2009 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                    swap
                    · omega
                    have f2010 := pair_fact E (i := 4) (j := 10) rfl rfl c1931 c1932
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2010
                    omega
                  have f2011 := pair_fact E (i := 4) (j := 8) rfl rfl c1927 c1928
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2011
                  omega
                by_cases c2012 : 0 < a0 + a2 + a4
                swap
                · omega
                have f2013 := pair_fact E (i := 4) (j := 0) rfl rfl c1804 c1925
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2013
                omega
              have f2014 := pair_fact E (i := 2) (j := 6) rfl rfl c1800 c1801
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2014
              by_cases c2015 : 0 < a0
              swap
              · omega
              by_cases c2016 : 0 < b2
              swap
              · -- branch
                by_cases c2017 : 0 < a2
                swap
                · omega
                by_cases c2018 : 0 < b2
                swap
                · -- branch
                  by_cases c2019 : 0 < a0
                  swap
                  · omega
                  by_cases c2020 : 0 < b4
                  swap
                  · -- branch
                    by_cases c2021 : 0 < a2
                    swap
                    · omega
                    by_cases c2022 : 0 < b4
                    swap
                    · -- branch
                      by_cases c2023 : 0 < a4
                      swap
                      · omega
                      by_cases c2024 : 0 < b0
                      swap
                      · omega
                      by_cases c2025 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c2026 : 0 < a4
                        swap
                        · omega
                        by_cases c2027 : 0 < b2
                        swap
                        · -- branch
                          by_cases c2028 : 0 < a4
                          swap
                          · omega
                          by_cases c2029 : 0 < b4
                          swap
                          · -- branch
                            by_cases c2030 : 0 < a4
                            swap
                            · omega
                            by_cases c2031 : 0 < b6
                            swap
                            · omega
                            by_cases c2032 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c2033 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · omega
                            have f2034 := pair_fact E (i := 4) (j := 6) rfl rfl c2030 c2031
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2034
                            by_cases c2035 : 0 < a4
                            swap
                            · omega
                            by_cases c2036 : 0 < b8
                            swap
                            · omega
                            by_cases c2037 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c2038 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c2039 : 0 < a4
                              swap
                              · omega
                              by_cases c2040 : 0 < b10
                              swap
                              · -- branch
                                by_cases c2041 : 0 < a6
                                swap
                                · -- branch
                                  by_cases c2042 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c2043 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c2044 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c2045 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f2046 := pair_fact E (i := 8) (j := 6) rfl rfl c2042 c2043
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2046
                                  omega
                                by_cases c2047 : 0 < b0
                                swap
                                · omega
                                by_cases c2048 : a0 + a2 + a4 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c2049 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c2050 : 0 < b2
                                  swap
                                  · -- branch
                                    by_cases c2051 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c2052 : 0 < b4
                                    swap
                                    · -- branch
                                      by_cases c2053 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c2054 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c2055 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c2056 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                      swap
                                      · -- branch
                                        by_cases c2057 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c2058 : 0 < b6
                                        swap
                                        · omega
                                        by_cases c2059 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                        swap
                                        · omega
                                        by_cases c2060 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f2061 := pair_fact E (i := 6) (j := 6) rfl rfl c2057 c2058
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2061
                                        by_cases c2062 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c2063 : 0 < b10
                                        swap
                                        · -- branch
                                          by_cases c2064 : 0 < a8
                                          swap
                                          · -- branch
                                            by_cases c2065 : 0 < a10
                                            swap
                                            · omega
                                            by_cases c2066 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c2067 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c2068 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                            swap
                                            · omega
                                            have f2069 := pair_fact E (i := 10) (j := 6) rfl rfl c2065 c2066
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2069
                                            omega
                                          by_cases c2070 : 0 < b6
                                          swap
                                          · omega
                                          by_cases c2071 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                          swap
                                          · omega
                                          by_cases c2072 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f2073 := pair_fact E (i := 8) (j := 6) rfl rfl c2064 c2070
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2073
                                          omega
                                        by_cases c2074 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c2075 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f2076 := pair_fact E (i := 6) (j := 10) rfl rfl c2062 c2063
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2076
                                        omega
                                      have f2077 := pair_fact E (i := 6) (j := 8) rfl rfl c2053 c2054
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2077
                                      omega
                                    by_cases c2078 : a0 + a2 + a4 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c2079 : b0 + b2 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f2080 := pair_fact E (i := 6) (j := 4) rfl rfl c2051 c2052
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2080
                                    omega
                                  by_cases c2081 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c2082 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f2083 := pair_fact E (i := 6) (j := 2) rfl rfl c2049 c2050
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2083
                                  omega
                                by_cases c2084 : 0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f2085 := pair_fact E (i := 6) (j := 0) rfl rfl c2041 c2047
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2085
                                omega
                              by_cases c2086 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c2087 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                              swap
                              · omega
                              have f2088 := pair_fact E (i := 4) (j := 10) rfl rfl c2039 c2040
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2088
                              omega
                            have f2089 := pair_fact E (i := 4) (j := 8) rfl rfl c2035 c2036
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2089
                            omega
                          by_cases c2090 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c2091 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f2092 := pair_fact E (i := 4) (j := 4) rfl rfl c2028 c2029
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2092
                          omega
                        by_cases c2093 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c2094 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f2095 := pair_fact E (i := 4) (j := 2) rfl rfl c2026 c2027
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2095
                        omega
                      by_cases c2096 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f2097 := pair_fact E (i := 4) (j := 0) rfl rfl c2023 c2024
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2097
                      omega
                    by_cases c2098 : a0 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c2099 : b0 + b2 < a0 + a2
                    swap
                    · omega
                    have f2100 := pair_fact E (i := 2) (j := 4) rfl rfl c2021 c2022
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2100
                    omega
                  by_cases c2101 : 0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c2102 : b0 + b2 < 0 + a0
                  swap
                  · -- branch
                    by_cases c2103 : 0 < a2
                    swap
                    · omega
                    by_cases c2104 : 0 < b4
                    swap
                    · omega
                    by_cases c2105 : a0 < b0 + b2 + b4
                    swap
                    · omega
                    by_cases c2106 : b0 + b2 < a0 + a2
                    swap
                    · omega
                    have f2107 := pair_fact E (i := 2) (j := 4) rfl rfl c2103 c2104
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2107
                    by_cases c2108 : 0 < a4
                    swap
                    · omega
                    by_cases c2109 : 0 < b0
                    swap
                    · omega
                    by_cases c2110 : a0 + a2 < 0 + b0
                    swap
                    · -- branch
                      by_cases c2111 : 0 < a4
                      swap
                      · omega
                      by_cases c2112 : 0 < b2
                      swap
                      · -- branch
                        by_cases c2113 : 0 < a4
                        swap
                        · omega
                        by_cases c2114 : 0 < b4
                        swap
                        · omega
                        by_cases c2115 : a0 + a2 < b0 + b2 + b4
                        swap
                        · -- branch
                          by_cases c2116 : 0 < a4
                          swap
                          · omega
                          by_cases c2117 : 0 < b6
                          swap
                          · omega
                          by_cases c2118 : a0 + a2 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c2119 : b0 + b2 + b4 < a0 + a2 + a4
                          swap
                          · omega
                          have f2120 := pair_fact E (i := 4) (j := 6) rfl rfl c2116 c2117
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2120
                          by_cases c2121 : 0 < a4
                          swap
                          · omega
                          by_cases c2122 : 0 < b8
                          swap
                          · omega
                          by_cases c2123 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c2124 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                          swap
                          · -- branch
                            by_cases c2125 : 0 < a4
                            swap
                            · omega
                            by_cases c2126 : 0 < b10
                            swap
                            · -- branch
                              by_cases c2127 : 0 < a6
                              swap
                              · -- branch
                                by_cases c2128 : 0 < a8
                                swap
                                · omega
                                by_cases c2129 : 0 < b6
                                swap
                                · omega
                                by_cases c2130 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c2131 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f2132 := pair_fact E (i := 8) (j := 6) rfl rfl c2128 c2129
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2132
                                omega
                              by_cases c2133 : 0 < b6
                              swap
                              · omega
                              by_cases c2134 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c2135 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                              swap
                              · omega
                              have f2136 := pair_fact E (i := 6) (j := 6) rfl rfl c2127 c2133
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2136
                              omega
                            by_cases c2137 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c2138 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                            swap
                            · omega
                            have f2139 := pair_fact E (i := 4) (j := 10) rfl rfl c2125 c2126
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2139
                            omega
                          have f2140 := pair_fact E (i := 4) (j := 8) rfl rfl c2121 c2122
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2140
                          omega
                        by_cases c2141 : b0 + b2 < a0 + a2 + a4
                        swap
                        · omega
                        have f2142 := pair_fact E (i := 4) (j := 4) rfl rfl c2113 c2114
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2142
                        omega
                      by_cases c2143 : a0 + a2 < b0 + b2
                      swap
                      · omega
                      by_cases c2144 : b0 < a0 + a2 + a4
                      swap
                      · omega
                      have f2145 := pair_fact E (i := 4) (j := 2) rfl rfl c2111 c2112
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2145
                      omega
                    by_cases c2146 : 0 < a0 + a2 + a4
                    swap
                    · omega
                    have f2147 := pair_fact E (i := 4) (j := 0) rfl rfl c2108 c2109
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2147
                    omega
                  have f2148 := pair_fact E (i := 0) (j := 4) rfl rfl c2019 c2020
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2148
                  omega
                by_cases c2149 : a0 < b0 + b2
                swap
                · omega
                by_cases c2150 : b0 < a0 + a2
                swap
                · omega
                have f2151 := pair_fact E (i := 2) (j := 2) rfl rfl c2017 c2018
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2151
                omega
              by_cases c2152 : 0 < b0 + b2
              swap
              · omega
              by_cases c2153 : b0 < 0 + a0
              swap
              · -- branch
                by_cases c2154 : 0 < a2
                swap
                · omega
                by_cases c2155 : 0 < b2
                swap
                · omega
                by_cases c2156 : a0 < b0 + b2
                swap
                · omega
                by_cases c2157 : b0 < a0 + a2
                swap
                · omega
                have f2158 := pair_fact E (i := 2) (j := 2) rfl rfl c2154 c2155
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2158
                by_cases c2159 : 0 < a4
                swap
                · omega
                by_cases c2160 : 0 < b6
                swap
                · omega
                by_cases c2161 : a0 + a2 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c2162 : b0 + b2 + b4 < a0 + a2 + a4
                swap
                · omega
                have f2163 := pair_fact E (i := 4) (j := 6) rfl rfl c2159 c2160
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2163
                omega
              have f2164 := pair_fact E (i := 0) (j := 2) rfl rfl c2015 c2016
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2164
              omega
            have f2165 := pair_fact E (i := 0) (j := 6) rfl rfl c1796 c1797
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2165
            by_cases c2166 : 0 < a2
            swap
            · omega
            by_cases c2167 : 0 < b6
            swap
            · omega
            by_cases c2168 : a0 < b0 + b2 + b4 + b6
            swap
            · omega
            by_cases c2169 : b0 + b2 + b4 < a0 + a2
            swap
            · omega
            have f2170 := pair_fact E (i := 2) (j := 6) rfl rfl c2166 c2167
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2170
            omega
          by_cases c2171 : 0 < a0 + a2
          swap
          · omega
          have f2172 := pair_fact E (i := 2) (j := 0) rfl rfl c1793 c1794
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2172
          by_cases c2173 : 0 < a0
          swap
          · omega
          by_cases c2174 : 0 < b2
          swap
          · -- branch
            by_cases c2175 : 0 < a0
            swap
            · omega
            by_cases c2176 : 0 < b6
            swap
            · omega
            by_cases c2177 : 0 < b0 + b2 + b4 + b6
            swap
            · omega
            by_cases c2178 : b0 + b2 + b4 < 0 + a0
            swap
            · -- branch
              by_cases c2179 : 0 < a2
              swap
              · omega
              by_cases c2180 : 0 < b2
              swap
              · -- branch
                by_cases c2181 : 0 < a2
                swap
                · omega
                by_cases c2182 : 0 < b6
                swap
                · omega
                by_cases c2183 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c2184 : b0 + b2 + b4 < a0 + a2
                swap
                · -- branch
                  by_cases c2185 : 0 < a6
                  swap
                  · omega
                  by_cases c2186 : 0 < b6
                  swap
                  · omega
                  by_cases c2187 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c2188 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                  swap
                  · omega
                  have f2189 := pair_fact E (i := 6) (j := 6) rfl rfl c2185 c2186
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2189
                  omega
                have f2190 := pair_fact E (i := 2) (j := 6) rfl rfl c2181 c2182
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2190
                omega
              by_cases c2191 : a0 < b0 + b2
              swap
              · omega
              by_cases c2192 : b0 < a0 + a2
              swap
              · omega
              have f2193 := pair_fact E (i := 2) (j := 2) rfl rfl c2179 c2180
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2193
              omega
            have f2194 := pair_fact E (i := 0) (j := 6) rfl rfl c2175 c2176
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2194
            omega
          by_cases c2195 : 0 < b0 + b2
          swap
          · omega
          by_cases c2196 : b0 < 0 + a0
          swap
          · -- branch
            by_cases c2197 : 0 < a2
            swap
            · omega
            by_cases c2198 : 0 < b2
            swap
            · omega
            by_cases c2199 : a0 < b0 + b2
            swap
            · omega
            by_cases c2200 : b0 < a0 + a2
            swap
            · -- branch
              by_cases c2201 : 0 < a6
              swap
              · omega
              by_cases c2202 : 0 < b2
              swap
              · omega
              by_cases c2203 : a0 + a2 + a4 < b0 + b2
              swap
              · -- branch
                by_cases c2204 : 0 < a4
                swap
                · omega
                by_cases c2205 : 0 < b2
                swap
                · omega
                by_cases c2206 : a0 + a2 < b0 + b2
                swap
                · omega
                by_cases c2207 : b0 < a0 + a2 + a4
                swap
                · omega
                have f2208 := pair_fact E (i := 4) (j := 2) rfl rfl c2204 c2205
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2208
                omega
              by_cases c2209 : b0 < a0 + a2 + a4 + a6
              swap
              · omega
              have f2210 := pair_fact E (i := 6) (j := 2) rfl rfl c2201 c2202
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2210
              omega
            have f2211 := pair_fact E (i := 2) (j := 2) rfl rfl c2197 c2198
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2211
            omega
          have f2212 := pair_fact E (i := 0) (j := 2) rfl rfl c2173 c2174
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2212
          omega
        by_cases c2213 : a0 < b0 + b2 + b4 + b6 + b8 + b10
        swap
        · omega
        by_cases c2214 : b0 + b2 + b4 + b6 + b8 < a0 + a2
        swap
        · omega
        have f2215 := pair_fact E (i := 2) (j := 10) rfl rfl c1791 c1792
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2215
        omega
      have f2216 := pair_fact E (i := 2) (j := 8) rfl rfl c1562 c1788
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2216
      omega
    by_cases c2217 : 0 < b0 + b2 + b4 + b6 + b8 + b10
    swap
    · omega
    by_cases c2218 : b0 + b2 + b4 + b6 + b8 < 0 + a0
    swap
    · -- branch
      by_cases c2219 : 0 < a2
      swap
      · -- branch
        by_cases c2220 : 0 < a2
        swap
        · -- branch
          by_cases c2221 : 0 < a2
          swap
          · -- branch
            by_cases c2222 : 0 < a2
            swap
            · -- branch
              by_cases c2223 : 0 < a2
              swap
              · -- branch
                by_cases c2224 : 0 < a2
                swap
                · -- branch
                  by_cases c2225 : 0 < a6
                  swap
                  · omega
                  by_cases c2226 : 0 < b10
                  swap
                  · omega
                  by_cases c2227 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c2228 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                  swap
                  · -- branch
                    by_cases c2229 : 0 < a0
                    swap
                    · omega
                    by_cases c2230 : 0 < b2
                    swap
                    · omega
                    by_cases c2231 : 0 < b0 + b2
                    swap
                    · omega
                    by_cases c2232 : b0 < 0 + a0
                    swap
                    · -- branch
                      by_cases c2233 : 0 < a0
                      swap
                      · omega
                      by_cases c2234 : 0 < b4
                      swap
                      · -- branch
                        by_cases c2235 : 0 < a0
                        swap
                        · omega
                        by_cases c2236 : 0 < b6
                        swap
                        · omega
                        by_cases c2237 : 0 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c2238 : b0 + b2 + b4 < 0 + a0
                        swap
                        · -- branch
                          by_cases c2239 : 0 < a4
                          swap
                          · omega
                          by_cases c2240 : 0 < b4
                          swap
                          · -- branch
                            by_cases c2241 : 0 < a4
                            swap
                            · omega
                            by_cases c2242 : 0 < b6
                            swap
                            · omega
                            by_cases c2243 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c2244 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c2245 : 0 < a4
                              swap
                              · omega
                              by_cases c2246 : 0 < b8
                              swap
                              · omega
                              by_cases c2247 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c2248 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c2249 : 0 < a4
                                swap
                                · omega
                                by_cases c2250 : 0 < b10
                                swap
                                · omega
                                by_cases c2251 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                swap
                                · omega
                                by_cases c2252 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c2253 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c2254 : 0 < b4
                                  swap
                                  · -- branch
                                    by_cases c2255 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c2256 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c2257 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c2258 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f2259 := pair_fact E (i := 6) (j := 6) rfl rfl c2255 c2256
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2259
                                    by_cases c2260 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c2261 : 0 < b0
                                    swap
                                    · omega
                                    by_cases c2262 : a0 + a2 < 0 + b0
                                    swap
                                    · -- branch
                                      by_cases c2263 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c2264 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c2265 : a0 + a2 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c2266 : b0 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f2267 := pair_fact E (i := 4) (j := 2) rfl rfl c2263 c2264
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2267
                                      by_cases c2268 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c2269 : 0 < b0
                                      swap
                                      · omega
                                      by_cases c2270 : a0 + a2 + a4 < 0 + b0
                                      swap
                                      · -- branch
                                        by_cases c2271 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c2272 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c2273 : a0 + a2 + a4 < b0 + b2
                                        swap
                                        · -- branch
                                          by_cases c2274 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c2275 : 0 < b8
                                          swap
                                          · omega
                                          by_cases c2276 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                          swap
                                          · omega
                                          by_cases c2277 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                          swap
                                          · -- branch
                                            by_cases c2278 : 0 < a8
                                            swap
                                            · -- branch
                                              by_cases c2279 : 0 < a10
                                              swap
                                              · omega
                                              by_cases c2280 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c2281 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c2282 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                              swap
                                              · omega
                                              have f2283 := pair_fact E (i := 10) (j := 6) rfl rfl c2279 c2280
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2283
                                              omega
                                            by_cases c2284 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c2285 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c2286 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f2287 := pair_fact E (i := 8) (j := 6) rfl rfl c2278 c2284
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2287
                                            omega
                                          have f2288 := pair_fact E (i := 6) (j := 8) rfl rfl c2274 c2275
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2288
                                          omega
                                        by_cases c2289 : b0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f2290 := pair_fact E (i := 6) (j := 2) rfl rfl c2271 c2272
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2290
                                        omega
                                      by_cases c2291 : 0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f2292 := pair_fact E (i := 6) (j := 0) rfl rfl c2268 c2269
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2292
                                      omega
                                    by_cases c2293 : 0 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f2294 := pair_fact E (i := 4) (j := 0) rfl rfl c2260 c2261
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2294
                                    omega
                                  by_cases c2295 : a0 + a2 + a4 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c2296 : b0 + b2 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f2297 := pair_fact E (i := 6) (j := 4) rfl rfl c2253 c2254
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2297
                                  omega
                                have f2298 := pair_fact E (i := 4) (j := 10) rfl rfl c2249 c2250
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2298
                                omega
                              have f2299 := pair_fact E (i := 4) (j := 8) rfl rfl c2245 c2246
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2299
                              omega
                            have f2300 := pair_fact E (i := 4) (j := 6) rfl rfl c2241 c2242
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2300
                            omega
                          by_cases c2301 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c2302 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f2303 := pair_fact E (i := 4) (j := 4) rfl rfl c2239 c2240
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2303
                          omega
                        have f2304 := pair_fact E (i := 0) (j := 6) rfl rfl c2235 c2236
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2304
                        omega
                      by_cases c2305 : 0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c2306 : b0 + b2 < 0 + a0
                      swap
                      · -- branch
                        by_cases c2307 : 0 < a6
                        swap
                        · omega
                        by_cases c2308 : 0 < b2
                        swap
                        · omega
                        by_cases c2309 : a0 + a2 + a4 < b0 + b2
                        swap
                        · omega
                        by_cases c2310 : b0 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f2311 := pair_fact E (i := 6) (j := 2) rfl rfl c2307 c2308
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2311
                        by_cases c2312 : 0 < a6
                        swap
                        · omega
                        by_cases c2313 : 0 < b0
                        swap
                        · omega
                        by_cases c2314 : a0 + a2 + a4 < 0 + b0
                        swap
                        · -- branch
                          by_cases c2315 : 0 < a6
                          swap
                          · omega
                          by_cases c2316 : 0 < b4
                          swap
                          · omega
                          by_cases c2317 : a0 + a2 + a4 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c2318 : b0 + b2 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f2319 := pair_fact E (i := 6) (j := 4) rfl rfl c2315 c2316
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2319
                          by_cases c2320 : 0 < a6
                          swap
                          · omega
                          by_cases c2321 : 0 < b8
                          swap
                          · omega
                          by_cases c2322 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c2323 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                          swap
                          · -- branch
                            by_cases c2324 : 0 < a0
                            swap
                            · omega
                            by_cases c2325 : 0 < b6
                            swap
                            · omega
                            by_cases c2326 : 0 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c2327 : b0 + b2 + b4 < 0 + a0
                            swap
                            · -- branch
                              by_cases c2328 : 0 < a4
                              swap
                              · -- branch
                                by_cases c2329 : 0 < a4
                                swap
                                · -- branch
                                  by_cases c2330 : 0 < a4
                                  swap
                                  · -- branch
                                    by_cases c2331 : 0 < a4
                                    swap
                                    · -- branch
                                      by_cases c2332 : 0 < a4
                                      swap
                                      · -- branch
                                        by_cases c2333 : 0 < a4
                                        swap
                                        · -- branch
                                          by_cases c2334 : 0 < a8
                                          swap
                                          · -- branch
                                            by_cases c2335 : 0 < a10
                                            swap
                                            · omega
                                            by_cases c2336 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c2337 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c2338 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                            swap
                                            · omega
                                            have f2339 := pair_fact E (i := 10) (j := 6) rfl rfl c2335 c2336
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2339
                                            omega
                                          by_cases c2340 : 0 < b6
                                          swap
                                          · omega
                                          by_cases c2341 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                          swap
                                          · omega
                                          by_cases c2342 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f2343 := pair_fact E (i := 8) (j := 6) rfl rfl c2334 c2340
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2343
                                          omega
                                        by_cases c2344 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c2345 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c2346 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f2347 := pair_fact E (i := 4) (j := 10) rfl rfl c2333 c2344
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2347
                                        omega
                                      by_cases c2348 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c2349 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c2350 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f2351 := pair_fact E (i := 4) (j := 8) rfl rfl c2332 c2348
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2351
                                      omega
                                    by_cases c2352 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c2353 : a0 + a2 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c2354 : b0 + b2 + b4 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f2355 := pair_fact E (i := 4) (j := 6) rfl rfl c2331 c2352
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2355
                                    omega
                                  by_cases c2356 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c2357 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c2358 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f2359 := pair_fact E (i := 4) (j := 4) rfl rfl c2330 c2356
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2359
                                  omega
                                by_cases c2360 : 0 < b2
                                swap
                                · omega
                                by_cases c2361 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c2362 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f2363 := pair_fact E (i := 4) (j := 2) rfl rfl c2329 c2360
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2363
                                omega
                              by_cases c2364 : 0 < b0
                              swap
                              · omega
                              by_cases c2365 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c2366 : 0 < a4
                                swap
                                · omega
                                by_cases c2367 : 0 < b2
                                swap
                                · omega
                                by_cases c2368 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c2369 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f2370 := pair_fact E (i := 4) (j := 2) rfl rfl c2366 c2367
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2370
                                by_cases c2371 : 0 < a4
                                swap
                                · omega
                                by_cases c2372 : 0 < b4
                                swap
                                · omega
                                by_cases c2373 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c2374 : b0 + b2 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c2375 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c2376 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c2377 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c2378 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c2379 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c2380 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c2381 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c2382 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c2383 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c2384 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c2385 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c2386 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c2387 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c2388 : 0 < b6
                                        swap
                                        · omega
                                        by_cases c2389 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                        swap
                                        · omega
                                        by_cases c2390 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                        swap
                                        · -- branch
                                          by_cases c2391 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c2392 : 0 < b6
                                          swap
                                          · omega
                                          by_cases c2393 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                          swap
                                          · omega
                                          by_cases c2394 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f2395 := pair_fact E (i := 8) (j := 6) rfl rfl c2391 c2392
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2395
                                          omega
                                        have f2396 := pair_fact E (i := 6) (j := 6) rfl rfl c2387 c2388
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2396
                                        omega
                                      have f2397 := pair_fact E (i := 4) (j := 10) rfl rfl c2383 c2384
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2397
                                      omega
                                    have f2398 := pair_fact E (i := 4) (j := 8) rfl rfl c2379 c2380
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2398
                                    omega
                                  have f2399 := pair_fact E (i := 4) (j := 6) rfl rfl c2375 c2376
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2399
                                  omega
                                have f2400 := pair_fact E (i := 4) (j := 4) rfl rfl c2371 c2372
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2400
                                omega
                              by_cases c2401 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2402 := pair_fact E (i := 4) (j := 0) rfl rfl c2328 c2364
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2402
                              omega
                            have f2403 := pair_fact E (i := 0) (j := 6) rfl rfl c2324 c2325
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2403
                            omega
                          have f2404 := pair_fact E (i := 6) (j := 8) rfl rfl c2320 c2321
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2404
                          omega
                        by_cases c2405 : 0 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f2406 := pair_fact E (i := 6) (j := 0) rfl rfl c2312 c2313
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2406
                        omega
                      have f2407 := pair_fact E (i := 0) (j := 4) rfl rfl c2233 c2234
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2407
                      omega
                    have f2408 := pair_fact E (i := 0) (j := 2) rfl rfl c2229 c2230
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2408
                    by_cases c2409 : 0 < a6
                    swap
                    · omega
                    by_cases c2410 : 0 < b0
                    swap
                    · omega
                    by_cases c2411 : a0 + a2 + a4 < 0 + b0
                    swap
                    · -- branch
                      by_cases c2412 : 0 < a6
                      swap
                      · omega
                      by_cases c2413 : 0 < b2
                      swap
                      · omega
                      by_cases c2414 : a0 + a2 + a4 < b0 + b2
                      swap
                      · -- branch
                        by_cases c2415 : 0 < a6
                        swap
                        · omega
                        by_cases c2416 : 0 < b6
                        swap
                        · omega
                        by_cases c2417 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c2418 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f2419 := pair_fact E (i := 6) (j := 6) rfl rfl c2415 c2416
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2419
                        omega
                      by_cases c2420 : b0 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f2421 := pair_fact E (i := 6) (j := 2) rfl rfl c2412 c2413
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2421
                      omega
                    by_cases c2422 : 0 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f2423 := pair_fact E (i := 6) (j := 0) rfl rfl c2409 c2410
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2423
                    omega
                  have f2424 := pair_fact E (i := 6) (j := 10) rfl rfl c2225 c2226
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2424
                  omega
                by_cases c2425 : 0 < b10
                swap
                · omega
                by_cases c2426 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                swap
                · omega
                by_cases c2427 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                swap
                · omega
                have f2428 := pair_fact E (i := 2) (j := 10) rfl rfl c2224 c2425
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2428
                omega
              by_cases c2429 : 0 < b6
              swap
              · omega
              by_cases c2430 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c2431 : b0 + b2 + b4 < a0 + a2
              swap
              · omega
              have f2432 := pair_fact E (i := 2) (j := 6) rfl rfl c2223 c2429
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2432
              omega
            by_cases c2433 : 0 < b4
            swap
            · omega
            by_cases c2434 : a0 < b0 + b2 + b4
            swap
            · omega
            by_cases c2435 : b0 + b2 < a0 + a2
            swap
            · omega
            have f2436 := pair_fact E (i := 2) (j := 4) rfl rfl c2222 c2433
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2436
            omega
          by_cases c2437 : 0 < b2
          swap
          · omega
          by_cases c2438 : a0 < b0 + b2
          swap
          · omega
          by_cases c2439 : b0 < a0 + a2
          swap
          · omega
          have f2440 := pair_fact E (i := 2) (j := 2) rfl rfl c2221 c2437
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2440
          omega
        by_cases c2441 : 0 < b0
        swap
        · omega
        by_cases c2442 : a0 < 0 + b0
        swap
        · omega
        by_cases c2443 : 0 < a0 + a2
        swap
        · omega
        have f2444 := pair_fact E (i := 2) (j := 0) rfl rfl c2220 c2441
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2444
        omega
      by_cases c2445 : 0 < b8
      swap
      · omega
      by_cases c2446 : a0 < b0 + b2 + b4 + b6 + b8
      swap
      · omega
      by_cases c2447 : b0 + b2 + b4 + b6 < a0 + a2
      swap
      · -- branch
        by_cases c2448 : 0 < a2
        swap
        · omega
        by_cases c2449 : 0 < b10
        swap
        · omega
        by_cases c2450 : a0 < b0 + b2 + b4 + b6 + b8 + b10
        swap
        · omega
        by_cases c2451 : b0 + b2 + b4 + b6 + b8 < a0 + a2
        swap
        · -- branch
          by_cases c2452 : 0 < a2
          swap
          · omega
          by_cases c2453 : 0 < b0
          swap
          · omega
          by_cases c2454 : a0 < 0 + b0
          swap
          · -- branch
            by_cases c2455 : 0 < a4
            swap
            · -- branch
              by_cases c2456 : 0 < a4
              swap
              · -- branch
                by_cases c2457 : 0 < a4
                swap
                · -- branch
                  by_cases c2458 : 0 < a4
                  swap
                  · -- branch
                    by_cases c2459 : 0 < a4
                    swap
                    · -- branch
                      by_cases c2460 : 0 < a4
                      swap
                      · -- branch
                        by_cases c2461 : 0 < a6
                        swap
                        · omega
                        by_cases c2462 : 0 < b0
                        swap
                        · omega
                        by_cases c2463 : a0 + a2 + a4 < 0 + b0
                        swap
                        · -- branch
                          by_cases c2464 : 0 < a6
                          swap
                          · omega
                          by_cases c2465 : 0 < b10
                          swap
                          · omega
                          by_cases c2466 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c2467 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                          swap
                          · -- branch
                            by_cases c2468 : 0 < a0
                            swap
                            · omega
                            by_cases c2469 : 0 < b4
                            swap
                            · omega
                            by_cases c2470 : 0 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c2471 : b0 + b2 < 0 + a0
                            swap
                            · -- branch
                              by_cases c2472 : 0 < a0
                              swap
                              · omega
                              by_cases c2473 : 0 < b6
                              swap
                              · omega
                              by_cases c2474 : 0 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c2475 : b0 + b2 + b4 < 0 + a0
                              swap
                              · -- branch
                                by_cases c2476 : 0 < a2
                                swap
                                · omega
                                by_cases c2477 : 0 < b6
                                swap
                                · omega
                                by_cases c2478 : a0 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c2479 : b0 + b2 + b4 < a0 + a2
                                swap
                                · -- branch
                                  by_cases c2480 : 0 < a2
                                  swap
                                  · omega
                                  by_cases c2481 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c2482 : a0 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c2483 : b0 + b2 < a0 + a2
                                  swap
                                  · -- branch
                                    by_cases c2484 : 0 < a2
                                    swap
                                    · omega
                                    by_cases c2485 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c2486 : a0 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c2487 : b0 < a0 + a2
                                    swap
                                    · omega
                                    have f2488 := pair_fact E (i := 2) (j := 2) rfl rfl c2484 c2485
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2488
                                    by_cases c2489 : 0 < a0
                                    swap
                                    · omega
                                    by_cases c2490 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c2491 : 0 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c2492 : b0 < 0 + a0
                                    swap
                                    · -- branch
                                      by_cases c2493 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c2494 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c2495 : a0 + a2 + a4 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c2496 : b0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f2497 := pair_fact E (i := 6) (j := 2) rfl rfl c2493 c2494
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2497
                                      by_cases c2498 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c2499 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c2500 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c2501 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f2502 := pair_fact E (i := 6) (j := 4) rfl rfl c2498 c2499
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2502
                                      omega
                                    have f2503 := pair_fact E (i := 0) (j := 2) rfl rfl c2489 c2490
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2503
                                    omega
                                  have f2504 := pair_fact E (i := 2) (j := 4) rfl rfl c2480 c2481
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2504
                                  by_cases c2505 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c2506 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c2507 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c2508 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                  swap
                                  · -- branch
                                    by_cases c2509 : 0 < a0
                                    swap
                                    · omega
                                    by_cases c2510 : 0 < b2
                                    swap
                                    · -- branch
                                      by_cases c2511 : 0 < a2
                                      swap
                                      · omega
                                      by_cases c2512 : 0 < b2
                                      swap
                                      · -- branch
                                        by_cases c2513 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c2514 : 0 < b2
                                        swap
                                        · -- branch
                                          by_cases c2515 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c2516 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c2517 : a0 + a2 + a4 < b0 + b2 + b4
                                          swap
                                          · -- branch
                                            by_cases c2518 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c2519 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c2520 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c2521 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f2522 := pair_fact E (i := 6) (j := 6) rfl rfl c2518 c2519
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2522
                                            by_cases c2523 : 0 < a8
                                            swap
                                            · -- branch
                                              by_cases c2524 : 0 < a10
                                              swap
                                              · omega
                                              by_cases c2525 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c2526 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c2527 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                              swap
                                              · omega
                                              have f2528 := pair_fact E (i := 10) (j := 6) rfl rfl c2524 c2525
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2528
                                              omega
                                            by_cases c2529 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c2530 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c2531 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f2532 := pair_fact E (i := 8) (j := 6) rfl rfl c2523 c2529
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2532
                                            omega
                                          by_cases c2533 : b0 + b2 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f2534 := pair_fact E (i := 6) (j := 4) rfl rfl c2515 c2516
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2534
                                          omega
                                        by_cases c2535 : a0 + a2 + a4 < b0 + b2
                                        swap
                                        · omega
                                        by_cases c2536 : b0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f2537 := pair_fact E (i := 6) (j := 2) rfl rfl c2513 c2514
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2537
                                        omega
                                      by_cases c2538 : a0 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c2539 : b0 < a0 + a2
                                      swap
                                      · omega
                                      have f2540 := pair_fact E (i := 2) (j := 2) rfl rfl c2511 c2512
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2540
                                      omega
                                    by_cases c2541 : 0 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c2542 : b0 < 0 + a0
                                    swap
                                    · -- branch
                                      by_cases c2543 : 0 < a2
                                      swap
                                      · omega
                                      by_cases c2544 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c2545 : a0 < b0 + b2
                                      swap
                                      · omega
                                      by_cases c2546 : b0 < a0 + a2
                                      swap
                                      · omega
                                      have f2547 := pair_fact E (i := 2) (j := 2) rfl rfl c2543 c2544
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2547
                                      by_cases c2548 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c2549 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c2550 : a0 + a2 + a4 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c2551 : b0 + b2 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f2552 := pair_fact E (i := 6) (j := 4) rfl rfl c2548 c2549
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2552
                                      omega
                                    have f2553 := pair_fact E (i := 0) (j := 2) rfl rfl c2509 c2510
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2553
                                    omega
                                  have f2554 := pair_fact E (i := 6) (j := 8) rfl rfl c2505 c2506
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2554
                                  omega
                                have f2555 := pair_fact E (i := 2) (j := 6) rfl rfl c2476 c2477
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2555
                                omega
                              have f2556 := pair_fact E (i := 0) (j := 6) rfl rfl c2472 c2473
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2556
                              omega
                            have f2557 := pair_fact E (i := 0) (j := 4) rfl rfl c2468 c2469
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2557
                            by_cases c2558 : 0 < a6
                            swap
                            · omega
                            by_cases c2559 : 0 < b6
                            swap
                            · omega
                            by_cases c2560 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c2561 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f2562 := pair_fact E (i := 6) (j := 6) rfl rfl c2558 c2559
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2562
                            omega
                          have f2563 := pair_fact E (i := 6) (j := 10) rfl rfl c2464 c2465
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2563
                          omega
                        by_cases c2564 : 0 < a0 + a2 + a4 + a6
                        swap
                        · omega
                        have f2565 := pair_fact E (i := 6) (j := 0) rfl rfl c2461 c2462
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2565
                        omega
                      by_cases c2566 : 0 < b10
                      swap
                      · omega
                      by_cases c2567 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                      swap
                      · omega
                      by_cases c2568 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                      swap
                      · omega
                      have f2569 := pair_fact E (i := 4) (j := 10) rfl rfl c2460 c2566
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2569
                      omega
                    by_cases c2570 : 0 < b8
                    swap
                    · omega
                    by_cases c2571 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c2572 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                    swap
                    · omega
                    have f2573 := pair_fact E (i := 4) (j := 8) rfl rfl c2459 c2570
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2573
                    omega
                  by_cases c2574 : 0 < b6
                  swap
                  · omega
                  by_cases c2575 : a0 + a2 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c2576 : b0 + b2 + b4 < a0 + a2 + a4
                  swap
                  · omega
                  have f2577 := pair_fact E (i := 4) (j := 6) rfl rfl c2458 c2574
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2577
                  omega
                by_cases c2578 : 0 < b4
                swap
                · omega
                by_cases c2579 : a0 + a2 < b0 + b2 + b4
                swap
                · omega
                by_cases c2580 : b0 + b2 < a0 + a2 + a4
                swap
                · omega
                have f2581 := pair_fact E (i := 4) (j := 4) rfl rfl c2457 c2578
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2581
                omega
              by_cases c2582 : 0 < b2
              swap
              · omega
              by_cases c2583 : a0 + a2 < b0 + b2
              swap
              · omega
              by_cases c2584 : b0 < a0 + a2 + a4
              swap
              · omega
              have f2585 := pair_fact E (i := 4) (j := 2) rfl rfl c2456 c2582
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2585
              omega
            by_cases c2586 : 0 < b0
            swap
            · omega
            by_cases c2587 : a0 + a2 < 0 + b0
            swap
            · -- branch
              by_cases c2588 : 0 < a4
              swap
              · omega
              by_cases c2589 : 0 < b10
              swap
              · omega
              by_cases c2590 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c2591 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
              swap
              · -- branch
                by_cases c2592 : 0 < a4
                swap
                · omega
                by_cases c2593 : 0 < b8
                swap
                · omega
                by_cases c2594 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c2595 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                swap
                · -- branch
                  by_cases c2596 : 0 < a6
                  swap
                  · -- branch
                    by_cases c2597 : 0 < a4
                    swap
                    · omega
                    by_cases c2598 : 0 < b6
                    swap
                    · omega
                    by_cases c2599 : a0 + a2 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c2600 : b0 + b2 + b4 < a0 + a2 + a4
                    swap
                    · omega
                    have f2601 := pair_fact E (i := 4) (j := 6) rfl rfl c2597 c2598
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2601
                    by_cases c2602 : 0 < a0
                    swap
                    · omega
                    by_cases c2603 : 0 < b6
                    swap
                    · omega
                    by_cases c2604 : 0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c2605 : b0 + b2 + b4 < 0 + a0
                    swap
                    · -- branch
                      by_cases c2606 : 0 < a8
                      swap
                      · omega
                      by_cases c2607 : 0 < b6
                      swap
                      · omega
                      by_cases c2608 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c2609 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f2610 := pair_fact E (i := 8) (j := 6) rfl rfl c2606 c2607
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2610
                      omega
                    have f2611 := pair_fact E (i := 0) (j := 6) rfl rfl c2602 c2603
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2611
                    omega
                  by_cases c2612 : 0 < b0
                  swap
                  · omega
                  by_cases c2613 : a0 + a2 + a4 < 0 + b0
                  swap
                  · -- branch
                    by_cases c2614 : 0 < a6
                    swap
                    · omega
                    by_cases c2615 : 0 < b10
                    swap
                    · omega
                    by_cases c2616 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c2617 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                    swap
                    · -- branch
                      by_cases c2618 : 0 < a0
                      swap
                      · omega
                      by_cases c2619 : 0 < b6
                      swap
                      · omega
                      by_cases c2620 : 0 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c2621 : b0 + b2 + b4 < 0 + a0
                      swap
                      · -- branch
                        by_cases c2622 : 0 < a2
                        swap
                        · omega
                        by_cases c2623 : 0 < b6
                        swap
                        · omega
                        by_cases c2624 : a0 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c2625 : b0 + b2 + b4 < a0 + a2
                        swap
                        · -- branch
                          by_cases c2626 : 0 < a0
                          swap
                          · omega
                          by_cases c2627 : 0 < b2
                          swap
                          · omega
                          by_cases c2628 : 0 < b0 + b2
                          swap
                          · omega
                          by_cases c2629 : b0 < 0 + a0
                          swap
                          · -- branch
                            by_cases c2630 : 0 < a2
                            swap
                            · omega
                            by_cases c2631 : 0 < b2
                            swap
                            · omega
                            by_cases c2632 : a0 < b0 + b2
                            swap
                            · omega
                            by_cases c2633 : b0 < a0 + a2
                            swap
                            · omega
                            have f2634 := pair_fact E (i := 2) (j := 2) rfl rfl c2630 c2631
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2634
                            by_cases c2635 : 0 < a6
                            swap
                            · omega
                            by_cases c2636 : 0 < b8
                            swap
                            · omega
                            by_cases c2637 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c2638 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                            swap
                            · -- branch
                              by_cases c2639 : 0 < a8
                              swap
                              · -- branch
                                by_cases c2640 : 0 < a10
                                swap
                                · omega
                                by_cases c2641 : 0 < b6
                                swap
                                · omega
                                by_cases c2642 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c2643 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f2644 := pair_fact E (i := 10) (j := 6) rfl rfl c2640 c2641
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2644
                                omega
                              by_cases c2645 : 0 < b6
                              swap
                              · omega
                              by_cases c2646 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c2647 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f2648 := pair_fact E (i := 8) (j := 6) rfl rfl c2639 c2645
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2648
                              omega
                            have f2649 := pair_fact E (i := 6) (j := 8) rfl rfl c2635 c2636
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2649
                            omega
                          have f2650 := pair_fact E (i := 0) (j := 2) rfl rfl c2626 c2627
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2650
                          by_cases c2651 : 0 < a2
                          swap
                          · omega
                          by_cases c2652 : 0 < b2
                          swap
                          · omega
                          by_cases c2653 : a0 < b0 + b2
                          swap
                          · -- branch
                            by_cases c2654 : 0 < a2
                            swap
                            · omega
                            by_cases c2655 : 0 < b4
                            swap
                            · omega
                            by_cases c2656 : a0 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c2657 : b0 + b2 < a0 + a2
                            swap
                            · omega
                            have f2658 := pair_fact E (i := 2) (j := 4) rfl rfl c2654 c2655
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2658
                            omega
                          by_cases c2659 : b0 < a0 + a2
                          swap
                          · omega
                          have f2660 := pair_fact E (i := 2) (j := 2) rfl rfl c2651 c2652
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2660
                          omega
                        have f2661 := pair_fact E (i := 2) (j := 6) rfl rfl c2622 c2623
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2661
                        by_cases c2662 : 0 < a4
                        swap
                        · omega
                        by_cases c2663 : 0 < b6
                        swap
                        · omega
                        by_cases c2664 : a0 + a2 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c2665 : b0 + b2 + b4 < a0 + a2 + a4
                        swap
                        · omega
                        have f2666 := pair_fact E (i := 4) (j := 6) rfl rfl c2662 c2663
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2666
                        by_cases c2667 : 0 < a6
                        swap
                        · omega
                        by_cases c2668 : 0 < b8
                        swap
                        · omega
                        by_cases c2669 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c2670 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                        swap
                        · -- branch
                          by_cases c2671 : 0 < a6
                          swap
                          · omega
                          by_cases c2672 : 0 < b6
                          swap
                          · omega
                          by_cases c2673 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c2674 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                          swap
                          · omega
                          have f2675 := pair_fact E (i := 6) (j := 6) rfl rfl c2671 c2672
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2675
                          by_cases c2676 : 0 < a0
                          swap
                          · omega
                          by_cases c2677 : 0 < b2
                          swap
                          · -- branch
                            by_cases c2678 : 0 < a2
                            swap
                            · omega
                            by_cases c2679 : 0 < b2
                            swap
                            · -- branch
                              by_cases c2680 : 0 < a4
                              swap
                              · omega
                              by_cases c2681 : 0 < b2
                              swap
                              · -- branch
                                by_cases c2682 : 0 < a6
                                swap
                                · omega
                                by_cases c2683 : 0 < b2
                                swap
                                · -- branch
                                  by_cases c2684 : 0 < a0
                                  swap
                                  · omega
                                  by_cases c2685 : 0 < b4
                                  swap
                                  · -- branch
                                    by_cases c2686 : 0 < a2
                                    swap
                                    · omega
                                    by_cases c2687 : 0 < b4
                                    swap
                                    · -- branch
                                      by_cases c2688 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c2689 : 0 < b4
                                      swap
                                      · -- branch
                                        by_cases c2690 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c2691 : 0 < b4
                                        swap
                                        · -- branch
                                          by_cases c2692 : 0 < a8
                                          swap
                                          · -- branch
                                            by_cases c2693 : 0 < a10
                                            swap
                                            · omega
                                            by_cases c2694 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c2695 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c2696 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                            swap
                                            · omega
                                            have f2697 := pair_fact E (i := 10) (j := 6) rfl rfl c2693 c2694
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2697
                                            omega
                                          by_cases c2698 : 0 < b6
                                          swap
                                          · omega
                                          by_cases c2699 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                          swap
                                          · omega
                                          by_cases c2700 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f2701 := pair_fact E (i := 8) (j := 6) rfl rfl c2692 c2698
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2701
                                          omega
                                        by_cases c2702 : a0 + a2 + a4 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c2703 : b0 + b2 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f2704 := pair_fact E (i := 6) (j := 4) rfl rfl c2690 c2691
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2704
                                        omega
                                      by_cases c2705 : a0 + a2 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c2706 : b0 + b2 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f2707 := pair_fact E (i := 4) (j := 4) rfl rfl c2688 c2689
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2707
                                      omega
                                    by_cases c2708 : a0 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c2709 : b0 + b2 < a0 + a2
                                    swap
                                    · omega
                                    have f2710 := pair_fact E (i := 2) (j := 4) rfl rfl c2686 c2687
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2710
                                    omega
                                  by_cases c2711 : 0 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c2712 : b0 + b2 < 0 + a0
                                  swap
                                  · -- branch
                                    by_cases c2713 : 0 < a2
                                    swap
                                    · omega
                                    by_cases c2714 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c2715 : a0 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c2716 : b0 + b2 < a0 + a2
                                    swap
                                    · omega
                                    have f2717 := pair_fact E (i := 2) (j := 4) rfl rfl c2713 c2714
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2717
                                    omega
                                  have f2718 := pair_fact E (i := 0) (j := 4) rfl rfl c2684 c2685
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2718
                                  omega
                                by_cases c2719 : a0 + a2 + a4 < b0 + b2
                                swap
                                · omega
                                by_cases c2720 : b0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f2721 := pair_fact E (i := 6) (j := 2) rfl rfl c2682 c2683
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2721
                                omega
                              by_cases c2722 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c2723 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f2724 := pair_fact E (i := 4) (j := 2) rfl rfl c2680 c2681
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2724
                              omega
                            by_cases c2725 : a0 < b0 + b2
                            swap
                            · omega
                            by_cases c2726 : b0 < a0 + a2
                            swap
                            · omega
                            have f2727 := pair_fact E (i := 2) (j := 2) rfl rfl c2678 c2679
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2727
                            omega
                          by_cases c2728 : 0 < b0 + b2
                          swap
                          · omega
                          by_cases c2729 : b0 < 0 + a0
                          swap
                          · -- branch
                            by_cases c2730 : 0 < a2
                            swap
                            · omega
                            by_cases c2731 : 0 < b2
                            swap
                            · omega
                            by_cases c2732 : a0 < b0 + b2
                            swap
                            · omega
                            by_cases c2733 : b0 < a0 + a2
                            swap
                            · omega
                            have f2734 := pair_fact E (i := 2) (j := 2) rfl rfl c2730 c2731
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2734
                            omega
                          have f2735 := pair_fact E (i := 0) (j := 2) rfl rfl c2676 c2677
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2735
                          omega
                        have f2736 := pair_fact E (i := 6) (j := 8) rfl rfl c2667 c2668
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2736
                        omega
                      have f2737 := pair_fact E (i := 0) (j := 6) rfl rfl c2618 c2619
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2737
                      by_cases c2738 : 0 < a2
                      swap
                      · omega
                      by_cases c2739 : 0 < b6
                      swap
                      · omega
                      by_cases c2740 : a0 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c2741 : b0 + b2 + b4 < a0 + a2
                      swap
                      · omega
                      have f2742 := pair_fact E (i := 2) (j := 6) rfl rfl c2738 c2739
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2742
                      omega
                    have f2743 := pair_fact E (i := 6) (j := 10) rfl rfl c2614 c2615
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2743
                    omega
                  by_cases c2744 : 0 < a0 + a2 + a4 + a6
                  swap
                  · omega
                  have f2745 := pair_fact E (i := 6) (j := 0) rfl rfl c2596 c2612
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2745
                  omega
                have f2746 := pair_fact E (i := 4) (j := 8) rfl rfl c2592 c2593
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2746
                by_cases c2747 : 0 < a4
                swap
                · omega
                by_cases c2748 : 0 < b6
                swap
                · omega
                by_cases c2749 : a0 + a2 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c2750 : b0 + b2 + b4 < a0 + a2 + a4
                swap
                · omega
                have f2751 := pair_fact E (i := 4) (j := 6) rfl rfl c2747 c2748
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2751
                omega
              have f2752 := pair_fact E (i := 4) (j := 10) rfl rfl c2588 c2589
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2752
              omega
            by_cases c2753 : 0 < a0 + a2 + a4
            swap
            · omega
            have f2754 := pair_fact E (i := 4) (j := 0) rfl rfl c2455 c2586
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2754
            omega
          by_cases c2755 : 0 < a0 + a2
          swap
          · omega
          have f2756 := pair_fact E (i := 2) (j := 0) rfl rfl c2452 c2453
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2756
          by_cases c2757 : 0 < a0
          swap
          · omega
          by_cases c2758 : 0 < b2
          swap
          · -- branch
            by_cases c2759 : 0 < a0
            swap
            · omega
            by_cases c2760 : 0 < b6
            swap
            · omega
            by_cases c2761 : 0 < b0 + b2 + b4 + b6
            swap
            · omega
            by_cases c2762 : b0 + b2 + b4 < 0 + a0
            swap
            · -- branch
              by_cases c2763 : 0 < a2
              swap
              · omega
              by_cases c2764 : 0 < b2
              swap
              · -- branch
                by_cases c2765 : 0 < a2
                swap
                · omega
                by_cases c2766 : 0 < b6
                swap
                · omega
                by_cases c2767 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c2768 : b0 + b2 + b4 < a0 + a2
                swap
                · -- branch
                  by_cases c2769 : 0 < a6
                  swap
                  · omega
                  by_cases c2770 : 0 < b6
                  swap
                  · omega
                  by_cases c2771 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c2772 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                  swap
                  · omega
                  have f2773 := pair_fact E (i := 6) (j := 6) rfl rfl c2769 c2770
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2773
                  omega
                have f2774 := pair_fact E (i := 2) (j := 6) rfl rfl c2765 c2766
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2774
                omega
              by_cases c2775 : a0 < b0 + b2
              swap
              · omega
              by_cases c2776 : b0 < a0 + a2
              swap
              · omega
              have f2777 := pair_fact E (i := 2) (j := 2) rfl rfl c2763 c2764
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2777
              omega
            have f2778 := pair_fact E (i := 0) (j := 6) rfl rfl c2759 c2760
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2778
            omega
          by_cases c2779 : 0 < b0 + b2
          swap
          · omega
          by_cases c2780 : b0 < 0 + a0
          swap
          · -- branch
            by_cases c2781 : 0 < a2
            swap
            · omega
            by_cases c2782 : 0 < b2
            swap
            · omega
            by_cases c2783 : a0 < b0 + b2
            swap
            · omega
            by_cases c2784 : b0 < a0 + a2
            swap
            · -- branch
              by_cases c2785 : 0 < a6
              swap
              · omega
              by_cases c2786 : 0 < b2
              swap
              · omega
              by_cases c2787 : a0 + a2 + a4 < b0 + b2
              swap
              · -- branch
                by_cases c2788 : 0 < a4
                swap
                · omega
                by_cases c2789 : 0 < b2
                swap
                · omega
                by_cases c2790 : a0 + a2 < b0 + b2
                swap
                · omega
                by_cases c2791 : b0 < a0 + a2 + a4
                swap
                · omega
                have f2792 := pair_fact E (i := 4) (j := 2) rfl rfl c2788 c2789
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2792
                omega
              by_cases c2793 : b0 < a0 + a2 + a4 + a6
              swap
              · omega
              have f2794 := pair_fact E (i := 6) (j := 2) rfl rfl c2785 c2786
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2794
              omega
            have f2795 := pair_fact E (i := 2) (j := 2) rfl rfl c2781 c2782
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2795
            omega
          have f2796 := pair_fact E (i := 0) (j := 2) rfl rfl c2757 c2758
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2796
          omega
        have f2797 := pair_fact E (i := 2) (j := 10) rfl rfl c2448 c2449
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2797
        omega
      have f2798 := pair_fact E (i := 2) (j := 8) rfl rfl c2219 c2445
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2798
      omega
    have f2799 := pair_fact E (i := 0) (j := 10) rfl rfl c1560 c1561
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2799
    omega
  have f2800 := pair_fact E (i := 0) (j := 8) rfl rfl c1091 c1092
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2800
  omega

end Blocks
