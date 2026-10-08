import LeanProofs.ShuffleBlocks.Basic

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Blocks

set_option maxHeartbeats 0 in
/-- Cut inside run 5 of `V`: no splitting of this rotation gives two equal copies. -/
theorem V_cut05 (L l m v k a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9 a10 b10 : Nat)
    (hl : 1 ≤ l) (hm : m = 2 * v + 1) (hL : 9 * l ≤ L) (hk : k ≤ m)
    (e0 : a0 + b0 = (m - k))
    (e1 : a1 + b1 = 2 * l)
    (e2 : a2 + b2 = m)
    (e3 : a3 + b3 = l)
    (e4 : a4 + b4 = 3 * m)
    (e5 : a5 + b5 = L)
    (e6 : a6 + b6 = m)
    (e7 : a7 + b7 = 5 * l)
    (e8 : a8 + b8 = 2 * m)
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
                          by_cases c13 : 0 < a8
                          swap
                          · -- branch
                            by_cases c14 : 0 < a4
                            swap
                            · omega
                            by_cases c15 : 0 < b2
                            swap
                            · omega
                            by_cases c16 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c17 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f18 := pair_fact E (i := 4) (j := 2) rfl rfl c14 c15
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f18
                            by_cases c19 : 0 < a4
                            swap
                            · omega
                            by_cases c20 : 0 < b0
                            swap
                            · -- branch
                              by_cases c21 : 0 < a4
                              swap
                              · omega
                              by_cases c22 : 0 < b8
                              swap
                              · omega
                              by_cases c23 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                              swap
                              · omega
                              by_cases c24 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c25 : 0 < a4
                                swap
                                · omega
                                by_cases c26 : 0 < b4
                                swap
                                · omega
                                by_cases c27 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c28 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f29 := pair_fact E (i := 4) (j := 4) rfl rfl c25 c26
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f29
                                by_cases c30 : 0 < a4
                                swap
                                · omega
                                by_cases c31 : 0 < b6
                                swap
                                · -- branch
                                  by_cases c32 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c33 : 0 < b10
                                  swap
                                  · -- branch
                                    by_cases c34 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c35 : 0 < b0
                                    swap
                                    · -- branch
                                      by_cases c36 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c37 : 0 < b2
                                      swap
                                      · omega
                                      by_cases c38 : a0 + a2 + a4 < b0 + b2
                                      swap
                                      · -- branch
                                        by_cases c39 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c40 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c41 : a0 + a2 + a4 < b0 + b2 + b4
                                        swap
                                        · -- branch
                                          by_cases c42 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c43 : 0 < b6
                                          swap
                                          · -- branch
                                            by_cases c44 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c45 : 0 < b8
                                            swap
                                            · omega
                                            by_cases c46 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                            swap
                                            · omega
                                            by_cases c47 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f48 := pair_fact E (i := 6) (j := 8) rfl rfl c44 c45
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f48
                                            by_cases c49 : 0 < a10
                                            swap
                                            · omega
                                            by_cases c50 : 0 < b8
                                            swap
                                            · omega
                                            by_cases c51 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                            swap
                                            · omega
                                            by_cases c52 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                            swap
                                            · omega
                                            have f53 := pair_fact E (i := 10) (j := 8) rfl rfl c49 c50
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f53
                                            omega
                                          by_cases c54 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                          swap
                                          · omega
                                          by_cases c55 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f56 := pair_fact E (i := 6) (j := 6) rfl rfl c42 c43
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f56
                                          omega
                                        by_cases c57 : b0 + b2 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f58 := pair_fact E (i := 6) (j := 4) rfl rfl c39 c40
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f58
                                        omega
                                      by_cases c59 : b0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f60 := pair_fact E (i := 6) (j := 2) rfl rfl c36 c37
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f60
                                      omega
                                    by_cases c61 : a0 + a2 + a4 < 0 + b0
                                    swap
                                    · omega
                                    by_cases c62 : 0 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f63 := pair_fact E (i := 6) (j := 0) rfl rfl c34 c35
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f63
                                    omega
                                  by_cases c64 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                  swap
                                  · omega
                                  by_cases c65 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f66 := pair_fact E (i := 4) (j := 10) rfl rfl c32 c33
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f66
                                  omega
                                by_cases c67 : a0 + a2 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c68 : b0 + b2 + b4 < a0 + a2 + a4
                                swap
                                · omega
                                have f69 := pair_fact E (i := 4) (j := 6) rfl rfl c30 c31
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f69
                                omega
                              have f70 := pair_fact E (i := 4) (j := 8) rfl rfl c21 c22
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f70
                              omega
                            by_cases c71 : a0 + a2 < 0 + b0
                            swap
                            · omega
                            by_cases c72 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f73 := pair_fact E (i := 4) (j := 0) rfl rfl c19 c20
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f73
                            omega
                          by_cases c74 : 0 < b2
                          swap
                          · omega
                          by_cases c75 : a0 + a2 + a4 + a6 < b0 + b2
                          swap
                          · -- branch
                            by_cases c76 : 0 < a8
                            swap
                            · omega
                            by_cases c77 : 0 < b0
                            swap
                            · -- branch
                              by_cases c78 : 0 < a4
                              swap
                              · -- branch
                                by_cases c79 : 0 < a8
                                swap
                                · omega
                                by_cases c80 : 0 < b4
                                swap
                                · omega
                                by_cases c81 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c82 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f83 := pair_fact E (i := 8) (j := 4) rfl rfl c79 c80
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f83
                                omega
                              by_cases c84 : 0 < b0
                              swap
                              · -- branch
                                by_cases c85 : 0 < a4
                                swap
                                · omega
                                by_cases c86 : 0 < b2
                                swap
                                · omega
                                by_cases c87 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c88 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f89 := pair_fact E (i := 4) (j := 2) rfl rfl c85 c86
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f89
                                by_cases c90 : 0 < a4
                                swap
                                · omega
                                by_cases c91 : 0 < b8
                                swap
                                · -- branch
                                  by_cases c92 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c93 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c94 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                  swap
                                  · -- branch
                                    by_cases c95 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c96 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c97 : a0 + a2 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c98 : b0 + b2 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f99 := pair_fact E (i := 4) (j := 4) rfl rfl c95 c96
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f99
                                    by_cases c100 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c101 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c102 : a0 + a2 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c103 : b0 + b2 + b4 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c104 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c105 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c106 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c107 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c108 : 0 < a6
                                        swap
                                        · -- branch
                                          by_cases c109 : 0 < a6
                                          swap
                                          · -- branch
                                            by_cases c110 : 0 < a6
                                            swap
                                            · -- branch
                                              by_cases c111 : 0 < a6
                                              swap
                                              · -- branch
                                                by_cases c112 : 0 < a6
                                                swap
                                                · -- branch
                                                  by_cases c113 : 0 < a6
                                                  swap
                                                  · -- branch
                                                    by_cases c114 : 0 < a8
                                                    swap
                                                    · omega
                                                    by_cases c115 : 0 < b6
                                                    swap
                                                    · omega
                                                    by_cases c116 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                    swap
                                                    · omega
                                                    by_cases c117 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                    swap
                                                    · omega
                                                    have f118 := pair_fact E (i := 8) (j := 6) rfl rfl c114 c115
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f118
                                                    by_cases c119 : 0 < a8
                                                    swap
                                                    · omega
                                                    by_cases c120 : 0 < b10
                                                    swap
                                                    · omega
                                                    by_cases c121 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                                    swap
                                                    · omega
                                                    by_cases c122 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                                    swap
                                                    · omega
                                                    have f123 := pair_fact E (i := 8) (j := 10) rfl rfl c119 c120
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f123
                                                    omega
                                                  by_cases c124 : 0 < b10
                                                  swap
                                                  · omega
                                                  by_cases c125 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                                  swap
                                                  · omega
                                                  by_cases c126 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                                  swap
                                                  · omega
                                                  have f127 := pair_fact E (i := 6) (j := 10) rfl rfl c113 c124
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f127
                                                  omega
                                                by_cases c128 : 0 < b8
                                                swap
                                                · omega
                                                by_cases c129 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                                swap
                                                · omega
                                                by_cases c130 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                                swap
                                                · omega
                                                have f131 := pair_fact E (i := 6) (j := 8) rfl rfl c112 c128
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f131
                                                omega
                                              by_cases c132 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c133 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c134 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f135 := pair_fact E (i := 6) (j := 6) rfl rfl c111 c132
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f135
                                              omega
                                            by_cases c136 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c137 : a0 + a2 + a4 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c138 : b0 + b2 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f139 := pair_fact E (i := 6) (j := 4) rfl rfl c110 c136
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f139
                                            omega
                                          by_cases c140 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c141 : a0 + a2 + a4 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c142 : b0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f143 := pair_fact E (i := 6) (j := 2) rfl rfl c109 c140
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f143
                                          omega
                                        by_cases c144 : 0 < b0
                                        swap
                                        · omega
                                        by_cases c145 : a0 + a2 + a4 < 0 + b0
                                        swap
                                        · omega
                                        by_cases c146 : 0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f147 := pair_fact E (i := 6) (j := 0) rfl rfl c108 c144
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f147
                                        omega
                                      have f148 := pair_fact E (i := 4) (j := 10) rfl rfl c104 c105
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f148
                                      omega
                                    have f149 := pair_fact E (i := 4) (j := 6) rfl rfl c100 c101
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f149
                                    omega
                                  by_cases c150 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f151 := pair_fact E (i := 8) (j := 4) rfl rfl c92 c93
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f151
                                  omega
                                by_cases c152 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                swap
                                · omega
                                by_cases c153 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                swap
                                · -- branch
                                  by_cases c154 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c155 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c156 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                  swap
                                  · -- branch
                                    by_cases c157 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c158 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c159 : a0 + a2 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c160 : b0 + b2 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f161 := pair_fact E (i := 4) (j := 4) rfl rfl c157 c158
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f161
                                    by_cases c162 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c163 : 0 < b10
                                    swap
                                    · -- branch
                                      by_cases c164 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c165 : 0 < b10
                                      swap
                                      · -- branch
                                        by_cases c166 : 0 < a10
                                        swap
                                        · omega
                                        by_cases c167 : 0 < b0
                                        swap
                                        · -- branch
                                          by_cases c168 : 0 < a10
                                          swap
                                          · omega
                                          by_cases c169 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c170 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                                          swap
                                          · -- branch
                                            by_cases c171 : 0 < a10
                                            swap
                                            · omega
                                            by_cases c172 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c173 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                            swap
                                            · -- branch
                                              by_cases c174 : 0 < a10
                                              swap
                                              · omega
                                              by_cases c175 : 0 < b8
                                              swap
                                              · omega
                                              by_cases c176 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                              swap
                                              · omega
                                              by_cases c177 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                              swap
                                              · omega
                                              have f178 := pair_fact E (i := 10) (j := 8) rfl rfl c174 c175
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f178
                                              by_cases c179 : 0 < a8
                                              swap
                                              · omega
                                              by_cases c180 : 0 < b8
                                              swap
                                              · omega
                                              by_cases c181 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                              swap
                                              · omega
                                              by_cases c182 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                              swap
                                              · -- branch
                                                by_cases c183 : 0 < a8
                                                swap
                                                · omega
                                                by_cases c184 : 0 < b6
                                                swap
                                                · omega
                                                by_cases c185 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                swap
                                                · omega
                                                by_cases c186 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                swap
                                                · omega
                                                have f187 := pair_fact E (i := 8) (j := 6) rfl rfl c183 c184
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f187
                                                omega
                                              have f188 := pair_fact E (i := 8) (j := 8) rfl rfl c179 c180
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f188
                                              omega
                                            by_cases c189 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                            swap
                                            · omega
                                            have f190 := pair_fact E (i := 10) (j := 4) rfl rfl c171 c172
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f190
                                            omega
                                          by_cases c191 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                                          swap
                                          · omega
                                          have f192 := pair_fact E (i := 10) (j := 2) rfl rfl c168 c169
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f192
                                          omega
                                        by_cases c193 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                                        swap
                                        · omega
                                        by_cases c194 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                                        swap
                                        · omega
                                        have f195 := pair_fact E (i := 10) (j := 0) rfl rfl c166 c167
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f195
                                        omega
                                      by_cases c196 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c197 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f198 := pair_fact E (i := 8) (j := 10) rfl rfl c164 c165
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f198
                                      omega
                                    by_cases c199 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c200 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c201 : 0 < a6
                                      swap
                                      · -- branch
                                        by_cases c202 : 0 < a6
                                        swap
                                        · -- branch
                                          by_cases c203 : 0 < a6
                                          swap
                                          · -- branch
                                            by_cases c204 : 0 < a6
                                            swap
                                            · -- branch
                                              by_cases c205 : 0 < a6
                                              swap
                                              · -- branch
                                                by_cases c206 : 0 < a6
                                                swap
                                                · -- branch
                                                  by_cases c207 : 0 < a8
                                                  swap
                                                  · omega
                                                  by_cases c208 : 0 < b6
                                                  swap
                                                  · omega
                                                  by_cases c209 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                  swap
                                                  · omega
                                                  by_cases c210 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · omega
                                                  have f211 := pair_fact E (i := 8) (j := 6) rfl rfl c207 c208
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f211
                                                  by_cases c212 : 0 < a4
                                                  swap
                                                  · omega
                                                  by_cases c213 : 0 < b6
                                                  swap
                                                  · omega
                                                  by_cases c214 : a0 + a2 < b0 + b2 + b4 + b6
                                                  swap
                                                  · omega
                                                  by_cases c215 : b0 + b2 + b4 < a0 + a2 + a4
                                                  swap
                                                  · -- branch
                                                    by_cases c216 : 0 < a8
                                                    swap
                                                    · omega
                                                    by_cases c217 : 0 < b8
                                                    swap
                                                    · omega
                                                    by_cases c218 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                                    swap
                                                    · omega
                                                    by_cases c219 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                                    swap
                                                    · omega
                                                    have f220 := pair_fact E (i := 8) (j := 8) rfl rfl c216 c217
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f220
                                                    by_cases c221 : 0 < a8
                                                    swap
                                                    · omega
                                                    by_cases c222 : 0 < b10
                                                    swap
                                                    · omega
                                                    by_cases c223 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                                    swap
                                                    · omega
                                                    by_cases c224 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                                    swap
                                                    · -- branch
                                                      by_cases c225 : 0 < a10
                                                      swap
                                                      · omega
                                                      by_cases c226 : 0 < b8
                                                      swap
                                                      · omega
                                                      by_cases c227 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                                      swap
                                                      · omega
                                                      by_cases c228 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                                      swap
                                                      · omega
                                                      have f229 := pair_fact E (i := 10) (j := 8) rfl rfl c225 c226
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f229
                                                      omega
                                                    have f230 := pair_fact E (i := 8) (j := 10) rfl rfl c221 c222
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f230
                                                    omega
                                                  have f231 := pair_fact E (i := 4) (j := 6) rfl rfl c212 c213
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f231
                                                  omega
                                                by_cases c232 : 0 < b10
                                                swap
                                                · omega
                                                by_cases c233 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                                swap
                                                · omega
                                                by_cases c234 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                                swap
                                                · omega
                                                have f235 := pair_fact E (i := 6) (j := 10) rfl rfl c206 c232
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f235
                                                omega
                                              by_cases c236 : 0 < b8
                                              swap
                                              · omega
                                              by_cases c237 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                              swap
                                              · omega
                                              by_cases c238 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f239 := pair_fact E (i := 6) (j := 8) rfl rfl c205 c236
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f239
                                              omega
                                            by_cases c240 : 0 < b6
                                            swap
                                            · omega
                                            by_cases c241 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c242 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f243 := pair_fact E (i := 6) (j := 6) rfl rfl c204 c240
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f243
                                            omega
                                          by_cases c244 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c245 : a0 + a2 + a4 < b0 + b2 + b4
                                          swap
                                          · omega
                                          by_cases c246 : b0 + b2 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f247 := pair_fact E (i := 6) (j := 4) rfl rfl c203 c244
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f247
                                          omega
                                        by_cases c248 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c249 : a0 + a2 + a4 < b0 + b2
                                        swap
                                        · omega
                                        by_cases c250 : b0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f251 := pair_fact E (i := 6) (j := 2) rfl rfl c202 c248
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f251
                                        omega
                                      by_cases c252 : 0 < b0
                                      swap
                                      · -- branch
                                        by_cases c253 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c254 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c255 : a0 + a2 + a4 < b0 + b2
                                        swap
                                        · -- branch
                                          by_cases c256 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c257 : 0 < b10
                                          swap
                                          · omega
                                          by_cases c258 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                          swap
                                          · omega
                                          by_cases c259 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                          swap
                                          · -- branch
                                            by_cases c260 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c261 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c262 : a0 + a2 + a4 < b0 + b2 + b4
                                            swap
                                            · -- branch
                                              by_cases c263 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c264 : 0 < b8
                                              swap
                                              · omega
                                              by_cases c265 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                              swap
                                              · omega
                                              by_cases c266 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                              swap
                                              · -- branch
                                                by_cases c267 : 0 < a6
                                                swap
                                                · omega
                                                by_cases c268 : 0 < b6
                                                swap
                                                · omega
                                                by_cases c269 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                                swap
                                                · omega
                                                by_cases c270 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                                swap
                                                · omega
                                                have f271 := pair_fact E (i := 6) (j := 6) rfl rfl c267 c268
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f271
                                                by_cases c272 : 0 < a4
                                                swap
                                                · omega
                                                by_cases c273 : 0 < b6
                                                swap
                                                · omega
                                                by_cases c274 : a0 + a2 < b0 + b2 + b4 + b6
                                                swap
                                                · omega
                                                by_cases c275 : b0 + b2 + b4 < a0 + a2 + a4
                                                swap
                                                · -- branch
                                                  by_cases c276 : 0 < a8
                                                  swap
                                                  · omega
                                                  by_cases c277 : 0 < b6
                                                  swap
                                                  · omega
                                                  by_cases c278 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                  swap
                                                  · omega
                                                  by_cases c279 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · omega
                                                  have f280 := pair_fact E (i := 8) (j := 6) rfl rfl c276 c277
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f280
                                                  by_cases c281 : 0 < a8
                                                  swap
                                                  · omega
                                                  by_cases c282 : 0 < b8
                                                  swap
                                                  · omega
                                                  by_cases c283 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                                  swap
                                                  · omega
                                                  by_cases c284 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · omega
                                                  have f285 := pair_fact E (i := 8) (j := 8) rfl rfl c281 c282
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f285
                                                  omega
                                                have f286 := pair_fact E (i := 4) (j := 6) rfl rfl c272 c273
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f286
                                                omega
                                              have f287 := pair_fact E (i := 6) (j := 8) rfl rfl c263 c264
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f287
                                              by_cases c288 : 0 < a8
                                              swap
                                              · omega
                                              by_cases c289 : 0 < b10
                                              swap
                                              · omega
                                              by_cases c290 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                              swap
                                              · omega
                                              by_cases c291 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                              swap
                                              · -- branch
                                                by_cases c292 : 0 < a10
                                                swap
                                                · omega
                                                by_cases c293 : 0 < b8
                                                swap
                                                · omega
                                                by_cases c294 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                                swap
                                                · omega
                                                by_cases c295 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                                swap
                                                · omega
                                                have f296 := pair_fact E (i := 10) (j := 8) rfl rfl c292 c293
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f296
                                                omega
                                              have f297 := pair_fact E (i := 8) (j := 10) rfl rfl c288 c289
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f297
                                              omega
                                            by_cases c298 : b0 + b2 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f299 := pair_fact E (i := 6) (j := 4) rfl rfl c260 c261
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f299
                                            by_cases c300 : 0 < a8
                                            swap
                                            · omega
                                            by_cases c301 : 0 < b8
                                            swap
                                            · omega
                                            by_cases c302 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                            swap
                                            · omega
                                            by_cases c303 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f304 := pair_fact E (i := 8) (j := 8) rfl rfl c300 c301
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f304
                                            omega
                                          have f305 := pair_fact E (i := 6) (j := 10) rfl rfl c256 c257
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f305
                                          omega
                                        by_cases c306 : b0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f307 := pair_fact E (i := 6) (j := 2) rfl rfl c253 c254
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f307
                                        omega
                                      by_cases c308 : a0 + a2 + a4 < 0 + b0
                                      swap
                                      · omega
                                      by_cases c309 : 0 < a0 + a2 + a4 + a6
                                      swap
                                      · omega
                                      have f310 := pair_fact E (i := 6) (j := 0) rfl rfl c201 c252
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f310
                                      omega
                                    have f311 := pair_fact E (i := 4) (j := 10) rfl rfl c162 c163
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f311
                                    omega
                                  by_cases c312 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f313 := pair_fact E (i := 8) (j := 4) rfl rfl c154 c155
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f313
                                  omega
                                have f314 := pair_fact E (i := 4) (j := 8) rfl rfl c90 c91
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f314
                                omega
                              by_cases c315 : a0 + a2 < 0 + b0
                              swap
                              · omega
                              by_cases c316 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f317 := pair_fact E (i := 4) (j := 0) rfl rfl c78 c84
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f317
                              omega
                            by_cases c318 : a0 + a2 + a4 + a6 < 0 + b0
                            swap
                            · -- branch
                              by_cases c319 : 0 < a4
                              swap
                              · omega
                              by_cases c320 : 0 < b0
                              swap
                              · omega
                              by_cases c321 : a0 + a2 < 0 + b0
                              swap
                              · omega
                              by_cases c322 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f323 := pair_fact E (i := 4) (j := 0) rfl rfl c319 c320
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f323
                              by_cases c324 : 0 < a4
                              swap
                              · omega
                              by_cases c325 : 0 < b2
                              swap
                              · omega
                              by_cases c326 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c327 : b0 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c328 : 0 < a8
                                swap
                                · omega
                                by_cases c329 : 0 < b4
                                swap
                                · omega
                                by_cases c330 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c331 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f332 := pair_fact E (i := 8) (j := 4) rfl rfl c328 c329
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f332
                                omega
                              have f333 := pair_fact E (i := 4) (j := 2) rfl rfl c324 c325
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f333
                              omega
                            by_cases c334 : 0 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f335 := pair_fact E (i := 8) (j := 0) rfl rfl c76 c77
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f335
                            omega
                          by_cases c336 : b0 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f337 := pair_fact E (i := 8) (j := 2) rfl rfl c13 c74
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f337
                          omega
                        by_cases c338 : 0 < b10
                        swap
                        · omega
                        by_cases c339 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c340 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                        swap
                        · omega
                        have f341 := pair_fact E (i := 2) (j := 10) rfl rfl c12 c338
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f341
                        omega
                      by_cases c342 : 0 < b8
                      swap
                      · omega
                      by_cases c343 : a0 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c344 : b0 + b2 + b4 + b6 < a0 + a2
                      swap
                      · omega
                      have f345 := pair_fact E (i := 2) (j := 8) rfl rfl c11 c342
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f345
                      omega
                    by_cases c346 : 0 < b6
                    swap
                    · omega
                    by_cases c347 : a0 < b0 + b2 + b4 + b6
                    swap
                    · omega
                    by_cases c348 : b0 + b2 + b4 < a0 + a2
                    swap
                    · omega
                    have f349 := pair_fact E (i := 2) (j := 6) rfl rfl c10 c346
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f349
                    omega
                  by_cases c350 : 0 < b4
                  swap
                  · omega
                  by_cases c351 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c352 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f353 := pair_fact E (i := 2) (j := 4) rfl rfl c9 c350
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f353
                  omega
                by_cases c354 : 0 < b2
                swap
                · omega
                by_cases c355 : a0 < b0 + b2
                swap
                · omega
                by_cases c356 : b0 < a0 + a2
                swap
                · omega
                have f357 := pair_fact E (i := 2) (j := 2) rfl rfl c8 c354
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f357
                omega
              by_cases c358 : 0 < b0
              swap
              · -- branch
                by_cases c359 : 0 < a2
                swap
                · omega
                by_cases c360 : 0 < b2
                swap
                · -- branch
                  by_cases c361 : 0 < a2
                  swap
                  · omega
                  by_cases c362 : 0 < b4
                  swap
                  · -- branch
                    by_cases c363 : 0 < a4
                    swap
                    · omega
                    by_cases c364 : 0 < b8
                    swap
                    · omega
                    by_cases c365 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c366 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                    swap
                    · omega
                    have f367 := pair_fact E (i := 4) (j := 8) rfl rfl c363 c364
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f367
                    omega
                  by_cases c368 : a0 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c369 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f370 := pair_fact E (i := 2) (j := 4) rfl rfl c361 c362
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f370
                  by_cases c371 : 0 < a2
                  swap
                  · omega
                  by_cases c372 : 0 < b8
                  swap
                  · -- branch
                    by_cases c373 : 0 < a8
                    swap
                    · omega
                    by_cases c374 : 0 < b0
                    swap
                    · -- branch
                      by_cases c375 : 0 < a8
                      swap
                      · omega
                      by_cases c376 : 0 < b2
                      swap
                      · -- branch
                        by_cases c377 : 0 < a8
                        swap
                        · omega
                        by_cases c378 : 0 < b4
                        swap
                        · omega
                        by_cases c379 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                        swap
                        · -- branch
                          by_cases c380 : 0 < a2
                          swap
                          · omega
                          by_cases c381 : 0 < b6
                          swap
                          · omega
                          by_cases c382 : a0 < b0 + b2 + b4 + b6
                          swap
                          · omega
                          by_cases c383 : b0 + b2 + b4 < a0 + a2
                          swap
                          · -- branch
                            by_cases c384 : 0 < a2
                            swap
                            · omega
                            by_cases c385 : 0 < b10
                            swap
                            · omega
                            by_cases c386 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c387 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                            swap
                            · -- branch
                              by_cases c388 : 0 < a4
                              swap
                              · omega
                              by_cases c389 : 0 < b0
                              swap
                              · -- branch
                                by_cases c390 : 0 < a4
                                swap
                                · omega
                                by_cases c391 : 0 < b2
                                swap
                                · -- branch
                                  by_cases c392 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c393 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c394 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c395 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f396 := pair_fact E (i := 4) (j := 4) rfl rfl c392 c393
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f396
                                  by_cases c397 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c398 : 0 < b6
                                  swap
                                  · omega
                                  by_cases c399 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c400 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c401 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c402 : 0 < b8
                                    swap
                                    · -- branch
                                      by_cases c403 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c404 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c405 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c406 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c407 : 0 < a6
                                        swap
                                        · -- branch
                                          by_cases c408 : 0 < a6
                                          swap
                                          · -- branch
                                            by_cases c409 : 0 < a6
                                            swap
                                            · -- branch
                                              by_cases c410 : 0 < a6
                                              swap
                                              · -- branch
                                                by_cases c411 : 0 < a6
                                                swap
                                                · -- branch
                                                  by_cases c412 : 0 < a6
                                                  swap
                                                  · -- branch
                                                    by_cases c413 : 0 < a8
                                                    swap
                                                    · omega
                                                    by_cases c414 : 0 < b6
                                                    swap
                                                    · omega
                                                    by_cases c415 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                    swap
                                                    · omega
                                                    by_cases c416 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                    swap
                                                    · omega
                                                    have f417 := pair_fact E (i := 8) (j := 6) rfl rfl c413 c414
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f417
                                                    by_cases c418 : 0 < a8
                                                    swap
                                                    · omega
                                                    by_cases c419 : 0 < b10
                                                    swap
                                                    · omega
                                                    by_cases c420 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                                    swap
                                                    · omega
                                                    by_cases c421 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                                    swap
                                                    · omega
                                                    have f422 := pair_fact E (i := 8) (j := 10) rfl rfl c418 c419
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f422
                                                    omega
                                                  by_cases c423 : 0 < b10
                                                  swap
                                                  · omega
                                                  by_cases c424 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                                  swap
                                                  · omega
                                                  by_cases c425 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
                                                  swap
                                                  · omega
                                                  have f426 := pair_fact E (i := 6) (j := 10) rfl rfl c412 c423
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f426
                                                  omega
                                                by_cases c427 : 0 < b8
                                                swap
                                                · omega
                                                by_cases c428 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                                swap
                                                · omega
                                                by_cases c429 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                                swap
                                                · omega
                                                have f430 := pair_fact E (i := 6) (j := 8) rfl rfl c411 c427
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f430
                                                omega
                                              by_cases c431 : 0 < b6
                                              swap
                                              · omega
                                              by_cases c432 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                              swap
                                              · omega
                                              by_cases c433 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f434 := pair_fact E (i := 6) (j := 6) rfl rfl c410 c431
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f434
                                              omega
                                            by_cases c435 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c436 : a0 + a2 + a4 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c437 : b0 + b2 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f438 := pair_fact E (i := 6) (j := 4) rfl rfl c409 c435
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f438
                                            omega
                                          by_cases c439 : 0 < b2
                                          swap
                                          · omega
                                          by_cases c440 : a0 + a2 + a4 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c441 : b0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f442 := pair_fact E (i := 6) (j := 2) rfl rfl c408 c439
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f442
                                          omega
                                        by_cases c443 : 0 < b0
                                        swap
                                        · omega
                                        by_cases c444 : a0 + a2 + a4 < 0 + b0
                                        swap
                                        · omega
                                        by_cases c445 : 0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f446 := pair_fact E (i := 6) (j := 0) rfl rfl c407 c443
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f446
                                        omega
                                      have f447 := pair_fact E (i := 4) (j := 10) rfl rfl c403 c404
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f447
                                      omega
                                    by_cases c448 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c449 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f450 := pair_fact E (i := 4) (j := 8) rfl rfl c401 c402
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f450
                                    omega
                                  have f451 := pair_fact E (i := 4) (j := 6) rfl rfl c397 c398
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f451
                                  omega
                                by_cases c452 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c453 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f454 := pair_fact E (i := 4) (j := 2) rfl rfl c390 c391
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f454
                                omega
                              by_cases c455 : a0 + a2 < 0 + b0
                              swap
                              · omega
                              by_cases c456 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f457 := pair_fact E (i := 4) (j := 0) rfl rfl c388 c389
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f457
                              omega
                            have f458 := pair_fact E (i := 2) (j := 10) rfl rfl c384 c385
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f458
                            omega
                          have f459 := pair_fact E (i := 2) (j := 6) rfl rfl c380 c381
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f459
                          omega
                        by_cases c460 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f461 := pair_fact E (i := 8) (j := 4) rfl rfl c377 c378
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f461
                        omega
                      by_cases c462 : a0 + a2 + a4 + a6 < b0 + b2
                      swap
                      · omega
                      by_cases c463 : b0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f464 := pair_fact E (i := 8) (j := 2) rfl rfl c375 c376
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f464
                      omega
                    by_cases c465 : a0 + a2 + a4 + a6 < 0 + b0
                    swap
                    · omega
                    by_cases c466 : 0 < a0 + a2 + a4 + a6 + a8
                    swap
                    · omega
                    have f467 := pair_fact E (i := 8) (j := 0) rfl rfl c373 c374
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f467
                    omega
                  by_cases c468 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c469 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · -- branch
                    by_cases c470 : 0 < a2
                    swap
                    · omega
                    by_cases c471 : 0 < b10
                    swap
                    · -- branch
                      by_cases c472 : 0 < a10
                      swap
                      · omega
                      by_cases c473 : 0 < b0
                      swap
                      · -- branch
                        by_cases c474 : 0 < a10
                        swap
                        · omega
                        by_cases c475 : 0 < b2
                        swap
                        · -- branch
                          by_cases c476 : 0 < a10
                          swap
                          · omega
                          by_cases c477 : 0 < b4
                          swap
                          · omega
                          by_cases c478 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                          swap
                          · -- branch
                            by_cases c479 : 0 < a10
                            swap
                            · omega
                            by_cases c480 : 0 < b8
                            swap
                            · omega
                            by_cases c481 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c482 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f483 := pair_fact E (i := 10) (j := 8) rfl rfl c479 c480
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f483
                            by_cases c484 : 0 < a10
                            swap
                            · omega
                            by_cases c485 : 0 < b10
                            swap
                            · -- branch
                              by_cases c486 : 0 < a2
                              swap
                              · omega
                              by_cases c487 : 0 < b6
                              swap
                              · -- branch
                                by_cases c488 : 0 < a6
                                swap
                                · omega
                                by_cases c489 : 0 < b0
                                swap
                                · -- branch
                                  by_cases c490 : 0 < a6
                                  swap
                                  · omega
                                  by_cases c491 : 0 < b2
                                  swap
                                  · -- branch
                                    by_cases c492 : 0 < a6
                                    swap
                                    · omega
                                    by_cases c493 : 0 < b6
                                    swap
                                    · -- branch
                                      by_cases c494 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c495 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c496 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c497 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                      swap
                                      · -- branch
                                        by_cases c498 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c499 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c500 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c501 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f502 := pair_fact E (i := 8) (j := 4) rfl rfl c498 c499
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f502
                                        omega
                                      have f503 := pair_fact E (i := 6) (j := 8) rfl rfl c494 c495
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f503
                                      omega
                                    by_cases c504 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c505 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                    swap
                                    · omega
                                    have f506 := pair_fact E (i := 6) (j := 6) rfl rfl c492 c493
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f506
                                    omega
                                  by_cases c507 : a0 + a2 + a4 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c508 : b0 < a0 + a2 + a4 + a6
                                  swap
                                  · omega
                                  have f509 := pair_fact E (i := 6) (j := 2) rfl rfl c490 c491
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f509
                                  omega
                                by_cases c510 : a0 + a2 + a4 < 0 + b0
                                swap
                                · omega
                                by_cases c511 : 0 < a0 + a2 + a4 + a6
                                swap
                                · omega
                                have f512 := pair_fact E (i := 6) (j := 0) rfl rfl c488 c489
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f512
                                omega
                              by_cases c513 : a0 < b0 + b2 + b4 + b6
                              swap
                              · omega
                              by_cases c514 : b0 + b2 + b4 < a0 + a2
                              swap
                              · -- branch
                                by_cases c515 : 0 < a10
                                swap
                                · omega
                                by_cases c516 : 0 < b6
                                swap
                                · omega
                                by_cases c517 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                swap
                                · -- branch
                                  by_cases c518 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c519 : 0 < b0
                                  swap
                                  · -- branch
                                    by_cases c520 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c521 : 0 < b2
                                    swap
                                    · -- branch
                                      by_cases c522 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c523 : 0 < b6
                                      swap
                                      · omega
                                      by_cases c524 : a0 + a2 < b0 + b2 + b4 + b6
                                      swap
                                      · omega
                                      by_cases c525 : b0 + b2 + b4 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c526 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c527 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c528 : a0 + a2 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c529 : b0 + b2 < a0 + a2 + a4
                                        swap
                                        · omega
                                        have f530 := pair_fact E (i := 4) (j := 4) rfl rfl c526 c527
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f530
                                        by_cases c531 : 0 < a4
                                        swap
                                        · omega
                                        by_cases c532 : 0 < b8
                                        swap
                                        · omega
                                        by_cases c533 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                        swap
                                        · omega
                                        by_cases c534 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                        swap
                                        · -- branch
                                          by_cases c535 : 0 < a4
                                          swap
                                          · omega
                                          by_cases c536 : 0 < b10
                                          swap
                                          · -- branch
                                            by_cases c537 : 0 < a8
                                            swap
                                            · omega
                                            by_cases c538 : 0 < b0
                                            swap
                                            · -- branch
                                              by_cases c539 : 0 < a8
                                              swap
                                              · omega
                                              by_cases c540 : 0 < b2
                                              swap
                                              · -- branch
                                                by_cases c541 : 0 < a8
                                                swap
                                                · omega
                                                by_cases c542 : 0 < b4
                                                swap
                                                · omega
                                                by_cases c543 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                                swap
                                                · -- branch
                                                  by_cases c544 : 0 < a8
                                                  swap
                                                  · omega
                                                  by_cases c545 : 0 < b6
                                                  swap
                                                  · omega
                                                  by_cases c546 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                  swap
                                                  · -- branch
                                                    by_cases c547 : 0 < a6
                                                    swap
                                                    · omega
                                                    by_cases c548 : 0 < b6
                                                    swap
                                                    · omega
                                                    by_cases c549 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                                    swap
                                                    · omega
                                                    by_cases c550 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                                    swap
                                                    · omega
                                                    have f551 := pair_fact E (i := 6) (j := 6) rfl rfl c547 c548
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f551
                                                    omega
                                                  by_cases c552 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · omega
                                                  have f553 := pair_fact E (i := 8) (j := 6) rfl rfl c544 c545
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f553
                                                  omega
                                                by_cases c554 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                                swap
                                                · omega
                                                have f555 := pair_fact E (i := 8) (j := 4) rfl rfl c541 c542
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f555
                                                omega
                                              by_cases c556 : a0 + a2 + a4 + a6 < b0 + b2
                                              swap
                                              · omega
                                              by_cases c557 : b0 < a0 + a2 + a4 + a6 + a8
                                              swap
                                              · omega
                                              have f558 := pair_fact E (i := 8) (j := 2) rfl rfl c539 c540
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f558
                                              omega
                                            by_cases c559 : a0 + a2 + a4 + a6 < 0 + b0
                                            swap
                                            · omega
                                            by_cases c560 : 0 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f561 := pair_fact E (i := 8) (j := 0) rfl rfl c537 c538
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f561
                                            omega
                                          by_cases c562 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                          swap
                                          · omega
                                          by_cases c563 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                          swap
                                          · omega
                                          have f564 := pair_fact E (i := 4) (j := 10) rfl rfl c535 c536
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f564
                                          omega
                                        have f565 := pair_fact E (i := 4) (j := 8) rfl rfl c531 c532
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f565
                                        omega
                                      have f566 := pair_fact E (i := 4) (j := 6) rfl rfl c522 c523
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f566
                                      omega
                                    by_cases c567 : a0 + a2 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c568 : b0 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f569 := pair_fact E (i := 4) (j := 2) rfl rfl c520 c521
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f569
                                    omega
                                  by_cases c570 : a0 + a2 < 0 + b0
                                  swap
                                  · omega
                                  by_cases c571 : 0 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f572 := pair_fact E (i := 4) (j := 0) rfl rfl c518 c519
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f572
                                  omega
                                by_cases c573 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f574 := pair_fact E (i := 10) (j := 6) rfl rfl c515 c516
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f574
                                omega
                              have f575 := pair_fact E (i := 2) (j := 6) rfl rfl c486 c487
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f575
                              omega
                            by_cases c576 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c577 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f578 := pair_fact E (i := 10) (j := 10) rfl rfl c484 c485
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f578
                            omega
                          by_cases c579 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                          swap
                          · omega
                          have f580 := pair_fact E (i := 10) (j := 4) rfl rfl c476 c477
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f580
                          omega
                        by_cases c581 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                        swap
                        · omega
                        by_cases c582 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                        swap
                        · omega
                        have f583 := pair_fact E (i := 10) (j := 2) rfl rfl c474 c475
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f583
                        omega
                      by_cases c584 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                      swap
                      · omega
                      by_cases c585 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f586 := pair_fact E (i := 10) (j := 0) rfl rfl c472 c473
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f586
                      omega
                    by_cases c587 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c588 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · -- branch
                      by_cases c589 : 0 < a4
                      swap
                      · -- branch
                        by_cases c590 : 0 < a8
                        swap
                        · omega
                        by_cases c591 : 0 < b4
                        swap
                        · omega
                        by_cases c592 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c593 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f594 := pair_fact E (i := 8) (j := 4) rfl rfl c590 c591
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f594
                        omega
                      by_cases c595 : 0 < b0
                      swap
                      · -- branch
                        by_cases c596 : 0 < a4
                        swap
                        · omega
                        by_cases c597 : 0 < b2
                        swap
                        · -- branch
                          by_cases c598 : 0 < a4
                          swap
                          · omega
                          by_cases c599 : 0 < b8
                          swap
                          · omega
                          by_cases c600 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                          swap
                          · omega
                          by_cases c601 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                          swap
                          · -- branch
                            by_cases c602 : 0 < a4
                            swap
                            · omega
                            by_cases c603 : 0 < b4
                            swap
                            · omega
                            by_cases c604 : a0 + a2 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c605 : b0 + b2 < a0 + a2 + a4
                            swap
                            · omega
                            have f606 := pair_fact E (i := 4) (j := 4) rfl rfl c602 c603
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f606
                            by_cases c607 : 0 < a4
                            swap
                            · omega
                            by_cases c608 : 0 < b10
                            swap
                            · omega
                            by_cases c609 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c610 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c611 : 0 < a8
                              swap
                              · omega
                              by_cases c612 : 0 < b0
                              swap
                              · -- branch
                                by_cases c613 : 0 < a8
                                swap
                                · omega
                                by_cases c614 : 0 < b2
                                swap
                                · -- branch
                                  by_cases c615 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c616 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c617 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                  swap
                                  · -- branch
                                    by_cases c618 : 0 < a2
                                    swap
                                    · omega
                                    by_cases c619 : 0 < b6
                                    swap
                                    · -- branch
                                      by_cases c620 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c621 : 0 < b6
                                      swap
                                      · -- branch
                                        by_cases c622 : 0 < a6
                                        swap
                                        · omega
                                        by_cases c623 : 0 < b0
                                        swap
                                        · -- branch
                                          by_cases c624 : 0 < a6
                                          swap
                                          · omega
                                          by_cases c625 : 0 < b2
                                          swap
                                          · -- branch
                                            by_cases c626 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c627 : 0 < b6
                                            swap
                                            · -- branch
                                              by_cases c628 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c629 : 0 < b8
                                              swap
                                              · omega
                                              by_cases c630 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                              swap
                                              · omega
                                              by_cases c631 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f632 := pair_fact E (i := 6) (j := 8) rfl rfl c628 c629
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f632
                                              by_cases c633 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c634 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c635 : a0 + a2 + a4 < b0 + b2 + b4
                                              swap
                                              · -- branch
                                                by_cases c636 : 0 < a6
                                                swap
                                                · omega
                                                by_cases c637 : 0 < b10
                                                swap
                                                · omega
                                                by_cases c638 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
                                                swap
                                                · omega
                                                by_cases c639 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
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
                                                    by_cases c643 : 0 < b10
                                                    swap
                                                    · omega
                                                    by_cases c644 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                                    swap
                                                    · omega
                                                    by_cases c645 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                                    swap
                                                    · -- branch
                                                      by_cases c646 : 0 < a10
                                                      swap
                                                      · omega
                                                      by_cases c647 : 0 < b8
                                                      swap
                                                      · omega
                                                      by_cases c648 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                                      swap
                                                      · omega
                                                      by_cases c649 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                                      swap
                                                      · omega
                                                      have f650 := pair_fact E (i := 10) (j := 8) rfl rfl c646 c647
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f650
                                                      omega
                                                    have f651 := pair_fact E (i := 8) (j := 10) rfl rfl c642 c643
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f651
                                                    omega
                                                  by_cases c652 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                  swap
                                                  · omega
                                                  by_cases c653 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · omega
                                                  have f654 := pair_fact E (i := 8) (j := 6) rfl rfl c640 c641
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f654
                                                  omega
                                                have f655 := pair_fact E (i := 6) (j := 10) rfl rfl c636 c637
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f655
                                                omega
                                              by_cases c656 : b0 + b2 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f657 := pair_fact E (i := 6) (j := 4) rfl rfl c633 c634
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f657
                                              omega
                                            by_cases c658 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                                            swap
                                            · omega
                                            by_cases c659 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f660 := pair_fact E (i := 6) (j := 6) rfl rfl c626 c627
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f660
                                            omega
                                          by_cases c661 : a0 + a2 + a4 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c662 : b0 < a0 + a2 + a4 + a6
                                          swap
                                          · omega
                                          have f663 := pair_fact E (i := 6) (j := 2) rfl rfl c624 c625
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f663
                                          omega
                                        by_cases c664 : a0 + a2 + a4 < 0 + b0
                                        swap
                                        · omega
                                        by_cases c665 : 0 < a0 + a2 + a4 + a6
                                        swap
                                        · omega
                                        have f666 := pair_fact E (i := 6) (j := 0) rfl rfl c622 c623
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f666
                                        omega
                                      by_cases c667 : a0 + a2 < b0 + b2 + b4 + b6
                                      swap
                                      · omega
                                      by_cases c668 : b0 + b2 + b4 < a0 + a2 + a4
                                      swap
                                      · omega
                                      have f669 := pair_fact E (i := 4) (j := 6) rfl rfl c620 c621
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f669
                                      omega
                                    by_cases c670 : a0 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c671 : b0 + b2 + b4 < a0 + a2
                                    swap
                                    · -- branch
                                      by_cases c672 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c673 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c674 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c675 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f676 := pair_fact E (i := 8) (j := 8) rfl rfl c672 c673
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f676
                                      by_cases c677 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c678 : 0 < b6
                                      swap
                                      · omega
                                      by_cases c679 : a0 + a2 < b0 + b2 + b4 + b6
                                      swap
                                      · omega
                                      by_cases c680 : b0 + b2 + b4 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c681 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c682 : 0 < b10
                                        swap
                                        · omega
                                        by_cases c683 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                        swap
                                        · omega
                                        by_cases c684 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · -- branch
                                          by_cases c685 : 0 < a10
                                          swap
                                          · omega
                                          by_cases c686 : 0 < b8
                                          swap
                                          · omega
                                          by_cases c687 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                          swap
                                          · omega
                                          by_cases c688 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                          swap
                                          · omega
                                          have f689 := pair_fact E (i := 10) (j := 8) rfl rfl c685 c686
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f689
                                          omega
                                        have f690 := pair_fact E (i := 8) (j := 10) rfl rfl c681 c682
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f690
                                        omega
                                      have f691 := pair_fact E (i := 4) (j := 6) rfl rfl c677 c678
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f691
                                      omega
                                    have f692 := pair_fact E (i := 2) (j := 6) rfl rfl c618 c619
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f692
                                    omega
                                  by_cases c693 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f694 := pair_fact E (i := 8) (j := 4) rfl rfl c615 c616
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
                                have f697 := pair_fact E (i := 8) (j := 2) rfl rfl c613 c614
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f697
                                omega
                              by_cases c698 : a0 + a2 + a4 + a6 < 0 + b0
                              swap
                              · omega
                              by_cases c699 : 0 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f700 := pair_fact E (i := 8) (j := 0) rfl rfl c611 c612
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f700
                              omega
                            have f701 := pair_fact E (i := 4) (j := 10) rfl rfl c607 c608
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f701
                            omega
                          have f702 := pair_fact E (i := 4) (j := 8) rfl rfl c598 c599
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f702
                          omega
                        by_cases c703 : a0 + a2 < b0 + b2
                        swap
                        · omega
                        by_cases c704 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f705 := pair_fact E (i := 4) (j := 2) rfl rfl c596 c597
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f705
                        omega
                      by_cases c706 : a0 + a2 < 0 + b0
                      swap
                      · omega
                      by_cases c707 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f708 := pair_fact E (i := 4) (j := 0) rfl rfl c589 c595
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f708
                      omega
                    have f709 := pair_fact E (i := 2) (j := 10) rfl rfl c470 c471
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f709
                    omega
                  have f710 := pair_fact E (i := 2) (j := 8) rfl rfl c371 c372
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f710
                  omega
                by_cases c711 : a0 < b0 + b2
                swap
                · omega
                by_cases c712 : b0 < a0 + a2
                swap
                · omega
                have f713 := pair_fact E (i := 2) (j := 2) rfl rfl c359 c360
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f713
                by_cases c714 : 0 < a2
                swap
                · omega
                by_cases c715 : 0 < b8
                swap
                · -- branch
                  by_cases c716 : 0 < a8
                  swap
                  · omega
                  by_cases c717 : 0 < b0
                  swap
                  · -- branch
                    by_cases c718 : 0 < a8
                    swap
                    · omega
                    by_cases c719 : 0 < b2
                    swap
                    · omega
                    by_cases c720 : a0 + a2 + a4 + a6 < b0 + b2
                    swap
                    · -- branch
                      by_cases c721 : 0 < a8
                      swap
                      · omega
                      by_cases c722 : 0 < b4
                      swap
                      · omega
                      by_cases c723 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                      swap
                      · -- branch
                        by_cases c724 : 0 < a2
                        swap
                        · omega
                        by_cases c725 : 0 < b6
                        swap
                        · omega
                        by_cases c726 : a0 < b0 + b2 + b4 + b6
                        swap
                        · omega
                        by_cases c727 : b0 + b2 + b4 < a0 + a2
                        swap
                        · -- branch
                          by_cases c728 : 0 < a2
                          swap
                          · omega
                          by_cases c729 : 0 < b10
                          swap
                          · omega
                          by_cases c730 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c731 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · -- branch
                            by_cases c732 : 0 < a4
                            swap
                            · omega
                            by_cases c733 : 0 < b0
                            swap
                            · -- branch
                              by_cases c734 : 0 < a4
                              swap
                              · omega
                              by_cases c735 : 0 < b4
                              swap
                              · omega
                              by_cases c736 : a0 + a2 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c737 : b0 + b2 < a0 + a2 + a4
                              swap
                              · omega
                              have f738 := pair_fact E (i := 4) (j := 4) rfl rfl c734 c735
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f738
                              by_cases c739 : 0 < a2
                              swap
                              · omega
                              by_cases c740 : 0 < b4
                              swap
                              · omega
                              by_cases c741 : a0 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c742 : b0 + b2 < a0 + a2
                              swap
                              · -- branch
                                by_cases c743 : 0 < a4
                                swap
                                · omega
                                by_cases c744 : 0 < b2
                                swap
                                · omega
                                by_cases c745 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c746 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f747 := pair_fact E (i := 4) (j := 2) rfl rfl c743 c744
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f747
                                omega
                              have f748 := pair_fact E (i := 2) (j := 4) rfl rfl c739 c740
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f748
                              omega
                            by_cases c749 : a0 + a2 < 0 + b0
                            swap
                            · omega
                            by_cases c750 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f751 := pair_fact E (i := 4) (j := 0) rfl rfl c732 c733
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f751
                            omega
                          have f752 := pair_fact E (i := 2) (j := 10) rfl rfl c728 c729
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f752
                          omega
                        have f753 := pair_fact E (i := 2) (j := 6) rfl rfl c724 c725
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f753
                        omega
                      by_cases c754 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f755 := pair_fact E (i := 8) (j := 4) rfl rfl c721 c722
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f755
                      omega
                    by_cases c756 : b0 < a0 + a2 + a4 + a6 + a8
                    swap
                    · omega
                    have f757 := pair_fact E (i := 8) (j := 2) rfl rfl c718 c719
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f757
                    omega
                  by_cases c758 : a0 + a2 + a4 + a6 < 0 + b0
                  swap
                  · omega
                  by_cases c759 : 0 < a0 + a2 + a4 + a6 + a8
                  swap
                  · omega
                  have f760 := pair_fact E (i := 8) (j := 0) rfl rfl c716 c717
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f760
                  omega
                by_cases c761 : a0 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c762 : b0 + b2 + b4 + b6 < a0 + a2
                swap
                · -- branch
                  by_cases c763 : 0 < a2
                  swap
                  · omega
                  by_cases c764 : 0 < b10
                  swap
                  · -- branch
                    by_cases c765 : 0 < a10
                    swap
                    · omega
                    by_cases c766 : 0 < b0
                    swap
                    · -- branch
                      by_cases c767 : 0 < a10
                      swap
                      · omega
                      by_cases c768 : 0 < b2
                      swap
                      · omega
                      by_cases c769 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                      swap
                      · -- branch
                        by_cases c770 : 0 < a10
                        swap
                        · omega
                        by_cases c771 : 0 < b4
                        swap
                        · omega
                        by_cases c772 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                        swap
                        · -- branch
                          by_cases c773 : 0 < a4
                          swap
                          · omega
                          by_cases c774 : 0 < b0
                          swap
                          · -- branch
                            by_cases c775 : 0 < a4
                            swap
                            · omega
                            by_cases c776 : 0 < b4
                            swap
                            · omega
                            by_cases c777 : a0 + a2 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c778 : b0 + b2 < a0 + a2 + a4
                            swap
                            · omega
                            have f779 := pair_fact E (i := 4) (j := 4) rfl rfl c775 c776
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f779
                            by_cases c780 : 0 < a2
                            swap
                            · omega
                            by_cases c781 : 0 < b4
                            swap
                            · omega
                            by_cases c782 : a0 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c783 : b0 + b2 < a0 + a2
                            swap
                            · -- branch
                              by_cases c784 : 0 < a4
                              swap
                              · omega
                              by_cases c785 : 0 < b2
                              swap
                              · omega
                              by_cases c786 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c787 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f788 := pair_fact E (i := 4) (j := 2) rfl rfl c784 c785
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f788
                              omega
                            have f789 := pair_fact E (i := 2) (j := 4) rfl rfl c780 c781
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f789
                            omega
                          by_cases c790 : a0 + a2 < 0 + b0
                          swap
                          · omega
                          by_cases c791 : 0 < a0 + a2 + a4
                          swap
                          · omega
                          have f792 := pair_fact E (i := 4) (j := 0) rfl rfl c773 c774
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f792
                          omega
                        by_cases c793 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                        swap
                        · omega
                        have f794 := pair_fact E (i := 10) (j := 4) rfl rfl c770 c771
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f794
                        omega
                      by_cases c795 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                      swap
                      · omega
                      have f796 := pair_fact E (i := 10) (j := 2) rfl rfl c767 c768
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f796
                      omega
                    by_cases c797 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                    swap
                    · omega
                    by_cases c798 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                    swap
                    · omega
                    have f799 := pair_fact E (i := 10) (j := 0) rfl rfl c765 c766
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f799
                    omega
                  by_cases c800 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c801 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                  swap
                  · -- branch
                    by_cases c802 : 0 < a4
                    swap
                    · -- branch
                      by_cases c803 : 0 < a8
                      swap
                      · omega
                      by_cases c804 : 0 < b4
                      swap
                      · omega
                      by_cases c805 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c806 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f807 := pair_fact E (i := 8) (j := 4) rfl rfl c803 c804
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f807
                      omega
                    by_cases c808 : 0 < b0
                    swap
                    · -- branch
                      by_cases c809 : 0 < a4
                      swap
                      · omega
                      by_cases c810 : 0 < b8
                      swap
                      · omega
                      by_cases c811 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                      swap
                      · omega
                      by_cases c812 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                      swap
                      · -- branch
                        by_cases c813 : 0 < a4
                        swap
                        · omega
                        by_cases c814 : 0 < b10
                        swap
                        · omega
                        by_cases c815 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                        swap
                        · omega
                        by_cases c816 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                        swap
                        · -- branch
                          by_cases c817 : 0 < a8
                          swap
                          · omega
                          by_cases c818 : 0 < b0
                          swap
                          · -- branch
                            by_cases c819 : 0 < a8
                            swap
                            · omega
                            by_cases c820 : 0 < b2
                            swap
                            · omega
                            by_cases c821 : a0 + a2 + a4 + a6 < b0 + b2
                            swap
                            · -- branch
                              by_cases c822 : 0 < a8
                              swap
                              · omega
                              by_cases c823 : 0 < b4
                              swap
                              · omega
                              by_cases c824 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                              swap
                              · -- branch
                                by_cases c825 : 0 < a4
                                swap
                                · omega
                                by_cases c826 : 0 < b4
                                swap
                                · omega
                                by_cases c827 : a0 + a2 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c828 : b0 + b2 < a0 + a2 + a4
                                swap
                                · omega
                                have f829 := pair_fact E (i := 4) (j := 4) rfl rfl c825 c826
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f829
                                by_cases c830 : 0 < a2
                                swap
                                · omega
                                by_cases c831 : 0 < b4
                                swap
                                · omega
                                by_cases c832 : a0 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c833 : b0 + b2 < a0 + a2
                                swap
                                · -- branch
                                  by_cases c834 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c835 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c836 : a0 + a2 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c837 : b0 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f838 := pair_fact E (i := 4) (j := 2) rfl rfl c834 c835
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f838
                                  omega
                                have f839 := pair_fact E (i := 2) (j := 4) rfl rfl c830 c831
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f839
                                omega
                              by_cases c840 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f841 := pair_fact E (i := 8) (j := 4) rfl rfl c822 c823
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f841
                              omega
                            by_cases c842 : b0 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f843 := pair_fact E (i := 8) (j := 2) rfl rfl c819 c820
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f843
                            omega
                          by_cases c844 : a0 + a2 + a4 + a6 < 0 + b0
                          swap
                          · omega
                          by_cases c845 : 0 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f846 := pair_fact E (i := 8) (j := 0) rfl rfl c817 c818
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f846
                          omega
                        have f847 := pair_fact E (i := 4) (j := 10) rfl rfl c813 c814
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f847
                        omega
                      have f848 := pair_fact E (i := 4) (j := 8) rfl rfl c809 c810
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f848
                      omega
                    by_cases c849 : a0 + a2 < 0 + b0
                    swap
                    · omega
                    by_cases c850 : 0 < a0 + a2 + a4
                    swap
                    · omega
                    have f851 := pair_fact E (i := 4) (j := 0) rfl rfl c802 c808
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f851
                    omega
                  have f852 := pair_fact E (i := 2) (j := 10) rfl rfl c763 c764
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f852
                  omega
                have f853 := pair_fact E (i := 2) (j := 8) rfl rfl c714 c715
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f853
                omega
              by_cases c854 : a0 < 0 + b0
              swap
              · omega
              by_cases c855 : 0 < a0 + a2
              swap
              · omega
              have f856 := pair_fact E (i := 2) (j := 0) rfl rfl c7 c358
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f856
              by_cases c857 : 0 < a2
              swap
              · omega
              by_cases c858 : 0 < b2
              swap
              · -- branch
                by_cases c859 : 0 < a2
                swap
                · omega
                by_cases c860 : 0 < b4
                swap
                · -- branch
                  by_cases c861 : 0 < a4
                  swap
                  · omega
                  by_cases c862 : 0 < b6
                  swap
                  · omega
                  by_cases c863 : a0 + a2 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c864 : b0 + b2 + b4 < a0 + a2 + a4
                  swap
                  · omega
                  have f865 := pair_fact E (i := 4) (j := 6) rfl rfl c861 c862
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f865
                  omega
                by_cases c866 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c867 : b0 + b2 < a0 + a2
                swap
                · -- branch
                  by_cases c868 : 0 < a2
                  swap
                  · omega
                  by_cases c869 : 0 < b10
                  swap
                  · -- branch
                    by_cases c870 : 0 < a4
                    swap
                    · -- branch
                      by_cases c871 : 0 < a8
                      swap
                      · omega
                      by_cases c872 : 0 < b4
                      swap
                      · omega
                      by_cases c873 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c874 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f875 := pair_fact E (i := 8) (j := 4) rfl rfl c871 c872
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
                    have f879 := pair_fact E (i := 4) (j := 4) rfl rfl c870 c876
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f879
                    omega
                  by_cases c880 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c881 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                  swap
                  · omega
                  have f882 := pair_fact E (i := 2) (j := 10) rfl rfl c868 c869
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f882
                  omega
                have f883 := pair_fact E (i := 2) (j := 4) rfl rfl c859 c860
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f883
                omega
              by_cases c884 : a0 < b0 + b2
              swap
              · omega
              by_cases c885 : b0 < a0 + a2
              swap
              · -- branch
                by_cases c886 : 0 < a2
                swap
                · omega
                by_cases c887 : 0 < b4
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
                  omega
                by_cases c893 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c894 : b0 + b2 < a0 + a2
                swap
                · -- branch
                  by_cases c895 : 0 < a2
                  swap
                  · omega
                  by_cases c896 : 0 < b6
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
                      by_cases c901 : 0 < b6
                      swap
                      · -- branch
                        by_cases c902 : 0 < a2
                        swap
                        · omega
                        by_cases c903 : 0 < b8
                        swap
                        · -- branch
                          by_cases c904 : 0 < a8
                          swap
                          · omega
                          by_cases c905 : 0 < b4
                          swap
                          · omega
                          by_cases c906 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c907 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                          swap
                          · omega
                          have f908 := pair_fact E (i := 8) (j := 4) rfl rfl c904 c905
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f908
                          omega
                        by_cases c909 : a0 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c910 : b0 + b2 + b4 + b6 < a0 + a2
                        swap
                        · -- branch
                          by_cases c911 : 0 < a4
                          swap
                          · omega
                          by_cases c912 : 0 < b2
                          swap
                          · omega
                          by_cases c913 : a0 + a2 < b0 + b2
                          swap
                          · omega
                          by_cases c914 : b0 < a0 + a2 + a4
                          swap
                          · omega
                          have f915 := pair_fact E (i := 4) (j := 2) rfl rfl c911 c912
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f915
                          omega
                        have f916 := pair_fact E (i := 2) (j := 8) rfl rfl c902 c903
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f916
                        omega
                      by_cases c917 : a0 + a2 + a4 < b0 + b2 + b4 + b6
                      swap
                      · omega
                      by_cases c918 : b0 + b2 + b4 < a0 + a2 + a4 + a6
                      swap
                      · omega
                      have f919 := pair_fact E (i := 6) (j := 6) rfl rfl c900 c901
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f919
                      omega
                    by_cases c920 : 0 < a0 + a2 + a4 + a6
                    swap
                    · omega
                    have f921 := pair_fact E (i := 6) (j := 0) rfl rfl c897 c898
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f921
                    omega
                  by_cases c922 : a0 < b0 + b2 + b4 + b6
                  swap
                  · omega
                  by_cases c923 : b0 + b2 + b4 < a0 + a2
                  swap
                  · -- branch
                    by_cases c924 : 0 < a4
                    swap
                    · omega
                    by_cases c925 : 0 < b2
                    swap
                    · omega
                    by_cases c926 : a0 + a2 < b0 + b2
                    swap
                    · omega
                    by_cases c927 : b0 < a0 + a2 + a4
                    swap
                    · omega
                    have f928 := pair_fact E (i := 4) (j := 2) rfl rfl c924 c925
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f928
                    omega
                  have f929 := pair_fact E (i := 2) (j := 6) rfl rfl c895 c896
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f929
                  omega
                have f930 := pair_fact E (i := 2) (j := 4) rfl rfl c886 c887
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f930
                omega
              have f931 := pair_fact E (i := 2) (j := 2) rfl rfl c857 c858
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f931
              omega
            by_cases c932 : 0 < b10
            swap
            · omega
            by_cases c933 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c934 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · omega
            have f935 := pair_fact E (i := 0) (j := 10) rfl rfl c6 c932
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f935
            omega
          by_cases c936 : 0 < b8
          swap
          · omega
          by_cases c937 : 0 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c938 : b0 + b2 + b4 + b6 < 0 + a0
          swap
          · omega
          have f939 := pair_fact E (i := 0) (j := 8) rfl rfl c5 c936
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f939
          omega
        by_cases c940 : 0 < b6
        swap
        · omega
        by_cases c941 : 0 < b0 + b2 + b4 + b6
        swap
        · omega
        by_cases c942 : b0 + b2 + b4 < 0 + a0
        swap
        · omega
        have f943 := pair_fact E (i := 0) (j := 6) rfl rfl c4 c940
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f943
        omega
      by_cases c944 : 0 < b4
      swap
      · omega
      by_cases c945 : 0 < b0 + b2 + b4
      swap
      · omega
      by_cases c946 : b0 + b2 < 0 + a0
      swap
      · omega
      have f947 := pair_fact E (i := 0) (j := 4) rfl rfl c3 c944
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f947
      omega
    by_cases c948 : 0 < b2
    swap
    · omega
    by_cases c949 : 0 < b0 + b2
    swap
    · omega
    by_cases c950 : b0 < 0 + a0
    swap
    · omega
    have f951 := pair_fact E (i := 0) (j := 2) rfl rfl c2 c948
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f951
    omega
  by_cases c952 : 0 < b0
  swap
  · -- branch
    by_cases c953 : 0 < a0
    swap
    · omega
    by_cases c954 : 0 < b2
    swap
    · -- branch
      by_cases c955 : 0 < a0
      swap
      · omega
      by_cases c956 : 0 < b4
      swap
      · omega
      by_cases c957 : 0 < b0 + b2 + b4
      swap
      · omega
      by_cases c958 : b0 + b2 < 0 + a0
      swap
      · omega
      have f959 := pair_fact E (i := 0) (j := 4) rfl rfl c955 c956
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f959
      by_cases c960 : 0 < a2
      swap
      · omega
      by_cases c961 : 0 < b0
      swap
      · -- branch
        by_cases c962 : 0 < a2
        swap
        · omega
        by_cases c963 : 0 < b2
        swap
        · -- branch
          by_cases c964 : 0 < a2
          swap
          · omega
          by_cases c965 : 0 < b4
          swap
          · omega
          by_cases c966 : a0 < b0 + b2 + b4
          swap
          · -- branch
            by_cases c967 : 0 < a4
            swap
            · omega
            by_cases c968 : 0 < b8
            swap
            · omega
            by_cases c969 : a0 + a2 < b0 + b2 + b4 + b6 + b8
            swap
            · omega
            by_cases c970 : b0 + b2 + b4 + b6 < a0 + a2 + a4
            swap
            · omega
            have f971 := pair_fact E (i := 4) (j := 8) rfl rfl c967 c968
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f971
            omega
          by_cases c972 : b0 + b2 < a0 + a2
          swap
          · omega
          have f973 := pair_fact E (i := 2) (j := 4) rfl rfl c964 c965
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f973
          omega
        by_cases c974 : a0 < b0 + b2
        swap
        · omega
        by_cases c975 : b0 < a0 + a2
        swap
        · omega
        have f976 := pair_fact E (i := 2) (j := 2) rfl rfl c962 c963
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f976
        omega
      by_cases c977 : a0 < 0 + b0
      swap
      · omega
      by_cases c978 : 0 < a0 + a2
      swap
      · omega
      have f979 := pair_fact E (i := 2) (j := 0) rfl rfl c960 c961
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f979
      omega
    by_cases c980 : 0 < b0 + b2
    swap
    · omega
    by_cases c981 : b0 < 0 + a0
    swap
    · omega
    have f982 := pair_fact E (i := 0) (j := 2) rfl rfl c953 c954
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f982
    by_cases c983 : 0 < a0
    swap
    · omega
    by_cases c984 : 0 < b6
    swap
    · -- branch
      by_cases c985 : 0 < a6
      swap
      · omega
      by_cases c986 : 0 < b0
      swap
      · -- branch
        by_cases c987 : 0 < a6
        swap
        · omega
        by_cases c988 : 0 < b2
        swap
        · omega
        by_cases c989 : a0 + a2 + a4 < b0 + b2
        swap
        · -- branch
          by_cases c990 : 0 < a6
          swap
          · omega
          by_cases c991 : 0 < b4
          swap
          · omega
          by_cases c992 : a0 + a2 + a4 < b0 + b2 + b4
          swap
          · -- branch
            by_cases c993 : 0 < a4
            swap
            · omega
            by_cases c994 : 0 < b4
            swap
            · omega
            by_cases c995 : a0 + a2 < b0 + b2 + b4
            swap
            · omega
            by_cases c996 : b0 + b2 < a0 + a2 + a4
            swap
            · omega
            have f997 := pair_fact E (i := 4) (j := 4) rfl rfl c993 c994
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f997
            omega
          by_cases c998 : b0 + b2 < a0 + a2 + a4 + a6
          swap
          · omega
          have f999 := pair_fact E (i := 6) (j := 4) rfl rfl c990 c991
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f999
          omega
        by_cases c1000 : b0 < a0 + a2 + a4 + a6
        swap
        · omega
        have f1001 := pair_fact E (i := 6) (j := 2) rfl rfl c987 c988
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1001
        omega
      by_cases c1002 : a0 + a2 + a4 < 0 + b0
      swap
      · omega
      by_cases c1003 : 0 < a0 + a2 + a4 + a6
      swap
      · omega
      have f1004 := pair_fact E (i := 6) (j := 0) rfl rfl c985 c986
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1004
      omega
    by_cases c1005 : 0 < b0 + b2 + b4 + b6
    swap
    · omega
    by_cases c1006 : b0 + b2 + b4 < 0 + a0
    swap
    · -- branch
      by_cases c1007 : 0 < a0
      swap
      · omega
      by_cases c1008 : 0 < b8
      swap
      · -- branch
        by_cases c1009 : 0 < a8
        swap
        · omega
        by_cases c1010 : 0 < b4
        swap
        · omega
        by_cases c1011 : a0 + a2 + a4 + a6 < b0 + b2 + b4
        swap
        · omega
        by_cases c1012 : b0 + b2 < a0 + a2 + a4 + a6 + a8
        swap
        · omega
        have f1013 := pair_fact E (i := 8) (j := 4) rfl rfl c1009 c1010
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1013
        omega
      by_cases c1014 : 0 < b0 + b2 + b4 + b6 + b8
      swap
      · omega
      by_cases c1015 : b0 + b2 + b4 + b6 < 0 + a0
      swap
      · -- branch
        by_cases c1016 : 0 < a0
        swap
        · omega
        by_cases c1017 : 0 < b10
        swap
        · -- branch
          by_cases c1018 : 0 < a2
          swap
          · -- branch
            by_cases c1019 : 0 < a2
            swap
            · -- branch
              by_cases c1020 : 0 < a2
              swap
              · -- branch
                by_cases c1021 : 0 < a2
                swap
                · -- branch
                  by_cases c1022 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1023 : 0 < a2
                    swap
                    · -- branch
                      by_cases c1024 : 0 < a4
                      swap
                      · omega
                      by_cases c1025 : 0 < b0
                      swap
                      · -- branch
                        by_cases c1026 : 0 < a4
                        swap
                        · omega
                        by_cases c1027 : 0 < b2
                        swap
                        · omega
                        by_cases c1028 : a0 + a2 < b0 + b2
                        swap
                        · -- branch
                          by_cases c1029 : 0 < a4
                          swap
                          · omega
                          by_cases c1030 : 0 < b4
                          swap
                          · -- branch
                            by_cases c1031 : 0 < a4
                            swap
                            · omega
                            by_cases c1032 : 0 < b8
                            swap
                            · omega
                            by_cases c1033 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1034 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                            swap
                            · omega
                            have f1035 := pair_fact E (i := 4) (j := 8) rfl rfl c1031 c1032
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1035
                            omega
                          by_cases c1036 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1037 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f1038 := pair_fact E (i := 4) (j := 4) rfl rfl c1029 c1030
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1038
                          omega
                        by_cases c1039 : b0 < a0 + a2 + a4
                        swap
                        · omega
                        have f1040 := pair_fact E (i := 4) (j := 2) rfl rfl c1026 c1027
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1040
                        omega
                      by_cases c1041 : a0 + a2 < 0 + b0
                      swap
                      · omega
                      by_cases c1042 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f1043 := pair_fact E (i := 4) (j := 0) rfl rfl c1024 c1025
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1043
                      omega
                    by_cases c1044 : 0 < b10
                    swap
                    · omega
                    by_cases c1045 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c1046 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · omega
                    have f1047 := pair_fact E (i := 2) (j := 10) rfl rfl c1023 c1044
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1047
                    omega
                  by_cases c1048 : 0 < b8
                  swap
                  · omega
                  by_cases c1049 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c1050 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · omega
                  have f1051 := pair_fact E (i := 2) (j := 8) rfl rfl c1022 c1048
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1051
                  omega
                by_cases c1052 : 0 < b6
                swap
                · omega
                by_cases c1053 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c1054 : b0 + b2 + b4 < a0 + a2
                swap
                · omega
                have f1055 := pair_fact E (i := 2) (j := 6) rfl rfl c1021 c1052
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1055
                omega
              by_cases c1056 : 0 < b4
              swap
              · omega
              by_cases c1057 : a0 < b0 + b2 + b4
              swap
              · omega
              by_cases c1058 : b0 + b2 < a0 + a2
              swap
              · omega
              have f1059 := pair_fact E (i := 2) (j := 4) rfl rfl c1020 c1056
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1059
              omega
            by_cases c1060 : 0 < b2
            swap
            · omega
            by_cases c1061 : a0 < b0 + b2
            swap
            · omega
            by_cases c1062 : b0 < a0 + a2
            swap
            · omega
            have f1063 := pair_fact E (i := 2) (j := 2) rfl rfl c1019 c1060
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1063
            omega
          by_cases c1064 : 0 < b0
          swap
          · -- branch
            by_cases c1065 : 0 < a2
            swap
            · omega
            by_cases c1066 : 0 < b2
            swap
            · omega
            by_cases c1067 : a0 < b0 + b2
            swap
            · -- branch
              by_cases c1068 : 0 < a2
              swap
              · omega
              by_cases c1069 : 0 < b4
              swap
              · omega
              by_cases c1070 : a0 < b0 + b2 + b4
              swap
              · -- branch
                by_cases c1071 : 0 < a4
                swap
                · omega
                by_cases c1072 : 0 < b8
                swap
                · omega
                by_cases c1073 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                swap
                · omega
                by_cases c1074 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                swap
                · omega
                have f1075 := pair_fact E (i := 4) (j := 8) rfl rfl c1071 c1072
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1075
                omega
              by_cases c1076 : b0 + b2 < a0 + a2
              swap
              · omega
              have f1077 := pair_fact E (i := 2) (j := 4) rfl rfl c1068 c1069
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1077
              omega
            by_cases c1078 : b0 < a0 + a2
            swap
            · omega
            have f1079 := pair_fact E (i := 2) (j := 2) rfl rfl c1065 c1066
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1079
            omega
          by_cases c1080 : a0 < 0 + b0
          swap
          · omega
          by_cases c1081 : 0 < a0 + a2
          swap
          · omega
          have f1082 := pair_fact E (i := 2) (j := 0) rfl rfl c1018 c1064
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1082
          omega
        by_cases c1083 : 0 < b0 + b2 + b4 + b6 + b8 + b10
        swap
        · omega
        by_cases c1084 : b0 + b2 + b4 + b6 + b8 < 0 + a0
        swap
        · -- branch
          by_cases c1085 : 0 < a2
          swap
          · -- branch
            by_cases c1086 : 0 < a4
            swap
            · omega
            by_cases c1087 : 0 < b2
            swap
            · omega
            by_cases c1088 : a0 + a2 < b0 + b2
            swap
            · omega
            by_cases c1089 : b0 < a0 + a2 + a4
            swap
            · omega
            have f1090 := pair_fact E (i := 4) (j := 2) rfl rfl c1086 c1087
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1090
            omega
          by_cases c1091 : 0 < b0
          swap
          · -- branch
            by_cases c1092 : 0 < a2
            swap
            · omega
            by_cases c1093 : 0 < b2
            swap
            · omega
            by_cases c1094 : a0 < b0 + b2
            swap
            · -- branch
              by_cases c1095 : 0 < a2
              swap
              · omega
              by_cases c1096 : 0 < b8
              swap
              · omega
              by_cases c1097 : a0 < b0 + b2 + b4 + b6 + b8
              swap
              · omega
              by_cases c1098 : b0 + b2 + b4 + b6 < a0 + a2
              swap
              · -- branch
                by_cases c1099 : 0 < a2
                swap
                · omega
                by_cases c1100 : 0 < b10
                swap
                · omega
                by_cases c1101 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                swap
                · omega
                by_cases c1102 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                swap
                · -- branch
                  by_cases c1103 : 0 < a2
                  swap
                  · omega
                  by_cases c1104 : 0 < b4
                  swap
                  · -- branch
                    by_cases c1105 : 0 < a4
                    swap
                    · omega
                    by_cases c1106 : 0 < b8
                    swap
                    · omega
                    by_cases c1107 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c1108 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                    swap
                    · omega
                    have f1109 := pair_fact E (i := 4) (j := 8) rfl rfl c1105 c1106
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1109
                    omega
                  by_cases c1110 : a0 < b0 + b2 + b4
                  swap
                  · -- branch
                    by_cases c1111 : 0 < a4
                    swap
                    · omega
                    by_cases c1112 : 0 < b8
                    swap
                    · omega
                    by_cases c1113 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                    swap
                    · omega
                    by_cases c1114 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                    swap
                    · omega
                    have f1115 := pair_fact E (i := 4) (j := 8) rfl rfl c1111 c1112
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1115
                    omega
                  by_cases c1116 : b0 + b2 < a0 + a2
                  swap
                  · omega
                  have f1117 := pair_fact E (i := 2) (j := 4) rfl rfl c1103 c1104
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1117
                  omega
                have f1118 := pair_fact E (i := 2) (j := 10) rfl rfl c1099 c1100
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1118
                omega
              have f1119 := pair_fact E (i := 2) (j := 8) rfl rfl c1095 c1096
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1119
              omega
            by_cases c1120 : b0 < a0 + a2
            swap
            · omega
            have f1121 := pair_fact E (i := 2) (j := 2) rfl rfl c1092 c1093
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1121
            omega
          by_cases c1122 : a0 < 0 + b0
          swap
          · omega
          by_cases c1123 : 0 < a0 + a2
          swap
          · omega
          have f1124 := pair_fact E (i := 2) (j := 0) rfl rfl c1085 c1091
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1124
          omega
        have f1125 := pair_fact E (i := 0) (j := 10) rfl rfl c1016 c1017
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1125
        omega
      have f1126 := pair_fact E (i := 0) (j := 8) rfl rfl c1007 c1008
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1126
      omega
    have f1127 := pair_fact E (i := 0) (j := 6) rfl rfl c983 c984
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1127
    omega
  by_cases c1128 : 0 < 0 + b0
  swap
  · omega
  by_cases c1129 : 0 < 0 + a0
  swap
  · omega
  have f1130 := pair_fact E (i := 0) (j := 0) rfl rfl c1 c952
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1130
  by_cases c1131 : 0 < a0
  swap
  · omega
  by_cases c1132 : 0 < b6
  swap
  · -- branch
    by_cases c1133 : 0 < a6
    swap
    · omega
    by_cases c1134 : 0 < b0
    swap
    · omega
    by_cases c1135 : a0 + a2 + a4 < 0 + b0
    swap
    · -- branch
      by_cases c1136 : 0 < a6
      swap
      · omega
      by_cases c1137 : 0 < b6
      swap
      · -- branch
        by_cases c1138 : 0 < a0
        swap
        · omega
        by_cases c1139 : 0 < b4
        swap
        · omega
        by_cases c1140 : 0 < b0 + b2 + b4
        swap
        · omega
        by_cases c1141 : b0 + b2 < 0 + a0
        swap
        · -- branch
          by_cases c1142 : 0 < a0
          swap
          · omega
          by_cases c1143 : 0 < b8
          swap
          · -- branch
            by_cases c1144 : 0 < a8
            swap
            · omega
            by_cases c1145 : 0 < b4
            swap
            · omega
            by_cases c1146 : a0 + a2 + a4 + a6 < b0 + b2 + b4
            swap
            · omega
            by_cases c1147 : b0 + b2 < a0 + a2 + a4 + a6 + a8
            swap
            · omega
            have f1148 := pair_fact E (i := 8) (j := 4) rfl rfl c1144 c1145
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1148
            omega
          by_cases c1149 : 0 < b0 + b2 + b4 + b6 + b8
          swap
          · omega
          by_cases c1150 : b0 + b2 + b4 + b6 < 0 + a0
          swap
          · -- branch
            by_cases c1151 : 0 < a0
            swap
            · omega
            by_cases c1152 : 0 < b10
            swap
            · -- branch
              by_cases c1153 : 0 < a6
              swap
              · omega
              by_cases c1154 : 0 < b10
              swap
              · -- branch
                by_cases c1155 : 0 < a2
                swap
                · -- branch
                  by_cases c1156 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1157 : 0 < a2
                    swap
                    · -- branch
                      by_cases c1158 : 0 < a2
                      swap
                      · -- branch
                        by_cases c1159 : 0 < a2
                        swap
                        · -- branch
                          by_cases c1160 : 0 < a2
                          swap
                          · -- branch
                            by_cases c1161 : 0 < a4
                            swap
                            · omega
                            by_cases c1162 : 0 < b2
                            swap
                            · omega
                            by_cases c1163 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c1164 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f1165 := pair_fact E (i := 4) (j := 2) rfl rfl c1161 c1162
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1165
                            by_cases c1166 : 0 < a0
                            swap
                            · omega
                            by_cases c1167 : 0 < b2
                            swap
                            · omega
                            by_cases c1168 : 0 < b0 + b2
                            swap
                            · omega
                            by_cases c1169 : b0 < 0 + a0
                            swap
                            · -- branch
                              by_cases c1170 : 0 < a4
                              swap
                              · omega
                              by_cases c1171 : 0 < b0
                              swap
                              · omega
                              by_cases c1172 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c1173 : 0 < a4
                                swap
                                · omega
                                by_cases c1174 : 0 < b6
                                swap
                                · -- branch
                                  by_cases c1175 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c1176 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c1177 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c1178 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c1179 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1180 : 0 < b10
                                    swap
                                    · -- branch
                                      by_cases c1181 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c1182 : 0 < b0
                                      swap
                                      · omega
                                      by_cases c1183 : a0 + a2 + a4 + a6 < 0 + b0
                                      swap
                                      · -- branch
                                        by_cases c1184 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c1185 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c1186 : a0 + a2 + a4 + a6 < b0 + b2
                                        swap
                                        · -- branch
                                          by_cases c1187 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c1188 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c1189 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                          swap
                                          · -- branch
                                            by_cases c1190 : 0 < a4
                                            swap
                                            · omega
                                            by_cases c1191 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c1192 : a0 + a2 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c1193 : b0 + b2 < a0 + a2 + a4
                                            swap
                                            · omega
                                            have f1194 := pair_fact E (i := 4) (j := 4) rfl rfl c1190 c1191
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1194
                                            by_cases c1195 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c1196 : 0 < b2
                                            swap
                                            · omega
                                            by_cases c1197 : a0 + a2 + a4 < b0 + b2
                                            swap
                                            · -- branch
                                              by_cases c1198 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c1199 : 0 < b8
                                              swap
                                              · omega
                                              by_cases c1200 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                              swap
                                              · omega
                                              by_cases c1201 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f1202 := pair_fact E (i := 6) (j := 8) rfl rfl c1198 c1199
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1202
                                              by_cases c1203 : 0 < a10
                                              swap
                                              · omega
                                              by_cases c1204 : 0 < b8
                                              swap
                                              · omega
                                              by_cases c1205 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                              swap
                                              · omega
                                              by_cases c1206 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                              swap
                                              · omega
                                              have f1207 := pair_fact E (i := 10) (j := 8) rfl rfl c1203 c1204
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1207
                                              omega
                                            by_cases c1208 : b0 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f1209 := pair_fact E (i := 6) (j := 2) rfl rfl c1195 c1196
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1209
                                            omega
                                          by_cases c1210 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f1211 := pair_fact E (i := 8) (j := 4) rfl rfl c1187 c1188
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1211
                                          omega
                                        by_cases c1212 : b0 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f1213 := pair_fact E (i := 8) (j := 2) rfl rfl c1184 c1185
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1213
                                        omega
                                      by_cases c1214 : 0 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f1215 := pair_fact E (i := 8) (j := 0) rfl rfl c1181 c1182
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1215
                                      omega
                                    by_cases c1216 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c1217 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f1218 := pair_fact E (i := 4) (j := 10) rfl rfl c1179 c1180
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1218
                                    omega
                                  have f1219 := pair_fact E (i := 4) (j := 8) rfl rfl c1175 c1176
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1219
                                  omega
                                by_cases c1220 : a0 + a2 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c1221 : b0 + b2 + b4 < a0 + a2 + a4
                                swap
                                · omega
                                have f1222 := pair_fact E (i := 4) (j := 6) rfl rfl c1173 c1174
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1222
                                omega
                              by_cases c1223 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f1224 := pair_fact E (i := 4) (j := 0) rfl rfl c1170 c1171
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1224
                              omega
                            have f1225 := pair_fact E (i := 0) (j := 2) rfl rfl c1166 c1167
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1225
                            omega
                          by_cases c1226 : 0 < b10
                          swap
                          · omega
                          by_cases c1227 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c1228 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · omega
                          have f1229 := pair_fact E (i := 2) (j := 10) rfl rfl c1160 c1226
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1229
                          omega
                        by_cases c1230 : 0 < b8
                        swap
                        · omega
                        by_cases c1231 : a0 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1232 : b0 + b2 + b4 + b6 < a0 + a2
                        swap
                        · omega
                        have f1233 := pair_fact E (i := 2) (j := 8) rfl rfl c1159 c1230
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1233
                        omega
                      by_cases c1234 : 0 < b4
                      swap
                      · omega
                      by_cases c1235 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c1236 : b0 + b2 < a0 + a2
                      swap
                      · omega
                      have f1237 := pair_fact E (i := 2) (j := 4) rfl rfl c1158 c1234
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1237
                      omega
                    by_cases c1238 : 0 < b2
                    swap
                    · omega
                    by_cases c1239 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c1240 : b0 < a0 + a2
                    swap
                    · omega
                    have f1241 := pair_fact E (i := 2) (j := 2) rfl rfl c1157 c1238
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1241
                    omega
                  by_cases c1242 : 0 < b0
                  swap
                  · omega
                  by_cases c1243 : a0 < 0 + b0
                  swap
                  · omega
                  by_cases c1244 : 0 < a0 + a2
                  swap
                  · omega
                  have f1245 := pair_fact E (i := 2) (j := 0) rfl rfl c1156 c1242
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1245
                  omega
                by_cases c1246 : 0 < b6
                swap
                · -- branch
                  by_cases c1247 : 0 < a2
                  swap
                  · omega
                  by_cases c1248 : 0 < b8
                  swap
                  · omega
                  by_cases c1249 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c1250 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · -- branch
                    by_cases c1251 : 0 < a2
                    swap
                    · omega
                    by_cases c1252 : 0 < b10
                    swap
                    · -- branch
                      by_cases c1253 : 0 < a2
                      swap
                      · omega
                      by_cases c1254 : 0 < b0
                      swap
                      · omega
                      by_cases c1255 : a0 < 0 + b0
                      swap
                      · -- branch
                        by_cases c1256 : 0 < a2
                        swap
                        · omega
                        by_cases c1257 : 0 < b4
                        swap
                        · omega
                        by_cases c1258 : a0 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c1259 : b0 + b2 < a0 + a2
                        swap
                        · -- branch
                          by_cases c1260 : 0 < a2
                          swap
                          · omega
                          by_cases c1261 : 0 < b2
                          swap
                          · omega
                          by_cases c1262 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c1263 : b0 < a0 + a2
                          swap
                          · omega
                          have f1264 := pair_fact E (i := 2) (j := 2) rfl rfl c1260 c1261
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1264
                          by_cases c1265 : 0 < a0
                          swap
                          · omega
                          by_cases c1266 : 0 < b2
                          swap
                          · omega
                          by_cases c1267 : 0 < b0 + b2
                          swap
                          · omega
                          by_cases c1268 : b0 < 0 + a0
                          swap
                          · -- branch
                            by_cases c1269 : 0 < a10
                            swap
                            · omega
                            by_cases c1270 : 0 < b0
                            swap
                            · omega
                            by_cases c1271 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                            swap
                            · -- branch
                              by_cases c1272 : 0 < a10
                              swap
                              · omega
                              by_cases c1273 : 0 < b2
                              swap
                              · omega
                              by_cases c1274 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                              swap
                              · -- branch
                                by_cases c1275 : 0 < a10
                                swap
                                · omega
                                by_cases c1276 : 0 < b4
                                swap
                                · omega
                                by_cases c1277 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                swap
                                · -- branch
                                  by_cases c1278 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c1279 : 0 < b0
                                  swap
                                  · omega
                                  by_cases c1280 : a0 + a2 < 0 + b0
                                  swap
                                  · -- branch
                                    by_cases c1281 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1282 : 0 < b2
                                    swap
                                    · omega
                                    by_cases c1283 : a0 + a2 < b0 + b2
                                    swap
                                    · omega
                                    by_cases c1284 : b0 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f1285 := pair_fact E (i := 4) (j := 2) rfl rfl c1281 c1282
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1285
                                    by_cases c1286 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1287 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c1288 : a0 + a2 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c1289 : b0 + b2 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c1290 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c1291 : 0 < b4
                                      swap
                                      · omega
                                      by_cases c1292 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                      swap
                                      · omega
                                      by_cases c1293 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f1294 := pair_fact E (i := 8) (j := 4) rfl rfl c1290 c1291
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1294
                                      omega
                                    have f1295 := pair_fact E (i := 4) (j := 4) rfl rfl c1286 c1287
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1295
                                    omega
                                  by_cases c1296 : 0 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f1297 := pair_fact E (i := 4) (j := 0) rfl rfl c1278 c1279
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1297
                                  omega
                                by_cases c1298 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f1299 := pair_fact E (i := 10) (j := 4) rfl rfl c1275 c1276
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1299
                                omega
                              by_cases c1300 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                              swap
                              · omega
                              have f1301 := pair_fact E (i := 10) (j := 2) rfl rfl c1272 c1273
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1301
                              omega
                            by_cases c1302 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                            swap
                            · omega
                            have f1303 := pair_fact E (i := 10) (j := 0) rfl rfl c1269 c1270
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1303
                            omega
                          have f1304 := pair_fact E (i := 0) (j := 2) rfl rfl c1265 c1266
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1304
                          omega
                        have f1305 := pair_fact E (i := 2) (j := 4) rfl rfl c1256 c1257
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1305
                        by_cases c1306 : 0 < a0
                        swap
                        · omega
                        by_cases c1307 : 0 < b2
                        swap
                        · -- branch
                          by_cases c1308 : 0 < a2
                          swap
                          · omega
                          by_cases c1309 : 0 < b2
                          swap
                          · -- branch
                            by_cases c1310 : 0 < a6
                            swap
                            · omega
                            by_cases c1311 : 0 < b2
                            swap
                            · -- branch
                              by_cases c1312 : 0 < a10
                              swap
                              · omega
                              by_cases c1313 : 0 < b0
                              swap
                              · omega
                              by_cases c1314 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                              swap
                              · -- branch
                                by_cases c1315 : 0 < a10
                                swap
                                · omega
                                by_cases c1316 : 0 < b2
                                swap
                                · -- branch
                                  by_cases c1317 : 0 < a10
                                  swap
                                  · omega
                                  by_cases c1318 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c1319 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                  swap
                                  · -- branch
                                    by_cases c1320 : 0 < a10
                                    swap
                                    · omega
                                    by_cases c1321 : 0 < b6
                                    swap
                                    · -- branch
                                      by_cases c1322 : 0 < a10
                                      swap
                                      · omega
                                      by_cases c1323 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c1324 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c1325 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                      swap
                                      · omega
                                      have f1326 := pair_fact E (i := 10) (j := 8) rfl rfl c1322 c1323
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1326
                                      by_cases c1327 : 0 < a6
                                      swap
                                      · omega
                                      by_cases c1328 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c1329 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · omega
                                      by_cases c1330 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                      swap
                                      · -- branch
                                        by_cases c1331 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c1332 : 0 < b4
                                        swap
                                        · omega
                                        by_cases c1333 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                        swap
                                        · omega
                                        by_cases c1334 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f1335 := pair_fact E (i := 8) (j := 4) rfl rfl c1331 c1332
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1335
                                        omega
                                      have f1336 := pair_fact E (i := 6) (j := 8) rfl rfl c1327 c1328
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1336
                                      omega
                                    by_cases c1337 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                    swap
                                    · omega
                                    by_cases c1338 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                    swap
                                    · omega
                                    have f1339 := pair_fact E (i := 10) (j := 6) rfl rfl c1320 c1321
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1339
                                    omega
                                  by_cases c1340 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                  swap
                                  · omega
                                  have f1341 := pair_fact E (i := 10) (j := 4) rfl rfl c1317 c1318
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1341
                                  omega
                                by_cases c1342 : a0 + a2 + a4 + a6 + a8 < b0 + b2
                                swap
                                · omega
                                by_cases c1343 : b0 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f1344 := pair_fact E (i := 10) (j := 2) rfl rfl c1315 c1316
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1344
                                omega
                              by_cases c1345 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                              swap
                              · omega
                              have f1346 := pair_fact E (i := 10) (j := 0) rfl rfl c1312 c1313
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1346
                              omega
                            by_cases c1347 : a0 + a2 + a4 < b0 + b2
                            swap
                            · omega
                            by_cases c1348 : b0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f1349 := pair_fact E (i := 6) (j := 2) rfl rfl c1310 c1311
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1349
                            omega
                          by_cases c1350 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c1351 : b0 < a0 + a2
                          swap
                          · omega
                          have f1352 := pair_fact E (i := 2) (j := 2) rfl rfl c1308 c1309
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1352
                          omega
                        by_cases c1353 : 0 < b0 + b2
                        swap
                        · omega
                        by_cases c1354 : b0 < 0 + a0
                        swap
                        · -- branch
                          by_cases c1355 : 0 < a2
                          swap
                          · omega
                          by_cases c1356 : 0 < b2
                          swap
                          · omega
                          by_cases c1357 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c1358 : b0 < a0 + a2
                          swap
                          · omega
                          have f1359 := pair_fact E (i := 2) (j := 2) rfl rfl c1355 c1356
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1359
                          by_cases c1360 : 0 < a4
                          swap
                          · -- branch
                            by_cases c1361 : 0 < a6
                            swap
                            · omega
                            by_cases c1362 : 0 < b4
                            swap
                            · omega
                            by_cases c1363 : a0 + a2 + a4 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c1364 : b0 + b2 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f1365 := pair_fact E (i := 6) (j := 4) rfl rfl c1361 c1362
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1365
                            omega
                          by_cases c1366 : 0 < b4
                          swap
                          · omega
                          by_cases c1367 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1368 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f1369 := pair_fact E (i := 4) (j := 4) rfl rfl c1360 c1366
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1369
                          omega
                        have f1370 := pair_fact E (i := 0) (j := 2) rfl rfl c1306 c1307
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1370
                        omega
                      by_cases c1371 : 0 < a0 + a2
                      swap
                      · omega
                      have f1372 := pair_fact E (i := 2) (j := 0) rfl rfl c1253 c1254
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1372
                      by_cases c1373 : 0 < a2
                      swap
                      · omega
                      by_cases c1374 : 0 < b4
                      swap
                      · omega
                      by_cases c1375 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c1376 : b0 + b2 < a0 + a2
                      swap
                      · -- branch
                        by_cases c1377 : 0 < a0
                        swap
                        · omega
                        by_cases c1378 : 0 < b2
                        swap
                        · omega
                        by_cases c1379 : 0 < b0 + b2
                        swap
                        · omega
                        by_cases c1380 : b0 < 0 + a0
                        swap
                        · -- branch
                          by_cases c1381 : 0 < a2
                          swap
                          · omega
                          by_cases c1382 : 0 < b2
                          swap
                          · omega
                          by_cases c1383 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c1384 : b0 < a0 + a2
                          swap
                          · -- branch
                            by_cases c1385 : 0 < a4
                            swap
                            · omega
                            by_cases c1386 : 0 < b2
                            swap
                            · omega
                            by_cases c1387 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c1388 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f1389 := pair_fact E (i := 4) (j := 2) rfl rfl c1385 c1386
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1389
                            omega
                          have f1390 := pair_fact E (i := 2) (j := 2) rfl rfl c1381 c1382
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1390
                          omega
                        have f1391 := pair_fact E (i := 0) (j := 2) rfl rfl c1377 c1378
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1391
                        omega
                      have f1392 := pair_fact E (i := 2) (j := 4) rfl rfl c1373 c1374
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1392
                      omega
                    by_cases c1393 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c1394 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · omega
                    have f1395 := pair_fact E (i := 2) (j := 10) rfl rfl c1251 c1252
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1395
                    omega
                  have f1396 := pair_fact E (i := 2) (j := 8) rfl rfl c1247 c1248
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1396
                  omega
                by_cases c1397 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c1398 : b0 + b2 + b4 < a0 + a2
                swap
                · omega
                have f1399 := pair_fact E (i := 2) (j := 6) rfl rfl c1155 c1246
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1399
                omega
              by_cases c1400 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c1401 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
              swap
              · omega
              have f1402 := pair_fact E (i := 6) (j := 10) rfl rfl c1153 c1154
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1402
              omega
            by_cases c1403 : 0 < b0 + b2 + b4 + b6 + b8 + b10
            swap
            · omega
            by_cases c1404 : b0 + b2 + b4 + b6 + b8 < 0 + a0
            swap
            · -- branch
              by_cases c1405 : 0 < a6
              swap
              · omega
              by_cases c1406 : 0 < b10
              swap
              · omega
              by_cases c1407 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8 + b10
              swap
              · omega
              by_cases c1408 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6
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
                            · omega
                            by_cases c1416 : 0 < b2
                            swap
                            · omega
                            by_cases c1417 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c1418 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f1419 := pair_fact E (i := 4) (j := 2) rfl rfl c1415 c1416
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1419
                            by_cases c1420 : 0 < a0
                            swap
                            · omega
                            by_cases c1421 : 0 < b2
                            swap
                            · omega
                            by_cases c1422 : 0 < b0 + b2
                            swap
                            · omega
                            by_cases c1423 : b0 < 0 + a0
                            swap
                            · -- branch
                              by_cases c1424 : 0 < a4
                              swap
                              · omega
                              by_cases c1425 : 0 < b0
                              swap
                              · omega
                              by_cases c1426 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c1427 : 0 < a4
                                swap
                                · omega
                                by_cases c1428 : 0 < b6
                                swap
                                · -- branch
                                  by_cases c1429 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c1430 : 0 < b8
                                  swap
                                  · omega
                                  by_cases c1431 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                  swap
                                  · omega
                                  by_cases c1432 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                  swap
                                  · -- branch
                                    by_cases c1433 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1434 : 0 < b10
                                    swap
                                    · omega
                                    by_cases c1435 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                    swap
                                    · omega
                                    by_cases c1436 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c1437 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c1438 : 0 < b0
                                      swap
                                      · omega
                                      by_cases c1439 : a0 + a2 + a4 + a6 < 0 + b0
                                      swap
                                      · -- branch
                                        by_cases c1440 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c1441 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c1442 : a0 + a2 + a4 + a6 < b0 + b2
                                        swap
                                        · -- branch
                                          by_cases c1443 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c1444 : 0 < b4
                                          swap
                                          · omega
                                          by_cases c1445 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                          swap
                                          · -- branch
                                            by_cases c1446 : 0 < a4
                                            swap
                                            · omega
                                            by_cases c1447 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c1448 : a0 + a2 < b0 + b2 + b4
                                            swap
                                            · omega
                                            by_cases c1449 : b0 + b2 < a0 + a2 + a4
                                            swap
                                            · omega
                                            have f1450 := pair_fact E (i := 4) (j := 4) rfl rfl c1446 c1447
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1450
                                            by_cases c1451 : 0 < a6
                                            swap
                                            · omega
                                            by_cases c1452 : 0 < b2
                                            swap
                                            · omega
                                            by_cases c1453 : a0 + a2 + a4 < b0 + b2
                                            swap
                                            · -- branch
                                              by_cases c1454 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c1455 : 0 < b8
                                              swap
                                              · omega
                                              by_cases c1456 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                              swap
                                              · omega
                                              by_cases c1457 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f1458 := pair_fact E (i := 6) (j := 8) rfl rfl c1454 c1455
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1458
                                              by_cases c1459 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c1460 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c1461 : a0 + a2 + a4 < b0 + b2 + b4
                                              swap
                                              · -- branch
                                                by_cases c1462 : 0 < a8
                                                swap
                                                · omega
                                                by_cases c1463 : 0 < b6
                                                swap
                                                · -- branch
                                                  by_cases c1464 : 0 < a8
                                                  swap
                                                  · omega
                                                  by_cases c1465 : 0 < b8
                                                  swap
                                                  · omega
                                                  by_cases c1466 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                                  swap
                                                  · omega
                                                  by_cases c1467 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · omega
                                                  have f1468 := pair_fact E (i := 8) (j := 8) rfl rfl c1464 c1465
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1468
                                                  by_cases c1469 : 0 < a8
                                                  swap
                                                  · omega
                                                  by_cases c1470 : 0 < b10
                                                  swap
                                                  · omega
                                                  by_cases c1471 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                                  swap
                                                  · omega
                                                  by_cases c1472 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · -- branch
                                                    by_cases c1473 : 0 < a10
                                                    swap
                                                    · omega
                                                    by_cases c1474 : 0 < b8
                                                    swap
                                                    · omega
                                                    by_cases c1475 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                                    swap
                                                    · omega
                                                    by_cases c1476 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                                    swap
                                                    · omega
                                                    have f1477 := pair_fact E (i := 10) (j := 8) rfl rfl c1473 c1474
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1477
                                                    omega
                                                  have f1478 := pair_fact E (i := 8) (j := 10) rfl rfl c1469 c1470
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1478
                                                  omega
                                                by_cases c1479 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                swap
                                                · omega
                                                by_cases c1480 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                swap
                                                · omega
                                                have f1481 := pair_fact E (i := 8) (j := 6) rfl rfl c1462 c1463
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1481
                                                omega
                                              by_cases c1482 : b0 + b2 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f1483 := pair_fact E (i := 6) (j := 4) rfl rfl c1459 c1460
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1483
                                              omega
                                            by_cases c1484 : b0 < a0 + a2 + a4 + a6
                                            swap
                                            · omega
                                            have f1485 := pair_fact E (i := 6) (j := 2) rfl rfl c1451 c1452
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1485
                                            omega
                                          by_cases c1486 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f1487 := pair_fact E (i := 8) (j := 4) rfl rfl c1443 c1444
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1487
                                          omega
                                        by_cases c1488 : b0 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f1489 := pair_fact E (i := 8) (j := 2) rfl rfl c1440 c1441
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1489
                                        omega
                                      by_cases c1490 : 0 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · omega
                                      have f1491 := pair_fact E (i := 8) (j := 0) rfl rfl c1437 c1438
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1491
                                      omega
                                    have f1492 := pair_fact E (i := 4) (j := 10) rfl rfl c1433 c1434
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1492
                                    omega
                                  have f1493 := pair_fact E (i := 4) (j := 8) rfl rfl c1429 c1430
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1493
                                  omega
                                by_cases c1494 : a0 + a2 < b0 + b2 + b4 + b6
                                swap
                                · omega
                                by_cases c1495 : b0 + b2 + b4 < a0 + a2 + a4
                                swap
                                · omega
                                have f1496 := pair_fact E (i := 4) (j := 6) rfl rfl c1427 c1428
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1496
                                omega
                              by_cases c1497 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f1498 := pair_fact E (i := 4) (j := 0) rfl rfl c1424 c1425
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1498
                              omega
                            have f1499 := pair_fact E (i := 0) (j := 2) rfl rfl c1420 c1421
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1499
                            omega
                          by_cases c1500 : 0 < b10
                          swap
                          · omega
                          by_cases c1501 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                          swap
                          · omega
                          by_cases c1502 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                          swap
                          · omega
                          have f1503 := pair_fact E (i := 2) (j := 10) rfl rfl c1414 c1500
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1503
                          omega
                        by_cases c1504 : 0 < b8
                        swap
                        · omega
                        by_cases c1505 : a0 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1506 : b0 + b2 + b4 + b6 < a0 + a2
                        swap
                        · omega
                        have f1507 := pair_fact E (i := 2) (j := 8) rfl rfl c1413 c1504
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1507
                        omega
                      by_cases c1508 : 0 < b4
                      swap
                      · omega
                      by_cases c1509 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c1510 : b0 + b2 < a0 + a2
                      swap
                      · omega
                      have f1511 := pair_fact E (i := 2) (j := 4) rfl rfl c1412 c1508
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1511
                      omega
                    by_cases c1512 : 0 < b2
                    swap
                    · omega
                    by_cases c1513 : a0 < b0 + b2
                    swap
                    · omega
                    by_cases c1514 : b0 < a0 + a2
                    swap
                    · omega
                    have f1515 := pair_fact E (i := 2) (j := 2) rfl rfl c1411 c1512
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1515
                    omega
                  by_cases c1516 : 0 < b0
                  swap
                  · omega
                  by_cases c1517 : a0 < 0 + b0
                  swap
                  · omega
                  by_cases c1518 : 0 < a0 + a2
                  swap
                  · omega
                  have f1519 := pair_fact E (i := 2) (j := 0) rfl rfl c1410 c1516
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1519
                  omega
                by_cases c1520 : 0 < b6
                swap
                · -- branch
                  by_cases c1521 : 0 < a2
                  swap
                  · omega
                  by_cases c1522 : 0 < b8
                  swap
                  · omega
                  by_cases c1523 : a0 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c1524 : b0 + b2 + b4 + b6 < a0 + a2
                  swap
                  · -- branch
                    by_cases c1525 : 0 < a2
                    swap
                    · omega
                    by_cases c1526 : 0 < b10
                    swap
                    · omega
                    by_cases c1527 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c1528 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                    swap
                    · -- branch
                      by_cases c1529 : 0 < a2
                      swap
                      · omega
                      by_cases c1530 : 0 < b0
                      swap
                      · omega
                      by_cases c1531 : a0 < 0 + b0
                      swap
                      · -- branch
                        by_cases c1532 : 0 < a2
                        swap
                        · omega
                        by_cases c1533 : 0 < b4
                        swap
                        · omega
                        by_cases c1534 : a0 < b0 + b2 + b4
                        swap
                        · omega
                        by_cases c1535 : b0 + b2 < a0 + a2
                        swap
                        · -- branch
                          by_cases c1536 : 0 < a2
                          swap
                          · omega
                          by_cases c1537 : 0 < b2
                          swap
                          · omega
                          by_cases c1538 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c1539 : b0 < a0 + a2
                          swap
                          · omega
                          have f1540 := pair_fact E (i := 2) (j := 2) rfl rfl c1536 c1537
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1540
                          by_cases c1541 : 0 < a0
                          swap
                          · omega
                          by_cases c1542 : 0 < b2
                          swap
                          · omega
                          by_cases c1543 : 0 < b0 + b2
                          swap
                          · omega
                          by_cases c1544 : b0 < 0 + a0
                          swap
                          · -- branch
                            by_cases c1545 : 0 < a4
                            swap
                            · -- branch
                              by_cases c1546 : 0 < a8
                              swap
                              · omega
                              by_cases c1547 : 0 < b4
                              swap
                              · omega
                              by_cases c1548 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c1549 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f1550 := pair_fact E (i := 8) (j := 4) rfl rfl c1546 c1547
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1550
                              omega
                            by_cases c1551 : 0 < b0
                            swap
                            · omega
                            by_cases c1552 : a0 + a2 < 0 + b0
                            swap
                            · -- branch
                              by_cases c1553 : 0 < a4
                              swap
                              · omega
                              by_cases c1554 : 0 < b2
                              swap
                              · omega
                              by_cases c1555 : a0 + a2 < b0 + b2
                              swap
                              · omega
                              by_cases c1556 : b0 < a0 + a2 + a4
                              swap
                              · omega
                              have f1557 := pair_fact E (i := 4) (j := 2) rfl rfl c1553 c1554
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1557
                              by_cases c1558 : 0 < a4
                              swap
                              · omega
                              by_cases c1559 : 0 < b4
                              swap
                              · omega
                              by_cases c1560 : a0 + a2 < b0 + b2 + b4
                              swap
                              · omega
                              by_cases c1561 : b0 + b2 < a0 + a2 + a4
                              swap
                              · -- branch
                                by_cases c1562 : 0 < a8
                                swap
                                · omega
                                by_cases c1563 : 0 < b4
                                swap
                                · omega
                                by_cases c1564 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c1565 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f1566 := pair_fact E (i := 8) (j := 4) rfl rfl c1562 c1563
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1566
                                omega
                              have f1567 := pair_fact E (i := 4) (j := 4) rfl rfl c1558 c1559
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1567
                              omega
                            by_cases c1568 : 0 < a0 + a2 + a4
                            swap
                            · omega
                            have f1569 := pair_fact E (i := 4) (j := 0) rfl rfl c1545 c1551
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1569
                            omega
                          have f1570 := pair_fact E (i := 0) (j := 2) rfl rfl c1541 c1542
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1570
                          omega
                        have f1571 := pair_fact E (i := 2) (j := 4) rfl rfl c1532 c1533
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1571
                        by_cases c1572 : 0 < a0
                        swap
                        · omega
                        by_cases c1573 : 0 < b2
                        swap
                        · -- branch
                          by_cases c1574 : 0 < a2
                          swap
                          · omega
                          by_cases c1575 : 0 < b2
                          swap
                          · -- branch
                            by_cases c1576 : 0 < a6
                            swap
                            · omega
                            by_cases c1577 : 0 < b2
                            swap
                            · -- branch
                              by_cases c1578 : 0 < a4
                              swap
                              · -- branch
                                by_cases c1579 : 0 < a8
                                swap
                                · omega
                                by_cases c1580 : 0 < b4
                                swap
                                · omega
                                by_cases c1581 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                swap
                                · omega
                                by_cases c1582 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f1583 := pair_fact E (i := 8) (j := 4) rfl rfl c1579 c1580
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1583
                                omega
                              by_cases c1584 : 0 < b0
                              swap
                              · omega
                              by_cases c1585 : a0 + a2 < 0 + b0
                              swap
                              · -- branch
                                by_cases c1586 : 0 < a4
                                swap
                                · omega
                                by_cases c1587 : 0 < b2
                                swap
                                · -- branch
                                  by_cases c1588 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c1589 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c1590 : a0 + a2 < b0 + b2 + b4
                                  swap
                                  · omega
                                  by_cases c1591 : b0 + b2 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f1592 := pair_fact E (i := 4) (j := 4) rfl rfl c1588 c1589
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1592
                                  by_cases c1593 : 0 < a4
                                  swap
                                  · omega
                                  by_cases c1594 : 0 < b6
                                  swap
                                  · -- branch
                                    by_cases c1595 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1596 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c1597 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c1598 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                                    swap
                                    · -- branch
                                      by_cases c1599 : 0 < a4
                                      swap
                                      · omega
                                      by_cases c1600 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c1601 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c1602 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                                      swap
                                      · -- branch
                                        by_cases c1603 : 0 < a8
                                        swap
                                        · omega
                                        by_cases c1604 : 0 < b0
                                        swap
                                        · omega
                                        by_cases c1605 : a0 + a2 + a4 + a6 < 0 + b0
                                        swap
                                        · -- branch
                                          by_cases c1606 : 0 < a8
                                          swap
                                          · omega
                                          by_cases c1607 : 0 < b2
                                          swap
                                          · -- branch
                                            by_cases c1608 : 0 < a8
                                            swap
                                            · omega
                                            by_cases c1609 : 0 < b4
                                            swap
                                            · omega
                                            by_cases c1610 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                            swap
                                            · -- branch
                                              by_cases c1611 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c1612 : 0 < b8
                                              swap
                                              · omega
                                              by_cases c1613 : a0 + a2 + a4 < b0 + b2 + b4 + b6 + b8
                                              swap
                                              · omega
                                              by_cases c1614 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f1615 := pair_fact E (i := 6) (j := 8) rfl rfl c1611 c1612
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1615
                                              by_cases c1616 : 0 < a6
                                              swap
                                              · omega
                                              by_cases c1617 : 0 < b4
                                              swap
                                              · omega
                                              by_cases c1618 : a0 + a2 + a4 < b0 + b2 + b4
                                              swap
                                              · -- branch
                                                by_cases c1619 : 0 < a8
                                                swap
                                                · omega
                                                by_cases c1620 : 0 < b6
                                                swap
                                                · -- branch
                                                  by_cases c1621 : 0 < a8
                                                  swap
                                                  · omega
                                                  by_cases c1622 : 0 < b8
                                                  swap
                                                  · omega
                                                  by_cases c1623 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                                  swap
                                                  · omega
                                                  by_cases c1624 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · omega
                                                  have f1625 := pair_fact E (i := 8) (j := 8) rfl rfl c1621 c1622
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1625
                                                  by_cases c1626 : 0 < a8
                                                  swap
                                                  · omega
                                                  by_cases c1627 : 0 < b10
                                                  swap
                                                  · omega
                                                  by_cases c1628 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                                  swap
                                                  · omega
                                                  by_cases c1629 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                                  swap
                                                  · -- branch
                                                    by_cases c1630 : 0 < a10
                                                    swap
                                                    · omega
                                                    by_cases c1631 : 0 < b8
                                                    swap
                                                    · omega
                                                    by_cases c1632 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                                    swap
                                                    · omega
                                                    by_cases c1633 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                                    swap
                                                    · omega
                                                    have f1634 := pair_fact E (i := 10) (j := 8) rfl rfl c1630 c1631
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1634
                                                    omega
                                                  have f1635 := pair_fact E (i := 8) (j := 10) rfl rfl c1626 c1627
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1635
                                                  omega
                                                by_cases c1636 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6
                                                swap
                                                · omega
                                                by_cases c1637 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8
                                                swap
                                                · omega
                                                have f1638 := pair_fact E (i := 8) (j := 6) rfl rfl c1619 c1620
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1638
                                                omega
                                              by_cases c1639 : b0 + b2 < a0 + a2 + a4 + a6
                                              swap
                                              · omega
                                              have f1640 := pair_fact E (i := 6) (j := 4) rfl rfl c1616 c1617
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1640
                                              omega
                                            by_cases c1641 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                            swap
                                            · omega
                                            have f1642 := pair_fact E (i := 8) (j := 4) rfl rfl c1608 c1609
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1642
                                            omega
                                          by_cases c1643 : a0 + a2 + a4 + a6 < b0 + b2
                                          swap
                                          · omega
                                          by_cases c1644 : b0 < a0 + a2 + a4 + a6 + a8
                                          swap
                                          · omega
                                          have f1645 := pair_fact E (i := 8) (j := 2) rfl rfl c1606 c1607
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1645
                                          omega
                                        by_cases c1646 : 0 < a0 + a2 + a4 + a6 + a8
                                        swap
                                        · omega
                                        have f1647 := pair_fact E (i := 8) (j := 0) rfl rfl c1603 c1604
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1647
                                        omega
                                      have f1648 := pair_fact E (i := 4) (j := 10) rfl rfl c1599 c1600
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1648
                                      omega
                                    have f1649 := pair_fact E (i := 4) (j := 8) rfl rfl c1595 c1596
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1649
                                    omega
                                  by_cases c1650 : a0 + a2 < b0 + b2 + b4 + b6
                                  swap
                                  · omega
                                  by_cases c1651 : b0 + b2 + b4 < a0 + a2 + a4
                                  swap
                                  · omega
                                  have f1652 := pair_fact E (i := 4) (j := 6) rfl rfl c1593 c1594
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1652
                                  omega
                                by_cases c1653 : a0 + a2 < b0 + b2
                                swap
                                · omega
                                by_cases c1654 : b0 < a0 + a2 + a4
                                swap
                                · omega
                                have f1655 := pair_fact E (i := 4) (j := 2) rfl rfl c1586 c1587
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1655
                                omega
                              by_cases c1656 : 0 < a0 + a2 + a4
                              swap
                              · omega
                              have f1657 := pair_fact E (i := 4) (j := 0) rfl rfl c1578 c1584
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1657
                              omega
                            by_cases c1658 : a0 + a2 + a4 < b0 + b2
                            swap
                            · omega
                            by_cases c1659 : b0 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f1660 := pair_fact E (i := 6) (j := 2) rfl rfl c1576 c1577
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1660
                            omega
                          by_cases c1661 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c1662 : b0 < a0 + a2
                          swap
                          · omega
                          have f1663 := pair_fact E (i := 2) (j := 2) rfl rfl c1574 c1575
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1663
                          omega
                        by_cases c1664 : 0 < b0 + b2
                        swap
                        · omega
                        by_cases c1665 : b0 < 0 + a0
                        swap
                        · -- branch
                          by_cases c1666 : 0 < a2
                          swap
                          · omega
                          by_cases c1667 : 0 < b2
                          swap
                          · omega
                          by_cases c1668 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c1669 : b0 < a0 + a2
                          swap
                          · omega
                          have f1670 := pair_fact E (i := 2) (j := 2) rfl rfl c1666 c1667
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1670
                          by_cases c1671 : 0 < a4
                          swap
                          · -- branch
                            by_cases c1672 : 0 < a6
                            swap
                            · omega
                            by_cases c1673 : 0 < b4
                            swap
                            · omega
                            by_cases c1674 : a0 + a2 + a4 < b0 + b2 + b4
                            swap
                            · omega
                            by_cases c1675 : b0 + b2 < a0 + a2 + a4 + a6
                            swap
                            · omega
                            have f1676 := pair_fact E (i := 6) (j := 4) rfl rfl c1672 c1673
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1676
                            omega
                          by_cases c1677 : 0 < b4
                          swap
                          · omega
                          by_cases c1678 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1679 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f1680 := pair_fact E (i := 4) (j := 4) rfl rfl c1671 c1677
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1680
                          omega
                        have f1681 := pair_fact E (i := 0) (j := 2) rfl rfl c1572 c1573
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1681
                        omega
                      by_cases c1682 : 0 < a0 + a2
                      swap
                      · omega
                      have f1683 := pair_fact E (i := 2) (j := 0) rfl rfl c1529 c1530
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1683
                      by_cases c1684 : 0 < a2
                      swap
                      · omega
                      by_cases c1685 : 0 < b4
                      swap
                      · omega
                      by_cases c1686 : a0 < b0 + b2 + b4
                      swap
                      · omega
                      by_cases c1687 : b0 + b2 < a0 + a2
                      swap
                      · -- branch
                        by_cases c1688 : 0 < a0
                        swap
                        · omega
                        by_cases c1689 : 0 < b2
                        swap
                        · omega
                        by_cases c1690 : 0 < b0 + b2
                        swap
                        · omega
                        by_cases c1691 : b0 < 0 + a0
                        swap
                        · -- branch
                          by_cases c1692 : 0 < a2
                          swap
                          · omega
                          by_cases c1693 : 0 < b2
                          swap
                          · omega
                          by_cases c1694 : a0 < b0 + b2
                          swap
                          · omega
                          by_cases c1695 : b0 < a0 + a2
                          swap
                          · -- branch
                            by_cases c1696 : 0 < a4
                            swap
                            · omega
                            by_cases c1697 : 0 < b2
                            swap
                            · omega
                            by_cases c1698 : a0 + a2 < b0 + b2
                            swap
                            · omega
                            by_cases c1699 : b0 < a0 + a2 + a4
                            swap
                            · omega
                            have f1700 := pair_fact E (i := 4) (j := 2) rfl rfl c1696 c1697
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1700
                            omega
                          have f1701 := pair_fact E (i := 2) (j := 2) rfl rfl c1692 c1693
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1701
                          omega
                        have f1702 := pair_fact E (i := 0) (j := 2) rfl rfl c1688 c1689
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1702
                        omega
                      have f1703 := pair_fact E (i := 2) (j := 4) rfl rfl c1684 c1685
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1703
                      omega
                    have f1704 := pair_fact E (i := 2) (j := 10) rfl rfl c1525 c1526
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1704
                    omega
                  have f1705 := pair_fact E (i := 2) (j := 8) rfl rfl c1521 c1522
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1705
                  omega
                by_cases c1706 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c1707 : b0 + b2 + b4 < a0 + a2
                swap
                · omega
                have f1708 := pair_fact E (i := 2) (j := 6) rfl rfl c1409 c1520
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1708
                omega
              have f1709 := pair_fact E (i := 6) (j := 10) rfl rfl c1405 c1406
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1709
              omega
            have f1710 := pair_fact E (i := 0) (j := 10) rfl rfl c1151 c1152
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1710
            omega
          have f1711 := pair_fact E (i := 0) (j := 8) rfl rfl c1142 c1143
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1711
          omega
        have f1712 := pair_fact E (i := 0) (j := 4) rfl rfl c1138 c1139
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1712
        by_cases c1713 : 0 < a2
        swap
        · omega
        by_cases c1714 : 0 < b4
        swap
        · omega
        by_cases c1715 : a0 < b0 + b2 + b4
        swap
        · omega
        by_cases c1716 : b0 + b2 < a0 + a2
        swap
        · omega
        have f1717 := pair_fact E (i := 2) (j := 4) rfl rfl c1713 c1714
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1717
        omega
      by_cases c1718 : a0 + a2 + a4 < b0 + b2 + b4 + b6
      swap
      · omega
      by_cases c1719 : b0 + b2 + b4 < a0 + a2 + a4 + a6
      swap
      · omega
      have f1720 := pair_fact E (i := 6) (j := 6) rfl rfl c1136 c1137
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1720
      omega
    by_cases c1721 : 0 < a0 + a2 + a4 + a6
    swap
    · omega
    have f1722 := pair_fact E (i := 6) (j := 0) rfl rfl c1133 c1134
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1722
    omega
  by_cases c1723 : 0 < b0 + b2 + b4 + b6
  swap
  · omega
  by_cases c1724 : b0 + b2 + b4 < 0 + a0
  swap
  · -- branch
    by_cases c1725 : 0 < a0
    swap
    · omega
    by_cases c1726 : 0 < b8
    swap
    · -- branch
      by_cases c1727 : 0 < a8
      swap
      · omega
      by_cases c1728 : 0 < b4
      swap
      · omega
      by_cases c1729 : a0 + a2 + a4 + a6 < b0 + b2 + b4
      swap
      · omega
      by_cases c1730 : b0 + b2 < a0 + a2 + a4 + a6 + a8
      swap
      · omega
      have f1731 := pair_fact E (i := 8) (j := 4) rfl rfl c1727 c1728
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1731
      omega
    by_cases c1732 : 0 < b0 + b2 + b4 + b6 + b8
    swap
    · omega
    by_cases c1733 : b0 + b2 + b4 + b6 < 0 + a0
    swap
    · -- branch
      by_cases c1734 : 0 < a0
      swap
      · omega
      by_cases c1735 : 0 < b10
      swap
      · -- branch
        by_cases c1736 : 0 < a2
        swap
        · -- branch
          by_cases c1737 : 0 < a2
          swap
          · -- branch
            by_cases c1738 : 0 < a2
            swap
            · -- branch
              by_cases c1739 : 0 < a2
              swap
              · -- branch
                by_cases c1740 : 0 < a2
                swap
                · -- branch
                  by_cases c1741 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1742 : 0 < a4
                    swap
                    · omega
                    by_cases c1743 : 0 < b2
                    swap
                    · omega
                    by_cases c1744 : a0 + a2 < b0 + b2
                    swap
                    · omega
                    by_cases c1745 : b0 < a0 + a2 + a4
                    swap
                    · omega
                    have f1746 := pair_fact E (i := 4) (j := 2) rfl rfl c1742 c1743
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1746
                    by_cases c1747 : 0 < a0
                    swap
                    · omega
                    by_cases c1748 : 0 < b2
                    swap
                    · omega
                    by_cases c1749 : 0 < b0 + b2
                    swap
                    · omega
                    by_cases c1750 : b0 < 0 + a0
                    swap
                    · -- branch
                      by_cases c1751 : 0 < a4
                      swap
                      · omega
                      by_cases c1752 : 0 < b0
                      swap
                      · omega
                      by_cases c1753 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c1754 : 0 < a4
                        swap
                        · omega
                        by_cases c1755 : 0 < b8
                        swap
                        · omega
                        by_cases c1756 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1757 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                        swap
                        · -- branch
                          by_cases c1758 : 0 < a0
                          swap
                          · omega
                          by_cases c1759 : 0 < b4
                          swap
                          · omega
                          by_cases c1760 : 0 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1761 : b0 + b2 < 0 + a0
                          swap
                          · -- branch
                            by_cases c1762 : 0 < a4
                            swap
                            · omega
                            by_cases c1763 : 0 < b10
                            swap
                            · -- branch
                              by_cases c1764 : 0 < a8
                              swap
                              · omega
                              by_cases c1765 : 0 < b0
                              swap
                              · omega
                              by_cases c1766 : a0 + a2 + a4 + a6 < 0 + b0
                              swap
                              · -- branch
                                by_cases c1767 : 0 < a8
                                swap
                                · omega
                                by_cases c1768 : 0 < b2
                                swap
                                · omega
                                by_cases c1769 : a0 + a2 + a4 + a6 < b0 + b2
                                swap
                                · -- branch
                                  by_cases c1770 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c1771 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c1772 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                  swap
                                  · -- branch
                                    by_cases c1773 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1774 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c1775 : a0 + a2 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c1776 : b0 + b2 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f1777 := pair_fact E (i := 4) (j := 4) rfl rfl c1773 c1774
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1777
                                    by_cases c1778 : 0 < a8
                                    swap
                                    · omega
                                    by_cases c1779 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c1780 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c1781 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                                    swap
                                    · omega
                                    have f1782 := pair_fact E (i := 8) (j := 8) rfl rfl c1778 c1779
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1782
                                    by_cases c1783 : 0 < a10
                                    swap
                                    · omega
                                    by_cases c1784 : 0 < b8
                                    swap
                                    · omega
                                    by_cases c1785 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                    swap
                                    · omega
                                    by_cases c1786 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                    swap
                                    · omega
                                    have f1787 := pair_fact E (i := 10) (j := 8) rfl rfl c1783 c1784
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1787
                                    omega
                                  by_cases c1788 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f1789 := pair_fact E (i := 8) (j := 4) rfl rfl c1770 c1771
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1789
                                  omega
                                by_cases c1790 : b0 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f1791 := pair_fact E (i := 8) (j := 2) rfl rfl c1767 c1768
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1791
                                omega
                              by_cases c1792 : 0 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f1793 := pair_fact E (i := 8) (j := 0) rfl rfl c1764 c1765
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1793
                              omega
                            by_cases c1794 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c1795 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                            swap
                            · omega
                            have f1796 := pair_fact E (i := 4) (j := 10) rfl rfl c1762 c1763
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1796
                            omega
                          have f1797 := pair_fact E (i := 0) (j := 4) rfl rfl c1758 c1759
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1797
                          omega
                        have f1798 := pair_fact E (i := 4) (j := 8) rfl rfl c1754 c1755
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1798
                        omega
                      by_cases c1799 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f1800 := pair_fact E (i := 4) (j := 0) rfl rfl c1751 c1752
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1800
                      omega
                    have f1801 := pair_fact E (i := 0) (j := 2) rfl rfl c1747 c1748
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1801
                    omega
                  by_cases c1802 : 0 < b10
                  swap
                  · omega
                  by_cases c1803 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c1804 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                  swap
                  · omega
                  have f1805 := pair_fact E (i := 2) (j := 10) rfl rfl c1741 c1802
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1805
                  omega
                by_cases c1806 : 0 < b6
                swap
                · omega
                by_cases c1807 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c1808 : b0 + b2 + b4 < a0 + a2
                swap
                · omega
                have f1809 := pair_fact E (i := 2) (j := 6) rfl rfl c1740 c1806
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1809
                omega
              by_cases c1810 : 0 < b4
              swap
              · omega
              by_cases c1811 : a0 < b0 + b2 + b4
              swap
              · omega
              by_cases c1812 : b0 + b2 < a0 + a2
              swap
              · omega
              have f1813 := pair_fact E (i := 2) (j := 4) rfl rfl c1739 c1810
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1813
              omega
            by_cases c1814 : 0 < b2
            swap
            · omega
            by_cases c1815 : a0 < b0 + b2
            swap
            · omega
            by_cases c1816 : b0 < a0 + a2
            swap
            · omega
            have f1817 := pair_fact E (i := 2) (j := 2) rfl rfl c1738 c1814
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1817
            omega
          by_cases c1818 : 0 < b0
          swap
          · omega
          by_cases c1819 : a0 < 0 + b0
          swap
          · omega
          by_cases c1820 : 0 < a0 + a2
          swap
          · omega
          have f1821 := pair_fact E (i := 2) (j := 0) rfl rfl c1737 c1818
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1821
          omega
        by_cases c1822 : 0 < b8
        swap
        · omega
        by_cases c1823 : a0 < b0 + b2 + b4 + b6 + b8
        swap
        · omega
        by_cases c1824 : b0 + b2 + b4 + b6 < a0 + a2
        swap
        · -- branch
          by_cases c1825 : 0 < a2
          swap
          · omega
          by_cases c1826 : 0 < b10
          swap
          · -- branch
            by_cases c1827 : 0 < a2
            swap
            · omega
            by_cases c1828 : 0 < b0
            swap
            · omega
            by_cases c1829 : a0 < 0 + b0
            swap
            · -- branch
              by_cases c1830 : 0 < a2
              swap
              · omega
              by_cases c1831 : 0 < b6
              swap
              · omega
              by_cases c1832 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c1833 : b0 + b2 + b4 < a0 + a2
              swap
              · -- branch
                by_cases c1834 : 0 < a4
                swap
                · -- branch
                  by_cases c1835 : 0 < a8
                  swap
                  · omega
                  by_cases c1836 : 0 < b4
                  swap
                  · omega
                  by_cases c1837 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c1838 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                  swap
                  · omega
                  have f1839 := pair_fact E (i := 8) (j := 4) rfl rfl c1835 c1836
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1839
                  omega
                by_cases c1840 : 0 < b0
                swap
                · omega
                by_cases c1841 : a0 + a2 < 0 + b0
                swap
                · -- branch
                  by_cases c1842 : 0 < a4
                  swap
                  · omega
                  by_cases c1843 : 0 < b8
                  swap
                  · omega
                  by_cases c1844 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c1845 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                  swap
                  · -- branch
                    by_cases c1846 : 0 < a4
                    swap
                    · omega
                    by_cases c1847 : 0 < b10
                    swap
                    · -- branch
                      by_cases c1848 : 0 < a8
                      swap
                      · omega
                      by_cases c1849 : 0 < b0
                      swap
                      · omega
                      by_cases c1850 : a0 + a2 + a4 + a6 < 0 + b0
                      swap
                      · -- branch
                        by_cases c1851 : 0 < a8
                        swap
                        · omega
                        by_cases c1852 : 0 < b4
                        swap
                        · omega
                        by_cases c1853 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                        swap
                        · -- branch
                          by_cases c1854 : 0 < a4
                          swap
                          · omega
                          by_cases c1855 : 0 < b4
                          swap
                          · omega
                          by_cases c1856 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1857 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f1858 := pair_fact E (i := 4) (j := 4) rfl rfl c1854 c1855
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1858
                          by_cases c1859 : 0 < a0
                          swap
                          · omega
                          by_cases c1860 : 0 < b4
                          swap
                          · omega
                          by_cases c1861 : 0 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1862 : b0 + b2 < 0 + a0
                          swap
                          · -- branch
                            by_cases c1863 : 0 < a8
                            swap
                            · omega
                            by_cases c1864 : 0 < b8
                            swap
                            · omega
                            by_cases c1865 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c1866 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f1867 := pair_fact E (i := 8) (j := 8) rfl rfl c1863 c1864
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1867
                            by_cases c1868 : 0 < a4
                            swap
                            · omega
                            by_cases c1869 : 0 < b6
                            swap
                            · omega
                            by_cases c1870 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c1871 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c1872 : 0 < a8
                              swap
                              · omega
                              by_cases c1873 : 0 < b10
                              swap
                              · -- branch
                                by_cases c1874 : 0 < a10
                                swap
                                · -- branch
                                  by_cases c1875 : 0 < a0
                                  swap
                                  · omega
                                  by_cases c1876 : 0 < b2
                                  swap
                                  · omega
                                  by_cases c1877 : 0 < b0 + b2
                                  swap
                                  · omega
                                  by_cases c1878 : b0 < 0 + a0
                                  swap
                                  · omega
                                  have f1879 := pair_fact E (i := 0) (j := 2) rfl rfl c1875 c1876
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1879
                                  omega
                                by_cases c1880 : 0 < b8
                                swap
                                · omega
                                by_cases c1881 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                swap
                                · omega
                                by_cases c1882 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f1883 := pair_fact E (i := 10) (j := 8) rfl rfl c1874 c1880
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1883
                                omega
                              by_cases c1884 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c1885 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f1886 := pair_fact E (i := 8) (j := 10) rfl rfl c1872 c1873
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1886
                              omega
                            have f1887 := pair_fact E (i := 4) (j := 6) rfl rfl c1868 c1869
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1887
                            omega
                          have f1888 := pair_fact E (i := 0) (j := 4) rfl rfl c1859 c1860
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1888
                          omega
                        by_cases c1889 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f1890 := pair_fact E (i := 8) (j := 4) rfl rfl c1851 c1852
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1890
                        omega
                      by_cases c1891 : 0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f1892 := pair_fact E (i := 8) (j := 0) rfl rfl c1848 c1849
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1892
                      omega
                    by_cases c1893 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c1894 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                    swap
                    · omega
                    have f1895 := pair_fact E (i := 4) (j := 10) rfl rfl c1846 c1847
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1895
                    omega
                  have f1896 := pair_fact E (i := 4) (j := 8) rfl rfl c1842 c1843
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1896
                  omega
                by_cases c1897 : 0 < a0 + a2 + a4
                swap
                · omega
                have f1898 := pair_fact E (i := 4) (j := 0) rfl rfl c1834 c1840
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1898
                omega
              have f1899 := pair_fact E (i := 2) (j := 6) rfl rfl c1830 c1831
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1899
              by_cases c1900 : 0 < a4
              swap
              · omega
              by_cases c1901 : 0 < b8
              swap
              · omega
              by_cases c1902 : a0 + a2 < b0 + b2 + b4 + b6 + b8
              swap
              · omega
              by_cases c1903 : b0 + b2 + b4 + b6 < a0 + a2 + a4
              swap
              · omega
              have f1904 := pair_fact E (i := 4) (j := 8) rfl rfl c1900 c1901
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1904
              omega
            by_cases c1905 : 0 < a0 + a2
            swap
            · omega
            have f1906 := pair_fact E (i := 2) (j := 0) rfl rfl c1827 c1828
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1906
            by_cases c1907 : 0 < a2
            swap
            · omega
            by_cases c1908 : 0 < b6
            swap
            · omega
            by_cases c1909 : a0 < b0 + b2 + b4 + b6
            swap
            · omega
            by_cases c1910 : b0 + b2 + b4 < a0 + a2
            swap
            · -- branch
              by_cases c1911 : 0 < a0
              swap
              · omega
              by_cases c1912 : 0 < b2
              swap
              · -- branch
                by_cases c1913 : 0 < a2
                swap
                · omega
                by_cases c1914 : 0 < b4
                swap
                · omega
                by_cases c1915 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c1916 : b0 + b2 < a0 + a2
                swap
                · omega
                have f1917 := pair_fact E (i := 2) (j := 4) rfl rfl c1913 c1914
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1917
                omega
              by_cases c1918 : 0 < b0 + b2
              swap
              · omega
              by_cases c1919 : b0 < 0 + a0
              swap
              · -- branch
                by_cases c1920 : 0 < a2
                swap
                · omega
                by_cases c1921 : 0 < b2
                swap
                · omega
                by_cases c1922 : a0 < b0 + b2
                swap
                · omega
                by_cases c1923 : b0 < a0 + a2
                swap
                · -- branch
                  by_cases c1924 : 0 < a4
                  swap
                  · omega
                  by_cases c1925 : 0 < b2
                  swap
                  · omega
                  by_cases c1926 : a0 + a2 < b0 + b2
                  swap
                  · omega
                  by_cases c1927 : b0 < a0 + a2 + a4
                  swap
                  · omega
                  have f1928 := pair_fact E (i := 4) (j := 2) rfl rfl c1924 c1925
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1928
                  omega
                have f1929 := pair_fact E (i := 2) (j := 2) rfl rfl c1920 c1921
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1929
                omega
              have f1930 := pair_fact E (i := 0) (j := 2) rfl rfl c1911 c1912
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1930
              omega
            have f1931 := pair_fact E (i := 2) (j := 6) rfl rfl c1907 c1908
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1931
            omega
          by_cases c1932 : a0 < b0 + b2 + b4 + b6 + b8 + b10
          swap
          · omega
          by_cases c1933 : b0 + b2 + b4 + b6 + b8 < a0 + a2
          swap
          · omega
          have f1934 := pair_fact E (i := 2) (j := 10) rfl rfl c1825 c1826
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1934
          omega
        have f1935 := pair_fact E (i := 2) (j := 8) rfl rfl c1736 c1822
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1935
        omega
      by_cases c1936 : 0 < b0 + b2 + b4 + b6 + b8 + b10
      swap
      · omega
      by_cases c1937 : b0 + b2 + b4 + b6 + b8 < 0 + a0
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
              by_cases c1941 : 0 < a2
              swap
              · -- branch
                by_cases c1942 : 0 < a2
                swap
                · -- branch
                  by_cases c1943 : 0 < a2
                  swap
                  · -- branch
                    by_cases c1944 : 0 < a4
                    swap
                    · omega
                    by_cases c1945 : 0 < b2
                    swap
                    · omega
                    by_cases c1946 : a0 + a2 < b0 + b2
                    swap
                    · omega
                    by_cases c1947 : b0 < a0 + a2 + a4
                    swap
                    · omega
                    have f1948 := pair_fact E (i := 4) (j := 2) rfl rfl c1944 c1945
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1948
                    by_cases c1949 : 0 < a0
                    swap
                    · omega
                    by_cases c1950 : 0 < b2
                    swap
                    · omega
                    by_cases c1951 : 0 < b0 + b2
                    swap
                    · omega
                    by_cases c1952 : b0 < 0 + a0
                    swap
                    · -- branch
                      by_cases c1953 : 0 < a4
                      swap
                      · omega
                      by_cases c1954 : 0 < b0
                      swap
                      · omega
                      by_cases c1955 : a0 + a2 < 0 + b0
                      swap
                      · -- branch
                        by_cases c1956 : 0 < a4
                        swap
                        · omega
                        by_cases c1957 : 0 < b8
                        swap
                        · omega
                        by_cases c1958 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                        swap
                        · omega
                        by_cases c1959 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                        swap
                        · -- branch
                          by_cases c1960 : 0 < a0
                          swap
                          · omega
                          by_cases c1961 : 0 < b4
                          swap
                          · omega
                          by_cases c1962 : 0 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c1963 : b0 + b2 < 0 + a0
                          swap
                          · -- branch
                            by_cases c1964 : 0 < a4
                            swap
                            · omega
                            by_cases c1965 : 0 < b10
                            swap
                            · omega
                            by_cases c1966 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                            swap
                            · omega
                            by_cases c1967 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c1968 : 0 < a8
                              swap
                              · omega
                              by_cases c1969 : 0 < b0
                              swap
                              · omega
                              by_cases c1970 : a0 + a2 + a4 + a6 < 0 + b0
                              swap
                              · -- branch
                                by_cases c1971 : 0 < a8
                                swap
                                · omega
                                by_cases c1972 : 0 < b2
                                swap
                                · omega
                                by_cases c1973 : a0 + a2 + a4 + a6 < b0 + b2
                                swap
                                · -- branch
                                  by_cases c1974 : 0 < a8
                                  swap
                                  · omega
                                  by_cases c1975 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c1976 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                                  swap
                                  · -- branch
                                    by_cases c1977 : 0 < a4
                                    swap
                                    · omega
                                    by_cases c1978 : 0 < b4
                                    swap
                                    · omega
                                    by_cases c1979 : a0 + a2 < b0 + b2 + b4
                                    swap
                                    · omega
                                    by_cases c1980 : b0 + b2 < a0 + a2 + a4
                                    swap
                                    · omega
                                    have f1981 := pair_fact E (i := 4) (j := 4) rfl rfl c1977 c1978
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
                                    · -- branch
                                      by_cases c1991 : 0 < a8
                                      swap
                                      · omega
                                      by_cases c1992 : 0 < b10
                                      swap
                                      · omega
                                      by_cases c1993 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                                      swap
                                      · omega
                                      by_cases c1994 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                                      swap
                                      · -- branch
                                        by_cases c1995 : 0 < a10
                                        swap
                                        · omega
                                        by_cases c1996 : 0 < b8
                                        swap
                                        · omega
                                        by_cases c1997 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                        swap
                                        · omega
                                        by_cases c1998 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                        swap
                                        · omega
                                        have f1999 := pair_fact E (i := 10) (j := 8) rfl rfl c1995 c1996
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f1999
                                        omega
                                      have f2000 := pair_fact E (i := 8) (j := 10) rfl rfl c1991 c1992
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2000
                                      omega
                                    have f2001 := pair_fact E (i := 4) (j := 6) rfl rfl c1987 c1988
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2001
                                    omega
                                  by_cases c2002 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                                  swap
                                  · omega
                                  have f2003 := pair_fact E (i := 8) (j := 4) rfl rfl c1974 c1975
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2003
                                  omega
                                by_cases c2004 : b0 < a0 + a2 + a4 + a6 + a8
                                swap
                                · omega
                                have f2005 := pair_fact E (i := 8) (j := 2) rfl rfl c1971 c1972
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2005
                                omega
                              by_cases c2006 : 0 < a0 + a2 + a4 + a6 + a8
                              swap
                              · omega
                              have f2007 := pair_fact E (i := 8) (j := 0) rfl rfl c1968 c1969
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2007
                              omega
                            have f2008 := pair_fact E (i := 4) (j := 10) rfl rfl c1964 c1965
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2008
                            omega
                          have f2009 := pair_fact E (i := 0) (j := 4) rfl rfl c1960 c1961
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2009
                          omega
                        have f2010 := pair_fact E (i := 4) (j := 8) rfl rfl c1956 c1957
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2010
                        omega
                      by_cases c2011 : 0 < a0 + a2 + a4
                      swap
                      · omega
                      have f2012 := pair_fact E (i := 4) (j := 0) rfl rfl c1953 c1954
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2012
                      omega
                    have f2013 := pair_fact E (i := 0) (j := 2) rfl rfl c1949 c1950
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2013
                    omega
                  by_cases c2014 : 0 < b10
                  swap
                  · omega
                  by_cases c2015 : a0 < b0 + b2 + b4 + b6 + b8 + b10
                  swap
                  · omega
                  by_cases c2016 : b0 + b2 + b4 + b6 + b8 < a0 + a2
                  swap
                  · omega
                  have f2017 := pair_fact E (i := 2) (j := 10) rfl rfl c1943 c2014
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2017
                  omega
                by_cases c2018 : 0 < b6
                swap
                · omega
                by_cases c2019 : a0 < b0 + b2 + b4 + b6
                swap
                · omega
                by_cases c2020 : b0 + b2 + b4 < a0 + a2
                swap
                · omega
                have f2021 := pair_fact E (i := 2) (j := 6) rfl rfl c1942 c2018
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2021
                omega
              by_cases c2022 : 0 < b4
              swap
              · omega
              by_cases c2023 : a0 < b0 + b2 + b4
              swap
              · omega
              by_cases c2024 : b0 + b2 < a0 + a2
              swap
              · omega
              have f2025 := pair_fact E (i := 2) (j := 4) rfl rfl c1941 c2022
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2025
              omega
            by_cases c2026 : 0 < b2
            swap
            · omega
            by_cases c2027 : a0 < b0 + b2
            swap
            · omega
            by_cases c2028 : b0 < a0 + a2
            swap
            · omega
            have f2029 := pair_fact E (i := 2) (j := 2) rfl rfl c1940 c2026
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2029
            omega
          by_cases c2030 : 0 < b0
          swap
          · omega
          by_cases c2031 : a0 < 0 + b0
          swap
          · omega
          by_cases c2032 : 0 < a0 + a2
          swap
          · omega
          have f2033 := pair_fact E (i := 2) (j := 0) rfl rfl c1939 c2030
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2033
          omega
        by_cases c2034 : 0 < b8
        swap
        · omega
        by_cases c2035 : a0 < b0 + b2 + b4 + b6 + b8
        swap
        · omega
        by_cases c2036 : b0 + b2 + b4 + b6 < a0 + a2
        swap
        · -- branch
          by_cases c2037 : 0 < a2
          swap
          · omega
          by_cases c2038 : 0 < b10
          swap
          · omega
          by_cases c2039 : a0 < b0 + b2 + b4 + b6 + b8 + b10
          swap
          · omega
          by_cases c2040 : b0 + b2 + b4 + b6 + b8 < a0 + a2
          swap
          · -- branch
            by_cases c2041 : 0 < a2
            swap
            · omega
            by_cases c2042 : 0 < b0
            swap
            · omega
            by_cases c2043 : a0 < 0 + b0
            swap
            · -- branch
              by_cases c2044 : 0 < a2
              swap
              · omega
              by_cases c2045 : 0 < b6
              swap
              · omega
              by_cases c2046 : a0 < b0 + b2 + b4 + b6
              swap
              · omega
              by_cases c2047 : b0 + b2 + b4 < a0 + a2
              swap
              · -- branch
                by_cases c2048 : 0 < a4
                swap
                · -- branch
                  by_cases c2049 : 0 < a8
                  swap
                  · omega
                  by_cases c2050 : 0 < b4
                  swap
                  · omega
                  by_cases c2051 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                  swap
                  · omega
                  by_cases c2052 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                  swap
                  · omega
                  have f2053 := pair_fact E (i := 8) (j := 4) rfl rfl c2049 c2050
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2053
                  omega
                by_cases c2054 : 0 < b0
                swap
                · omega
                by_cases c2055 : a0 + a2 < 0 + b0
                swap
                · -- branch
                  by_cases c2056 : 0 < a4
                  swap
                  · omega
                  by_cases c2057 : 0 < b8
                  swap
                  · omega
                  by_cases c2058 : a0 + a2 < b0 + b2 + b4 + b6 + b8
                  swap
                  · omega
                  by_cases c2059 : b0 + b2 + b4 + b6 < a0 + a2 + a4
                  swap
                  · -- branch
                    by_cases c2060 : 0 < a4
                    swap
                    · omega
                    by_cases c2061 : 0 < b10
                    swap
                    · omega
                    by_cases c2062 : a0 + a2 < b0 + b2 + b4 + b6 + b8 + b10
                    swap
                    · omega
                    by_cases c2063 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4
                    swap
                    · -- branch
                      by_cases c2064 : 0 < a8
                      swap
                      · omega
                      by_cases c2065 : 0 < b0
                      swap
                      · omega
                      by_cases c2066 : a0 + a2 + a4 + a6 < 0 + b0
                      swap
                      · -- branch
                        by_cases c2067 : 0 < a8
                        swap
                        · omega
                        by_cases c2068 : 0 < b4
                        swap
                        · omega
                        by_cases c2069 : a0 + a2 + a4 + a6 < b0 + b2 + b4
                        swap
                        · -- branch
                          by_cases c2070 : 0 < a4
                          swap
                          · omega
                          by_cases c2071 : 0 < b4
                          swap
                          · omega
                          by_cases c2072 : a0 + a2 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c2073 : b0 + b2 < a0 + a2 + a4
                          swap
                          · omega
                          have f2074 := pair_fact E (i := 4) (j := 4) rfl rfl c2070 c2071
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2074
                          by_cases c2075 : 0 < a0
                          swap
                          · omega
                          by_cases c2076 : 0 < b4
                          swap
                          · omega
                          by_cases c2077 : 0 < b0 + b2 + b4
                          swap
                          · omega
                          by_cases c2078 : b0 + b2 < 0 + a0
                          swap
                          · -- branch
                            by_cases c2079 : 0 < a8
                            swap
                            · omega
                            by_cases c2080 : 0 < b8
                            swap
                            · omega
                            by_cases c2081 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8
                            swap
                            · omega
                            by_cases c2082 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8
                            swap
                            · omega
                            have f2083 := pair_fact E (i := 8) (j := 8) rfl rfl c2079 c2080
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2083
                            by_cases c2084 : 0 < a4
                            swap
                            · omega
                            by_cases c2085 : 0 < b6
                            swap
                            · omega
                            by_cases c2086 : a0 + a2 < b0 + b2 + b4 + b6
                            swap
                            · omega
                            by_cases c2087 : b0 + b2 + b4 < a0 + a2 + a4
                            swap
                            · -- branch
                              by_cases c2088 : 0 < a8
                              swap
                              · omega
                              by_cases c2089 : 0 < b10
                              swap
                              · omega
                              by_cases c2090 : a0 + a2 + a4 + a6 < b0 + b2 + b4 + b6 + b8 + b10
                              swap
                              · omega
                              by_cases c2091 : b0 + b2 + b4 + b6 + b8 < a0 + a2 + a4 + a6 + a8
                              swap
                              · -- branch
                                by_cases c2092 : 0 < a10
                                swap
                                · omega
                                by_cases c2093 : 0 < b0
                                swap
                                · omega
                                by_cases c2094 : a0 + a2 + a4 + a6 + a8 < 0 + b0
                                swap
                                · -- branch
                                  by_cases c2095 : 0 < a10
                                  swap
                                  · omega
                                  by_cases c2096 : 0 < b4
                                  swap
                                  · omega
                                  by_cases c2097 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4
                                  swap
                                  · -- branch
                                    by_cases c2098 : 0 < a10
                                    swap
                                    · omega
                                    by_cases c2099 : 0 < b6
                                    swap
                                    · omega
                                    by_cases c2100 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6
                                    swap
                                    · -- branch
                                      by_cases c2101 : 0 < a10
                                      swap
                                      · omega
                                      by_cases c2102 : 0 < b8
                                      swap
                                      · omega
                                      by_cases c2103 : a0 + a2 + a4 + a6 + a8 < b0 + b2 + b4 + b6 + b8
                                      swap
                                      · -- branch
                                        by_cases c2104 : 0 < a0
                                        swap
                                        · omega
                                        by_cases c2105 : 0 < b2
                                        swap
                                        · omega
                                        by_cases c2106 : 0 < b0 + b2
                                        swap
                                        · omega
                                        by_cases c2107 : b0 < 0 + a0
                                        swap
                                        · omega
                                        have f2108 := pair_fact E (i := 0) (j := 2) rfl rfl c2104 c2105
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2108
                                        omega
                                      by_cases c2109 : b0 + b2 + b4 + b6 < a0 + a2 + a4 + a6 + a8 + a10
                                      swap
                                      · omega
                                      have f2110 := pair_fact E (i := 10) (j := 8) rfl rfl c2101 c2102
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2110
                                      omega
                                    by_cases c2111 : b0 + b2 + b4 < a0 + a2 + a4 + a6 + a8 + a10
                                    swap
                                    · omega
                                    have f2112 := pair_fact E (i := 10) (j := 6) rfl rfl c2098 c2099
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2112
                                    omega
                                  by_cases c2113 : b0 + b2 < a0 + a2 + a4 + a6 + a8 + a10
                                  swap
                                  · omega
                                  have f2114 := pair_fact E (i := 10) (j := 4) rfl rfl c2095 c2096
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2114
                                  omega
                                by_cases c2115 : 0 < a0 + a2 + a4 + a6 + a8 + a10
                                swap
                                · omega
                                have f2116 := pair_fact E (i := 10) (j := 0) rfl rfl c2092 c2093
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2116
                                omega
                              have f2117 := pair_fact E (i := 8) (j := 10) rfl rfl c2088 c2089
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2117
                              omega
                            have f2118 := pair_fact E (i := 4) (j := 6) rfl rfl c2084 c2085
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2118
                            omega
                          have f2119 := pair_fact E (i := 0) (j := 4) rfl rfl c2075 c2076
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2119
                          omega
                        by_cases c2120 : b0 + b2 < a0 + a2 + a4 + a6 + a8
                        swap
                        · omega
                        have f2121 := pair_fact E (i := 8) (j := 4) rfl rfl c2067 c2068
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2121
                        omega
                      by_cases c2122 : 0 < a0 + a2 + a4 + a6 + a8
                      swap
                      · omega
                      have f2123 := pair_fact E (i := 8) (j := 0) rfl rfl c2064 c2065
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2123
                      omega
                    have f2124 := pair_fact E (i := 4) (j := 10) rfl rfl c2060 c2061
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2124
                    omega
                  have f2125 := pair_fact E (i := 4) (j := 8) rfl rfl c2056 c2057
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2125
                  omega
                by_cases c2126 : 0 < a0 + a2 + a4
                swap
                · omega
                have f2127 := pair_fact E (i := 4) (j := 0) rfl rfl c2048 c2054
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2127
                omega
              have f2128 := pair_fact E (i := 2) (j := 6) rfl rfl c2044 c2045
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2128
              by_cases c2129 : 0 < a4
              swap
              · omega
              by_cases c2130 : 0 < b8
              swap
              · omega
              by_cases c2131 : a0 + a2 < b0 + b2 + b4 + b6 + b8
              swap
              · omega
              by_cases c2132 : b0 + b2 + b4 + b6 < a0 + a2 + a4
              swap
              · omega
              have f2133 := pair_fact E (i := 4) (j := 8) rfl rfl c2129 c2130
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2133
              omega
            by_cases c2134 : 0 < a0 + a2
            swap
            · omega
            have f2135 := pair_fact E (i := 2) (j := 0) rfl rfl c2041 c2042
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2135
            by_cases c2136 : 0 < a2
            swap
            · omega
            by_cases c2137 : 0 < b6
            swap
            · omega
            by_cases c2138 : a0 < b0 + b2 + b4 + b6
            swap
            · omega
            by_cases c2139 : b0 + b2 + b4 < a0 + a2
            swap
            · -- branch
              by_cases c2140 : 0 < a0
              swap
              · omega
              by_cases c2141 : 0 < b2
              swap
              · -- branch
                by_cases c2142 : 0 < a2
                swap
                · omega
                by_cases c2143 : 0 < b4
                swap
                · omega
                by_cases c2144 : a0 < b0 + b2 + b4
                swap
                · omega
                by_cases c2145 : b0 + b2 < a0 + a2
                swap
                · omega
                have f2146 := pair_fact E (i := 2) (j := 4) rfl rfl c2142 c2143
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2146
                omega
              by_cases c2147 : 0 < b0 + b2
              swap
              · omega
              by_cases c2148 : b0 < 0 + a0
              swap
              · -- branch
                by_cases c2149 : 0 < a2
                swap
                · omega
                by_cases c2150 : 0 < b2
                swap
                · omega
                by_cases c2151 : a0 < b0 + b2
                swap
                · omega
                by_cases c2152 : b0 < a0 + a2
                swap
                · -- branch
                  by_cases c2153 : 0 < a4
                  swap
                  · omega
                  by_cases c2154 : 0 < b2
                  swap
                  · omega
                  by_cases c2155 : a0 + a2 < b0 + b2
                  swap
                  · omega
                  by_cases c2156 : b0 < a0 + a2 + a4
                  swap
                  · omega
                  have f2157 := pair_fact E (i := 4) (j := 2) rfl rfl c2153 c2154
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2157
                  omega
                have f2158 := pair_fact E (i := 2) (j := 2) rfl rfl c2149 c2150
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2158
                omega
              have f2159 := pair_fact E (i := 0) (j := 2) rfl rfl c2140 c2141
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2159
              omega
            have f2160 := pair_fact E (i := 2) (j := 6) rfl rfl c2136 c2137
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2160
            omega
          have f2161 := pair_fact E (i := 2) (j := 10) rfl rfl c2037 c2038
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2161
          omega
        have f2162 := pair_fact E (i := 2) (j := 8) rfl rfl c1938 c2034
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2162
        omega
      have f2163 := pair_fact E (i := 0) (j := 10) rfl rfl c1734 c1735
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2163
      omega
    have f2164 := pair_fact E (i := 0) (j := 8) rfl rfl c1725 c1726
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2164
    omega
  have f2165 := pair_fact E (i := 0) (j := 6) rfl rfl c1131 c1132
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f2165
  omega

end Blocks
