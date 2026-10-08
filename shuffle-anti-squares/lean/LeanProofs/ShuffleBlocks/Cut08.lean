import LeanProofs.ShuffleBlocks.Basic

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Blocks

set_option maxHeartbeats 0 in
/-- Cut inside run 8 of `V`: no splitting of this rotation gives two equal copies. -/
theorem V_cut08 (L l m v k a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9 a10 b10 : Nat)
    (hl : 1 ≤ l) (hm : m = 2 * v + 1) (hL : 9 * l ≤ L) (hk : k ≤ l)
    (e0 : a0 + b0 = (l - k))
    (e1 : a1 + b1 = 3 * m)
    (e2 : a2 + b2 = L)
    (e3 : a3 + b3 = m)
    (e4 : a4 + b4 = 5 * l)
    (e5 : a5 + b5 = 2 * m)
    (e6 : a6 + b6 = L)
    (e7 : a7 + b7 = m)
    (e8 : a8 + b8 = 2 * l)
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
    by_cases c2 : 0 < a5
    swap
    · omega
    by_cases c3 : 0 < b1
    swap
    · omega
    by_cases c4 : a1 + a3 < 0 + b1
    swap
    · omega
    by_cases c5 : 0 < a1 + a3 + a5
    swap
    · omega
    have f6 := pair_fact E (i := 5) (j := 1) rfl rfl c2 c3
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f6
    omega
  by_cases c7 : 0 < b1
  swap
  · -- branch
    by_cases c8 : 0 < a1
    swap
    · omega
    by_cases c9 : 0 < b5
    swap
    · omega
    by_cases c10 : 0 < b1 + b3 + b5
    swap
    · omega
    by_cases c11 : b1 + b3 < 0 + a1
    swap
    · omega
    have f12 := pair_fact E (i := 1) (j := 5) rfl rfl c8 c9
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f12
    omega
  by_cases c13 : 0 < 0 + b1
  swap
  · omega
  by_cases c14 : 0 < 0 + a1
  swap
  · omega
  have f15 := pair_fact E (i := 1) (j := 1) rfl rfl c1 c7
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f15
  by_cases c16 : 0 < a1
  swap
  · omega
  by_cases c17 : 0 < b5
  swap
  · -- branch
    by_cases c18 : 0 < a5
    swap
    · omega
    by_cases c19 : 0 < b1
    swap
    · omega
    by_cases c20 : a1 + a3 < 0 + b1
    swap
    · -- branch
      by_cases c21 : 0 < a1
      swap
      · omega
      by_cases c22 : 0 < b7
      swap
      · omega
      by_cases c23 : 0 < b1 + b3 + b5 + b7
      swap
      · omega
      by_cases c24 : b1 + b3 + b5 < 0 + a1
      swap
      · -- branch
        by_cases c25 : 0 < a1
        swap
        · omega
        by_cases c26 : 0 < b9
        swap
        · omega
        by_cases c27 : 0 < b1 + b3 + b5 + b7 + b9
        swap
        · omega
        by_cases c28 : b1 + b3 + b5 + b7 < 0 + a1
        swap
        · -- branch
          by_cases c29 : 0 < a5
          swap
          · omega
          by_cases c30 : 0 < b5
          swap
          · -- branch
            by_cases c31 : 0 < a5
            swap
            · omega
            by_cases c32 : 0 < b7
            swap
            · omega
            by_cases c33 : a1 + a3 < b1 + b3 + b5 + b7
            swap
            · omega
            by_cases c34 : b1 + b3 + b5 < a1 + a3 + a5
            swap
            · omega
            have f35 := pair_fact E (i := 5) (j := 7) rfl rfl c31 c32
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f35
            by_cases c36 : 0 < a5
            swap
            · omega
            by_cases c37 : 0 < b9
            swap
            · omega
            by_cases c38 : a1 + a3 < b1 + b3 + b5 + b7 + b9
            swap
            · omega
            by_cases c39 : b1 + b3 + b5 + b7 < a1 + a3 + a5
            swap
            · omega
            have f40 := pair_fact E (i := 5) (j := 9) rfl rfl c36 c37
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f40
            omega
          by_cases c41 : a1 + a3 < b1 + b3 + b5
          swap
          · omega
          by_cases c42 : b1 + b3 < a1 + a3 + a5
          swap
          · omega
          have f43 := pair_fact E (i := 5) (j := 5) rfl rfl c29 c30
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f43
          omega
        have f44 := pair_fact E (i := 1) (j := 9) rfl rfl c25 c26
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f44
        omega
      have f45 := pair_fact E (i := 1) (j := 7) rfl rfl c21 c22
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f45
      omega
    by_cases c46 : 0 < a1 + a3 + a5
    swap
    · omega
    have f47 := pair_fact E (i := 5) (j := 1) rfl rfl c18 c19
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f47
    omega
  by_cases c48 : 0 < b1 + b3 + b5
  swap
  · omega
  by_cases c49 : b1 + b3 < 0 + a1
  swap
  · -- branch
    by_cases c50 : 0 < a1
    swap
    · omega
    by_cases c51 : 0 < b7
    swap
    · -- branch
      by_cases c52 : 0 < a7
      swap
      · omega
      by_cases c53 : 0 < b1
      swap
      · omega
      by_cases c54 : a1 + a3 + a5 < 0 + b1
      swap
      · -- branch
        by_cases c55 : 0 < a7
        swap
        · omega
        by_cases c56 : 0 < b7
        swap
        · -- branch
          by_cases c57 : 0 < a1
          swap
          · omega
          by_cases c58 : 0 < b9
          swap
          · -- branch
            by_cases c59 : 0 < a7
            swap
            · omega
            by_cases c60 : 0 < b9
            swap
            · -- branch
              by_cases c61 : 0 < a9
              swap
              · omega
              by_cases c62 : 0 < b1
              swap
              · omega
              by_cases c63 : a1 + a3 + a5 + a7 < 0 + b1
              swap
              · -- branch
                by_cases c64 : 0 < a9
                swap
                · omega
                by_cases c65 : 0 < b5
                swap
                · omega
                by_cases c66 : a1 + a3 + a5 + a7 < b1 + b3 + b5
                swap
                · omega
                by_cases c67 : b1 + b3 < a1 + a3 + a5 + a7 + a9
                swap
                · omega
                have f68 := pair_fact E (i := 9) (j := 5) rfl rfl c64 c65
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f68
                by_cases c69 : 0 < a7
                swap
                · omega
                by_cases c70 : 0 < b5
                swap
                · omega
                by_cases c71 : a1 + a3 + a5 < b1 + b3 + b5
                swap
                · omega
                by_cases c72 : b1 + b3 < a1 + a3 + a5 + a7
                swap
                · -- branch
                  by_cases c73 : 0 < a5
                  swap
                  · omega
                  by_cases c74 : 0 < b1
                  swap
                  · omega
                  by_cases c75 : a1 + a3 < 0 + b1
                  swap
                  · omega
                  by_cases c76 : 0 < a1 + a3 + a5
                  swap
                  · omega
                  have f77 := pair_fact E (i := 5) (j := 1) rfl rfl c73 c74
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f77
                  omega
                have f78 := pair_fact E (i := 7) (j := 5) rfl rfl c69 c70
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f78
                omega
              by_cases c79 : 0 < a1 + a3 + a5 + a7 + a9
              swap
              · omega
              have f80 := pair_fact E (i := 9) (j := 1) rfl rfl c61 c62
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f80
              omega
            by_cases c81 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
            swap
            · omega
            by_cases c82 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
            swap
            · omega
            have f83 := pair_fact E (i := 7) (j := 9) rfl rfl c59 c60
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f83
            omega
          by_cases c84 : 0 < b1 + b3 + b5 + b7 + b9
          swap
          · omega
          by_cases c85 : b1 + b3 + b5 + b7 < 0 + a1
          swap
          · -- branch
            by_cases c86 : 0 < a3
            swap
            · -- branch
              by_cases c87 : 0 < a3
              swap
              · -- branch
                by_cases c88 : 0 < a3
                swap
                · -- branch
                  by_cases c89 : 0 < a3
                  swap
                  · -- branch
                    by_cases c90 : 0 < a3
                    swap
                    · -- branch
                      by_cases c91 : 0 < a5
                      swap
                      · omega
                      by_cases c92 : 0 < b1
                      swap
                      · omega
                      by_cases c93 : a1 + a3 < 0 + b1
                      swap
                      · -- branch
                        by_cases c94 : 0 < a1
                        swap
                        · omega
                        by_cases c95 : 0 < b3
                        swap
                        · omega
                        by_cases c96 : 0 < b1 + b3
                        swap
                        · omega
                        by_cases c97 : b1 < 0 + a1
                        swap
                        · omega
                        have f98 := pair_fact E (i := 1) (j := 3) rfl rfl c94 c95
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f98
                        by_cases c99 : 0 < a5
                        swap
                        · omega
                        by_cases c100 : 0 < b3
                        swap
                        · omega
                        by_cases c101 : a1 + a3 < b1 + b3
                        swap
                        · -- branch
                          by_cases c102 : 0 < a5
                          swap
                          · omega
                          by_cases c103 : 0 < b5
                          swap
                          · omega
                          by_cases c104 : a1 + a3 < b1 + b3 + b5
                          swap
                          · omega
                          by_cases c105 : b1 + b3 < a1 + a3 + a5
                          swap
                          · omega
                          have f106 := pair_fact E (i := 5) (j := 5) rfl rfl c102 c103
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f106
                          omega
                        by_cases c107 : b1 < a1 + a3 + a5
                        swap
                        · omega
                        have f108 := pair_fact E (i := 5) (j := 3) rfl rfl c99 c100
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f108
                        omega
                      by_cases c109 : 0 < a1 + a3 + a5
                      swap
                      · omega
                      have f110 := pair_fact E (i := 5) (j := 1) rfl rfl c91 c92
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f110
                      omega
                    by_cases c111 : 0 < b9
                    swap
                    · omega
                    by_cases c112 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c113 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · omega
                    have f114 := pair_fact E (i := 3) (j := 9) rfl rfl c90 c111
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f114
                    omega
                  by_cases c115 : 0 < b5
                  swap
                  · omega
                  by_cases c116 : a1 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c117 : b1 + b3 < a1 + a3
                  swap
                  · omega
                  have f118 := pair_fact E (i := 3) (j := 5) rfl rfl c89 c115
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f118
                  omega
                by_cases c119 : 0 < b3
                swap
                · omega
                by_cases c120 : a1 < b1 + b3
                swap
                · omega
                by_cases c121 : b1 < a1 + a3
                swap
                · omega
                have f122 := pair_fact E (i := 3) (j := 3) rfl rfl c88 c119
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f122
                omega
              by_cases c123 : 0 < b1
              swap
              · omega
              by_cases c124 : a1 < 0 + b1
              swap
              · omega
              by_cases c125 : 0 < a1 + a3
              swap
              · omega
              have f126 := pair_fact E (i := 3) (j := 1) rfl rfl c87 c123
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f126
              omega
            by_cases c127 : 0 < b7
            swap
            · -- branch
              by_cases c128 : 0 < a3
              swap
              · omega
              by_cases c129 : 0 < b9
              swap
              · omega
              by_cases c130 : a1 < b1 + b3 + b5 + b7 + b9
              swap
              · omega
              by_cases c131 : b1 + b3 + b5 + b7 < a1 + a3
              swap
              · -- branch
                by_cases c132 : 0 < a3
                swap
                · omega
                by_cases c133 : 0 < b1
                swap
                · omega
                by_cases c134 : a1 < 0 + b1
                swap
                · -- branch
                  by_cases c135 : 0 < a1
                  swap
                  · omega
                  by_cases c136 : 0 < b3
                  swap
                  · omega
                  by_cases c137 : 0 < b1 + b3
                  swap
                  · omega
                  by_cases c138 : b1 < 0 + a1
                  swap
                  · omega
                  have f139 := pair_fact E (i := 1) (j := 3) rfl rfl c135 c136
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f139
                  by_cases c140 : 0 < a3
                  swap
                  · omega
                  by_cases c141 : 0 < b3
                  swap
                  · omega
                  by_cases c142 : a1 < b1 + b3
                  swap
                  · -- branch
                    by_cases c143 : 0 < a3
                    swap
                    · omega
                    by_cases c144 : 0 < b5
                    swap
                    · omega
                    by_cases c145 : a1 < b1 + b3 + b5
                    swap
                    · omega
                    by_cases c146 : b1 + b3 < a1 + a3
                    swap
                    · omega
                    have f147 := pair_fact E (i := 3) (j := 5) rfl rfl c143 c144
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f147
                    omega
                  by_cases c148 : b1 < a1 + a3
                  swap
                  · omega
                  have f149 := pair_fact E (i := 3) (j := 3) rfl rfl c140 c141
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f149
                  omega
                by_cases c150 : 0 < a1 + a3
                swap
                · omega
                have f151 := pair_fact E (i := 3) (j := 1) rfl rfl c132 c133
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f151
                by_cases c152 : 0 < a3
                swap
                · omega
                by_cases c153 : 0 < b5
                swap
                · omega
                by_cases c154 : a1 < b1 + b3 + b5
                swap
                · omega
                by_cases c155 : b1 + b3 < a1 + a3
                swap
                · -- branch
                  by_cases c156 : 0 < a5
                  swap
                  · omega
                  by_cases c157 : 0 < b1
                  swap
                  · omega
                  by_cases c158 : a1 + a3 < 0 + b1
                  swap
                  · -- branch
                    by_cases c159 : 0 < a5
                    swap
                    · omega
                    by_cases c160 : 0 < b5
                    swap
                    · omega
                    by_cases c161 : a1 + a3 < b1 + b3 + b5
                    swap
                    · omega
                    by_cases c162 : b1 + b3 < a1 + a3 + a5
                    swap
                    · -- branch
                      by_cases c163 : 0 < a5
                      swap
                      · omega
                      by_cases c164 : 0 < b3
                      swap
                      · omega
                      by_cases c165 : a1 + a3 < b1 + b3
                      swap
                      · omega
                      by_cases c166 : b1 < a1 + a3 + a5
                      swap
                      · omega
                      have f167 := pair_fact E (i := 5) (j := 3) rfl rfl c163 c164
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f167
                      omega
                    have f168 := pair_fact E (i := 5) (j := 5) rfl rfl c159 c160
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f168
                    omega
                  by_cases c169 : 0 < a1 + a3 + a5
                  swap
                  · omega
                  have f170 := pair_fact E (i := 5) (j := 1) rfl rfl c156 c157
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f170
                  omega
                have f171 := pair_fact E (i := 3) (j := 5) rfl rfl c152 c153
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f171
                omega
              have f172 := pair_fact E (i := 3) (j := 9) rfl rfl c128 c129
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f172
              omega
            by_cases c173 : a1 < b1 + b3 + b5 + b7
            swap
            · omega
            by_cases c174 : b1 + b3 + b5 < a1 + a3
            swap
            · omega
            have f175 := pair_fact E (i := 3) (j := 7) rfl rfl c86 c127
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f175
            omega
          have f176 := pair_fact E (i := 1) (j := 9) rfl rfl c57 c58
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f176
          omega
        by_cases c177 : a1 + a3 + a5 < b1 + b3 + b5 + b7
        swap
        · omega
        by_cases c178 : b1 + b3 + b5 < a1 + a3 + a5 + a7
        swap
        · omega
        have f179 := pair_fact E (i := 7) (j := 7) rfl rfl c55 c56
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f179
        omega
      by_cases c180 : 0 < a1 + a3 + a5 + a7
      swap
      · omega
      have f181 := pair_fact E (i := 7) (j := 1) rfl rfl c52 c53
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f181
      omega
    by_cases c182 : 0 < b1 + b3 + b5 + b7
    swap
    · omega
    by_cases c183 : b1 + b3 + b5 < 0 + a1
    swap
    · -- branch
      by_cases c184 : 0 < a1
      swap
      · omega
      by_cases c185 : 0 < b9
      swap
      · -- branch
        by_cases c186 : 0 < a9
        swap
        · omega
        by_cases c187 : 0 < b1
        swap
        · omega
        by_cases c188 : a1 + a3 + a5 + a7 < 0 + b1
        swap
        · -- branch
          by_cases c189 : 0 < a9
          swap
          · omega
          by_cases c190 : 0 < b7
          swap
          · omega
          by_cases c191 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7
          swap
          · omega
          by_cases c192 : b1 + b3 + b5 < a1 + a3 + a5 + a7 + a9
          swap
          · omega
          have f193 := pair_fact E (i := 9) (j := 7) rfl rfl c189 c190
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f193
          by_cases c194 : 0 < a9
          swap
          · omega
          by_cases c195 : 0 < b9
          swap
          · -- branch
            by_cases c196 : 0 < a3
            swap
            · -- branch
              by_cases c197 : 0 < a3
              swap
              · -- branch
                by_cases c198 : 0 < a3
                swap
                · -- branch
                  by_cases c199 : 0 < a3
                  swap
                  · -- branch
                    by_cases c200 : 0 < a3
                    swap
                    · -- branch
                      by_cases c201 : 0 < a5
                      swap
                      · omega
                      by_cases c202 : 0 < b1
                      swap
                      · omega
                      by_cases c203 : a1 + a3 < 0 + b1
                      swap
                      · -- branch
                        by_cases c204 : 0 < a1
                        swap
                        · omega
                        by_cases c205 : 0 < b3
                        swap
                        · omega
                        by_cases c206 : 0 < b1 + b3
                        swap
                        · omega
                        by_cases c207 : b1 < 0 + a1
                        swap
                        · omega
                        have f208 := pair_fact E (i := 1) (j := 3) rfl rfl c204 c205
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f208
                        by_cases c209 : 0 < a5
                        swap
                        · omega
                        by_cases c210 : 0 < b3
                        swap
                        · omega
                        by_cases c211 : a1 + a3 < b1 + b3
                        swap
                        · -- branch
                          by_cases c212 : 0 < a5
                          swap
                          · omega
                          by_cases c213 : 0 < b5
                          swap
                          · omega
                          by_cases c214 : a1 + a3 < b1 + b3 + b5
                          swap
                          · omega
                          by_cases c215 : b1 + b3 < a1 + a3 + a5
                          swap
                          · omega
                          have f216 := pair_fact E (i := 5) (j := 5) rfl rfl c212 c213
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f216
                          omega
                        by_cases c217 : b1 < a1 + a3 + a5
                        swap
                        · omega
                        have f218 := pair_fact E (i := 5) (j := 3) rfl rfl c209 c210
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f218
                        omega
                      by_cases c219 : 0 < a1 + a3 + a5
                      swap
                      · omega
                      have f220 := pair_fact E (i := 5) (j := 1) rfl rfl c201 c202
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f220
                      omega
                    by_cases c221 : 0 < b9
                    swap
                    · omega
                    by_cases c222 : a1 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c223 : b1 + b3 + b5 + b7 < a1 + a3
                    swap
                    · omega
                    have f224 := pair_fact E (i := 3) (j := 9) rfl rfl c200 c221
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f224
                    omega
                  by_cases c225 : 0 < b5
                  swap
                  · omega
                  by_cases c226 : a1 < b1 + b3 + b5
                  swap
                  · omega
                  by_cases c227 : b1 + b3 < a1 + a3
                  swap
                  · omega
                  have f228 := pair_fact E (i := 3) (j := 5) rfl rfl c199 c225
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f228
                  omega
                by_cases c229 : 0 < b3
                swap
                · omega
                by_cases c230 : a1 < b1 + b3
                swap
                · omega
                by_cases c231 : b1 < a1 + a3
                swap
                · omega
                have f232 := pair_fact E (i := 3) (j := 3) rfl rfl c198 c229
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f232
                omega
              by_cases c233 : 0 < b1
              swap
              · omega
              by_cases c234 : a1 < 0 + b1
              swap
              · omega
              by_cases c235 : 0 < a1 + a3
              swap
              · omega
              have f236 := pair_fact E (i := 3) (j := 1) rfl rfl c197 c233
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f236
              omega
            by_cases c237 : 0 < b7
            swap
            · omega
            by_cases c238 : a1 < b1 + b3 + b5 + b7
            swap
            · omega
            by_cases c239 : b1 + b3 + b5 < a1 + a3
            swap
            · -- branch
              by_cases c240 : 0 < a3
              swap
              · omega
              by_cases c241 : 0 < b9
              swap
              · -- branch
                by_cases c242 : 0 < a3
                swap
                · omega
                by_cases c243 : 0 < b1
                swap
                · omega
                by_cases c244 : a1 < 0 + b1
                swap
                · -- branch
                  by_cases c245 : 0 < a1
                  swap
                  · omega
                  by_cases c246 : 0 < b3
                  swap
                  · omega
                  by_cases c247 : 0 < b1 + b3
                  swap
                  · omega
                  by_cases c248 : b1 < 0 + a1
                  swap
                  · omega
                  have f249 := pair_fact E (i := 1) (j := 3) rfl rfl c245 c246
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f249
                  by_cases c250 : 0 < a3
                  swap
                  · omega
                  by_cases c251 : 0 < b3
                  swap
                  · omega
                  by_cases c252 : a1 < b1 + b3
                  swap
                  · -- branch
                    by_cases c253 : 0 < a3
                    swap
                    · omega
                    by_cases c254 : 0 < b5
                    swap
                    · omega
                    by_cases c255 : a1 < b1 + b3 + b5
                    swap
                    · omega
                    by_cases c256 : b1 + b3 < a1 + a3
                    swap
                    · omega
                    have f257 := pair_fact E (i := 3) (j := 5) rfl rfl c253 c254
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f257
                    omega
                  by_cases c258 : b1 < a1 + a3
                  swap
                  · omega
                  have f259 := pair_fact E (i := 3) (j := 3) rfl rfl c250 c251
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f259
                  omega
                by_cases c260 : 0 < a1 + a3
                swap
                · omega
                have f261 := pair_fact E (i := 3) (j := 1) rfl rfl c242 c243
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f261
                by_cases c262 : 0 < a3
                swap
                · omega
                by_cases c263 : 0 < b5
                swap
                · omega
                by_cases c264 : a1 < b1 + b3 + b5
                swap
                · omega
                by_cases c265 : b1 + b3 < a1 + a3
                swap
                · -- branch
                  by_cases c266 : 0 < a5
                  swap
                  · omega
                  by_cases c267 : 0 < b1
                  swap
                  · omega
                  by_cases c268 : a1 + a3 < 0 + b1
                  swap
                  · -- branch
                    by_cases c269 : 0 < a5
                    swap
                    · omega
                    by_cases c270 : 0 < b5
                    swap
                    · omega
                    by_cases c271 : a1 + a3 < b1 + b3 + b5
                    swap
                    · omega
                    by_cases c272 : b1 + b3 < a1 + a3 + a5
                    swap
                    · -- branch
                      by_cases c273 : 0 < a5
                      swap
                      · omega
                      by_cases c274 : 0 < b3
                      swap
                      · omega
                      by_cases c275 : a1 + a3 < b1 + b3
                      swap
                      · omega
                      by_cases c276 : b1 < a1 + a3 + a5
                      swap
                      · omega
                      have f277 := pair_fact E (i := 5) (j := 3) rfl rfl c273 c274
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f277
                      omega
                    have f278 := pair_fact E (i := 5) (j := 5) rfl rfl c269 c270
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f278
                    omega
                  by_cases c279 : 0 < a1 + a3 + a5
                  swap
                  · omega
                  have f280 := pair_fact E (i := 5) (j := 1) rfl rfl c266 c267
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f280
                  omega
                have f281 := pair_fact E (i := 3) (j := 5) rfl rfl c262 c263
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f281
                omega
              by_cases c282 : a1 < b1 + b3 + b5 + b7 + b9
              swap
              · omega
              by_cases c283 : b1 + b3 + b5 + b7 < a1 + a3
              swap
              · omega
              have f284 := pair_fact E (i := 3) (j := 9) rfl rfl c240 c241
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f284
              omega
            have f285 := pair_fact E (i := 3) (j := 7) rfl rfl c196 c237
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f285
            omega
          by_cases c286 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
          swap
          · omega
          by_cases c287 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
          swap
          · omega
          have f288 := pair_fact E (i := 9) (j := 9) rfl rfl c194 c195
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f288
          omega
        by_cases c289 : 0 < a1 + a3 + a5 + a7 + a9
        swap
        · omega
        have f290 := pair_fact E (i := 9) (j := 1) rfl rfl c186 c187
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f290
        omega
      by_cases c291 : 0 < b1 + b3 + b5 + b7 + b9
      swap
      · omega
      by_cases c292 : b1 + b3 + b5 + b7 < 0 + a1
      swap
      · -- branch
        by_cases c293 : 0 < a3
        swap
        · -- branch
          by_cases c294 : 0 < a3
          swap
          · -- branch
            by_cases c295 : 0 < a3
            swap
            · -- branch
              by_cases c296 : 0 < a3
              swap
              · -- branch
                by_cases c297 : 0 < a3
                swap
                · -- branch
                  by_cases c298 : 0 < a5
                  swap
                  · omega
                  by_cases c299 : 0 < b1
                  swap
                  · omega
                  by_cases c300 : a1 + a3 < 0 + b1
                  swap
                  · -- branch
                    by_cases c301 : 0 < a1
                    swap
                    · omega
                    by_cases c302 : 0 < b3
                    swap
                    · omega
                    by_cases c303 : 0 < b1 + b3
                    swap
                    · omega
                    by_cases c304 : b1 < 0 + a1
                    swap
                    · omega
                    have f305 := pair_fact E (i := 1) (j := 3) rfl rfl c301 c302
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f305
                    by_cases c306 : 0 < a5
                    swap
                    · omega
                    by_cases c307 : 0 < b3
                    swap
                    · omega
                    by_cases c308 : a1 + a3 < b1 + b3
                    swap
                    · -- branch
                      by_cases c309 : 0 < a5
                      swap
                      · omega
                      by_cases c310 : 0 < b5
                      swap
                      · omega
                      by_cases c311 : a1 + a3 < b1 + b3 + b5
                      swap
                      · omega
                      by_cases c312 : b1 + b3 < a1 + a3 + a5
                      swap
                      · omega
                      have f313 := pair_fact E (i := 5) (j := 5) rfl rfl c309 c310
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f313
                      omega
                    by_cases c314 : b1 < a1 + a3 + a5
                    swap
                    · omega
                    have f315 := pair_fact E (i := 5) (j := 3) rfl rfl c306 c307
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f315
                    omega
                  by_cases c316 : 0 < a1 + a3 + a5
                  swap
                  · omega
                  have f317 := pair_fact E (i := 5) (j := 1) rfl rfl c298 c299
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f317
                  omega
                by_cases c318 : 0 < b9
                swap
                · omega
                by_cases c319 : a1 < b1 + b3 + b5 + b7 + b9
                swap
                · omega
                by_cases c320 : b1 + b3 + b5 + b7 < a1 + a3
                swap
                · omega
                have f321 := pair_fact E (i := 3) (j := 9) rfl rfl c297 c318
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f321
                omega
              by_cases c322 : 0 < b5
              swap
              · omega
              by_cases c323 : a1 < b1 + b3 + b5
              swap
              · omega
              by_cases c324 : b1 + b3 < a1 + a3
              swap
              · omega
              have f325 := pair_fact E (i := 3) (j := 5) rfl rfl c296 c322
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f325
              omega
            by_cases c326 : 0 < b3
            swap
            · omega
            by_cases c327 : a1 < b1 + b3
            swap
            · omega
            by_cases c328 : b1 < a1 + a3
            swap
            · omega
            have f329 := pair_fact E (i := 3) (j := 3) rfl rfl c295 c326
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f329
            omega
          by_cases c330 : 0 < b1
          swap
          · omega
          by_cases c331 : a1 < 0 + b1
          swap
          · omega
          by_cases c332 : 0 < a1 + a3
          swap
          · omega
          have f333 := pair_fact E (i := 3) (j := 1) rfl rfl c294 c330
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f333
          omega
        by_cases c334 : 0 < b7
        swap
        · omega
        by_cases c335 : a1 < b1 + b3 + b5 + b7
        swap
        · omega
        by_cases c336 : b1 + b3 + b5 < a1 + a3
        swap
        · -- branch
          by_cases c337 : 0 < a3
          swap
          · omega
          by_cases c338 : 0 < b9
          swap
          · omega
          by_cases c339 : a1 < b1 + b3 + b5 + b7 + b9
          swap
          · omega
          by_cases c340 : b1 + b3 + b5 + b7 < a1 + a3
          swap
          · -- branch
            by_cases c341 : 0 < a3
            swap
            · omega
            by_cases c342 : 0 < b1
            swap
            · omega
            by_cases c343 : a1 < 0 + b1
            swap
            · -- branch
              by_cases c344 : 0 < a1
              swap
              · omega
              by_cases c345 : 0 < b3
              swap
              · omega
              by_cases c346 : 0 < b1 + b3
              swap
              · omega
              by_cases c347 : b1 < 0 + a1
              swap
              · omega
              have f348 := pair_fact E (i := 1) (j := 3) rfl rfl c344 c345
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f348
              by_cases c349 : 0 < a3
              swap
              · omega
              by_cases c350 : 0 < b3
              swap
              · omega
              by_cases c351 : a1 < b1 + b3
              swap
              · -- branch
                by_cases c352 : 0 < a3
                swap
                · omega
                by_cases c353 : 0 < b5
                swap
                · omega
                by_cases c354 : a1 < b1 + b3 + b5
                swap
                · omega
                by_cases c355 : b1 + b3 < a1 + a3
                swap
                · omega
                have f356 := pair_fact E (i := 3) (j := 5) rfl rfl c352 c353
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f356
                omega
              by_cases c357 : b1 < a1 + a3
              swap
              · omega
              have f358 := pair_fact E (i := 3) (j := 3) rfl rfl c349 c350
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f358
              omega
            by_cases c359 : 0 < a1 + a3
            swap
            · omega
            have f360 := pair_fact E (i := 3) (j := 1) rfl rfl c341 c342
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f360
            by_cases c361 : 0 < a3
            swap
            · omega
            by_cases c362 : 0 < b5
            swap
            · omega
            by_cases c363 : a1 < b1 + b3 + b5
            swap
            · omega
            by_cases c364 : b1 + b3 < a1 + a3
            swap
            · -- branch
              by_cases c365 : 0 < a5
              swap
              · omega
              by_cases c366 : 0 < b1
              swap
              · omega
              by_cases c367 : a1 + a3 < 0 + b1
              swap
              · -- branch
                by_cases c368 : 0 < a5
                swap
                · omega
                by_cases c369 : 0 < b5
                swap
                · omega
                by_cases c370 : a1 + a3 < b1 + b3 + b5
                swap
                · omega
                by_cases c371 : b1 + b3 < a1 + a3 + a5
                swap
                · -- branch
                  by_cases c372 : 0 < a5
                  swap
                  · omega
                  by_cases c373 : 0 < b3
                  swap
                  · omega
                  by_cases c374 : a1 + a3 < b1 + b3
                  swap
                  · omega
                  by_cases c375 : b1 < a1 + a3 + a5
                  swap
                  · omega
                  have f376 := pair_fact E (i := 5) (j := 3) rfl rfl c372 c373
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f376
                  omega
                have f377 := pair_fact E (i := 5) (j := 5) rfl rfl c368 c369
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f377
                omega
              by_cases c378 : 0 < a1 + a3 + a5
              swap
              · omega
              have f379 := pair_fact E (i := 5) (j := 1) rfl rfl c365 c366
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f379
              omega
            have f380 := pair_fact E (i := 3) (j := 5) rfl rfl c361 c362
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f380
            omega
          have f381 := pair_fact E (i := 3) (j := 9) rfl rfl c337 c338
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f381
          omega
        have f382 := pair_fact E (i := 3) (j := 7) rfl rfl c293 c334
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f382
        omega
      have f383 := pair_fact E (i := 1) (j := 9) rfl rfl c184 c185
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f383
      omega
    have f384 := pair_fact E (i := 1) (j := 7) rfl rfl c50 c51
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f384
    omega
  have f385 := pair_fact E (i := 1) (j := 5) rfl rfl c16 c17
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f385
  omega

end Blocks
