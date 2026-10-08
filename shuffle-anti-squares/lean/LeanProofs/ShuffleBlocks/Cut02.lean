import LeanProofs.ShuffleBlocks.Basic

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Blocks

set_option maxHeartbeats 0 in
/-- Cut inside run 2 of `V`: no splitting of this rotation gives two equal copies. -/
theorem V_cut02 (L l m v k a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9 a10 b10 : Nat)
    (hl : 1 ≤ l) (hm : m = 2 * v + 1) (hL : 9 * l ≤ L) (hk : k ≤ 5 * l)
    (e0 : a0 + b0 = (5 * l - k))
    (e1 : a1 + b1 = 2 * m)
    (e2 : a2 + b2 = L)
    (e3 : a3 + b3 = m)
    (e4 : a4 + b4 = 2 * l)
    (e5 : a5 + b5 = m)
    (e6 : a6 + b6 = l)
    (e7 : a7 + b7 = 3 * m)
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
                      by_cases c11 : 0 < a7
                      swap
                      · omega
                      by_cases c12 : 0 < b1
                      swap
                      · omega
                      by_cases c13 : a1 + a3 + a5 < 0 + b1
                      swap
                      · omega
                      by_cases c14 : 0 < a1 + a3 + a5 + a7
                      swap
                      · omega
                      have f15 := pair_fact E (i := 7) (j := 1) rfl rfl c11 c12
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f15
                      by_cases c16 : 0 < a7
                      swap
                      · omega
                      by_cases c17 : 0 < b3
                      swap
                      · omega
                      by_cases c18 : a1 + a3 + a5 < b1 + b3
                      swap
                      · omega
                      by_cases c19 : b1 < a1 + a3 + a5 + a7
                      swap
                      · omega
                      have f20 := pair_fact E (i := 7) (j := 3) rfl rfl c16 c17
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
            by_cases c41 : 0 < a7
            swap
            · omega
            by_cases c42 : 0 < b3
            swap
            · -- branch
              by_cases c43 : 0 < a3
              swap
              · omega
              by_cases c44 : 0 < b3
              swap
              · -- branch
                by_cases c45 : 0 < a7
                swap
                · omega
                by_cases c46 : 0 < b5
                swap
                · -- branch
                  by_cases c47 : 0 < a7
                  swap
                  · omega
                  by_cases c48 : 0 < b7
                  swap
                  · omega
                  by_cases c49 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                  swap
                  · omega
                  by_cases c50 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                  swap
                  · omega
                  have f51 := pair_fact E (i := 7) (j := 7) rfl rfl c47 c48
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f51
                  omega
                by_cases c52 : a1 + a3 + a5 < b1 + b3 + b5
                swap
                · omega
                by_cases c53 : b1 + b3 < a1 + a3 + a5 + a7
                swap
                · omega
                have f54 := pair_fact E (i := 7) (j := 5) rfl rfl c45 c46
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f54
                omega
              by_cases c55 : a1 < b1 + b3
              swap
              · omega
              by_cases c56 : b1 < a1 + a3
              swap
              · omega
              have f57 := pair_fact E (i := 3) (j := 3) rfl rfl c43 c44
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f57
              omega
            by_cases c58 : a1 + a3 + a5 < b1 + b3
            swap
            · omega
            by_cases c59 : b1 < a1 + a3 + a5 + a7
            swap
            · omega
            have f60 := pair_fact E (i := 7) (j := 3) rfl rfl c41 c42
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f60
            omega
          by_cases c61 : 0 < b9
          swap
          · omega
          by_cases c62 : 0 < b1 + b3 + b5 + b7 + b9
          swap
          · omega
          by_cases c63 : b1 + b3 + b5 + b7 < 0 + a1
          swap
          · omega
          have f64 := pair_fact E (i := 1) (j := 9) rfl rfl c5 c61
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f64
          omega
        by_cases c65 : 0 < b7
        swap
        · omega
        by_cases c66 : 0 < b1 + b3 + b5 + b7
        swap
        · omega
        by_cases c67 : b1 + b3 + b5 < 0 + a1
        swap
        · omega
        have f68 := pair_fact E (i := 1) (j := 7) rfl rfl c4 c65
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f68
        omega
      by_cases c69 : 0 < b5
      swap
      · omega
      by_cases c70 : 0 < b1 + b3 + b5
      swap
      · omega
      by_cases c71 : b1 + b3 < 0 + a1
      swap
      · omega
      have f72 := pair_fact E (i := 1) (j := 5) rfl rfl c3 c69
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f72
      omega
    by_cases c73 : 0 < b3
    swap
    · omega
    by_cases c74 : 0 < b1 + b3
    swap
    · omega
    by_cases c75 : b1 < 0 + a1
    swap
    · omega
    have f76 := pair_fact E (i := 1) (j := 3) rfl rfl c2 c73
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f76
    omega
  by_cases c77 : 0 < b1
  swap
  · -- branch
    by_cases c78 : 0 < a1
    swap
    · omega
    by_cases c79 : 0 < b3
    swap
    · -- branch
      by_cases c80 : 0 < a1
      swap
      · omega
      by_cases c81 : 0 < b7
      swap
      · omega
      by_cases c82 : 0 < b1 + b3 + b5 + b7
      swap
      · omega
      by_cases c83 : b1 + b3 + b5 < 0 + a1
      swap
      · omega
      have f84 := pair_fact E (i := 1) (j := 7) rfl rfl c80 c81
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f84
      by_cases c85 : 0 < a3
      swap
      · omega
      by_cases c86 : 0 < b7
      swap
      · omega
      by_cases c87 : a1 < b1 + b3 + b5 + b7
      swap
      · omega
      by_cases c88 : b1 + b3 + b5 < a1 + a3
      swap
      · omega
      have f89 := pair_fact E (i := 3) (j := 7) rfl rfl c85 c86
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f89
      omega
    by_cases c90 : 0 < b1 + b3
    swap
    · omega
    by_cases c91 : b1 < 0 + a1
    swap
    · omega
    have f92 := pair_fact E (i := 1) (j := 3) rfl rfl c78 c79
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f92
    by_cases c93 : 0 < a3
    swap
    · -- branch
      by_cases c94 : 0 < a3
      swap
      · -- branch
        by_cases c95 : 0 < a3
        swap
        · -- branch
          by_cases c96 : 0 < a3
          swap
          · -- branch
            by_cases c97 : 0 < a3
            swap
            · -- branch
              by_cases c98 : 0 < a5
              swap
              · -- branch
                by_cases c99 : 0 < a7
                swap
                · omega
                by_cases c100 : 0 < b7
                swap
                · omega
                by_cases c101 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                swap
                · omega
                by_cases c102 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                swap
                · omega
                have f103 := pair_fact E (i := 7) (j := 7) rfl rfl c99 c100
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f103
                omega
              by_cases c104 : 0 < b7
              swap
              · omega
              by_cases c105 : a1 + a3 < b1 + b3 + b5 + b7
              swap
              · omega
              by_cases c106 : b1 + b3 + b5 < a1 + a3 + a5
              swap
              · omega
              have f107 := pair_fact E (i := 5) (j := 7) rfl rfl c98 c104
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f107
              omega
            by_cases c108 : 0 < b9
            swap
            · omega
            by_cases c109 : a1 < b1 + b3 + b5 + b7 + b9
            swap
            · omega
            by_cases c110 : b1 + b3 + b5 + b7 < a1 + a3
            swap
            · omega
            have f111 := pair_fact E (i := 3) (j := 9) rfl rfl c97 c108
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f111
            omega
          by_cases c112 : 0 < b5
          swap
          · omega
          by_cases c113 : a1 < b1 + b3 + b5
          swap
          · omega
          by_cases c114 : b1 + b3 < a1 + a3
          swap
          · omega
          have f115 := pair_fact E (i := 3) (j := 5) rfl rfl c96 c112
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f115
          omega
        by_cases c116 : 0 < b3
        swap
        · omega
        by_cases c117 : a1 < b1 + b3
        swap
        · omega
        by_cases c118 : b1 < a1 + a3
        swap
        · omega
        have f119 := pair_fact E (i := 3) (j := 3) rfl rfl c95 c116
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f119
        omega
      by_cases c120 : 0 < b1
      swap
      · omega
      by_cases c121 : a1 < 0 + b1
      swap
      · omega
      by_cases c122 : 0 < a1 + a3
      swap
      · omega
      have f123 := pair_fact E (i := 3) (j := 1) rfl rfl c94 c120
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f123
      omega
    by_cases c124 : 0 < b7
    swap
    · omega
    by_cases c125 : a1 < b1 + b3 + b5 + b7
    swap
    · omega
    by_cases c126 : b1 + b3 + b5 < a1 + a3
    swap
    · omega
    have f127 := pair_fact E (i := 3) (j := 7) rfl rfl c93 c124
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f127
    omega
  by_cases c128 : 0 < 0 + b1
  swap
  · omega
  by_cases c129 : 0 < 0 + a1
  swap
  · omega
  have f130 := pair_fact E (i := 1) (j := 1) rfl rfl c1 c77
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f130
  by_cases c131 : 0 < a1
  swap
  · omega
  by_cases c132 : 0 < b9
  swap
  · -- branch
    by_cases c133 : 0 < a9
    swap
    · omega
    by_cases c134 : 0 < b1
    swap
    · omega
    by_cases c135 : a1 + a3 + a5 + a7 < 0 + b1
    swap
    · -- branch
      by_cases c136 : 0 < a9
      swap
      · omega
      by_cases c137 : 0 < b7
      swap
      · omega
      by_cases c138 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7
      swap
      · omega
      by_cases c139 : b1 + b3 + b5 < a1 + a3 + a5 + a7 + a9
      swap
      · omega
      have f140 := pair_fact E (i := 9) (j := 7) rfl rfl c136 c137
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f140
      by_cases c141 : 0 < a1
      swap
      · omega
      by_cases c142 : 0 < b7
      swap
      · omega
      by_cases c143 : 0 < b1 + b3 + b5 + b7
      swap
      · omega
      by_cases c144 : b1 + b3 + b5 < 0 + a1
      swap
      · -- branch
        by_cases c145 : 0 < a9
        swap
        · omega
        by_cases c146 : 0 < b9
        swap
        · -- branch
          by_cases c147 : 0 < a1
          swap
          · omega
          by_cases c148 : 0 < b3
          swap
          · -- branch
            by_cases c149 : 0 < a3
            swap
            · omega
            by_cases c150 : 0 < b3
            swap
            · -- branch
              by_cases c151 : 0 < a3
              swap
              · omega
              by_cases c152 : 0 < b7
              swap
              · omega
              by_cases c153 : a1 < b1 + b3 + b5 + b7
              swap
              · omega
              by_cases c154 : b1 + b3 + b5 < a1 + a3
              swap
              · -- branch
                by_cases c155 : 0 < a7
                swap
                · omega
                by_cases c156 : 0 < b7
                swap
                · omega
                by_cases c157 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                swap
                · omega
                by_cases c158 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                swap
                · omega
                have f159 := pair_fact E (i := 7) (j := 7) rfl rfl c155 c156
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f159
                omega
              have f160 := pair_fact E (i := 3) (j := 7) rfl rfl c151 c152
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f160
              omega
            by_cases c161 : a1 < b1 + b3
            swap
            · omega
            by_cases c162 : b1 < a1 + a3
            swap
            · omega
            have f163 := pair_fact E (i := 3) (j := 3) rfl rfl c149 c150
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f163
            omega
          by_cases c164 : 0 < b1 + b3
          swap
          · omega
          by_cases c165 : b1 < 0 + a1
          swap
          · -- branch
            by_cases c166 : 0 < a7
            swap
            · omega
            by_cases c167 : 0 < b1
            swap
            · omega
            by_cases c168 : a1 + a3 + a5 < 0 + b1
            swap
            · -- branch
              by_cases c169 : 0 < a7
              swap
              · omega
              by_cases c170 : 0 < b3
              swap
              · omega
              by_cases c171 : a1 + a3 + a5 < b1 + b3
              swap
              · -- branch
                by_cases c172 : 0 < a7
                swap
                · omega
                by_cases c173 : 0 < b7
                swap
                · omega
                by_cases c174 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                swap
                · omega
                by_cases c175 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                swap
                · omega
                have f176 := pair_fact E (i := 7) (j := 7) rfl rfl c172 c173
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f176
                omega
              by_cases c177 : b1 < a1 + a3 + a5 + a7
              swap
              · omega
              have f178 := pair_fact E (i := 7) (j := 3) rfl rfl c169 c170
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f178
              omega
            by_cases c179 : 0 < a1 + a3 + a5 + a7
            swap
            · omega
            have f180 := pair_fact E (i := 7) (j := 1) rfl rfl c166 c167
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f180
            omega
          have f181 := pair_fact E (i := 1) (j := 3) rfl rfl c147 c148
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f181
          omega
        by_cases c182 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
        swap
        · omega
        by_cases c183 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
        swap
        · omega
        have f184 := pair_fact E (i := 9) (j := 9) rfl rfl c145 c146
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f184
        omega
      have f185 := pair_fact E (i := 1) (j := 7) rfl rfl c141 c142
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f185
      omega
    by_cases c186 : 0 < a1 + a3 + a5 + a7 + a9
    swap
    · omega
    have f187 := pair_fact E (i := 9) (j := 1) rfl rfl c133 c134
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f187
    omega
  by_cases c188 : 0 < b1 + b3 + b5 + b7 + b9
  swap
  · omega
  by_cases c189 : b1 + b3 + b5 + b7 < 0 + a1
  swap
  · -- branch
    by_cases c190 : 0 < a3
    swap
    · -- branch
      by_cases c191 : 0 < a3
      swap
      · -- branch
        by_cases c192 : 0 < a3
        swap
        · -- branch
          by_cases c193 : 0 < a3
          swap
          · -- branch
            by_cases c194 : 0 < a3
            swap
            · -- branch
              by_cases c195 : 0 < a1
              swap
              · omega
              by_cases c196 : 0 < b3
              swap
              · omega
              by_cases c197 : 0 < b1 + b3
              swap
              · omega
              by_cases c198 : b1 < 0 + a1
              swap
              · -- branch
                by_cases c199 : 0 < a1
                swap
                · omega
                by_cases c200 : 0 < b5
                swap
                · -- branch
                  by_cases c201 : 0 < a1
                  swap
                  · omega
                  by_cases c202 : 0 < b7
                  swap
                  · omega
                  by_cases c203 : 0 < b1 + b3 + b5 + b7
                  swap
                  · omega
                  by_cases c204 : b1 + b3 + b5 < 0 + a1
                  swap
                  · -- branch
                    by_cases c205 : 0 < a5
                    swap
                    · omega
                    by_cases c206 : 0 < b5
                    swap
                    · -- branch
                      by_cases c207 : 0 < a5
                      swap
                      · omega
                      by_cases c208 : 0 < b7
                      swap
                      · omega
                      by_cases c209 : a1 + a3 < b1 + b3 + b5 + b7
                      swap
                      · omega
                      by_cases c210 : b1 + b3 + b5 < a1 + a3 + a5
                      swap
                      · -- branch
                        by_cases c211 : 0 < a5
                        swap
                        · omega
                        by_cases c212 : 0 < b9
                        swap
                        · omega
                        by_cases c213 : a1 + a3 < b1 + b3 + b5 + b7 + b9
                        swap
                        · omega
                        by_cases c214 : b1 + b3 + b5 + b7 < a1 + a3 + a5
                        swap
                        · -- branch
                          by_cases c215 : 0 < a7
                          swap
                          · omega
                          by_cases c216 : 0 < b5
                          swap
                          · -- branch
                            by_cases c217 : 0 < a7
                            swap
                            · omega
                            by_cases c218 : 0 < b7
                            swap
                            · omega
                            by_cases c219 : a1 + a3 + a5 < b1 + b3 + b5 + b7
                            swap
                            · omega
                            by_cases c220 : b1 + b3 + b5 < a1 + a3 + a5 + a7
                            swap
                            · omega
                            have f221 := pair_fact E (i := 7) (j := 7) rfl rfl c217 c218
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f221
                            by_cases c222 : 0 < a5
                            swap
                            · omega
                            by_cases c223 : 0 < b1
                            swap
                            · omega
                            by_cases c224 : a1 + a3 < 0 + b1
                            swap
                            · -- branch
                              by_cases c225 : 0 < a5
                              swap
                              · omega
                              by_cases c226 : 0 < b3
                              swap
                              · omega
                              by_cases c227 : a1 + a3 < b1 + b3
                              swap
                              · omega
                              by_cases c228 : b1 < a1 + a3 + a5
                              swap
                              · omega
                              have f229 := pair_fact E (i := 5) (j := 3) rfl rfl c225 c226
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f229
                              by_cases c230 : 0 < a7
                              swap
                              · omega
                              by_cases c231 : 0 < b1
                              swap
                              · omega
                              by_cases c232 : a1 + a3 + a5 < 0 + b1
                              swap
                              · -- branch
                                by_cases c233 : 0 < a7
                                swap
                                · omega
                                by_cases c234 : 0 < b3
                                swap
                                · omega
                                by_cases c235 : a1 + a3 + a5 < b1 + b3
                                swap
                                · -- branch
                                  by_cases c236 : 0 < a7
                                  swap
                                  · omega
                                  by_cases c237 : 0 < b9
                                  swap
                                  · omega
                                  by_cases c238 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
                                  swap
                                  · omega
                                  by_cases c239 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
                                  swap
                                  · -- branch
                                    by_cases c240 : 0 < a9
                                    swap
                                    · omega
                                    by_cases c241 : 0 < b7
                                    swap
                                    · omega
                                    by_cases c242 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7
                                    swap
                                    · omega
                                    by_cases c243 : b1 + b3 + b5 < a1 + a3 + a5 + a7 + a9
                                    swap
                                    · omega
                                    have f244 := pair_fact E (i := 9) (j := 7) rfl rfl c240 c241
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f244
                                    omega
                                  have f245 := pair_fact E (i := 7) (j := 9) rfl rfl c236 c237
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f245
                                  omega
                                by_cases c246 : b1 < a1 + a3 + a5 + a7
                                swap
                                · omega
                                have f247 := pair_fact E (i := 7) (j := 3) rfl rfl c233 c234
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f247
                                omega
                              by_cases c248 : 0 < a1 + a3 + a5 + a7
                              swap
                              · omega
                              have f249 := pair_fact E (i := 7) (j := 1) rfl rfl c230 c231
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f249
                              omega
                            by_cases c250 : 0 < a1 + a3 + a5
                            swap
                            · omega
                            have f251 := pair_fact E (i := 5) (j := 1) rfl rfl c222 c223
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f251
                            omega
                          by_cases c252 : a1 + a3 + a5 < b1 + b3 + b5
                          swap
                          · omega
                          by_cases c253 : b1 + b3 < a1 + a3 + a5 + a7
                          swap
                          · omega
                          have f254 := pair_fact E (i := 7) (j := 5) rfl rfl c215 c216
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f254
                          omega
                        have f255 := pair_fact E (i := 5) (j := 9) rfl rfl c211 c212
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f255
                        omega
                      have f256 := pair_fact E (i := 5) (j := 7) rfl rfl c207 c208
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f256
                      omega
                    by_cases c257 : a1 + a3 < b1 + b3 + b5
                    swap
                    · omega
                    by_cases c258 : b1 + b3 < a1 + a3 + a5
                    swap
                    · omega
                    have f259 := pair_fact E (i := 5) (j := 5) rfl rfl c205 c206
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f259
                    omega
                  have f260 := pair_fact E (i := 1) (j := 7) rfl rfl c201 c202
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f260
                  omega
                by_cases c261 : 0 < b1 + b3 + b5
                swap
                · omega
                by_cases c262 : b1 + b3 < 0 + a1
                swap
                · -- branch
                  by_cases c263 : 0 < a7
                  swap
                  · omega
                  by_cases c264 : 0 < b3
                  swap
                  · omega
                  by_cases c265 : a1 + a3 + a5 < b1 + b3
                  swap
                  · omega
                  by_cases c266 : b1 < a1 + a3 + a5 + a7
                  swap
                  · omega
                  have f267 := pair_fact E (i := 7) (j := 3) rfl rfl c263 c264
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f267
                  by_cases c268 : 0 < a7
                  swap
                  · omega
                  by_cases c269 : 0 < b1
                  swap
                  · omega
                  by_cases c270 : a1 + a3 + a5 < 0 + b1
                  swap
                  · -- branch
                    by_cases c271 : 0 < a7
                    swap
                    · omega
                    by_cases c272 : 0 < b5
                    swap
                    · omega
                    by_cases c273 : a1 + a3 + a5 < b1 + b3 + b5
                    swap
                    · omega
                    by_cases c274 : b1 + b3 < a1 + a3 + a5 + a7
                    swap
                    · omega
                    have f275 := pair_fact E (i := 7) (j := 5) rfl rfl c271 c272
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f275
                    by_cases c276 : 0 < a7
                    swap
                    · omega
                    by_cases c277 : 0 < b9
                    swap
                    · omega
                    by_cases c278 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
                    swap
                    · omega
                    by_cases c279 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
                    swap
                    · -- branch
                      by_cases c280 : 0 < a9
                      swap
                      · omega
                      by_cases c281 : 0 < b7
                      swap
                      · omega
                      by_cases c282 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7
                      swap
                      · omega
                      by_cases c283 : b1 + b3 + b5 < a1 + a3 + a5 + a7 + a9
                      swap
                      · omega
                      have f284 := pair_fact E (i := 9) (j := 7) rfl rfl c280 c281
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f284
                      omega
                    have f285 := pair_fact E (i := 7) (j := 9) rfl rfl c276 c277
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f285
                    omega
                  by_cases c286 : 0 < a1 + a3 + a5 + a7
                  swap
                  · omega
                  have f287 := pair_fact E (i := 7) (j := 1) rfl rfl c268 c269
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f287
                  omega
                have f288 := pair_fact E (i := 1) (j := 5) rfl rfl c199 c200
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f288
                omega
              have f289 := pair_fact E (i := 1) (j := 3) rfl rfl c195 c196
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f289
              by_cases c290 : 0 < a7
              swap
              · omega
              by_cases c291 : 0 < b7
              swap
              · omega
              by_cases c292 : a1 + a3 + a5 < b1 + b3 + b5 + b7
              swap
              · omega
              by_cases c293 : b1 + b3 + b5 < a1 + a3 + a5 + a7
              swap
              · omega
              have f294 := pair_fact E (i := 7) (j := 7) rfl rfl c290 c291
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f294
              omega
            by_cases c295 : 0 < b7
            swap
            · omega
            by_cases c296 : a1 < b1 + b3 + b5 + b7
            swap
            · omega
            by_cases c297 : b1 + b3 + b5 < a1 + a3
            swap
            · omega
            have f298 := pair_fact E (i := 3) (j := 7) rfl rfl c194 c295
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f298
            omega
          by_cases c299 : 0 < b5
          swap
          · omega
          by_cases c300 : a1 < b1 + b3 + b5
          swap
          · omega
          by_cases c301 : b1 + b3 < a1 + a3
          swap
          · omega
          have f302 := pair_fact E (i := 3) (j := 5) rfl rfl c193 c299
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f302
          omega
        by_cases c303 : 0 < b3
        swap
        · omega
        by_cases c304 : a1 < b1 + b3
        swap
        · omega
        by_cases c305 : b1 < a1 + a3
        swap
        · omega
        have f306 := pair_fact E (i := 3) (j := 3) rfl rfl c192 c303
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f306
        omega
      by_cases c307 : 0 < b1
      swap
      · omega
      by_cases c308 : a1 < 0 + b1
      swap
      · omega
      by_cases c309 : 0 < a1 + a3
      swap
      · omega
      have f310 := pair_fact E (i := 3) (j := 1) rfl rfl c191 c307
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f310
      omega
    by_cases c311 : 0 < b9
    swap
    · omega
    by_cases c312 : a1 < b1 + b3 + b5 + b7 + b9
    swap
    · omega
    by_cases c313 : b1 + b3 + b5 + b7 < a1 + a3
    swap
    · -- branch
      by_cases c314 : 0 < a3
      swap
      · omega
      by_cases c315 : 0 < b1
      swap
      · omega
      by_cases c316 : a1 < 0 + b1
      swap
      · -- branch
        by_cases c317 : 0 < a1
        swap
        · omega
        by_cases c318 : 0 < b7
        swap
        · omega
        by_cases c319 : 0 < b1 + b3 + b5 + b7
        swap
        · omega
        by_cases c320 : b1 + b3 + b5 < 0 + a1
        swap
        · -- branch
          by_cases c321 : 0 < a7
          swap
          · omega
          by_cases c322 : 0 < b1
          swap
          · omega
          by_cases c323 : a1 + a3 + a5 < 0 + b1
          swap
          · -- branch
            by_cases c324 : 0 < a3
            swap
            · omega
            by_cases c325 : 0 < b7
            swap
            · omega
            by_cases c326 : a1 < b1 + b3 + b5 + b7
            swap
            · omega
            by_cases c327 : b1 + b3 + b5 < a1 + a3
            swap
            · -- branch
              by_cases c328 : 0 < a7
              swap
              · omega
              by_cases c329 : 0 < b7
              swap
              · omega
              by_cases c330 : a1 + a3 + a5 < b1 + b3 + b5 + b7
              swap
              · omega
              by_cases c331 : b1 + b3 + b5 < a1 + a3 + a5 + a7
              swap
              · omega
              have f332 := pair_fact E (i := 7) (j := 7) rfl rfl c328 c329
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f332
              by_cases c333 : 0 < a7
              swap
              · omega
              by_cases c334 : 0 < b9
              swap
              · omega
              by_cases c335 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
              swap
              · omega
              by_cases c336 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
              swap
              · -- branch
                by_cases c337 : 0 < a9
                swap
                · omega
                by_cases c338 : 0 < b7
                swap
                · omega
                by_cases c339 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7
                swap
                · omega
                by_cases c340 : b1 + b3 + b5 < a1 + a3 + a5 + a7 + a9
                swap
                · omega
                have f341 := pair_fact E (i := 9) (j := 7) rfl rfl c337 c338
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                  (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f341
                omega
              have f342 := pair_fact E (i := 7) (j := 9) rfl rfl c333 c334
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f342
              omega
            have f343 := pair_fact E (i := 3) (j := 7) rfl rfl c324 c325
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f343
            by_cases c344 : 0 < a7
            swap
            · omega
            by_cases c345 : 0 < b9
            swap
            · omega
            by_cases c346 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
            swap
            · omega
            by_cases c347 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
            swap
            · -- branch
              by_cases c348 : 0 < a9
              swap
              · omega
              by_cases c349 : 0 < b7
              swap
              · omega
              by_cases c350 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7
              swap
              · omega
              by_cases c351 : b1 + b3 + b5 < a1 + a3 + a5 + a7 + a9
              swap
              · omega
              have f352 := pair_fact E (i := 9) (j := 7) rfl rfl c348 c349
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
                (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f352
              omega
            have f353 := pair_fact E (i := 7) (j := 9) rfl rfl c344 c345
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f353
            omega
          by_cases c354 : 0 < a1 + a3 + a5 + a7
          swap
          · omega
          have f355 := pair_fact E (i := 7) (j := 1) rfl rfl c321 c322
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f355
          omega
        have f356 := pair_fact E (i := 1) (j := 7) rfl rfl c317 c318
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f356
        by_cases c357 : 0 < a3
        swap
        · omega
        by_cases c358 : 0 < b7
        swap
        · omega
        by_cases c359 : a1 < b1 + b3 + b5 + b7
        swap
        · omega
        by_cases c360 : b1 + b3 + b5 < a1 + a3
        swap
        · omega
        have f361 := pair_fact E (i := 3) (j := 7) rfl rfl c357 c358
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f361
        omega
      by_cases c362 : 0 < a1 + a3
      swap
      · omega
      have f363 := pair_fact E (i := 3) (j := 1) rfl rfl c314 c315
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f363
      by_cases c364 : 0 < a7
      swap
      · omega
      by_cases c365 : 0 < b9
      swap
      · omega
      by_cases c366 : a1 + a3 + a5 < b1 + b3 + b5 + b7 + b9
      swap
      · omega
      by_cases c367 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7
      swap
      · -- branch
        by_cases c368 : 0 < a9
        swap
        · omega
        by_cases c369 : 0 < b1
        swap
        · omega
        by_cases c370 : a1 + a3 + a5 + a7 < 0 + b1
        swap
        · -- branch
          by_cases c371 : 0 < a9
          swap
          · omega
          by_cases c372 : 0 < b9
          swap
          · omega
          by_cases c373 : a1 + a3 + a5 + a7 < b1 + b3 + b5 + b7 + b9
          swap
          · omega
          by_cases c374 : b1 + b3 + b5 + b7 < a1 + a3 + a5 + a7 + a9
          swap
          · omega
          have f375 := pair_fact E (i := 9) (j := 9) rfl rfl c371 c372
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f375
          by_cases c376 : 0 < a7
          swap
          · omega
          by_cases c377 : 0 < b1
          swap
          · omega
          by_cases c378 : a1 + a3 + a5 < 0 + b1
          swap
          · -- branch
            by_cases c379 : 0 < a7
            swap
            · omega
            by_cases c380 : 0 < b7
            swap
            · omega
            by_cases c381 : a1 + a3 + a5 < b1 + b3 + b5 + b7
            swap
            · omega
            by_cases c382 : b1 + b3 + b5 < a1 + a3 + a5 + a7
            swap
            · omega
            have f383 := pair_fact E (i := 7) (j := 7) rfl rfl c379 c380
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
              (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f383
            omega
          by_cases c384 : 0 < a1 + a3 + a5 + a7
          swap
          · omega
          have f385 := pair_fact E (i := 7) (j := 1) rfl rfl c376 c377
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
            (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f385
          omega
        by_cases c386 : 0 < a1 + a3 + a5 + a7 + a9
        swap
        · omega
        have f387 := pair_fact E (i := 9) (j := 1) rfl rfl c368 c369
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
          (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f387
        omega
      have f388 := pair_fact E (i := 7) (j := 9) rfl rfl c364 c365
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
        (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f388
      omega
    have f389 := pair_fact E (i := 3) (j := 9) rfl rfl c190 c311
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
      (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f389
    omega
  have f390 := pair_fact E (i := 1) (j := 9) rfl rfl c131 c132
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
    (by simp only [onesB, ↓reduceIte, Bool.false_eq_true]; omega)
  simp only [zerosB, ↓reduceIte, Bool.false_eq_true] at f390
  omega

end Blocks
