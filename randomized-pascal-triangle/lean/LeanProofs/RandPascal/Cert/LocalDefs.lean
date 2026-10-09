import Mathlib.Tactic
import Mathlib.Basic.Real.Basic

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace RandPascal.Cert

noncomputable def upd (h : Bool) (a b : ℝ) : ℝ := if h then a+b else |a-b|

noncomputable def inputCost (a b c d : ℝ) : ℝ :=
  (a+b+c+d)/4 + (1249/2500 : ℝ)*(|a-b|+|b-c|+|c-d|)/3 +
  (3/100 : ℝ)*(|a-c|+|b-d|)/2 +
  (557/2500 : ℝ)*(abs (|a-b| - |b-c|)+abs (|b-c| - |c-d|))/2

noncomputable def outputCost (A B C : ℝ) : ℝ :=
  (A+B+C)/3 + (1249/2500 : ℝ)*(|A-B|+|B-C|)/2 +
  (3/100 : ℝ)*|A-C| + (557/2500 : ℝ)*abs (|A-B| - |B-C|) -
  (81/2500 : ℝ)*(A+C-2*B)

noncomputable def base (a b c d : ℝ) : ℝ :=
  -(5001/5000 : ℝ)*inputCost a b c d + (999/10000 : ℝ)*(a+d-b-c)

noncomputable def out000 (a b c d : ℝ) : ℝ :=
  outputCost (upd false a b) (upd false b c) (upd false c d)

noncomputable def out001 (a b c d : ℝ) : ℝ :=
  outputCost (upd false a b) (upd false b c) (upd true c d)

noncomputable def out010 (a b c d : ℝ) : ℝ :=
  outputCost (upd false a b) (upd true b c) (upd false c d)

noncomputable def out011 (a b c d : ℝ) : ℝ :=
  outputCost (upd false a b) (upd true b c) (upd true c d)

noncomputable def out100 (a b c d : ℝ) : ℝ :=
  outputCost (upd true a b) (upd false b c) (upd false c d)

noncomputable def out101 (a b c d : ℝ) : ℝ :=
  outputCost (upd true a b) (upd false b c) (upd true c d)

noncomputable def out110 (a b c d : ℝ) : ℝ :=
  outputCost (upd true a b) (upd true b c) (upd false c d)

noncomputable def out111 (a b c d : ℝ) : ℝ :=
  outputCost (upd true a b) (upd true b c) (upd true c d)

noncomputable def b0 (a b c d : ℝ) : ℝ := base a b c d +
  (884736 / 1953125 : ℝ) * out000 a b c d +
  (267264 / 1953125 : ℝ) * out001 a b c d +
  (267264 / 1953125 : ℝ) * out010 a b c d +
  (80736 / 1953125 : ℝ) * out011 a b c d +
  (267264 / 1953125 : ℝ) * out100 a b c d +
  (80736 / 1953125 : ℝ) * out101 a b c d +
  (80736 / 1953125 : ℝ) * out110 a b c d +
  (24389 / 1953125 : ℝ) * out111 a b c d

noncomputable def b1 (a b c d : ℝ) : ℝ := base a b c d +
  (3072 / 15625 : ℝ) * out001 a b c d +
  (3072 / 15625 : ℝ) * out010 a b c d +
  (1856 / 15625 : ℝ) * out011 a b c d +
  (3072 / 15625 : ℝ) * out100 a b c d +
  (1856 / 15625 : ℝ) * out101 a b c d +
  (1856 / 15625 : ℝ) * out110 a b c d +
  (841 / 15625 : ℝ) * out111 a b c d

noncomputable def b2 (a b c d : ℝ) : ℝ := base a b c d +
  (32 / 125 : ℝ) * out011 a b c d +
  (32 / 125 : ℝ) * out101 a b c d +
  (32 / 125 : ℝ) * out110 a b c d +
  (29 / 125 : ℝ) * out111 a b c d

noncomputable def b3 (a b c d : ℝ) : ℝ := base a b c d +
  1 * out111 a b c d

end RandPascal.Cert
