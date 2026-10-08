import Mathlib.Tactic.CasesM
import LeanProofs.Shuffle

/-- `W k = 0^(k+5) 1 0^2 1^4 0^(k+4) 1^3 0 1^4`: length 2k + 24, twelve 1s. -/
def W (k : Nat) : List Bool := ofGaps [k + 5, 2, 0, 0, 0, k + 4, 0, 0, 1, 0, 0, 0, 0]
