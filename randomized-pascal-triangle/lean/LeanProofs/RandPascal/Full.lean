import LeanProofs.RandPascal.CertBridge
import LeanProofs.RandPascal.Cert.Local
import LeanProofs.RandPascal.Mean

/-!
# Theorem B, unconditionally

`RandPascal.Cert.local_inequality` proves the certificate's local inequality for every nonnegative
real quadruple and every `p ∈ [29/125, 1]`: the Bernstein identity reduces it to four
coefficients, and their nonnegativity is checked in Lean on each of the 688 sign regions of the
hyperplane arrangement. With `Gloc_main` it is exactly `LocalIneq mainCert p`, so the hypothesis
of Theorem B is discharged.
-/

open Filter

namespace RandPascal

/-- The local inequality of Theorem B, proved. -/
theorem localIneq_main {p : ℝ} (hp0 : 29 / 125 ≤ p) (hp1 : p ≤ 1) : LocalIneq mainCert p := by
  intro a b c d ha hb hc hd
  have h := Cert.local_inequality hp0 hp1 ha hb hc hd
  unfold Cert.localExpect at h
  rw [Gloc_main]
  linarith

/-- **Theorem B.** For `29/125 ≤ p ≤ 1`, `E[S_n] ≥ (5001/5000)ⁿ`. -/
theorem theoremB_full {p : ℝ} (hp0 : 29 / 125 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (5001 / 5000 : ℝ) ^ n ≤ Exp p n (S (n + 4)) :=
  theoremB hp0 hp1 (localIneq_main hp0 hp1) n

/-- **Answer for `p ≥ 29/125`:** `L_p = ∞`. -/
theorem meanN_diverges_B_full {p : ℝ} (hp0 : 29 / 125 ≤ p) (hp1 : p ≤ 1) :
    Tendsto (meanN p) atTop atTop :=
  meanN_diverges_B hp0 hp1 (localIneq_main hp0 hp1)

end RandPascal
