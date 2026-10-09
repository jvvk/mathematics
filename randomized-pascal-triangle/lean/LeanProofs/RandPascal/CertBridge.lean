import LeanProofs.RandPascal.TheoremB
import LeanProofs.RandPascal.Cert.LocalDefs

/-!
# The certificate's local function is `Gloc mainCert`

`RandPascal.Cert` (generated from the exact certificate, then checked by Lean region by region)
states the local inequality with its own names: `inputCost`, `outputCost`, `upd` and the eight
coin outcomes `out000`, …, `out111`. Here we show that these are the `Iloc`, `Oloc`, `cell` and
`E3` of Theorem B for `mainCert`, so the certificate proves exactly the hypothesis `LocalIneq`.
-/

namespace RandPascal

open Cert

lemma Iloc_main (a b c d : ℝ) : Iloc mainCert a b c d = inputCost a b c d := by
  simp only [Iloc, inputCost, mainCert]
  rw [abs_sub_comm b a, abs_sub_comm c b, abs_sub_comm d c, abs_sub_comm c a, abs_sub_comm d b,
    abs_sub_comm (|b - c|) (|a - b|), abs_sub_comm (|c - d|) (|b - c|)]
  ring

lemma Oloc_main (A B D : ℝ) : Oloc mainCert A B D = outputCost A B D := by
  simp only [Oloc, outputCost, mainCert]
  rw [abs_sub_comm B A, abs_sub_comm D B, abs_sub_comm D A, abs_sub_comm (|B - D|) (|A - B|)]
  ring

lemma cell_eq_upd (h : Bool) (u v : ℝ) : cell h u v = upd h u v := rfl

/-- `Gloc mainCert` written with the certificate's names. -/
lemma Gloc_main (p a b c d : ℝ) :
    Gloc mainCert p a b c d =
      ((1-p)^3*out000 a b c d + (1-p)^2*p*out001 a b c d +
        (1-p)^2*p*out010 a b c d + (1-p)*p^2*out011 a b c d +
        (1-p)^2*p*out100 a b c d + (1-p)*p^2*out101 a b c d +
        (1-p)*p^2*out110 a b c d + p^3*out111 a b c d)
      - (5001/5000 : ℝ) * inputCost a b c d + (999/10000 : ℝ) * (a + d - b - c) := by
  have hO : Oloc mainCert = outputCost := by funext A B D; exact Oloc_main A B D
  unfold Gloc
  rw [Iloc_main, hO]
  simp only [E3, Fintype.sum_bool, w, cell_eq_upd, out000, out001, out010, out011, out100, out101,
    out110, out111, mainCert, ↓reduceIte, Bool.false_eq_true]
  ring

end RandPascal
