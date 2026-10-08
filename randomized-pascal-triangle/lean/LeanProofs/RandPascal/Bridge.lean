import LeanProofs.RandPascal.TheoremB

/-!
# Bridge to the external certificate

`Gloc mainCert` evaluated in Lean at `p = 29/125` agrees exactly with the value computed by the
independent Python checker (`recheck.py`, `G_poly`) at five points, so the hypothesis `LocalIneq`
is a statement about the same function the certificate checks.
-/

namespace RandPascal

open Finset


lemma bridge1 : Gloc mainCert (29 / 125) 1 0 0 0 = 6757339 / 18750000 := by
  simp [Gloc, E3, Oloc, Iloc, cell, w, mainCert, abs_of_nonneg, abs_of_nonpos]; norm_num
lemma bridge2 : Gloc mainCert (29 / 125) 0 1 0 0 = 14705929 / 37500000 := by
  simp [Gloc, E3, Oloc, Iloc, cell, w, mainCert]; norm_num
lemma bridge3 : Gloc mainCert (29 / 125) 1 1 0 0 = 329423 / 2500000 := by
  simp [Gloc, E3, Oloc, Iloc, cell, w, mainCert]; norm_num
lemma bridge4 : Gloc mainCert (29 / 125) 1 2 1 0 = 1383017 / 234375000 := by
  simp [Gloc, E3, Oloc, Iloc, cell, w, mainCert]; norm_num
lemma bridge5 : Gloc mainCert (29 / 125) 2 1 0 1 = 400627 / 9375000 := by
  simp [Gloc, E3, Oloc, Iloc, cell, w, mainCert]; norm_num

end RandPascal
