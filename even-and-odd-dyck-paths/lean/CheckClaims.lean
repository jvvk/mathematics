import LeanProofs

open QNarayana
-- Theorem 1
#check @signed_dyck
#print axioms signed_dyck
-- Lemmas 1 and 2: Dyck paths and their words (flags, the run decoder, heights, maj, mirror images)
#print axioms dec_flags
#print axioms dec_spec
#print axioms dk_dec
#print axioms okTo_count
#print axioms encW_mem
#print axioms decW_mem
#print axioms maj_sign
#print axioms sym_iff
-- Lemma 3: the partner rule
#print axioms partner_facts
#print axioms ι_ι
#print axioms okTo_ι
#print axioms wt2_ι
#print axioms sgn_ι
#print axioms fix_to_F
#print axioms F_to_fix
#print axioms sgn_F
#print axioms signed_sum_eq_card_fix
-- Lemma 4: halving and last departures
#print axioms minRel_half
#print axioms unhalf_half
#print axioms F_unhalf
#print axioms sym_decomp
#print axioms card_Fix_eq_card_Sym
#print axioms signed_sum_eq_card_sym
-- the definitions are not vacuous: Narayana row n = 5, then E - O and S for n = 5 and n = 6
#eval (List.range 5).map fun k => (Dyck 5 k).card
#eval (List.range 5).map fun k => ∑ P ∈ Dyck 5 k, (-1 : ℤ) ^ maj P
#eval (List.range 5).map fun k => ((Dyck 5 k).filter (fun P => rc P = P)).card
#eval (List.range 6).map fun k => ((Dyck 6 k).filter (fun P => rc P = P)).card
