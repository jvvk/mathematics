import EnclosingCopy.Poisson.IIDBounds

/-! The fixed-window probability ingredients for Theorem 1 of MO 458571.
Localization and optimum stability are supplied by the Theorem1* modules. -/
#check @PoissonPP.tendsto_mass_l1
#check @PoissonPP.binomial_mass_average
#check @PoissonPP.countMix_poisson
#check @PoissonPP.iid_window_prob
#check @PoissonPP.tuple_event_limit_of_ae
#check @PoissonPP.iid_window_event_limit
#check @PoissonPP.iid_void_limit
#check @PoissonPP.iid_hit_limit_zero
#print axioms PoissonPP.tendsto_mass_l1
#print axioms PoissonPP.binomial_mass_average
#print axioms PoissonPP.countMix_poisson
#print axioms PoissonPP.iid_window_prob
#print axioms PoissonPP.tuple_event_limit_of_ae
#print axioms PoissonPP.iid_window_event_limit
#print axioms PoissonPP.iid_void_limit
#print axioms PoissonPP.iid_hit_limit_zero
