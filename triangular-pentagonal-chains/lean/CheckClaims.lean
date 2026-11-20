import LeanProofs

-- The base chains enter as a hypothesis; these print exactly what it says.
#print TriChains.BaseHyp
#print PentChains.BaseHyp

#check @TriChains.berlekamp_guy
#print axioms TriChains.berlekamp_guy
#check @TriChains.good_all
#print axioms TriChains.good_all
#check @PentChains.berlekamp_guy
#print axioms PentChains.berlekamp_guy
#check @PentChains.good_all
#print axioms PentChains.good_all
