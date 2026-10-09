import LeanProofs

-- Section 3: a tiling by translates under `ker φ` is a bijection of the cells onto `G`
#check @CubeUnfoldings.tilesBy_ker_iff
#print axioms CubeUnfoldings.tilesBy_ker_iff
-- Lemma 3 (lattice tilings)
#check @CubeUnfoldings.tiles_one_iff
#print axioms CubeUnfoldings.tiles_one_iff
-- Lemma 4 (two tiles)
#check @CubeUnfoldings.tiles_two_iff
#print axioms CubeUnfoldings.tiles_two_iff
-- Lemma 5 (P and t − P; the sumset A + A)
#check @CubeUnfoldings.tiles_refl_iff
#print axioms CubeUnfoldings.tiles_refl_iff
#check @CubeUnfoldings.exists_tiles_refl_iff
#print axioms CubeUnfoldings.exists_tiles_refl_iff
-- Example 6 (an unfolding of the five-cube)
#check @CubeUnfoldings.example_five
#print axioms CubeUnfoldings.example_five
