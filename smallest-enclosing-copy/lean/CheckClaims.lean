import EnclosingCopy

-- Every name in EnclosingCopy/Enclosing/Main.lean's #check (136) and #print axioms (99) lists: statement and axioms.
-- 152 names, in the order of Main.lean; output in axiom-validation.txt.

namespace Enclosing

#check @vertex_limit
#print axioms vertex_limit
#check @point_limit
#print axioms point_limit
#check @vertex_event
#print axioms vertex_event
#check @sum_len_nrm
#print axioms sum_len_nrm
#check @sum_len_hsup
#print axioms sum_len_hsup
#check @sum_len_b
#print axioms sum_len_b
#check @sum_len_a
#print axioms sum_len_a
#check @void_area
#print axioms void_area
#check @kkt_segment_iff
#print axioms kkt_segment_iff
#check @kkt_iff_origin_inside
#print axioms kkt_iff_origin_inside
#check @sigma_inner
#print axioms sigma_inner
#check @segment_prob
#print axioms segment_prob
#check @law_restrict_eq
#print axioms law_restrict_eq
#check @segment_event_prob
#print axioms segment_event_prob
#check @segment_event_closed
#print axioms segment_event_closed
#check @scale_tilt
#print axioms scale_tilt
#check @S_regular
#print axioms S_regular
#check @R_eq_smul
#print axioms R_eq_smul
#check @volume_R
#print axioms volume_R
#check @width_R
#print axioms width_R
#check @V_regular
#print axioms V_regular
#check @segment_term_regular
#print axioms segment_term_regular
#check @segment_term_measure
#print axioms segment_term_measure
#check @segment_term_square
#print axioms segment_term_square
#check @volume_Preg
#print axioms volume_Preg
#check @segment_term_full
#print axioms segment_term_full
#check @V_regular_full
#print axioms V_regular_full
#check @integrand_zero_of_not_bij
#print axioms integrand_zero_of_not_bij
#check @integrand_perm
#print axioms integrand_perm
#check @det_id
#print axioms det_id
#check @KKT_id_iff
#print axioms KKT_id_iff
#check @integral_id
#print axioms integral_id
#check @Tnd_square
#print axioms Tnd_square
#check @p_square
#print axioms p_square
#check @theta_height
#print axioms theta_height
#check @Ik_eq
#print axioms Ik_eq
#check @p_from_Ik
#print axioms p_from_Ik
#check @g_closed
#print axioms g_closed
#check @g_small
#print axioms g_small
#check @p_equilateral
#print axioms p_equilateral
#check @p_right_isosceles
#print axioms p_right_isosceles
#check @p_30_60_90
#print axioms p_30_60_90
#check @p_flat_isosceles
#print axioms p_flat_isosceles
#check @p_needle
#print axioms p_needle
#check @p_thin_right
#print axioms p_thin_right
#check @vertex_mecke
#print axioms vertex_mecke
#check @lintegral_depths
#print axioms lintegral_depths
#check @vertex_count_factor
#print axioms vertex_count_factor
#check @vertex_count_limit
#print axioms vertex_count_limit
#check @model_void_mask
#print axioms model_void_mask
#check @segment_groups_independent
#print axioms segment_groups_independent
#check @maskVoidFn_deriv
#print axioms maskVoidFn_deriv
#check @badExtra_prob_zero
#print axioms badExtra_prob_zero
#check @no_extra_tight_vertex
#print axioms no_extra_tight_vertex
#check @vertex_candidate_prob
#print axioms vertex_candidate_prob
#check @vertex_candidate_prob_factor
#print axioms vertex_candidate_prob_factor
#check @vertex_candidate_prob_limit
#print axioms vertex_candidate_prob_limit
#check @vertex_candidate_unique_optimum
#print axioms vertex_candidate_unique_optimum
#check @segment_bounds_independent
#print axioms segment_bounds_independent
#check @segmentLower_cdf
#print axioms segmentLower_cdf
#check @segmentUpper_survival
#print axioms segmentUpper_survival
#check @segment_bounds_event_prob
#print axioms segment_bounds_event_prob
#check @chord_feasible_prob
#print axioms chord_feasible_prob
#check @segment_lintegral_depths
#print axioms segment_lintegral_depths
#check @fit_integral_eq_spatial
#print axioms fit_integral_eq_spatial
#check @vertexDensity_eq_cone
#print axioms vertexDensity_eq_cone
#check @vertex_candidate_formula_limit
#print axioms vertex_candidate_formula_limit
#check @spatial_square
#print axioms spatial_square
#check @cone_square
#print axioms cone_square
#check @square_vertex_candidate_limit
#print axioms square_vertex_candidate_limit
#check @seg_certificate
#print axioms seg_certificate
#check @segCand_unique
#print axioms segCand_unique
#check @segOrderedCount_eq_law
#print axioms segOrderedCount_eq_law
#check @chord_prob
#print axioms chord_prob
#check @seg_count_factor
#print axioms seg_count_factor
#check @seg_candidate_limit
#print axioms seg_candidate_limit
#check @segDensity_square
#print axioms segDensity_square
#check @chordInf_square
#print axioms chordInf_square
#check @square_seg_candidate_limit
#print axioms square_seg_candidate_limit
#check @square_candidates_limit
#print axioms square_candidates_limit
#check @LPDual.lp_kkt
#print axioms LPDual.lp_kkt
#check @optimum_kkt
#print axioms optimum_kkt
#check @square_support
#print axioms square_support
#check @square_classify
#print axioms square_classify
#check @square_optFit_prob
#print axioms square_optFit_prob
#check @square_optFit_limit
#print axioms square_optFit_limit
#check @general_support
#print axioms general_support
#check @general_classify
#print axioms general_classify
#check @general_optFit_prob
#print axioms general_optFit_prob
#check @general_optFit_limit
#print axioms general_optFit_limit
#check @squareGood
#print axioms squareGood
#check @parPairs_tri
#print axioms parPairs_tri
#check @fit_integral_triangle
#print axioms fit_integral_triangle
#check @coneTerm_perm
#print axioms coneTerm_perm
#check @coneTerm_missing
#print axioms coneTerm_missing
#check @card_class
#print axioms card_class
#check @cone_canon_iff
#print axioms cone_canon_iff
#check @inner_pair
#print axioms inner_pair
#check @coneTerm_canon
#print axioms coneTerm_canon
#check @cone_triangle
#print axioms cone_triangle
#check @triangle_optFit_limit
#print axioms triangle_optFit_limit
#check @equilateral_optFit_limit
#print axioms equilateral_optFit_limit
#check @ConvexPos
#print axioms ConvexPos
#check @sidesOf
#print axioms sidesOf
#check @goodSides_of_convex
#print axioms goodSides_of_convex
#check @convex_optFit_limit
#print axioms convex_optFit_limit
#check @convexPos_triangle
#print axioms convexPos_triangle
#check @triangle_vertices_optFit_limit
#print axioms triangle_vertices_optFit_limit
#check @PoissonPP.superpose
#print axioms PoissonPP.superpose
#check @PoissonPP.superpose_fun
#print axioms PoissonPP.superpose_fun
#check @PoissonPP.lintegral_firstSlabs
#print axioms PoissonPP.lintegral_firstSlabs
#check @model_trunc
#print axioms model_trunc
#check @tilt_bound
#print axioms tilt_bound
#check @stable
#print axioms stable
#check @ae_good
#print axioms ae_good
#check @untruncated_prob
#print axioms untruncated_prob
#check @untruncated_triangle
#print axioms untruncated_triangle
#check @untruncated_equilateral
#print axioms untruncated_equilateral
#check @optimum_structure
#print axioms optimum_structure
#check @optimum_tilt_gap
#print axioms optimum_tilt_gap
#check @nonDeg_ae
#print axioms nonDeg_ae
#check @strict_rep
#print axioms strict_rep
#check @measurableSet_optFit
#print axioms measurableSet_optFit
#check @poisson_stable
#print axioms poisson_stable
#check @evF_iff_optFit
#print axioms evF_iff_optFit
#check @witness_fail_le
#print axioms witness_fail_le
#check @step0
#print axioms step0
#check @step0_sample
#print axioms step0_sample
#check @tangent_param
#print axioms tangent_param
#check @trueEv_iff_evN
#print axioms trueEv_iff_evN
#check @theorem1
#print axioms theorem1
#check @theorem1_model
#print axioms theorem1_model
#check @theorem1_triangle
#print axioms theorem1_triangle
#check @theorem1_equilateral
#print axioms theorem1_equilateral
#check @tetW_eq
#print axioms tetW_eq
#check @theorem1_regular
#print axioms theorem1_regular
#check @model_void
#print axioms model_void
#check @vertex_unique
#print axioms vertex_unique
#check @PoissonPP.law_prob
#print axioms PoissonPP.law_prob
#check @PoissonPP.void_sigma_independent
#print axioms PoissonPP.void_sigma_independent
#check @exists_affine_iff
#print axioms exists_affine_iff
#check @LPDual.farkas
#print axioms LPDual.farkas
#check @badP_prob_zero
#print axioms badP_prob_zero
#check @regVerts_convex
#print axioms regVerts_convex
#check @regVerts_area
#print axioms regVerts_area
#check @spatial_reg
#print axioms spatial_reg
#check @cone_reg
#print axioms cone_reg
#check @segDensity_reg
#print axioms segDensity_reg
#check @slopeSum_reg
#print axioms slopeSum_reg
#check @chordInf_reg
#print axioms chordInf_reg
#check @vertex_term_reg
#print axioms vertex_term_reg
#check @segment_term_reg
#print axioms segment_term_reg

end Enclosing
