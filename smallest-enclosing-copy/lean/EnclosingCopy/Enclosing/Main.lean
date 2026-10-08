import EnclosingCopy.Enclosing.Void
import EnclosingCopy.Enclosing.SquareVertex
import EnclosingCopy.Enclosing.SegmentProb
import EnclosingCopy.Enclosing.Linearise
import EnclosingCopy.Enclosing.LP
import EnclosingCopy.Enclosing.TriangleDeriv
import EnclosingCopy.Enclosing.VertexCount
import EnclosingCopy.Enclosing.SegmentModel
import EnclosingCopy.Enclosing.NullEvents
import EnclosingCopy.Enclosing.VertexEvent
import EnclosingCopy.Enclosing.SegmentBounds
import EnclosingCopy.Enclosing.SegmentCoordinates
import EnclosingCopy.Enclosing.VertexSpatial
import EnclosingCopy.Enclosing.SquareModel
import EnclosingCopy.Enclosing.SegmentCount
import EnclosingCopy.Enclosing.SquareSegment
import EnclosingCopy.Enclosing.Classification
import EnclosingCopy.Enclosing.GeneralClassify
import EnclosingCopy.Enclosing.TriangleCone
import EnclosingCopy.Enclosing.ConvexPolygon
import EnclosingCopy.Enclosing.Untruncated
import EnclosingCopy.Enclosing.WindowAudit
import EnclosingCopy.Enclosing.GeometryAudit
import EnclosingCopy.Enclosing.BoundaryAudit
import EnclosingCopy.Enclosing.EndpointAudit
import EnclosingCopy.Enclosing.AreaAudit
import EnclosingCopy.Enclosing.TangentAudit
import EnclosingCopy.Enclosing.UniformAudit
import EnclosingCopy.Enclosing.Theorem1
import EnclosingCopy.Enclosing.Theorem1Regular

/-!
# Smallest enclosing copy (MO 458571): the formalised results

See `README.md` in this folder for the map from the paper to these names, and for what is not
formalised. The finite Poisson model and the vertex- and segment-candidate probabilities (with their
cutoff limits, and the square's values `1/12` and `4 · 1/24`) are included; for the square the
optimum is classified almost surely, so `P(E) → 1/4` in the model. Finite-sample convergence
(Theorem 1) is `theorem1` (Theorem1), assembled from the fixed-window probability ingredients
(Poisson/CountConvergence, MarkedWindow, IIDWindow, WindowLimit, IIDBounds), the polygon
sampling law, witness windows and corner overlaps (PolygonSampling, PolygonOverlap,
PolygonWitnesses), the boundary-window Poisson limits (BoundaryLimit, FullBoundaryLimit,
UniformBoundary, VaryingBoundaryLimit), the tangent-coordinate modules, and the Theorem1*
modules (localization, null events, strict representatives, almost-sure stabilization, cutoff
removal). Corollary 3 is `theorem1_regular` (Theorem1Regular).
-/

namespace Enclosing

-- Section 2: the limit LP and event E are the first-order limits of the geometry
#check @vertex_limit
#check @point_limit
#check @vertex_event
-- identities (1) and Lemma 7
#check @sum_len_nrm
#check @sum_len_hsup
#check @sum_len_b
#check @sum_len_a
#check @void_area
-- Theorem 8, segment optima
#check @kkt_segment_iff
#check @kkt_iff_origin_inside
#check @sigma_inner
#check @segment_prob
#check @law_restrict_eq
#check @segment_event_prob
#check @segment_event_closed
-- Section 7, regular polygons
#check @scale_tilt
#check @S_regular
#check @R_eq_smul
#check @volume_R
#check @width_R
#check @V_regular
#check @segment_term_regular
#check @segment_term_measure
#check @segment_term_square
#check @volume_Preg
#check @segment_term_full
#check @V_regular_full
-- the square: vertex term and p₄ = 1/4
#check @integrand_zero_of_not_bij
#check @integrand_perm
#check @det_id
#check @KKT_id_iff
#check @integral_id
#check @Tnd_square
#check @p_square
-- Section 6 and Corollary 2, triangles
#check @theta_height
#check @Ik_eq
#check @p_from_Ik
#check @g_closed
#check @g_small
#check @p_equilateral
#check @p_right_isosceles
#check @p_30_60_90
#check @p_flat_isosceles
#check @p_needle
#check @p_thin_right

-- The Poisson model: candidates, Mecke, Jacobian and removal of the cutoff
#check @vertex_mecke
#check @lintegral_depths
#check @vertex_count_factor
#check @vertex_count_limit
-- Segment side groups and the null event needed for vertex classification
#check @model_void_mask
#check @segment_groups_independent
#check @maskVoidFn_deriv
#check @badExtra_prob_zero
#check @no_extra_tight_vertex

-- Actual event probabilities and the segment depth-to-copy Jacobian
#check @vertex_candidate_prob
#check @vertex_candidate_prob_factor
#check @vertex_candidate_prob_limit
#check @vertex_candidate_unique_optimum
#check @segment_bounds_independent
#check @segmentLower_cdf
#check @segmentUpper_survival
#check @segment_bounds_event_prob
#check @chord_feasible_prob
#check @segment_lintegral_depths
#check @fit_integral_eq_spatial
#check @vertexDensity_eq_cone
#check @vertex_candidate_formula_limit
-- the square inside the Poisson model
#check @spatial_square
#check @cone_square
#check @square_vertex_candidate_limit
-- Theorem 8, segment case, inside the Poisson model
#check @seg_certificate
#check @segCand_unique
#check @segOrderedCount_eq_law
#check @chord_prob
#check @seg_count_factor
#check @seg_candidate_limit
#check @segDensity_square
#check @chordInf_square
#check @square_seg_candidate_limit
#check @square_candidates_limit
-- classification of fitting optima: P(E) → 1/4 for the square in the model
#check @LPDual.lp_kkt
#check @optimum_kkt
#check @square_support
#check @square_classify
#check @square_optFit_prob
#check @square_optFit_limit
-- Theorem 8 in the model, any polygon with `GoodSides`
#check @general_support
#check @general_classify
#check @general_optFit_prob
#check @general_optFit_limit
#check @squareGood
-- triangles in the model: P(E) → p(L₁², L₂², L₃²) of Corollary 2; equilateral 13/48
#check @parPairs_tri
#check @fit_integral_triangle
#check @coneTerm_perm
#check @coneTerm_missing
#check @card_class
#check @cone_canon_iff
#check @inner_pair
#check @coneTerm_canon
#check @cone_triangle
#check @triangle_optFit_limit
#check @equilateral_optFit_limit
-- genuine convex polygons: strict convex position ⇒ GoodSides
#check @ConvexPos
#check @sidesOf
#check @goodSides_of_convex
#check @convex_optFit_limit
#check @convexPos_triangle
#check @triangle_vertices_optFit_limit
-- the untruncated model: infinite strips from independent slabs
#check @PoissonPP.superpose
#check @PoissonPP.superpose_fun
#check @PoissonPP.lintegral_firstSlabs
#check @model_trunc
#check @tilt_bound
#check @stable
#check @ae_good
#check @untruncated_prob
#check @untruncated_triangle
#check @untruncated_equilateral

-- Theorem 1 (finite-sample convergence)
#check @optimum_structure
#check @optimum_tilt_gap
#check @nonDeg_ae
#check @strict_rep
#check @measurableSet_optFit
#check @poisson_stable
#check @evF_iff_optFit
#check @witness_fail_le
#check @step0
#check @step0_sample
#check @tangent_param
#check @trueEv_iff_evN
#check @theorem1
#check @theorem1_model
#check @theorem1_triangle
#check @theorem1_equilateral
#check @tetW_eq
#check @theorem1_regular

end Enclosing

#print axioms Enclosing.void_area
#print axioms Enclosing.segment_term_square
#print axioms Enclosing.segment_term_measure
#print axioms Enclosing.V_regular
#print axioms Enclosing.p_from_Ik
#print axioms Enclosing.Ik_eq
#print axioms Enclosing.theta_height
#print axioms Enclosing.p_equilateral
#print axioms Enclosing.p_30_60_90
#print axioms Enclosing.p_flat_isosceles
#print axioms Enclosing.p_thin_right
#print axioms Enclosing.kkt_segment_iff
#print axioms Enclosing.segment_prob
#print axioms Enclosing.volume_Preg
#print axioms Enclosing.segment_term_full
#print axioms Enclosing.V_regular_full
#print axioms Enclosing.Tnd_square
#print axioms Enclosing.p_square
#print axioms Enclosing.segment_event_prob
#print axioms Enclosing.segment_event_closed
#print axioms Enclosing.vertex_event
#print axioms Enclosing.point_limit
#print axioms Enclosing.model_void
#print axioms Enclosing.vertex_unique

#print axioms PoissonPP.law_prob
#print axioms PoissonPP.void_sigma_independent
#print axioms Enclosing.vertex_count_factor
#print axioms Enclosing.vertex_count_limit
#print axioms Enclosing.model_void_mask
#print axioms Enclosing.segment_groups_independent
#print axioms Enclosing.maskVoidFn_deriv
#print axioms Enclosing.badExtra_prob_zero
#print axioms Enclosing.no_extra_tight_vertex

#print axioms Enclosing.vertex_candidate_prob
#print axioms Enclosing.vertex_candidate_prob_factor
#print axioms Enclosing.vertex_candidate_prob_limit
#print axioms Enclosing.vertex_candidate_unique_optimum
#print axioms Enclosing.segment_bounds_independent
#print axioms Enclosing.segmentLower_cdf
#print axioms Enclosing.segmentUpper_survival
#print axioms Enclosing.segment_bounds_event_prob
#print axioms Enclosing.chord_feasible_prob
#print axioms Enclosing.segment_lintegral_depths

#print axioms Enclosing.fit_integral_eq_spatial
#print axioms Enclosing.vertexDensity_eq_cone
#print axioms Enclosing.vertex_candidate_formula_limit
#print axioms Enclosing.square_vertex_candidate_limit
#print axioms Enclosing.exists_affine_iff
#print axioms Enclosing.seg_certificate
#print axioms Enclosing.segCand_unique
#print axioms Enclosing.segOrderedCount_eq_law
#print axioms Enclosing.chord_prob
#print axioms Enclosing.seg_count_factor
#print axioms Enclosing.seg_candidate_limit
#print axioms Enclosing.segDensity_square
#print axioms Enclosing.chordInf_square
#print axioms Enclosing.square_seg_candidate_limit
#print axioms Enclosing.square_candidates_limit
#print axioms LPDual.farkas
#print axioms LPDual.lp_kkt
#print axioms Enclosing.badP_prob_zero
#print axioms Enclosing.square_classify
#print axioms Enclosing.square_optFit_prob
#print axioms Enclosing.square_optFit_limit
#print axioms Enclosing.general_classify
#print axioms Enclosing.general_optFit_prob
#print axioms Enclosing.general_optFit_limit
#print axioms Enclosing.squareGood
#print axioms Enclosing.fit_integral_triangle
#print axioms Enclosing.cone_triangle
#print axioms Enclosing.triangle_optFit_limit
#print axioms Enclosing.equilateral_optFit_limit
#print axioms Enclosing.goodSides_of_convex
#print axioms Enclosing.convex_optFit_limit
#print axioms Enclosing.triangle_vertices_optFit_limit
#print axioms PoissonPP.superpose_fun
#print axioms PoissonPP.lintegral_firstSlabs
#print axioms Enclosing.untruncated_prob
#print axioms Enclosing.untruncated_triangle
#print axioms Enclosing.untruncated_equilateral
#print axioms Enclosing.strict_rep
#print axioms Enclosing.poisson_stable
#print axioms Enclosing.step0
#print axioms Enclosing.trueEv_iff_evN
#print axioms Enclosing.theorem1
#print axioms Enclosing.theorem1_model
#print axioms Enclosing.theorem1_triangle
#print axioms Enclosing.theorem1_equilateral
#print axioms Enclosing.tetW_eq
#print axioms Enclosing.regVerts_convex
#print axioms Enclosing.regVerts_area
#print axioms Enclosing.spatial_reg
#print axioms Enclosing.cone_reg
#print axioms Enclosing.segDensity_reg
#print axioms Enclosing.slopeSum_reg
#print axioms Enclosing.chordInf_reg
#print axioms Enclosing.vertex_term_reg
#print axioms Enclosing.segment_term_reg
#print axioms Enclosing.theorem1_regular
