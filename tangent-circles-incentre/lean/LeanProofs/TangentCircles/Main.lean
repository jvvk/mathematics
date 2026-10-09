import LeanProofs.TangentCircles.Chords
import LeanProofs.TangentCircles.Integral
import LeanProofs.TangentCircles.Crossing
import LeanProofs.TangentCircles.Incircle
import LeanProofs.TangentCircles.Sphere

/-!
# A random triangle on three tangent circles contains the incentre with probability 1/2 (MO 498968)

Formalised, following the note:
* `halfchord_A`, `halfchord_B`, `midpoints_sum`, `product_identity`, `tidy`, `a_div`: chord
  geometry;
* `hasDerivAt_u`, `integral_g`: the substitution `u = arcsin (sin η / cos s)` and the integral `π`;
* `density_form`, `cdf`, `half_mass`, `half`, `tail`: the crossing law and its distribution
  function;
* `tangent_length`, `half_angles`, `rho_sq_lt`, `miss_side`, `conclusion`, `inner_arcs`: the
  triangle
  of centres and the final sum `1/2`;
* `fold_element`, `fold_pair`, `element_change`, `lune`, `lune_fraction`: the uniform sphere.

Not formalised: the change of variables from pairs of points to lines (the Jacobian
`dθ dφ = cos ω |PQ| / (c_A c_B) dz dω`) as a statement about measures, and the plane-geometry facts
(sectors seen from the incentre tile the turn; a side misses iff its crossing lies beyond `I`).
-/
