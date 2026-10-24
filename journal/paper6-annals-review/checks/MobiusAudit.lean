import Vinogradov.Mobius.Main
import Vinogradov.Mobius.GeneralForward
import Vinogradov.Mobius.ReviewBoundary

/-! Analytic implication audit. The forward 11/12 power bound and the converse
are checked below. The external zero-free input remains explicit. The general
boundary statements and the fresh full external proof build have separate
coverage; this file must not be reported as their completed audit. -/

#print axioms Vinogradov.Mobius.negative_real_part_bound
#print axioms Vinogradov.Mobius.reciprocal_bound_of_nonvanishing
#print axioms Vinogradov.Mobius.smoothed_mellin_identity
#print axioms Vinogradov.Mobius.nonvanishing_of_one_smoothed_bound
#print axioms Vinogradov.Mobius.explicit_test_weight
#print axioms Vinogradov.Mobius.nonvanishing_of_smoothed_mobius_cancellation
#print axioms Vinogradov.Mobius.mellin_eq_mellinSchwartz
#print axioms Vinogradov.Mobius.mellin_polynomial_weight_integrable
#print axioms Vinogradov.Mobius.mellin_uniform_strip_bound
#print axioms Vinogradov.Mobius.scaledSum_mellin_convergent_two
#print axioms Vinogradov.Mobius.forward_mellin_inversion
#print axioms Vinogradov.Mobius.forwardKernel_line_integrable
#print axioms Vinogradov.Mobius.smoothedSum_eq_forward_integral
#print axioms Vinogradov.Mobius.shifted_forward_integral
#print axioms Vinogradov.Mobius.smoothed_mobius_bound_of_seven_eighths
#print axioms Vinogradov.Mobius.polynomial_reciprocal_of_nonvanishing
#print axioms Vinogradov.Mobius.smoothed_bounds_of_nonvanishing
#print axioms Vinogradov.Mobius.nonvanishing_iff_smoothed_bounds
#print axioms Vinogradov.Mobius.ReviewBoundary.riesz_at_boundary_of_nonvanishing
