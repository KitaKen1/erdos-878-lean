import Erdos878.TrackBBilinear
import Erdos878.TrackBExponentialPhase
import Erdos878.TrackBFirstDerivativeTest
import Erdos878.TrackBEndpointParameters

/-! Kernel audit for Track B, including the concrete endpoint proof of the
ordinary maximal-order statement. -/

#print axioms Erdos878.TrackB.vaughan_weighted_sum
#print axioms Erdos878.TrackB.sum_Ioc_card_divisors_sq_le
#print axioms Erdos878.TrackB.abs_typeICoeff_le_log
#print axioms Erdos878.TrackB.typeICoeff_eq_zero_of_mul_lt
#print axioms Erdos878.TrackB.sum_typeIICoeff_sq_le_on_dyadic
#print axioms Erdos878.TrackB.sum_lambdaGT_sq_le_on_dyadic
#print axioms Erdos878.TrackB.correlation_product_filter_eq_Ioc
#print axioms Erdos878.TrackB.weightedArithmeticSum_convolution_band
#print axioms Erdos878.TrackB.weightedArithmeticSum_typeII_eq_dyadic
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_typeII_le_dyadic
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_typeII_le_of_box_bound
#print axioms Erdos878.TrackB.deriv2_reciprocalLogPhase
#print axioms Erdos878.TrackB.deriv2_reciprocalLogCorrelation
#print axioms Erdos878.TrackB.deriv2_reciprocalLogPhase_bounds
#print axioms Erdos878.TrackB.deriv2_reciprocalLogCorrelation_comparable
#print axioms Erdos878.TrackB.correlation_curvature_on_product_band
#print axioms Erdos878.TrackB.norm_reciprocalLogWeight
#print axioms Erdos878.TrackB.sum_bandPhase_correlation
#print axioms Erdos878.TrackB.correlation_real_hull_bounds
#print axioms Erdos878.TrackB.phaseResolvent_eq
#print axioms Erdos878.TrackB.norm_phaseResolvent_le
#print axioms Erdos878.TrackB.sum_norm_phaseResolvent_sub
#print axioms Erdos878.TrackB.norm_sum_phaseCharacter_le_of_monotone_increments
#print axioms Erdos878.TrackB.norm_sum_phaseCharacter_le_of_monotone_increments_closed
#print axioms Erdos878.TrackB.norm_sum_phaseCharacter_le_of_monotone_deriv
#print axioms Erdos878.TrackB.norm_sum_phaseCharacter_le_of_monotone_deriv_strip
#print axioms Erdos878.TrackB.sub_bounds_of_hasDerivAt_bounds
#print axioms Erdos878.TrackB.card_image_floor_le
#print axioms Erdos878.TrackB.card_derivativeNear_le
#print axioms Erdos878.TrackB.sum_eq_derivative_near_add_far
#print axioms Erdos878.TrackB.norm_sum_derivativeFar_le
#print axioms Erdos878.TrackB.second_derivative_test_parameterized
#print axioms Erdos878.TrackB.second_derivative_test_small
#print axioms Erdos878.TrackB.second_derivative_test_small_of_deriv
#print axioms Erdos878.TrackB.norm_sum_reciprocalLogPhase_Icc_le
#print axioms Erdos878.TrackB.norm_sum_reciprocalLogCorrelation_Icc_le
#print axioms Erdos878.TrackB.norm_sum_bandPhase_correlation_le
#print axioms Erdos878.TrackB.norm_sum_range_smul_le_two_mul_endpoint
#print axioms Erdos878.TrackB.norm_sum_range_log_mul_le
#print axioms Erdos878.TrackB.norm_sum_Icc_log_mul_le
#print axioms Erdos878.TrackB.norm_sum_log_mul_reciprocalLogPhase_Icc_le
#print axioms Erdos878.TrackB.ofReal_sum_norm_sq_eq_sum_correlation
#print axioms Erdos878.TrackB.sum_norm_sq_inner_le_sum_abs_mul_norm_correlation
#print axioms Erdos878.TrackB.norm_sq_sum_mul_sum_le_sq_sum_mul_correlation
#print axioms Erdos878.TrackB.norm_sq_sum_productBandTerm_reciprocalLogWeight_le
#print axioms Erdos878.TrackB.norm_sum_bandPhase_correlation_comm
#print axioms Erdos878.TrackB.norm_sum_bandPhase_correlation_le_symmetric
#print axioms Erdos878.TrackB.norm_sq_sum_productBandTerm_le_diagonal_offDiagonal
#print axioms Erdos878.TrackB.norm_sq_sum_productBandTerm_le_explicit_correlationBound
#print axioms Erdos878.TrackB.norm_sq_sum_productBandTerm_le_explicit_correlationBound_with_moment
#print axioms Erdos878.TrackB.sum_abs_mul_ite_eq_diagonal_add_offDiagonal
#print axioms Erdos878.TrackB.norm_sq_sum_productBandTerm_le_moment_mul_diagonal_add_offDiagonal
#print axioms Erdos878.TrackB.typeII_diagonal_le
#print axioms Erdos878.TrackB.norm_sq_sum_productBandTerm_le_explicit_diagonal_add_offDiagonal
#print axioms Erdos878.TrackB.sum_typeIIUpperPairs_eq_sum_typeIIShiftPairs
#print axioms Erdos878.TrackB.sum_offDiagonal_eq_two_mul_sum_shifts
#print axioms Erdos878.TrackB.sum_sq_shift_le_sum_sq
#print axioms Erdos878.TrackB.sum_abs_mul_shift_le_sum_sq
#print axioms Erdos878.TrackB.sum_shift_kernel_le_moment_mul_sum
#print axioms Erdos878.TrackB.sum_offDiagonal_distanceKernel_le
#print axioms Erdos878.TrackB.typeIICorrelationBound_le_typeIIDistanceBound
#print axioms Erdos878.TrackB.sum_offDiagonal_typeIICorrelationBound_le_distanceMoment
#print axioms Erdos878.TrackB.sum_sqrt_Ioc_le_mul_sqrt
#print axioms Erdos878.TrackB.sum_inv_sqrt_Ioc_le
#print axioms Erdos878.TrackB.norm_sq_sum_productBandTerm_le_distanceSum
#print axioms Erdos878.TrackB.sum_Ioc_sub_eq
#print axioms Erdos878.TrackB.one_div_sqrt_le_two_mul_sqrt_sub
#print axioms Erdos878.TrackB.sum_inv_sqrt_Ioc_le_two_mul_sqrt
#print axioms Erdos878.TrackB.typeIIDistanceBound_eq_scale
#print axioms Erdos878.TrackB.sum_typeIIDistanceBound_le_explicit_sqrt
#print axioms Erdos878.TrackB.norm_sq_sum_productBandTerm_le_explicitDistance
#print axioms Erdos878.TrackB.typeII_lambda_le_one_of_scale
#print axioms Erdos878.TrackB.norm_sq_sum_productBandTerm_le_explicitDistance_of_scale
#print axioms Erdos878.TrackB.norm_sq_productBand_box_le_moments
#print axioms Erdos878.TrackB.sum_typeIICoeff_sq_le_common
#print axioms Erdos878.TrackB.sum_lambdaGT_sq_le_common
#print axioms Erdos878.TrackB.sqrt_typeIILambdaScale_eq
#print axioms Erdos878.TrackB.sum_typeIIDistanceBound_le_frequency
#print axioms Erdos878.TrackB.norm_sq_productBand_box_le_common_moments
#print axioms Erdos878.TrackB.typeII_scale_of_long_box
#print axioms Erdos878.TrackB.typeII_normalized_error_le
#print axioms Erdos878.TrackB.norm_productBand_box_le_uniform
#print axioms Erdos878.TrackB.productBandTerm_typeII_ne_zero_properties
#print axioms Erdos878.TrackB.norm_typeII_productBand_box_le_uniform
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_typeII_le_explicit
#print axioms Erdos878.TrackB.typeIIUniformBoxBound_eq
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_typeII_le_normalized
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_typeII_le_uniform_endpoint
#print axioms Erdos878.TrackB.reciprocalLogPhase_curvature_of_ratio
#print axioms Erdos878.TrackB.norm_sum_reciprocalLogPhase_Icc_le_of_ratio
#print axioms Erdos878.TrackB.typeIInnerBound_nonneg
#print axioms Erdos878.TrackB.typeI_lambda_le_one
#print axioms Erdos878.TrackB.sqrt_typeI_lambda
#print axioms Erdos878.TrackB.typeI_scalar_bound
#print axioms Erdos878.TrackB.norm_sum_reciprocalLogWeight_subinterval_le
#print axioms Erdos878.TrackB.norm_sum_reciprocalLogWeight_quotient_le
#print axioms Erdos878.TrackB.norm_sum_log_mul_reciprocalLogWeight_quotient_le
#print axioms Erdos878.TrackB.typeIOuterBound_nonneg
#print axioms Erdos878.TrackB.sum_typeIInnerBound_le
#print axioms Erdos878.TrackB.weightedArithmeticSum_convolution_band_eq_quotient
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_short_convolution_le
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_typeILog_le
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_typeILambda_le
#print axioms Erdos878.TrackB.vaughanReciprocalLogBound_nonneg
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_vonMangoldt_le_uniform_endpoint
#print axioms Erdos878.TrackB.trackBCutoff_bounds
#print axioms Erdos878.TrackB.trackBCutoff_pos
#print axioms Erdos878.TrackB.trackBScaleCondition_sixteen_le
#print axioms Erdos878.TrackB.trackBCutoff_sq_sq_le
#print axioms Erdos878.TrackB.trackBScaleCondition_sqrt_lower
#print axioms Erdos878.TrackB.eventually_trackBScaleCondition
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_vonMangoldt_le_polylogCutoff
#print axioms Erdos878.TrackB.trackBFrequency_positive_le
#print axioms Erdos878.TrackB.trackBFrequency_sqrt_lower
#print axioms Erdos878.TrackB.trackBFrequencyRoot_upper
#print axioms Erdos878.TrackB.trackBFrequencyRoot_lower
#print axioms Erdos878.TrackB.typeIIUniformError_logSaving_le
#print axioms Erdos878.TrackB.sqrt_typeIIUniformError_logSaving_le
#print axioms Erdos878.TrackB.trackBEndpoint_log_bounds
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_typeII_le_logSaving
#print axioms Erdos878.TrackB.typeIOuterBound_le_polylog
#print axioms Erdos878.TrackB.sqrt_mul_log_pow_le_logSaving
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_typeI_le_logSaving
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_vonMangoldt_le_logSaving
#print axioms Erdos878.TrackB.eventually_vonMangoldt_logSaving
#print axioms Erdos878.TrackB.trackBHarmonicWindow_nonempty
#print axioms Erdos878.TrackB.phaseCharacter_neg_eq_conj
#print axioms Erdos878.TrackB.weightedArithmeticSum_neg_frequency
#print axioms Erdos878.TrackB.norm_weightedArithmeticSum_abs_frequency
#print axioms Erdos878.TrackB.eventually_vonMangoldt_signed_logSaving
#print axioms Erdos878.TrackB.eventually_vonMangoldt_harmonics_logSaving
#print axioms Erdos878.TrackB.inPhaseWindow_iff_fract_mem
#print axioms Erdos878.TrackB.phaseCharacter_fract
#print axioms Erdos878.TrackB.fejerPhaseSum_mul_one_sub
#print axioms Erdos878.TrackB.norm_fejerPhaseSum_le
#print axioms Erdos878.TrackB.finiteFejerKernel_nonneg
#print axioms Erdos878.TrackB.finiteFejerKernel_le_one
#print axioms Erdos878.TrackB.finiteFejerKernel_zero
#print axioms Erdos878.TrackB.norm_fejerPhaseSum_le_of_far
#print axioms Erdos878.TrackB.finiteFejerKernel_le_leakage
#print axioms Erdos878.TrackB.finiteFejerMinorant_le_indicator
#print axioms Erdos878.TrackB.fejer_constant_coefficient_lower
#print axioms Erdos878.TrackB.weightedPhaseSum_shift
#print axioms Erdos878.TrackB.norm_weightedPhaseSum_shift
#print axioms Erdos878.TrackB.fejerPhaseSum_sq_expand
#print axioms Erdos878.TrackB.weighted_fejerPhaseSum_sq_expand
#print axioms Erdos878.TrackB.fejer_pair_frequency
#print axioms Erdos878.TrackB.abs_weighted_finiteFejerKernel_sub_mean_le
#print axioms Erdos878.TrackB.weighted_phaseWindow_mass_lower
#print axioms Erdos878.TrackB.weighted_phaseWindow_mass_lower_half
#print axioms Erdos878.TrackB.weightedPhaseSum_reciprocalLog
#print axioms Erdos878.TrackB.eventually_vonMangoldt_phaseWindow_mass_lower
#print axioms Erdos878.TrackB.trackBFejerOrder_bounds
#print axioms Erdos878.TrackB.trackBFejerOrder_width
#print axioms Erdos878.TrackB.inPhaseWindow_log_squared_iff
#print axioms Erdos878.TrackB.eventually_vonMangoldt_logSquaredWindow_mass_lower
#print axioms Erdos878.TrackB.sum_vonMangoldt_Ioc_eq_psi_sub
#print axioms Erdos878.TrackB.sum_prime_vonMangoldt_Ioc_eq_theta_sub
#print axioms Erdos878.TrackB.sum_vonMangoldt_wide_band_lower
#print axioms Erdos878.TrackB.sum_nonprime_vonMangoldt_wide_upper
#print axioms Erdos878.TrackB.logSquaredGoodSet_sum_split
#print axioms Erdos878.TrackB.logSquaredGoodSet_nonprime_subset
#print axioms Erdos878.TrackB.eventually_goodPrime_vonMangoldt_mass_lower
#print axioms Erdos878.TrackB.goodPrime_vonMangoldt_le_two_log
#print axioms Erdos878.TrackB.eventually_logSquaredGoodPrimes_card_lower
#print axioms Erdos878.TrackB.exists_logSquaredGoodPrime_family_of_card_le
#print axioms Erdos878.TrackB.eventually_exists_logSquaredGoodPrime_family
#print axioms Erdos878.TrackB.phaseExponent_mul_log
#print axioms Erdos878.TrackB.phaseExponent_power_eq_exp
#print axioms Erdos878.TrackB.goodPrime_phaseExponent_power_bounds
#print axioms Erdos878.TrackB.sum_phaseExponent_power_lower
#print axioms Erdos878.TrackB.goodPrime_family_prime
#print axioms Erdos878.TrackB.goodPrime_family_product_le
#print axioms Erdos878.TrackB.phaseExponent_le_log_multipleBelow
#print axioms Erdos878.TrackB.card_mul_exp_le_maxUpTo_f_of_goodPrime_family
#print axioms Erdos878.TrackB.card_mul_exp_le_maxUpTo_f_of_goodPrime_family_of_power_budget
#print axioms Erdos878.TrackB.card_mul_exp_le_maxUpTo_f_of_goodPrime_family_of_additive_budget
#print axioms Erdos878.TrackB.eventually_maxUpTo_ratio_ge_one_sub_of_endpointConditions
#print axioms Erdos878.TrackB.second_question_of_endpointParameters
#print axioms Erdos878.TrackB.tendsto_endpointT
#print axioms Erdos878.TrackB.tendsto_endpointV
#print axioms Erdos878.TrackB.tendsto_endpointV_div_endpointT
#print axioms Erdos878.TrackB.eventually_endpointPrimeReal_ge_endpointT
#print axioms Erdos878.TrackB.tendsto_endpointPrimeReal
#print axioms Erdos878.TrackB.tendsto_endpointPrimeScale
#print axioms Erdos878.TrackB.eventually_endpointPrimeReal_nonneg
#print axioms Erdos878.TrackB.endpointPrimeScale_bounds
#print axioms Erdos878.TrackB.tendsto_endpointLogScale
#print axioms Erdos878.TrackB.tendsto_log_endpointPrimeReal_div_endpointV
#print axioms Erdos878.TrackB.tendsto_endpointLogScale_div_endpointV
#print axioms Erdos878.TrackB.tendsto_endpointBandLog_div_endpointV
#print axioms Erdos878.TrackB.eventually_endpointLogScale_between_half_two
#print axioms Erdos878.TrackB.eventually_endpointT_in_frequencyWindow
#print axioms Erdos878.TrackB.eventually_endpointSelectedCount_le_primeCapacity
#print axioms Erdos878.TrackB.eventually_endpoint_additiveBudget
#print axioms Erdos878.TrackB.tendsto_endpointV_div_endpointBandLog
#print axioms Erdos878.TrackB.tendsto_endpointSelectedCount_normalized
#print axioms Erdos878.TrackB.tendsto_endpointExpShift
#print axioms Erdos878.TrackB.tendsto_endpointNormalizedWeight
#print axioms Erdos878.TrackB.eventually_endpointNormalizedWeight_ge_one_sub
#print axioms Erdos878.TrackB.eventually_endpointConditions_concrete
#print axioms Erdos878.TrackB.second_question_of_concreteEndpoints
#print axioms Erdos878.second_question_iff
#print axioms Erdos878.TrackB.erdos_878_parts_ii_proved

/- Degenerate orders and a nonzero integer translate of the closed boundary. -/
example (u : ℝ) : Erdos878.TrackB.finiteFejerKernel 0 u = 0 := by
  simp [Erdos878.TrackB.finiteFejerKernel]

example (u : ℝ) : Erdos878.TrackB.finiteFejerKernel 1 u = 1 := by
  simp [Erdos878.TrackB.finiteFejerKernel, Erdos878.TrackB.fejerPhaseSum, Erdos878.TrackB.phaseCharacter]

example : Erdos878.TrackB.inPhaseWindow (1/4) (1/8) (9/8) := by
  rw [Erdos878.TrackB.inPhaseWindow_iff_fract_mem _ _ _ (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Int.fract]

example : ¬ Erdos878.TrackB.inPhaseWindow (1/4) (1/8) 0 := by
  rw [Erdos878.TrackB.inPhaseWindow_iff_fract_mem _ _ _ (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/- Concrete C = 16 window, with every nonzero integer Fourier frequency. -/
example : ∀ᶠ P : ℕ in Filter.atTop, ∀ t : ℝ,
    (P : ℝ)/Real.log (P : ℝ)^130 ≤ t → t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
    ∀ k : ℤ, k ≠ 0 → |(k : ℝ)| ≤ Real.log (P : ℝ)^6 →
    ‖Erdos878.TrackB.weightedArithmeticSum (Finset.Ioc P (16*P))
      (Erdos878.TrackB.reciprocalLogWeight ((k : ℝ)*t)) ArithmeticFunction.vonMangoldt‖ ≤
        256000000*P/Real.log (P : ℝ)^25 := by
  filter_upwards [Erdos878.TrackB.eventually_vonMangoldt_harmonics_logSaving 16 (by norm_num)] with P hp
  intro t htlo hthi k hk hkhi
  have ht := hp t htlo hthi k hk hkhi (16*P) (16*P) (by omega) (by norm_num) le_rfl
  norm_num at ht ⊢
  exact ht

/- An empty product band is bounded even without analytic size assumptions. -/
example (a C : ℝ) (U V P X : ℕ) (hC : 0 ≤ C) :
    ‖Erdos878.TrackB.weightedArithmeticSum (Finset.Ioc P P)
      (Erdos878.TrackB.reciprocalLogWeight a) ArithmeticFunction.vonMangoldt‖ ≤
        Erdos878.TrackB.vaughanReciprocalLogBound a C U V P X := by
  simpa [Erdos878.TrackB.weightedArithmeticSum] using
    Erdos878.TrackB.vaughanReciprocalLogBound_nonneg a C U V P X hC

/- Boundary regression: increments exactly one half are admitted, with a
length-independent bound. This also checks that the new hypotheses are inhabited. -/
example (N : ℕ) :
    ‖∑ k ∈ Finset.range (N + 1), Erdos878.TrackB.phaseCharacter ((k : ℝ) / 2)‖ ≤ 2 := by
  have hd (k : ℕ) : ((k + 1 : ℕ) : ℝ) / 2 - (k : ℝ) / 2 = 1 / 2 := by
    push_cast
    ring
  have h := Erdos878.TrackB.norm_sum_phaseCharacter_le_of_monotone_increments
    (fun k => (k : ℝ) / 2) N (1 / 2) (by norm_num)
    (fun k _ => by rw [hd]) (fun k _ => by rw [hd]; norm_num)
    (fun i _ j _ _ => by dsimp only; rw [hd, hd])
  norm_num at h ⊢
  exact h

/- Regression with genuine curvature, for every positive l ≤ 1 and every N,
including the one-sample case N = 0. -/
example (N : ℕ) (l : ℝ) (hl : 0 < l) (hl1 : l ≤ 1) :
    ‖∑ k ∈ Finset.range (N + 1), Erdos878.TrackB.phaseCharacter (l * (k : ℝ) ^ 2 / 2)‖ ≤
      10 * ((N : ℝ) * Real.sqrt l + 1 / Real.sqrt l) := by
  have hf (x : ℝ) : HasDerivAt (fun y : ℝ => l * y ^ 2 / 2) (l * x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul l).div_const 2 using 1 <;>
      first | rfl | (dsimp; ring)
  have hh (x : ℝ) : HasDerivAt (fun y : ℝ => l * y) l x := by
    convert (hasDerivAt_id x).const_mul l using 1 <;>
      first | rfl | ring
  have h := Erdos878.TrackB.second_derivative_test_small
    (fun x => l * x ^ 2 / 2) (fun x => l * x) (fun _ => l) 0 N l 1 hl hl1 (by norm_num)
    (fun x _ => (hf x).continuousAt.continuousWithinAt) (fun x _ => hf x)
    (fun x _ => (hh x).continuousAt.continuousWithinAt) (fun x _ => hh x)
    (fun _ _ => by simp)
  simpa only [zero_add, one_mul] using h
