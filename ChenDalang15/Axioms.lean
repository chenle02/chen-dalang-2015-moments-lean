module

import ChenDalang15.S5MomentHeadline
import ChenDalang15.Kernel
import ChenDalang15.Resolvent
import ChenDalang15.Summability
import ChenDalang15.ErfSeries
import ChenDalang15.PhiE
import ChenDalang15.KClosed
import ChenDalang15.KConv
import ChenDalang15.H
import ChenDalang15.IntGG
import ChenDalang15.IntBC
import ChenDalang15.IntHG
import ChenDalang15.GrowthDefs
import ChenDalang15.GrowthIndex
import ChenDalang15.GrowthUpper
import ChenDalang15.GrowthLower
import ChenDalang15.GrowthTheorem
import ChenDalang15.TwoPoint
import ChenDalang15.TPLebesgue
import ChenDalang15.TPDelta
import ChenDalang15.Eac
import ChenDalang15.EacProps
import ChenDalang15.ExExpLower
import ChenDalang15.ExExpEnvelope
import ChenDalang15.MomentBridge
import ChenDalang15.S1Glue
import ChenDalang15.LConv
import ChenDalang15.StochDefs
import ChenDalang15.StochBridge
import ChenDalang15.HeatCausalKernel
import ChenDalang15.ItoIdentity
import ChenDalang15.MomentTheorems
import ChenDalang15.SolutionMoments
import ChenDalang15.NonAdaptedFixture
import ChenDalang15.PicardExistence
import ChenDalang15.S4SolutionContinuity
import ChenDalang15.S5GrowthConsequences
import ChenDalang15.S5Headlines

-- The lower-tier receipt reads this output (verify.sh builds this module).
#print axioms ChenDalang15.G_eq_formula
#print axioms ChenDalang15.integral_rpow_mul_sub_rpow
#print axioms ChenDalang15.L_eq
#print axioms ChenDalang15.L_eq_L_zero_mul_BCoeff
#print axioms ChenDalang15.summable_BCoeff_rpow
#print axioms ChenDalang15.Phi_eq_erf
#print axioms ChenDalang15.hasSum_pow_div_Gamma
#print axioms ChenDalang15.integral_exp_mul_Phi
#print axioms ChenDalang15.integral_exp_mul_Phi_false_of_neg
#print axioms ChenDalang15.hasSum_L
#print axioms ChenDalang15.K_eq
#print axioms ChenDalang15.K_conv_L_zero
#print axioms ChenDalang15.one_conv_K
#print axioms ChenDalang15.integral_G_mul_G_time
#print axioms ChenDalang15.integral_G_div_sqrt
#print axioms ChenDalang15.integral_G_div_sqrt_le
#print axioms ChenDalang15.integral_G_time
#print axioms ChenDalang15.integral_integral_G_mul_G
#print axioms ChenDalang15.integral_integral_G_mul_G_diag
#print axioms ChenDalang15.integral_H_add_one_mul_G
#print axioms ChenDalang15.integral_one_conv_K_add_one_mul_G
#print axioms ChenDalang15.L2_IntHG_BC
#print axioms ChenDalang15.L2_IntHG_BC_t_zero_junk
#print axioms ChenDalang15.L2_TP_Delta_BC
#print axioms ChenDalang15.L2_TP_Delta_BC_false_of_eq
#print axioms ChenDalang15.T2_Growth_lower
#print axioms ChenDalang15.T2_Growth_lower_top
#print axioms ChenDalang15.T2_Growth_upper
#print axioms ChenDalang15.L2_Growth
#print axioms ChenDalang15.L2_pLbd
#print axioms ChenDalang15.L2_MaxGGE
#print axioms ChenDalang15.L2_InDt_G_J0
#print axioms ChenDalang15.L2_InDt_G_conv
#print axioms ChenDalang15.upperGrowthIndex_le_piecewise
#print axioms ChenDalang15.exExp_lowerIndex_of_envelope
#print axioms ChenDalang15.exExp_growth_eq
#print axioms ChenDalang15.C2_SecMom_Lebesgue
#print axioms ChenDalang15.C2_TP_Lebesgue_integral
#print axioms ChenDalang15.C2_TP_Lebesgue_diag
#print axioms ChenDalang15.C2_TP_Lebesgue_lt
#print axioms ChenDalang15.C2_TP_Lebesgue_false
#print axioms ChenDalang15.C2_SecMom_Delta
#print axioms ChenDalang15.C2_TP_Delta
#print axioms ChenDalang15.integral_exp_mul_abs_mul_G
#print axioms ChenDalang15.strictConvexOn_Eac
#print axioms ChenDalang15.Eac_le_exp_neg_abs
#print axioms ChenDalang15.Eac_deriv2_zero_neg
#print axioms ChenDalang15.logRel_tendsto
#print axioms ChenDalang15.logRel_sInf
#print axioms ChenDalang15.logRel_inf_claim_false
#print axioms ChenDalang15.logRel_lim_claim_false
#print axioms ChenDalang15.logRel_isGreatest
#print axioms ChenDalang15.J0_exp_measure
#print axioms ChenDalang15.exExp_envelope_of_secondMoment
#print axioms ChenDalang15.P2_Ex_Exp_lower
#print axioms ChenDalang15.P2_Ex_Exp
#print axioms ChenDalang15.L2_MaxGGE_cases
#print axioms ChenDalang15.G_sq
#print axioms ChenDalang15.one_div_le_log_div_div_sub
#print axioms ChenDalang15.logRel_antitoneOn
#print axioms ChenDalang15.Eac_zero_beta
#print axioms ChenDalang15.integrable_exp_mul_abs_mul_G
#print axioms ChenDalang15.Eac_hasDerivAt
#print axioms ChenDalang15.Eac_hasDerivAt_deriv
#print axioms ChenDalang15.exp_mul_abs_le_Eac
#print axioms ChenDalang15.Eac_lt_exp_add_exp
#print axioms ChenDalang15.Phi_mul_sqrt_Eac_two_mul_le_Eac
#print axioms ChenDalang15.Eac_zero
#print axioms ChenDalang15.Eac_zero_le
#print axioms ChenDalang15.isLeast_Eac_zero
#print axioms ChenDalang15.one_lt_Eac_zero
#print axioms ChenDalang15.antitoneOn_Eac_Ici
#print axioms ChenDalang15.monotoneOn_Eac_Iic
#print axioms ChenDalang15.Eac_le_Eac_zero
#print axioms ChenDalang15.isGreatest_Eac_zero
#print axioms ChenDalang15.Eac_zero_lt_one
#print axioms ChenDalang15.Eac_hasDerivAt_deriv_zero
#print axioms ChenDalang15.Eac_deriv2_zero_pos
#print axioms ChenDalang15.Eac_hasDerivAt_a
#print axioms ChenDalang15.monotoneOn_Eac_a
#print axioms ChenDalang15.antitoneOn_Eac_a
#print axioms ChenDalang15.MomentBridge.stConv_J0_sq_K_eq_lintegral
#print axioms ChenDalang15.MomentBridge.lintegral_J0_sq_K_lt_top
#print axioms ChenDalang15.MomentBridge.integrable_J0_sq_K
#print axioms ChenDalang15.T2_Growth_upper_lintegral
#print axioms ChenDalang15.P2_Ex_Exp_lintegral
#print axioms ChenDalang15.L2_InDt_A
#print axioms ChenDalang15.L2_InDt_L0
#print axioms ChenDalang15.L2_InDt
#print axioms ChenDalang15.L2_InDt_lt_top
#print axioms ChenDalang15.L2_InDt_L0_lt_top
#print axioms ChenDalang15.L2_InDt_tempered
#print axioms ChenDalang15.L2_InDt_stConv
#print axioms ChenDalang15.S1Glue.integrable_exp_neg_sq_iff
#print axioms ChenDalang15.S1Glue.isGaussianTempered_of_integrable_exp
#print axioms ChenDalang15.T2_Growth_lower_all_p
#print axioms ChenDalang15.T2_Growth_lower_top_all_p
#print axioms ChenDalang15.T2_Growth_three
#print axioms ChenDalang15.T2_Growth_three_top
#print axioms ChenDalang15.lstConv_assoc
#print axioms ChenDalang15.ofReal_stConv_le_lstConv
#print axioms ChenDalang15.ofReal_stConv_eq_lstConv_of_integrable
#print axioms ChenDalang15.lstConv_ofReal_K_L_zero_add
#print axioms ChenDalang15.lstConv_ofReal_L_le_BCoeff_mul
#print axioms ChenDalang15.Stoch.walshL2_isWalshIntegral
#print axioms ChenDalang15.Stoch.isWalshIntegral_eq_walshL2
#print axioms ChenDalang15.Stoch.exists_isWalshIntegral
#print axioms ChenDalang15.Stoch.exists_augmentedWhiteNoise
#print axioms ChenDalang15.Stoch.rho_zero_headline
#print axioms ChenDalang15.Stoch.isRandomFieldSolution_rho_zero
#print axioms ChenDalang15.Stoch.not_isRandomFieldSolution_notAdapted
#print axioms ChenDalang15.Stoch.not_isRandomFieldSolution_J0_add_one
#print axioms ChenDalang15.heatCausalKernel_K
#print axioms ChenDalang15.kernelVariance_heatCausalKernel
#print axioms ChenDalang15.kernelVariance_heatCausalKernel_det_iter
#print axioms ChenDalang15.exists_predictable_modification_heat
#print axioms ChenDalang15.Stoch.lintegral_sq_isWalshIntegral
#print axioms ChenDalang15.Stoch.lintegral_sq_integralField
#print axioms ChenDalang15.Stoch.integral_mul_integralField
#print axioms ChenDalang15.Stoch.walshMeanZero_of_isWalshIntegral
#print axioms ChenDalang15.Stoch.momentFn_two_eq_renewal
#print axioms ChenDalang15.MomentTheorems.renewal_lower
#print axioms ChenDalang15.MomentTheorems.renewal_upper
#print axioms ChenDalang15.MomentTheorems.secondMoment_eq
#print axioms ChenDalang15.MomentTheorems.eq_zero_of_le_lstConv_L_zero
#print axioms ChenDalang15.Stoch.secondMoment_upper_of_solution
#print axioms ChenDalang15.Stoch.secondMoment_lower_of_solution
#print axioms ChenDalang15.Stoch.secondMoment_eq_of_solution
#print axioms ChenDalang15.Stoch.solution_unique
#print axioms ChenDalang15.Stoch.upperGrowthIndex_le_of_solution
#print axioms ChenDalang15.Stoch.lowerGrowthIndex_ge_of_solution
#print axioms ChenDalang15.Stoch.P2_Ex_Exp_of_solution
#print axioms ChenDalang15.Stoch.T2_Growth_three_of_solution

#print axioms ChenDalang15.Stoch.secondMoment_eq_quasilinear_of_solution

#print axioms ChenDalang15.NonAdaptedFixture.futureNoiseField_not_measurable
#print axioms ChenDalang15.NonAdaptedFixture.futureNoiseField_not_solution

-- S3 checkpoint: existence without integral-field L²-continuity.
#print axioms ChenDalang15.Stoch.PicardStep.momentFn_sub_eq
#print axioms ChenDalang15.Stoch.PicardStep.momentFn_sub_le
#print axioms ChenDalang15.Stoch.PicardStep.momentFn_sub_J0_eq
#print axioms ChenDalang15.Stoch.PicardStep.first_difference_le
#print axioms ChenDalang15.Picard.iterate_difference_le
#print axioms ChenDalang15.Picard.iterate_difference_le_BCoeff
#print axioms ChenDalang15.Picard.difference_base_lt_top
#print axioms ChenDalang15.Picard.exists_predictable_solution₀
#print axioms ChenDalang15.Picard.exists_predictable_solution₀_of_separate_constants
#print axioms ChenDalang15.Picard.exists_predictable_step_with_bound
#print axioms ChenDalang15.Picard.exists_predictable_iterates
#print axioms ChenDalang15.Picard.limit_of_iterates
#print axioms ChenDalang15.Picard.measurable_source
#print axioms ChenDalang15.Picard.measurable_remainder
#print axioms ChenDalang15.Picard.measurable_majorant
#print axioms ChenDalang15.Picard.source_lt_top
#print axioms ChenDalang15.Picard.majorant_eq_secondMomentExpr
#print axioms ChenDalang15.Picard.majorant_lt_top
#print axioms ChenDalang15.Picard.remainder_lt_top
#print axioms ChenDalang15.Picard.majorant_forward_invariant
#print axioms ChenDalang15.Stoch.PicardStep.momentFn_two_eq
#print axioms ChenDalang15.Stoch.PicardStep.momentFn_two_le
#print axioms ChenDalang15.Stoch.PicardStep.preserves_majorant
#print axioms ChenDalang15.Picard.solution₀_of_predictable_fixed_step
#print axioms ChenDalang15.Picard.kernelField_heat_ae
#print axioms ChenDalang15.Picard.exists_predictable_step
#print axioms ChenDalang15.Picard.measurable_momentFn_two
#print axioms ChenDalang15.Picard.lstConv_tendsto_zero_of_majorant
#print axioms ChenDalang15.Picard.step_tendsto_L2
#print axioms ChenDalang15.Picard.eLpNorm_two_le_of_moment_bound
#print axioms ChenDalang15.Picard.tsum_eLpNorm_two_lt_top_of_moment_bound
#print axioms ChenDalang15.Picard.tsum_eLpNorm_two_lt_top_of_BCoeff
#print axioms ChenDalang15.Picard.memLp_two_of_BCoeff
#print axioms ChenDalang15.Picard.kernelVariance_le_lstConv_of_moment_le
#print axioms ChenDalang15.Picard.kernelVariance_rho_le_remainder
#print axioms ChenDalang15.Picard.kernelVariance_rho_lt_top

-- S4 full existence and S5 actual-solution growth consequences.
#print axioms ChenDalang15.S4CompactMajorant.majorant_le_envelope
#print axioms ChenDalang15.S4CompactMajorant.continuousAt_J0
#print axioms ChenDalang15.S4CompactMajorant.continuousAt_envelope
#print axioms ChenDalang15.S4CompactMajorant.exists_bound_rect
#print axioms ChenDalang15.S4GaussianMargin.G_sq_le_future_of_far
#print axioms ChenDalang15.S4IntegralIncrements.enorm_sub_sq_eq
#print axioms ChenDalang15.S4IntegralIncrements.enorm_sub_sq_eq_prod
#print axioms ChenDalang15.S4SolutionContinuity.measurable_coefficient_moment
#print axioms ChenDalang15.S4SolutionContinuity.exists_coefficient_bound_rect
#print axioms ChenDalang15.S4SolutionContinuity.coefficient_weighted_variance_lt_top
#print axioms ChenDalang15.S4SolutionContinuity.continuousOn_integralField
#print axioms ChenDalang15.S4SolutionContinuity.solution_of_solution₀
#print axioms ChenDalang15.S4SolutionContinuity.exists_predictable_solution
#print axioms ChenDalang15.S4SolutionContinuity.exists_predictable_solution_of_separate_constants
#print axioms ChenDalang15.S4WeightedKernel.tendsto_weighted_sq_difference
#print axioms ChenDalang15.S5GrowthConsequences.lowerGrowthIndex_ge_all_p_of_solution
#print axioms ChenDalang15.S5GrowthConsequences.growthIndices_eq_top_all_p_of_solution
#print axioms ChenDalang15.S5GrowthConsequences.quasilinear_growthIndices_eq_top_all_p_of_solution
#print axioms ChenDalang15.S5GrowthConsequences.quasilinear_growthIndices_eq_of_solution

-- Data-only headlines and actual nontrivial noise/solution witness.
#print axioms ChenDalang15.S5Headlines.T2_ExUni_p2_headline
#print axioms ChenDalang15.S5Headlines.T2_Growth_one_zero_headline
#print axioms ChenDalang15.S5Headlines.T2_Growth_one_top_headline
#print axioms ChenDalang15.S5Headlines.T2_Growth_two_headline
#print axioms ChenDalang15.S5Headlines.T2_Growth_three_zero_headline
#print axioms ChenDalang15.S5Headlines.T2_Growth_three_top_headline
#print axioms ChenDalang15.S5Headlines.P2_Ex_Exp_headline
#print axioms ChenDalang15.S5Headlines.exists_dirac_pam
#print axioms ChenDalang15.HeatCausalKernel.heatK_eq_upstream
#print axioms ChenDalang15.HeatCausalKernel.timeSpaceVolume_eq_upstream

#print axioms ChenDalang15.S5MomentHeadline.T2_ExUni_secondMoment_headline
