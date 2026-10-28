module

public import ChenDalang15.PicardMajorant
public import ChenDalang15.SolutionMoments
public import ChenDalang15.HeatCausalKernel

/-!
# Finite stochastic integration domains from the Picard majorant

The input field need not be a solution. Its explicit moment bound gives a
finite integration domain for the next Picard step. The comparison is made
before Tonelli, so measurable sections suffice; joint measurability of the
input is not assumed by this domain estimate.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.Picard

open MeasureTheory Set
open WalshIntegral.Modification
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- A measurable deterministic envelope for the second moments bounds the heat
kernel variance. Only positive-time values of the envelope and field are read. -/
theorem kernelVariance_le_lstConv_of_moment_le {ν : ℝ} (hν : 0 < ν)
    (Φ : ℝ → ℝ → Ω → ℝ) (hΦ : ∀ s y, AEStronglyMeasurable (Φ s y) P)
    {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    (hbound : ∀ s > 0, ∀ y, momentFn P Φ 2 s y ≤ f s y) (t x : ℝ) :
    kernelVariance P (heatCausalKernel ν hν) Φ t x ≤
      lstConv f (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x := by
  rw [kernelVariance_heatCausalKernel hν P Φ hΦ t x]
  have hle : (∫⁻ w, ENNReal.ofReal (HeatCausalKernel.heatK ν t x w.1 w.2 ^ 2) *
      ∫⁻ ω, ENNReal.ofReal (Φ w.1 w.2 ω ^ 2) ∂P
        ∂WalshIntegral.WhiteNoise.timeSpaceVolume) ≤
      ∫⁻ w, ENNReal.ofReal (HeatCausalKernel.heatK ν t x w.1 w.2 ^ 2) * f w.1 w.2
        ∂WalshIntegral.WhiteNoise.timeSpaceVolume := by
    refine lintegral_mono fun w => ?_
    by_cases hs : 0 < w.1 ∧ w.1 < t
    · have hb := hbound w.1 hs.1 w.2
      simp only [momentFn, SolutionMoments.enorm_rpow_two] at hb
      exact mul_le_mul_right hb _
    · simp [HeatCausalKernel.heatK_of_not hs]
  refine hle.trans_eq ?_
  have hm : Measurable (fun w : ℝ × ℝ =>
      ENNReal.ofReal (HeatCausalKernel.heatK ν t x w.1 w.2 ^ 2) * f w.1 w.2) :=
    ((HeatCausalKernel.measurable_heatK_section ν t x).pow_const 2).ennreal_ofReal.mul hf
  rw [WalshIntegral.WhiteNoise.timeSpaceVolume, lintegral_prod _ hm.aemeasurable]
  have hin : ∀ s, (∫⁻ y, ENNReal.ofReal (HeatCausalKernel.heatK ν t x s y ^ 2) * f s y) =
      (Ioo 0 t).indicator (fun s => ∫⁻ y,
        ENNReal.ofReal (G ν (t - s) (x - y) ^ 2) * f s y) s := by
    intro s
    by_cases hs : 0 < s ∧ s < t
    · rw [Set.indicator_of_mem (show s ∈ Ioo 0 t from hs)]
      simp [HeatCausalKernel.heatK, hs]
    · rw [Set.indicator_of_notMem (show s ∉ Ioo 0 t from hs)]
      simp [HeatCausalKernel.heatK_of_not hs]
  simp_rw [hin]
  rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_left.mpr (show Ioo 0 t ⊆ Ioi 0 from fun s hs => hs.1)]
  unfold lstConv
  simp_rw [mul_comm (ENNReal.ofReal _)]

/-- Quadratic growth and the explicit Picard moment majorant bound the next
stochastic integration domain by the finite resolvent contribution. -/
theorem kernelVariance_rho_le_remainder [IsProbabilityMeasure P]
    {ν : ℝ} (hν : 0 < ν) {μ : Measure ℝ} [SFinite μ]
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {Lip V : ℝ}
    (hρ : ∀ z, ρ z ^ 2 ≤ Lip ^ 2 * (V ^ 2 + z ^ 2))
    (v : ℝ → ℝ → Ω → ℝ) (hv : ∀ s y, Measurable (v s y))
    (hb : ∀ s > 0, ∀ y, momentFn P v 2 s y ≤ majorant ν V Lip μ s y)
    (t x : ℝ) :
    kernelVariance P (heatCausalKernel ν hν) (fun s y ω => ρ (v s y ω)) t x ≤
      remainder ν V Lip μ t x := by
  let f := fun s y => ENNReal.ofReal (Lip ^ 2) *
    (ENNReal.ofReal (V ^ 2) + majorant ν V Lip μ s y)
  have hf : Measurable (Function.uncurry f) :=
    measurable_const.mul (measurable_const.add (measurable_majorant hν V Lip μ))
  have hm : ∀ s > 0, ∀ y, momentFn P (fun s y ω => ρ (v s y ω)) 2 s y ≤ f s y := by
    intro s hs y
    exact (SolutionMoments.momentFn_rho_le hρ v s y).trans
      (mul_le_mul_right (add_le_add le_rfl (hb s hs y)) _)
  refine (kernelVariance_le_lstConv_of_moment_le hν _
    (fun s y => (hρm.comp (hv s y)).aestronglyMeasurable) hf hm t x).trans_eq ?_
  rw [← majorant_forward_invariant hν V Lip μ t x]
  unfold lstConv
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro y
  simp only [f, L, ENNReal.ofReal_mul (sq_nonneg Lip)]
  ring

/-- Every next-step heat integral has a genuine finite domain, including zero
Lipschitz/growth coefficient. No solution, output bound or convergence is assumed. -/
theorem kernelVariance_rho_lt_top [IsProbabilityMeasure P]
    {ν : ℝ} (hν : 0 < ν) {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {Lip V : ℝ}
    (hρ : ∀ z, ρ z ^ 2 ≤ Lip ^ 2 * (V ^ 2 + z ^ 2))
    (v : ℝ → ℝ → Ω → ℝ) (hv : ∀ s y, Measurable (v s y))
    (hb : ∀ s > 0, ∀ y, momentFn P v 2 s y ≤ majorant ν V Lip μ s y)
    (t x : ℝ) :
    kernelVariance P (heatCausalKernel ν hν) (fun s y ω => ρ (v s y ω)) t x < ⊤ := by
  by_cases ht : 0 < t
  · exact (kernelVariance_rho_le_remainder hν hρm hρ v hv hb t x).trans_lt
      (remainder_lt_top hT hν V Lip ht x)
  · rw [kernelVariance_heatCausalKernel_of_nonpos hν P _ (not_lt.mp ht)]
    exact bot_lt_top

end ChenDalang15.Picard

end
