module

public import ChenDalang15.PicardExistence
public import ChenDalang15.S4CompactMajorant
public import ChenDalang15.S4WeightedKernel
public import ChenDalang15.S4IntegralIncrements

/-!
# Full random-field solution existence, including integral-field L² continuity

The coefficient moment weight inherits measurability, compact bounds and
finite future variances from the actual Picard majorant. Weighted causal
kernel continuity and the actual Walsh increment identity then give
continuity of the existing integral field in L². The S3 construction supplies
the remaining solution clauses without assuming continuity or convergence.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.S4SolutionContinuity

open MeasureTheory ProbabilityTheory Filter Set Stoch
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Predictability supplies joint measurability of the actual coefficient's
second-moment weight. No integrability or continuity is assumed here. -/
theorem measurable_coefficient_moment [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {ρ : ℝ → ℝ} (hρm : Measurable ρ)
    {u : ℝ → ℝ → Ω → ℝ}
    (hu : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => u q.1 q.2.1 q.2.2)) :
    Measurable (Function.uncurry (momentFn P (fun s y ω => ρ (u s y ω)) 2)) :=
  Picard.measurable_momentFn_two _
    (hρm.comp (hu.mono (WalshIntegral.Predictable.predictableSigma_le F) le_rfl))

/-- The actual field's majorant gives a finite compact bound for the coefficient
moment. Zero growth coefficient, offset and initial profile are retained. -/
theorem exists_coefficient_bound_rect [IsProbabilityMeasure P]
    {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {V C : ℝ}
    (hgrowth : ∀ z, ρ z ^ 2 ≤ C ^ 2 * (V ^ 2 + z ^ 2))
    (u : ℝ → ℝ → Ω → ℝ)
    (hb : ∀ t > 0, ∀ x, momentFn P u 2 t x ≤ Picard.majorant ν V C μ t x)
    {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hR : 0 ≤ R) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ s ∈ Icc a b, ∀ y ∈ Icc (-R) R,
        momentFn P (fun r z ω => ρ (u r z ω)) 2 s y ≤ B := by
  obtain ⟨B, hB, hbound⟩ := S4CompactMajorant.exists_bound_rect hT hν V C ha hab hR
  refine ⟨ENNReal.ofReal (C ^ 2) * B, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB, ?_⟩
  intro s hs y hy
  calc
    _ ≤ ENNReal.ofReal (C ^ 2) * (ENNReal.ofReal (V ^ 2) + momentFn P u 2 s y) :=
      SolutionMoments.momentFn_rho_le hgrowth u s y
    _ ≤ ENNReal.ofReal (C ^ 2) *
        (ENNReal.ofReal (V ^ 2) + Picard.majorant ν V C μ s y) := by
      gcongr
      exact hb s (ha.trans_le hs.1) y
    _ ≤ ENNReal.ofReal (C ^ 2) * B := by
      gcongr
      exact hbound s hs y hy

/-- Every output variance of the coefficient weight is finite by the actual
majorant estimate. In particular this supplies the later-output DCT envelope. -/
theorem coefficient_weighted_variance_lt_top [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {V C : ℝ}
    (hgrowth : ∀ z, ρ z ^ 2 ≤ C ^ 2 * (V ^ 2 + z ^ 2))
    (u : ℝ → ℝ → Ω → ℝ)
    (hu : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => u q.1 q.2.1 q.2.2))
    (hb : ∀ t > 0, ∀ x, momentFn P u 2 t x ≤ Picard.majorant ν V C μ t x)
    (t x : ℝ) :
    (∫⁻ q, ENNReal.ofReal (HeatCausalKernel.heatK ν t x q.1 q.2 ^ 2) *
      momentFn P (fun s y ω => ρ (u s y ω)) 2 q.1 q.2 ∂timeSpaceVolume) < ⊤ := by
  have hum := hu.mono (WalshIntegral.Predictable.predictableSigma_le F) le_rfl
  have hsec (s y : ℝ) : Measurable (u s y) :=
    hum.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hfin := Picard.kernelVariance_rho_lt_top hν hT hρm hgrowth u hsec hb t x
  have hvar := kernelVariance_heatCausalKernel hν P (fun s y ω => ρ (u s y ω))
    (fun s y => (hρm.comp (hsec s y)).aestronglyMeasurable) t x
  simpa only [momentFn, SolutionMoments.enorm_rpow_two, Stoch.timeSpaceVolume,
    WalshIntegral.WhiteNoise.timeSpaceVolume] using
    (lt_of_eq_of_lt hvar.symm hfin)

/-- The existing Walsh integral field is L²-continuous at positive times.
The measurable coefficient weight, compact bound, future envelope and actual
increment identity are derived; no weighted convergence is a hypothesis. -/
theorem continuousOn_integralField [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {V C : ℝ}
    (hgrowth : ∀ z, ρ z ^ 2 ≤ C ^ 2 * (V ^ 2 + z ^ 2))
    {u : ℝ → ℝ → Ω → ℝ}
    (hu : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => u q.1 q.2.1 q.2.2))
    (hb : ∀ t > 0, ∀ x, momentFn P u 2 t x ≤ Picard.majorant ν V C μ t x)
    {I : ℝ → ℝ → Lp ℝ 2 P} (hI : IsIntegralField J ν ρ u I) :
    ContinuousOn (fun z : ℝ × ℝ => I z.1 z.2) (Ioi 0 ×ˢ univ) := by
  rintro ⟨t, x⟩ hz
  have ht : 0 < t := hz.1
  apply ContinuousAt.continuousWithinAt
  have hw := measurable_coefficient_moment (P := P) (F := F) (u := u) hρm hu
  have hR : 0 ≤ |x| + 8 * (1 + ν * t) := by positivity
  obtain ⟨B, hB, hbound⟩ := exists_coefficient_bound_rect hT hν hgrowth u hb
    (a := t / 4) (b := 5 * t / 4) (R := |x| + 8 * (1 + ν * t))
    (by positivity) (by linarith) hR
  have hconv := S4WeightedKernel.tendsto_weighted_sq_difference hν ht
    (Function.uncurry (momentFn P (fun s y ω => ρ (u s y ω)) 2)) hw
    (coefficient_weighted_variance_lt_top hT hν hρm hgrowth u hu hb (2 * t) x)
    ⟨B, hB, fun q hq => hbound q.1 hq.1 q.2 hq.2⟩
  have hpos : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x), 0 < z.1 :=
    (continuous_fst.tendsto (t, x)).eventually (Ioi_mem_nhds ht)
  have hsq : Tendsto (fun z : ℝ × ℝ => ‖I z.1 z.2 - I t x‖ₑ ^ (2 : ℕ))
      (𝓝 (t, x)) (𝓝 0) := by
    apply Tendsto.congr' ?_ hconv
    filter_upwards [hpos] with z hz
    exact (S4IntegralIncrements.enorm_sub_sq_eq_prod hW hJ hν hI hw hz ht z.2 x).symm
  have hroot := (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).tendsto 0 |>.comp hsq
  have hroot_eq (a : ℝ≥0∞) : (a ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = a := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hnorm : Tendsto (fun z : ℝ × ℝ => ‖I z.1 z.2 - I t x‖ₑ)
      (𝓝 (t, x)) (𝓝 0) := by
    simpa only [Function.comp_def,
      hroot_eq,
      ENNReal.zero_rpow_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹)] using hroot
  exact tendsto_iff_enorm_sub_tendsto_zero.mpr hnorm

/-- The S3 field becomes a full `D2:Solution` using its proved moment majorant
to establish continuity of its actual integral witness. -/
theorem solution_of_solution₀ [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {V C : ℝ}
    (hgrowth : ∀ z, ρ z ^ 2 ≤ C ^ 2 * (V ^ 2 + z ^ 2))
    {u : ℝ → ℝ → Ω → ℝ}
    (hu : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => u q.1 q.2.1 q.2.2))
    (hb : ∀ t > 0, ∀ x, momentFn P u 2 t x ≤ Picard.majorant ν V C μ t x)
    (hs : IsRandomFieldSolution₀ J ν ρ μ u) : IsRandomFieldSolution J ν ρ μ u := by
  obtain ⟨I, hI, heq⟩ := hs.integral
  exact ⟨hs.adapted, hs.jointlyMeasurable, hs.finite, I, hI,
    continuousOn_integralField hW hJ hν hT hρm hgrowth hu hb hI, heq⟩

/-- Full predictable random-field solution existence from the data only,
including L²-continuity of the integral and the proved moment majorant. -/
theorem exists_predictable_solution [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {V C : ℝ}
    (hgrowth : ∀ z, ρ z ^ 2 ≤ C ^ 2 * (V ^ 2 + z ^ 2))
    (hlip : ∀ a b, |ρ a - ρ b| ≤ C * |a - b|) :
    ∃ u : ℝ → ℝ → Ω → ℝ,
      Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => u q.1 q.2.1 q.2.2) ∧
      IsRandomFieldSolution J ν ρ μ u ∧
      ∀ t > 0, ∀ x, momentFn P u 2 t x ≤ Picard.majorant ν V C μ t x := by
  obtain ⟨u, hu, hs, hb⟩ := Picard.exists_predictable_solution₀ hW hJ hν hT hρm hgrowth hlip
  exact ⟨u, hu, solution_of_solution₀ hW hJ hν hT hρm hgrowth hu hb hs, hb⟩

/-- Full solution existence also accepts separate coefficient growth and
Lipschitz constants, using their absolute-value maximum only in the majorant. -/
theorem exists_predictable_solution_of_separate_constants [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {A B V : ℝ}
    (hgrowth : ∀ z, ρ z ^ 2 ≤ A ^ 2 * (V ^ 2 + z ^ 2))
    (hlip : ∀ a b, |ρ a - ρ b| ≤ B * |a - b|) :
    ∃ u : ℝ → ℝ → Ω → ℝ,
      Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => u q.1 q.2.1 q.2.2) ∧
      IsRandomFieldSolution J ν ρ μ u ∧
      ∀ t > 0, ∀ x, momentFn P u 2 t x ≤ Picard.majorant ν V (max |A| |B|) μ t x := by
  have hC : 0 ≤ max |A| |B| := (abs_nonneg A).trans (le_max_left _ _)
  have hsq : A ^ 2 ≤ (max |A| |B|) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg A) hC).mpr (le_max_left _ _)
  apply exists_predictable_solution hW hJ hν hT hρm
  · intro z
    exact (hgrowth z).trans (mul_le_mul_of_nonneg_right hsq (by positivity))
  · intro a b
    exact (hlip a b).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self B).trans (le_max_right _ _)) (abs_nonneg _))

end ChenDalang15.S4SolutionContinuity

end
