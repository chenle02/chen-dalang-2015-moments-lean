module

public import ChenDalang15.PicardLimit
public import ChenDalang15.PicardStepStability
public import ChenDalang15.PicardSolution

/-!
# Picard existence before the continuity step

The actual iterates converge to one predictable field. A genuine Picard step
driven by that field has the same pointwise L² limit, so the field solves the
equation. This proves the S3 checkpoint, not full `D2:Solution` existence.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.Picard

open MeasureTheory ProbabilityTheory Filter Set Stoch
open scoped ENNReal NNReal Topology
open WalshIntegral.Modification

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Data-only existence of a predictable field satisfying every solution clause
except L²-continuity of the integral. Convergence, the moment bound and the
fixed-point equation are all derived from the data hypotheses. -/
theorem exists_predictable_solution₀ [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {C V : ℝ}
    (hgrowth : ∀ z, ρ z ^ 2 ≤ C ^ 2 * (V ^ 2 + z ^ 2))
    (hlip : ∀ a b, |ρ a - ρ b| ≤ C * |a - b|) :
    ∃ u : ℝ → ℝ → Ω → ℝ,
      Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => u q.1 q.2.1 q.2.2) ∧
      IsRandomFieldSolution₀ J ν ρ μ u ∧
      ∀ t > 0, ∀ x, momentFn P u 2 t x ≤ majorant ν V C μ t x := by
  obtain ⟨u, hzero, hpred, hb, hstep⟩ :=
    exists_predictable_iterates hW hJ hν hT hρm hgrowth
  obtain ⟨hpredlim, hlim⟩ :=
    limit_of_iterates hW hJ hν hT hgrowth hlip u hzero hpred hstep hb
  let v := limitField u
  have hbl : ∀ t > 0, ∀ x, momentFn P v 2 t x ≤ majorant ν V C μ t x :=
    fun t ht x => (hlim t ht x).2.2.2
  obtain ⟨w, _, hsw, _⟩ :=
    exists_predictable_step_with_bound hW hJ hν hT hρm hgrowth v hpredlim hbl
  have heq : ∀ t > 0, ∀ x, v t x =ᵐ[P] w t x := by
    intro t ht x
    have hconv := step_tendsto_L2 hW hJ hν hT hlip u
      (fun n => u (n + 1)) v w
      (fun n => (hpred n).mono (WalshIntegral.Predictable.predictableSigma_le F) le_rfl)
      (hpredlim.mono (WalshIntegral.Predictable.predictableSigma_le F) le_rfl)
      hb hbl hstep hsw (fun s hs y => (hlim s hs y).2.2.1) ht x
    have hshift : Tendsto (fun n => eLpNorm (u (n + 1) t x - v t x) 2 P)
        atTop (𝓝 0) :=
      ((hlim t ht x).2.2.1).comp (tendsto_add_atTop_nat 1)
    exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hshift)
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hconv)
  have hfixed : PicardStep J ν ρ μ v v := by
    obtain ⟨I, hI, hweq⟩ := hsw
    exact ⟨I, hI, fun t ht x => (heq t ht x).trans (hweq t ht x)⟩
  exact ⟨v, hpredlim, solution₀_of_predictable_fixed_step hW hJ hν hρm hpredlim hfixed, hbl⟩

/-- Separate growth and Lipschitz constants are dominated by one nonnegative
constant. In particular neither original constant nor the profile is divided
by, so their zero cases are retained. -/
theorem exists_predictable_solution₀_of_separate_constants [IsProbabilityMeasure P]
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
      IsRandomFieldSolution₀ J ν ρ μ u ∧
      ∀ t > 0, ∀ x, momentFn P u 2 t x ≤ majorant ν V (max |A| |B|) μ t x := by
  have hC : 0 ≤ max |A| |B| := (abs_nonneg A).trans (le_max_left _ _)
  have hsq : A ^ 2 ≤ (max |A| |B|) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg A) hC).mpr (le_max_left _ _)
  apply exists_predictable_solution₀ hW hJ hν hT hρm
  · intro z
    exact (hgrowth z).trans (mul_le_mul_of_nonneg_right hsq (by positivity))
  · intro a b
    exact (hlip a b).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self B).trans (le_max_right _ _)) (abs_nonneg _))

end ChenDalang15.Picard

end
