module

public import ChenDalang15.PicardStepConstruction
public import ChenDalang15.PicardVariance
public import ChenDalang15.PicardMoments

/-!
# Actual predictable Picard iterates with a uniform second-moment majorant

This constructs the sequence used in Steps 1–2 of the proof of `T2:ExUni`.
It does not assert convergence, the fixed-point equation or L²-continuity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.Picard

open MeasureTheory ProbabilityTheory Set Stoch
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Construct one predictable Picard step and prove its moment bound, deriving
all finite integration domains from Gaussian tempering and the input bound. -/
theorem exists_predictable_step_with_bound [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {Lip V : ℝ}
    (hρ : ∀ z, ρ z ^ 2 ≤ Lip ^ 2 * (V ^ 2 + z ^ 2))
    (v : ℝ → ℝ → Ω → ℝ)
    (hv : Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => v q.1 q.2.1 q.2.2))
    (hb : ∀ t > 0, ∀ x, momentFn P v 2 t x ≤ majorant ν V Lip μ t x) :
    ∃ u : ℝ → ℝ → Ω → ℝ,
      Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => u q.1 q.2.1 q.2.2) ∧
      PicardStep J ν ρ μ v u ∧
      ∀ t > 0, ∀ x, momentFn P u 2 t x ≤ majorant ν V Lip μ t x := by
  have hvm : Measurable (fun q : ℝ × ℝ × Ω => v q.1 q.2.1 q.2.2) :=
    hv.mono (WalshIntegral.Predictable.predictableSigma_le F) le_rfl
  have hvsec (s y : ℝ) : Measurable (v s y) :=
    hvm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  obtain ⟨u, hu, hstep⟩ := exists_predictable_step hW hJ hν μ hρm v hv
    (kernelVariance_rho_lt_top hν hT hρm hρ v hvsec hb)
  exact ⟨u, hu, hstep, fun t ht x => hstep.preserves_majorant hW hJ hν hρ hb ht x⟩

/-- Actual predictable iterates starting at `J₀`, with genuine Picard-step
relations and a proved uniform second-moment bound. Convergence remains open. -/
theorem exists_predictable_iterates [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {Lip V : ℝ}
    (hρ : ∀ z, ρ z ^ 2 ≤ Lip ^ 2 * (V ^ 2 + z ^ 2)) :
    ∃ u : ℕ → ℝ → ℝ → Ω → ℝ,
      u 0 = (fun t x _ => J0 ν μ t x) ∧
      (∀ n, Measurable[predictableSigma F]
        (fun q : ℝ × ℝ × Ω => u n q.1 q.2.1 q.2.2)) ∧
      (∀ n t, 0 < t → ∀ x, momentFn P (u n) 2 t x ≤ majorant ν V Lip μ t x) ∧
      ∀ n, PicardStep J ν ρ μ (u n) (u (n + 1)) := by
  let B := {v : ℝ → ℝ → Ω → ℝ //
    Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => v q.1 q.2.1 q.2.2) ∧
    ∀ t > 0, ∀ x, momentFn P v 2 t x ≤ majorant ν V Lip μ t x}
  have hbase : ∀ t > 0, ∀ x,
      momentFn P (fun t x _ => J0 ν μ t x) 2 t x ≤ majorant ν V Lip μ t x := by
    intro t _ x
    simp only [momentFn, SolutionMoments.enorm_rpow_two, lintegral_const,
      measure_univ, mul_one]
    exact le_add_right (le_refl _)
  let base : B := ⟨fun t x _ => J0 ν μ t x,
    (Stoch.measurable_J0_uncurry ν μ).comp
      (WalshIntegral.Predictable.measurable_coord F), hbase⟩
  have hnext (v : B) : ∃ u : B, PicardStep J ν ρ μ v.val u.val := by
    obtain ⟨u, hu, hs, hb⟩ := exists_predictable_step_with_bound hW hJ hν hT hρm hρ
      v.val v.property.1 v.property.2
    exact ⟨⟨u, hu, hb⟩, hs⟩
  choose next hnext using hnext
  let seq : ℕ → B := Nat.rec base (fun _ v => next v)
  refine ⟨fun n => (seq n).val, rfl, fun n => (seq n).property.1,
    fun n => (seq n).property.2, ?_⟩
  intro n
  exact hnext (seq n)

end ChenDalang15.Picard

end
