module

public import ChenDalang15.PicardDefs
public import ChenDalang15.HeatCausalKernel
public import ChenDalang15.StochBridge

/-!
# A genuine predictable Picard step on the finite integration domain

Chen–Dalang (2015), proof of `T2:ExUni`, Steps 1–2: construct the next
iterate from a predictable input whose weighted variance is finite. The
finite-variance premise is an integration-domain obligation, to be supplied
by the deterministic majorant; it is not an assumed solution or output bound.
The constructed output is a predictable modification, with the equation
holding almost surely separately at each positive time-space point.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.Picard

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- On the positive-input-time product measure, the causal heat kernel gives
the literal integrand used in `IsIntegralField`. For `s ≥ t`, `G` is zero. -/
theorem kernelField_heat_ae [IsProbabilityMeasure P] {ν : ℝ} (hν : 0 < ν)
    (Φ : ℝ → ℝ → Ω → ℝ) (t x : ℝ) :
    (fun q : ℝ × ℝ × Ω => WalshIntegral.Modification.kernelField
      (heatCausalKernel ν hν) t x Φ q.1 q.2.1 q.2.2) =ᵐ[Stoch.spaceTimeSample P]
      (fun q => G ν (t - q.1) (x - q.2.1) * Φ q.1 q.2.1 q.2.2) := by
  have hpos : ∀ᵐ q : ℝ × ℝ × Ω ∂Stoch.spaceTimeSample P, 0 < q.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hpos] with q hq
  change HeatCausalKernel.heatK ν t x q.1 q.2.1 * Φ q.1 q.2.1 q.2.2 = _
  by_cases hqt : q.1 < t
  · simp only [HeatCausalKernel.heatK, hq, hqt, and_self, ite_true]
  · rw [HeatCausalKernel.heatK_of_not (by simpa [hq] using hqt),
      LConv.G_of_nonpos hν.le (sub_nonpos.mpr (not_lt.mp hqt))]

/-- Given a predictable input and finite weighted variances, construct a
predictable next iterate and all its actual predictable L² class witnesses. -/
theorem exists_predictable_step [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : Stoch.H →L[ℝ] Lp ℝ 2 P}
    (hW : Stoch.IsAugmentedWhiteNoise P F W)
    {J : Stoch.PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : Stoch.IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) (μ : Measure ℝ) [SFinite μ]
    {ρ : ℝ → ℝ} (hρ : Measurable ρ) (v : ℝ → ℝ → Ω → ℝ)
    (hv : Measurable[Stoch.predictableSigma F]
      (fun q : ℝ × ℝ × Ω => v q.1 q.2.1 q.2.2))
    (hfin : ∀ t x, WalshIntegral.Modification.kernelVariance P (heatCausalKernel ν hν)
      (fun s y ω => ρ (v s y ω)) t x < ⊤) :
    ∃ u : ℝ → ℝ → Ω → ℝ,
      Measurable[Stoch.predictableSigma F]
        (fun q : ℝ × ℝ × Ω => u q.1 q.2.1 q.2.2) ∧
      Stoch.PicardStep J ν ρ μ v u := by
  let Φ := fun s y ω => ρ (v s y ω)
  have hΦ : Measurable[WalshIntegral.Predictable.predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2) := hρ.comp hv
  let hnoise := (Stoch.isWhiteNoise_iff F W).1 hW.whiteNoise
  have hdom (t x : ℝ) : WalshIntegral.Integral.InDomain F P
      (WalshIntegral.Modification.kernelField (heatCausalKernel ν hν) t x Φ) :=
    (WalshIntegral.Modification.kernelField_inDomain_iff
      (heatCausalKernel ν hν) t x Φ hΦ).2 (hfin t x)
  let g (t x : ℝ) : Stoch.PredL2 F P := WalshIntegral.Integral.toPredL2
    (WalshIntegral.Modification.kernelField (heatCausalKernel ν hν) t x Φ) (hdom t x)
  let I (t x : ℝ) : Lp ℝ 2 P := J (g t x)
  obtain ⟨Ψ, hΨ, heqΨ⟩ := exists_predictable_modification_heat hν hnoise Φ hΦ hfin
  refine ⟨fun t x ω => J0 ν μ t x + Ψ t x ω, ?_, I, ?_, ?_⟩
  · exact ((Stoch.measurable_J0_uncurry ν μ).comp
      (WalshIntegral.Predictable.measurable_coord F)).add hΨ
  · intro t ht x
    refine ⟨g t x, ?_, rfl⟩
    exact (WalshIntegral.Integral.toPredL2_ae _ (hdom t x)).trans
      (kernelField_heat_ae hν Φ t x)
  · intro t ht x
    have hJeq := (Stoch.isWalshIntegral_iff hW.whiteNoise J).1 hJ
    have heqI : (fun ω => I t x ω) =ᵐ[P] Ψ t x := by
      change (fun ω => J (g t x) ω) =ᵐ[P] Ψ t x
      rw [hJeq]
      exact (WalshIntegral.Integral.walshT_ae_eq hnoise _ (hdom t x)).symm.trans (heqΨ t x)
    filter_upwards [heqI] with ω hω
    rw [hω]

end ChenDalang15.Picard

end
