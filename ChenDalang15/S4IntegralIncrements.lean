module

public import ChenDalang15.ItoIdentity
public import ChenDalang15.PicardStepConstruction

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace ChenDalang15.S4IntegralIncrements
open MeasureTheory ProbabilityTheory Set Stoch
open scoped ENNReal NNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The actual stochastic integral's output increment is the weighted causal
kernel increment. No continuity or increment identity is assumed. -/
theorem enorm_sub_sq_eq [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {u : ℝ → ℝ → Ω → ℝ}
    {I : ℝ → ℝ → Lp ℝ 2 P} (hI : IsIntegralField J ν ρ u I)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x z : ℝ) :
    ‖I t x - I r z‖ₑ ^ 2 =
      ∫⁻ s in Ioi 0, ∫⁻ y,
        ENNReal.ofReal ((HeatCausalKernel.heatK ν t x s y -
          HeatCausalKernel.heatK ν r z s y) ^ 2) *
          momentFn P (fun s y ω => ρ (u s y ω)) 2 s y := by
  obtain ⟨g, hg, hIg⟩ := hI t ht x
  obtain ⟨k, hk, hIk⟩ := hI r hr z
  have hgc := hg.trans (Picard.kernelField_heat_ae hν (fun s y ω => ρ (u s y ω)) t x).symm
  have hkc := hk.trans (Picard.kernelField_heat_ae hν (fun s y ω => ρ (u s y ω)) r z).symm
  let d : ℝ × ℝ × Ω → ℝ := fun q =>
    (HeatCausalKernel.heatK ν t x q.1 q.2.1 - HeatCausalKernel.heatK ν r z q.1 q.2.1) *
      ρ (u q.1 q.2.1 q.2.2)
  have hd : (fun q => ((g-k : PredL2 F P) : Lp ℝ 2 (spaceTimeSample P)) q) =ᵐ[spaceTimeSample P] d := by
    filter_upwards [Lp.coeFn_sub (g : Lp ℝ 2 (spaceTimeSample P))
      (k : Lp ℝ 2 (spaceTimeSample P)), hgc, hkc] with q hq hgq hkq
    change ((g : Lp ℝ 2 (spaceTimeSample P)) - (k : Lp ℝ 2 (spaceTimeSample P))) q = _
    rw [hq, Pi.sub_apply, hgq, hkq]
    dsimp only [d, WalshIntegral.Modification.kernelField]
    change HeatCausalKernel.heatK ν t x q.1 q.2.1 * ρ (u q.1 q.2.1 q.2.2) -
      HeatCausalKernel.heatK ν r z q.1 q.2.1 * ρ (u q.1 q.2.1 q.2.2) = _
    ring
  rw [hIg, hIk, ← map_sub, ← ItoIdentity.lintegral_enorm_sq,
    lintegral_sq_isWalshIntegral hW.whiteNoise hJ]
  let f : ℝ × ℝ × Ω → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((HeatCausalKernel.heatK ν t x q.1 q.2.1 -
      HeatCausalKernel.heatK ν r z q.1 q.2.1)^2) * ‖ρ (u q.1 q.2.1 q.2.2)‖ₑ^2
  have heq : (fun q => ‖((g-k : PredL2 F P) : Lp ℝ 2 (spaceTimeSample P)) q‖ₑ^2) =ᵐ[spaceTimeSample P] f :=
    hd.mono fun q hq => by
      change ‖((g-k : PredL2 F P) : Lp ℝ 2 (spaceTimeSample P)) q‖ₑ ^ 2 = _
      change ((g-k : PredL2 F P) : Lp ℝ 2 (spaceTimeSample P)) q = d q at hq
      rw [hq]
      exact ItoIdentity.enorm_mul_sq _ _
  have hf : AEMeasurable f (spaceTimeSample P) :=
    ((Lp.aestronglyMeasurable ((g-k : PredL2 F P) : Lp ℝ 2 (spaceTimeSample P))).enorm.pow_const 2).congr heq
  rw [lintegral_congr_ae heq, ItoIdentity.lintegral_spaceTimeSample hf]
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro y
  simp only [f, momentFn, ENNReal.rpow_two]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
/-- Product-measure form for a measurable second-moment weight. The substantive
increment identity above does not require this additional measurability input. -/
theorem enorm_sub_sq_eq_prod [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {u : ℝ → ℝ → Ω → ℝ}
    {I : ℝ → ℝ → Lp ℝ 2 P} (hI : IsIntegralField J ν ρ u I)
    (hw : Measurable (Function.uncurry (momentFn P (fun s y ω => ρ (u s y ω)) 2)))
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x z : ℝ) :
    ‖I t x - I r z‖ₑ ^ 2 =
      ∫⁻ q, ENNReal.ofReal ((HeatCausalKernel.heatK ν t x q.1 q.2 -
        HeatCausalKernel.heatK ν r z q.1 q.2)^2) *
        momentFn P (fun s y ω => ρ (u s y ω)) 2 q.1 q.2 ∂timeSpaceVolume := by
  rw [enorm_sub_sq_eq hW hJ hν hI ht hr x z]
  have hkt : Measurable (fun q : ℝ × ℝ => HeatCausalKernel.heatK ν t x q.1 q.2) :=
    (HeatCausalKernel.measurable_heatK ν).comp
      ((measurable_const : Measurable (fun _ : ℝ × ℝ => (t, x))).prodMk measurable_id)
  have hkr : Measurable (fun q : ℝ × ℝ => HeatCausalKernel.heatK ν r z q.1 q.2) :=
    (HeatCausalKernel.measurable_heatK ν).comp
      ((measurable_const : Measurable (fun _ : ℝ × ℝ => (r, z))).prodMk measurable_id)
  exact (lintegral_prod _ (((hkt.sub hkr).pow_const 2).ennreal_ofReal.mul hw).aemeasurable).symm

end ChenDalang15.S4IntegralIncrements
end
