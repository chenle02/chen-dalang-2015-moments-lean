module
public import ChenDalang15.SolutionMoments
public import ChenDalang15.S1Glue
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace ChenDalang15.S5GrowthConsequences
open MeasureTheory ProbabilityTheory Filter Set Stoch
open scoped ENNReal NNReal Topology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

private theorem indices_eq_of_eq_pos {f g : ℝ → ℝ → ℝ≥0∞}
    (h : ∀ t > 0, ∀ x, f t x = g t x) :
    lowerGrowthIndex f = lowerGrowthIndex g ∧ upperGrowthIndex f = upperGrowthIndex g := by
  have hr : tailRate f = tailRate g := by
    funext α
    unfold tailRate
    apply Filter.limsup_congr
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have he : f t = g t := funext (h t ht)
    simp only [tailSup, he]
  exact ⟨by simp only [lowerGrowthIndex, hr], by simp only [upperGrowthIndex, hr]⟩

private def positiveCut (u : ℝ → ℝ → Ω → ℝ) : ℝ → ℝ → Ω → ℝ :=
  fun t x ω => if 0 < t then u t x ω else 0

private theorem positiveCut_measurable [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} {ν : ℝ} {ρ : ℝ → ℝ} {μ : Measure ℝ}
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u) :
    ∀ t x, AEMeasurable (positiveCut u t x) P := by
  intro t x
  by_cases ht : 0 < t
  · have he : positiveCut u t x = u t x := by
      funext ω
      exact ite_eq_left ht
    rw [he]
    exact ((hu.adapted t ht x).mono (F.le _) le_rfl).aemeasurable
  · have he : positiveCut u t x = (fun _ : Ω => (0 : ℝ)) := by
      funext ω
      exact ite_eq_right ht
    rw [he]
    exact aemeasurable_const

/-- Theorem 2.12(1), zero offset, for every full solution and every real p≥2.
The second-moment premise is discharged by the proved solution moment bound. -/
theorem lowerGrowthIndex_ge_all_p_of_solution [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} [SFinite μ] (hμ0 : μ ≠ 0) (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} {lip : ℝ} (hlip : lip ≠ 0) (hρ : ∀ z, lip^2*z^2 ≤ ρ z^2)
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u)
    {p : ℝ} (hp : 2 ≤ p) :
    ((lip^2/2 : ℝ) : EReal) ≤ lowerGrowthIndex (momentFn P u p) := by
  have hlow := secondMoment_lower_of_solution hW hJ hν hT (ϑ := 0)
    (fun z => by simpa using hρ z) hu
  have h := T2_Growth_lower_all_p P (positiveCut u) (positiveCut_measurable hu)
    hμ0 (S1Glue.integrable_exp_neg_sq_iff.2 hT) hν hlip (fun t ht x => ?_) hp
  · have he := indices_eq_of_eq_pos (f := momentFn P (positiveCut u) p) (g := momentFn P u p)
      (fun t ht x => by simp only [momentFn, positiveCut, ite_eq_left ht])
    exact he.1 ▸ h
  · simp only [momentFn, positiveCut, ite_eq_left ht]
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) (hlow t ht x)
    rw [secondMomentExpr]
    nlinarith [sq_nonneg (J0 ν μ t x), MomentBridge.stConv_J0_sq_K_nonneg hν μ lip ht x]

/-- Theorem 2.12(1), nonzero offset: both indices are infinite for every real
p≥2. Zero initial measure is allowed. -/
theorem growthIndices_eq_top_all_p_of_solution [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} {lip ϑ : ℝ} (hlip : lip ≠ 0) (hϑ : ϑ ≠ 0)
    (hρ : ∀ z, lip^2*(ϑ^2+z^2) ≤ ρ z^2)
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u)
    {p : ℝ} (hp : 2 ≤ p) :
    lowerGrowthIndex (momentFn P u p) = ⊤ ∧ upperGrowthIndex (momentFn P u p) = ⊤ := by
  have hlow := secondMoment_lower_of_solution hW hJ hν hT hρ hu
  have h := T2_Growth_lower_top_all_p P (positiveCut u) (positiveCut_measurable hu)
    hν hlip hϑ (fun t ht x => ?_) hp
  · have he := indices_eq_of_eq_pos (f := momentFn P (positiveCut u) p) (g := momentFn P u p)
      (fun t ht x => by simp only [momentFn, positiveCut, ite_eq_left ht])
    exact ⟨he.1 ▸ h.1, he.2 ▸ h.2⟩
  · simp only [momentFn, positiveCut, ite_eq_left ht]
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) (hlow t ht x)
    have hHx : stConv (fun _ _ => (1 : ℝ)) (K ν lip) t x = Hfun ν lip t :=
      (one_conv_K hν ht.le x).trans (one_conv_K hν ht.le 0).symm
    rw [hHx]
    rw [secondMomentExpr]
    nlinarith [sq_nonneg (J0 ν μ t x), MomentBridge.stConv_J0_sq_K_nonneg hν μ lip ht x]

/-- Theorem 2.12(3), quasi-linear nonzero offset, all real p≥2. -/
theorem quasilinear_growthIndices_eq_top_all_p_of_solution [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} {lam ϑ : ℝ} (hlam : lam ≠ 0) (hϑ : ϑ ≠ 0)
    (hρ : ∀ z, ρ z^2 = lam^2*(ϑ^2+z^2))
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u)
    {p : ℝ} (hp : 2 ≤ p) :
    lowerGrowthIndex (momentFn P u p) = ⊤ ∧ upperGrowthIndex (momentFn P u p) = ⊤ :=
  growthIndices_eq_top_all_p_of_solution hW hJ hν hT hlam hϑ (fun z => (hρ z).ge) hu hp
/-- Theorem 2.12(3), zero offset, for general measurable coefficients with
ρ(z)²=λ²z², not restricted to a literal linear coefficient. -/
theorem quasilinear_growthIndices_eq_of_solution [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} (hμ0 : μ ≠ 0) {lam β : ℝ} (hlam : lam ≠ 0)
    (hβ : lam^2/(2*ν) ≤ β) (hI : Integrable (fun y => Real.exp (β*|y|)) μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) (hρ : ∀ z, ρ z^2 = lam^2*z^2)
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u) :
    lowerGrowthIndex (momentFn P u 2) = ((lam^2/2 : ℝ) : EReal) ∧
      upperGrowthIndex (momentFn P u 2) = ((lam^2/2 : ℝ) : EReal) := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have := GrowthUpper.isFiniteMeasure_of_integrable_exp hβ0.le hI
  have hT := RoughHeatKernel.isGaussianTempered_of_isFiniteMeasure μ
  have heq := secondMoment_eq_quasilinear_of_solution hW hJ hν hT hρm (ϑ := 0)
    (fun z => by simpa using hρ z) hu
  refine T2_Growth_three hμ0 hν hlam hβ hI (fun t ht x => ?_) (fun t ht x => ?_)
  · rw [heq t ht x]
    apply ENNReal.ofReal_le_ofReal
    rw [secondMomentExpr]
    nlinarith [sq_nonneg (J0 ν μ t x)]
  · rw [heq t ht x, ← MomentBridge.ofReal_J0_sq_add_stConv hT hν lam ht x, secondMomentExpr]
    simp

end ChenDalang15.S5GrowthConsequences
end
