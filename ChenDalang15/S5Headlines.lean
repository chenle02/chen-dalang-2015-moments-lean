module

public import ChenDalang15.S4SolutionContinuity
public import ChenDalang15.S5GrowthConsequences
public import Mathlib.Analysis.Normed.MulAction

/-!
# Data-only existence, uniqueness and growth-index headlines

These theorem types use only the Mathlib-facing stochastic and growth
constants. Gaussian integrability supplies the internal rough-data and
s-finiteness bridges. Every Lipschitz coefficient supplies its own quadratic
growth bound for existence. Each headline includes a genuine Walsh integral,
full solution existence for every such integral, and the assertion for every
full solution. No solution, moment, convergence or continuity premise is added.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.S5Headlines

open MeasureTheory ProbabilityTheory Set Stoch
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

private theorem quadratic_growth_of_lipschitz {ρ : ℝ → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L ρ) :
    ∀ z : ℝ, ρ z ^ 2 ≤ (2 * ((L : ℝ) + |ρ 0|)) ^ 2 * ((1 : ℝ) ^ 2 + z ^ 2) := by
  intro z
  have hL : 0 ≤ (L : ℝ) := L.coe_nonneg
  have habs : |ρ z| ≤ (L : ℝ) * |z| + |ρ 0| := by
    calc
      |ρ z| = |(ρ z - ρ 0) + ρ 0| := by congr 1; ring
      _ ≤ |ρ z - ρ 0| + |ρ 0| := abs_add_le _ _
      _ ≤ (L : ℝ) * |z| + |ρ 0| := by
        simpa only [sub_zero] using
          add_le_add (SolutionMoments.abs_sub_le_of_lipschitzWith hLip z 0) le_rfl
  have hsum : |ρ z| ≤ ((L : ℝ) + |ρ 0|) * (|z| + 1) := by
    apply habs.trans
    nlinarith [mul_nonneg (abs_nonneg (ρ 0)) (abs_nonneg z)]
  have hsq : ρ z ^ 2 ≤ ((L : ℝ) + |ρ 0|) ^ 2 * (|z| + 1) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (ρ z)) (by positivity)).mpr hsum
    simpa only [sq_abs, mul_pow] using h
  have hz : (|z| + 1) ^ 2 ≤ 2 * (1 + z ^ 2) := by
    nlinarith [sq_nonneg (|z| - 1), sq_abs z]
  have hm := mul_le_mul_of_nonneg_left hz (sq_nonneg ((L : ℝ) + |ρ 0|))
  calc
    ρ z ^ 2 ≤ ((L : ℝ) + |ρ 0|) ^ 2 * (|z| + 1) ^ 2 := hsq
    _ ≤ ((L : ℝ) + |ρ 0|) ^ 2 * (2 * (1 + z ^ 2)) := hm
    _ ≤ (2 * ((L : ℝ) + |ρ 0|)) ^ 2 * ((1 : ℝ) ^ 2 + z ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg ((L : ℝ) + |ρ 0|))
        (show 0 ≤ 1 + z ^ 2 by positivity)]

private theorem exists_solution_of_lipschitz [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ}
    (hμ : ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) μ)
    {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) :
    ∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u := by
  have hT := S1Glue.integrable_exp_neg_sq_iff.mp hμ
  let : IsLocallyFiniteMeasure μ := hT.isLocallyFiniteMeasure
  let : SigmaFinite μ := inferInstance
  obtain ⟨u, _, hu, _⟩ := S4SolutionContinuity.exists_predictable_solution_of_separate_constants
    hW hJ hν hT hLip.continuous.measurable (quadratic_growth_of_lipschitz hLip)
    (SolutionMoments.abs_sub_le_of_lipschitzWith hLip)
  exact ⟨u, hu⟩

/-- Full solution existence and uniqueness under literal Gaussian integrability and a globally Lipschitz coefficient. -/
theorem T2_ExUni_p2_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ}
    (hμ : ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) μ)
    {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        ∀ v : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ v →
          ∀ t : ℝ, 0 < t → ∀ x : ℝ, u t x =ᵐ[P] v t x := by
  have hT := S1Glue.integrable_exp_neg_sq_iff.mp hμ
  let : IsLocallyFiniteMeasure μ := hT.isLocallyFiniteMeasure
  let : SigmaFinite μ := inferInstance
  refine ⟨exists_isWalshIntegral hW.whiteNoise, ?_⟩
  intro J hJ
  refine ⟨exists_solution_of_lipschitz hW hν hμ hLip hJ, ?_⟩
  intro u hu v hv
  exact solution_unique hW hJ hν hT hLip.continuous.measurable
    (SolutionMoments.abs_sub_le_of_lipschitzWith hLip) hu hv

/-- Theorem 2.12(1), zero offset, with full existence and the lower bound for every real p ≥ 2. -/
theorem T2_Growth_one_zero_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ}
    (hμ : ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) μ) (hμ0 : μ ≠ 0)
    {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) {lip : ℝ} (hlip : lip ≠ 0)
    (hρ : ∀ z : ℝ, lip ^ 2 * z ^ 2 ≤ ρ z ^ 2) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        ∀ p : ℝ, 2 ≤ p → ((lip ^ 2 / 2 : ℝ) : EReal) ≤ lowerGrowthIndex (momentFn P u p) := by
  have hT := S1Glue.integrable_exp_neg_sq_iff.mp hμ
  let : IsLocallyFiniteMeasure μ := hT.isLocallyFiniteMeasure
  let : SigmaFinite μ := inferInstance
  refine ⟨exists_isWalshIntegral hW.whiteNoise, ?_⟩
  intro J hJ
  refine ⟨exists_solution_of_lipschitz hW hν hμ hLip hJ, ?_⟩
  intro u hu p hp
  exact S5GrowthConsequences.lowerGrowthIndex_ge_all_p_of_solution
    hW hJ hν hμ0 hT hlip hρ hu hp

/-- Theorem 2.12(1), nonzero offset, with full existence and both indices infinite for every real p ≥ 2; zero initial measure is allowed. -/
theorem T2_Growth_one_top_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ}
    (hμ : ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) μ)
    {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) {lip θ : ℝ} (hlip : lip ≠ 0) (hθ : θ ≠ 0)
    (hρ : ∀ z : ℝ, lip ^ 2 * (θ ^ 2 + z ^ 2) ≤ ρ z ^ 2) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        ∀ p : ℝ, 2 ≤ p →
        lowerGrowthIndex (momentFn P u p) = ⊤ ∧ upperGrowthIndex (momentFn P u p) = ⊤ := by
  have hT := S1Glue.integrable_exp_neg_sq_iff.mp hμ
  let : IsLocallyFiniteMeasure μ := hT.isLocallyFiniteMeasure
  let : SigmaFinite μ := inferInstance
  refine ⟨exists_isWalshIntegral hW.whiteNoise, ?_⟩
  intro J hJ
  refine ⟨exists_solution_of_lipschitz hW hν hμ hLip hJ, ?_⟩
  intro u hu p hp
  exact S5GrowthConsequences.growthIndices_eq_top_all_p_of_solution
    hW hJ hν hT hlip hθ hρ hu hp

/-- Theorem 2.12(2) at p = 2, with full existence and the exact strict-branch upper bound. -/
theorem T2_Growth_two_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) {β Lip : ℝ} (hβ : 0 < β)
    (hI : Integrable (fun y : ℝ => Real.exp (β * |y|)) μ)
    (hLip0 : Lip ≠ 0) (hρ : ∀ z : ℝ, ρ z ^ 2 ≤ Lip ^ 2 * z ^ 2) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        upperGrowthIndex (momentFn P u 2) ≤
          ((if β < Lip ^ 2 / (2 * ν) then β * ν / 2 + Lip ^ 4 / (8 * ν * β)
            else Lip ^ 2 / 2 : ℝ) : EReal) := by
  have hμ := S1Glue.integrable_exp_neg_sq_of_integrable_exp hβ.le hI
  refine ⟨exists_isWalshIntegral hW.whiteNoise, ?_⟩
  intro J hJ
  refine ⟨exists_solution_of_lipschitz hW hν hμ hLip hJ, ?_⟩
  intro u hu
  exact upperGrowthIndex_le_of_solution hW hJ hν hβ hI hLip.continuous.measurable hLip0 hρ hu

/-- Theorem 2.12(3) at p = 2, zero offset, for the general coefficient square identity, with full existence. -/
theorem T2_Growth_three_zero_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) {lam β : ℝ} (hlam : lam ≠ 0) (hμ0 : μ ≠ 0)
    (hβ : lam ^ 2 / (2 * ν) ≤ β)
    (hI : Integrable (fun y : ℝ => Real.exp (β * |y|)) μ)
    (hρ : ∀ z : ℝ, ρ z ^ 2 = lam ^ 2 * z ^ 2) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        lowerGrowthIndex (momentFn P u 2) = ((lam ^ 2 / 2 : ℝ) : EReal) ∧
          upperGrowthIndex (momentFn P u 2) = ((lam ^ 2 / 2 : ℝ) : EReal) := by
  have hβ0 : 0 < β :=
    lt_of_lt_of_le (div_pos (sq_pos_of_ne_zero hlam) (by positivity)) hβ
  have hμ := S1Glue.integrable_exp_neg_sq_of_integrable_exp hβ0.le hI
  refine ⟨exists_isWalshIntegral hW.whiteNoise, ?_⟩
  intro J hJ
  refine ⟨exists_solution_of_lipschitz hW hν hμ hLip hJ, ?_⟩
  intro u hu
  exact S5GrowthConsequences.quasilinear_growthIndices_eq_of_solution
    hW hJ hν hμ0 hlam hβ hI hLip.continuous.measurable hρ hu

/-- Theorem 2.12(3), nonzero offset, with full existence and both indices infinite for every real p ≥ 2. -/
theorem T2_Growth_three_top_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ}
    (hμ : ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) μ)
    {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) {lam θ : ℝ} (hlam : lam ≠ 0) (hθ : θ ≠ 0)
    (hρ : ∀ z : ℝ, ρ z ^ 2 = lam ^ 2 * (θ ^ 2 + z ^ 2)) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        ∀ p : ℝ, 2 ≤ p →
        lowerGrowthIndex (momentFn P u p) = ⊤ ∧ upperGrowthIndex (momentFn P u p) = ⊤ := by
  have hT := S1Glue.integrable_exp_neg_sq_iff.mp hμ
  let : IsLocallyFiniteMeasure μ := hT.isLocallyFiniteMeasure
  let : SigmaFinite μ := inferInstance
  refine ⟨exists_isWalshIntegral hW.whiteNoise, ?_⟩
  intro J hJ
  refine ⟨exists_solution_of_lipschitz hW hν hμ hLip hJ, ?_⟩
  intro u hu p hp
  exact S5GrowthConsequences.quasilinear_growthIndices_eq_top_all_p_of_solution
    hW hJ hν hT hlam hθ hρ hu hp

/-- Proposition 2.14 at p = 2 for the literal exponential initial density, with full existence and the exact non-strict branch. -/
theorem P2_Ex_Exp_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {lam β : ℝ} (hlam : lam ≠ 0) (hβ : 0 < β) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν (fun z : ℝ => lam * z)
          (volume.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (-β * |y|)))) u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν (fun z : ℝ => lam * z)
          (volume.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (-β * |y|)))) u →
        lowerGrowthIndex (momentFn P u 2) =
          ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β)
            else lam ^ 2 / 2 : ℝ) : EReal) ∧
        upperGrowthIndex (momentFn P u 2) =
          ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β)
            else lam ^ 2 / 2 : ℝ) : EReal) := by
  have hμ : ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ => Real.exp (-a * y ^ 2))
      (volume.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (-β * |y|)))) :=
    S1Glue.integrable_exp_neg_sq_iff.mpr (ExExpEnvelope.isGaussianTempered_expMeasure hβ)
  have hLip : LipschitzWith ‖lam‖₊ (fun z : ℝ => lam * z) := by
    simpa only [smul_eq_mul] using (lipschitzWith_smul (β := ℝ) lam)
  refine ⟨exists_isWalshIntegral hW.whiteNoise, ?_⟩
  intro J hJ
  refine ⟨exists_solution_of_lipschitz hW hν hμ hLip hJ, ?_⟩
  intro u hu
  exact P2_Ex_Exp_of_solution hW hJ hν hlam hβ hu

/-- A nonzero Dirac initial measure and identity coefficient instantiate the
headline on an actual augmented white-noise space, with both p=2 indices 1/2. -/
theorem exists_dirac_pam :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (F : Filtration ℝ≥0 m) (W : H →L[ℝ] Lp ℝ 2 P)
      (J : PredL2 F P →L[ℝ] Lp ℝ 2 P) (u : ℝ → ℝ → Ω → ℝ),
      IsAugmentedWhiteNoise P F W ∧ IsWalshIntegral W J ∧
      IsRandomFieldSolution J 1 (fun z : ℝ => z) (Measure.dirac (0 : ℝ)) u ∧
      lowerGrowthIndex (momentFn P u 2) = ((1 / 2 : ℝ) : EReal) ∧
      upperGrowthIndex (momentFn P u 2) = ((1 / 2 : ℝ) : EReal) := by
  obtain ⟨Ω, m, P, hP, F, W, hW⟩ := exists_augmentedWhiteNoise
  let : MeasurableSpace Ω := m
  let : IsProbabilityMeasure P := hP
  have hLip : LipschitzWith (1 : ℝ≥0) (fun z : ℝ => z) := LipschitzWith.id
  have hI : Integrable (fun y : ℝ => Real.exp ((1 : ℝ) * |y|)) (Measure.dirac (0 : ℝ)) :=
    integrable_dirac (by simp)
  have hhead := T2_Growth_three_zero_headline hW (ν := 1) (by norm_num)
    (μ := Measure.dirac (0 : ℝ)) (ρ := fun z : ℝ => z) hLip
    (lam := 1) (β := 1) (by norm_num) (by simp) (by norm_num) hI (fun z => by ring)
  obtain ⟨J, hJ⟩ := hhead.1
  obtain ⟨⟨u, hu⟩, hall⟩ := hhead.2 J hJ
  refine ⟨Ω, m, P, hP, F, W, J, u, hW, hJ, hu, ?_⟩
  simpa only [one_pow] using hall u hu

end ChenDalang15.S5Headlines

end
