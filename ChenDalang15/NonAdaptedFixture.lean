module

public import ChenDalang15.StochBridge

/-!
# Future-noise negative fixture in the paper's augmented setting

The field at time `t` reads the white noise on `(t,t+1] × (0,1]`. At positive
time `1` this variable has variance one and is independent of the past. It
therefore cannot be measurable for the augmented natural filtration at `1`,
and the paper's random-field solution predicate rejects it.

This tests rejection in the actual noise setting. It does not claim that the
field satisfies the other solution clauses (in particular the equation).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.NonAdaptedFixture

open MeasureTheory ProbabilityTheory Set ChenDalang15.Stoch
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Noise from the next unit time interval and a unit spatial interval. -/
def futureNoiseField (W : H →L[ℝ] Lp ℝ 2 P) (t : ℝ) (_x : ℝ) : Ω → ℝ :=
  fun ω => W (WalshIntegral.WhiteNoise.rectangle t.toNNReal (t.toNNReal + 1)
    (Ioc 0 1) measurableSet_Ioc (by simp)) ω

/-- Future noise at time one is not measurable for the past, even in the
paper's completed natural filtration. -/
theorem futureNoiseField_not_measurable [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) (x : ℝ) :
    ¬ Measurable[F 1] (futureNoiseField W 1 x) := by
  intro hm
  let h : WalshIntegral.WhiteNoise.H := WalshIntegral.WhiteNoise.rectangle 1 2
    (Ioc 0 1) measurableSet_Ioc (by simp)
  have hnorm : ‖h‖ = 1 := by
    unfold h WalshIntegral.WhiteNoise.rectangle
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    norm_num [WalshIntegral.WhiteNoise.timeSpaceVolume, Measure.real,
      Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioi]
  have hnoise := (isWhiteNoise_iff F W).1 hW.whiteNoise
  have hm' : Measurable[F 1] (fun ω => W h ω) := by
    unfold futureNoiseField at hm
    have he : (1 : ℝ).toNNReal = 1 := by ext; norm_num [Real.toNNReal]
    rw [he] at hm
    norm_num only [one_add_one_eq_two] at hm
    exact hm
  have hi : IndepFun (fun ω => W h ω) (fun ω => W h ω) P :=
    WalshIntegral.Integral.future_past_indep hnoise 1 hm'
      (WalshIntegral.Integral.future_measurable 1 h
        (WalshIntegral.WhiteNoise.rectangle_supportedAfter _ _ _ _ _))
  have hc := hi.covariance_eq_zero (Lp.memLp (W h)) (Lp.memLp (W h))
  have hc' : inner ℝ h h = 0 := (hnoise.covariance_eq_inner h h).symm.trans hc
  rw [real_inner_self_eq_norm_sq, hnorm] at hc'
  norm_num at hc'

/-- The literal adaptedness clause rejects the future-noise field at `t = 1`.
No choice of data or integral map can make it a random-field solution. -/
theorem futureNoiseField_not_solution [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W)
    (J : PredL2 F P →L[ℝ] Lp ℝ 2 P) (ν : ℝ) (ρ : ℝ → ℝ) (μ : Measure ℝ) :
    ¬ IsRandomFieldSolution J ν ρ μ (futureNoiseField W) := by
  intro hu
  apply futureNoiseField_not_measurable hW 0
  have hm := hu.adapted 1 one_pos 0
  have he : (1 : ℝ).toNNReal = 1 := by ext; norm_num [Real.toNNReal]
  rw [he] at hm
  exact hm

end ChenDalang15.NonAdaptedFixture

end
