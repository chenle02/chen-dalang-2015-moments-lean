module

public import WalshIntegral
public import ChenDalang15.StochDefs

/-!
# Bridges from the Mathlib-only stochastic layer to `WalshIntegral`

`ChenDalang15.StochDefs` copies the white-noise, filtration and predictable-class definitions of
`WalshIntegral` v0.7.0 and characterizes the Walsh integral abstractly (`IsWalshIntegral`). This
module proves that the copies agree with the originals and that the characterization is
satisfiable and pins down the integral:

* `isWhiteNoise_iff`, `isCompletedNatural_iff`, `predL2_eq` (by `rfl`);
* `walshL2_isWalshIntegral`: `WalshIntegral.Integral.walshL2` satisfies `IsWalshIntegral`;
* `isWalshIntegral_iff`: a map satisfies `IsWalshIntegral` iff it is `walshL2`
  (from `WalshIntegral.Integral.walshL2_unique`);
* `exists_augmentedWhiteNoise`: the paper's setting (complete probability space, white noise,
  augmented natural filtration) exists (from `exists_completed_whiteNoise`);
* `exists_isWalshIntegral`: hence `∃ J, IsWalshIntegral W J` for every white noise;
* `rho_zero_headline`: the headline shape `(∃ J) ∧ ∀ J, (∃ u) ∧ ∀ u, …` holds in the degenerate
  case `ρ = 0`, with second moment `J₀²`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.Stoch

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The Mathlib-only white-noise predicate is `WalshIntegral`'s. -/
theorem isWhiteNoise_iff [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (W : H →L[ℝ] Lp ℝ 2 P) :
    IsWhiteNoise P F W ↔ WalshIntegral.WhiteNoise.IsWhiteNoise P F W :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

/-- The Mathlib-only augmented natural filtration predicate is `WalshIntegral`'s. -/
theorem isCompletedNatural_iff (F : Filtration ℝ≥0 mΩ) (W : H →L[ℝ] Lp ℝ 2 P) :
    IsCompletedNatural P F W ↔ WalshIntegral.WhiteNoise.IsCompletedNatural P F W :=
  Iff.rfl

/-- The paper's setting in terms of `WalshIntegral`. -/
theorem isAugmentedWhiteNoise_iff [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (W : H →L[ℝ] Lp ℝ 2 P) :
    IsAugmentedWhiteNoise P F W ↔ P.IsComplete ∧ WalshIntegral.WhiteNoise.IsWhiteNoise P F W ∧
      WalshIntegral.WhiteNoise.IsCompletedNatural P F W :=
  ⟨fun h => ⟨h.1, (isWhiteNoise_iff F W).1 h.2, h.3⟩,
    fun h => ⟨h.1, (isWhiteNoise_iff F W).2 h.2.1, h.2.2⟩⟩

/-- The Mathlib-only predictable class is `WalshIntegral`'s, definitionally. -/
theorem predL2_eq (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    PredL2 F P = WalshIntegral.Integral.PredL2 F P :=
  rfl

/-- `WalshIntegral`'s choice-defined `walshL2` satisfies the abstract characterization. -/
theorem walshL2_isWalshIntegral [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : WalshIntegral.WhiteNoise.IsWhiteNoise P F W) :
    IsWalshIntegral (F := F) W (WalshIntegral.Integral.walshL2 hW).toContinuousLinearMap := by
  intro s t A c hst hA hAfin hc hcb g r hg hr
  obtain ⟨C, hC⟩ := hcb
  let e : WalshIntegral.Integral.Elementary F :=
    ⟨s, t, hst, A, hA, hAfin, c, hc, ⟨C, fun ω => by simpa [Real.norm_eq_abs] using hC ω⟩⟩
  have hge : g = WalshIntegral.Integral.elementaryClass P e := by
    apply Subtype.ext
    apply Lp.ext
    exact hg.trans (WalshIntegral.Integral.toPredL2_ae (F := F) (P := P) e.field e.inDomain).symm
  have hr' : WalshIntegral.WhiteNoise.rectangle s t A hA hAfin = r := by
    apply Lp.ext
    exact (WalshIntegral.WhiteNoise.rectangle_ae s t A hA hAfin).trans hr.symm
  have h1 := WalshIntegral.Integral.walshL2_elementary hW e
  rw [hge]
  change (fun ω => WalshIntegral.Integral.walshL2 hW
      (WalshIntegral.Integral.elementaryClass P e) ω) =ᵐ[P] _
  rw [h1, ← hr']
  exact WalshIntegral.Integral.elementaryIntegral_ae W e

/-- Every map satisfying the characterization is `walshL2`. -/
theorem isWalshIntegral_eq_walshL2 [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : WalshIntegral.WhiteNoise.IsWhiteNoise P F W)
    (J : PredL2 F P →L[ℝ] Lp ℝ 2 P) (hJ : IsWalshIntegral W J) :
    J = (WalshIntegral.Integral.walshL2 hW).toContinuousLinearMap := by
  refine WalshIntegral.Integral.walshL2_unique hW J (fun e => ?_)
  obtain ⟨C, hC⟩ := e.bounded_coeff
  apply Lp.ext
  have := hJ e.s e.t e.A e.coeff e.s_lt_t e.measurableSet_A e.volume_A_ne_top
    e.measurable_coeff ⟨C, fun ω => by simpa [Real.norm_eq_abs] using hC ω⟩
    (WalshIntegral.Integral.elementaryClass P e)
    (WalshIntegral.WhiteNoise.rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top)
    (WalshIntegral.Integral.toPredL2_ae _ _)
    (WalshIntegral.WhiteNoise.rectangle_ae _ _ _ _ _)
  exact this.trans (WalshIntegral.Integral.elementaryIntegral_ae W e).symm

/-- `IsWalshIntegral W J` holds exactly for `J = walshL2`: the characterization is satisfiable
and determines the integral, so `∀ J` and `∃ J` statements are about the Walsh integral. -/
theorem isWalshIntegral_iff [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W) (J : PredL2 F P →L[ℝ] Lp ℝ 2 P) :
    IsWalshIntegral W J ↔
      J = (WalshIntegral.Integral.walshL2 ((isWhiteNoise_iff F W).1 hW)).toContinuousLinearMap :=
  ⟨isWalshIntegral_eq_walshL2 _ J, fun h => h ▸ walshL2_isWalshIntegral _⟩

/-- The `∃ J` conjunct of the headlines. -/
theorem exists_isWalshIntegral [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W) :
    ∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J :=
  ⟨_, walshL2_isWalshIntegral ((isWhiteNoise_iff F W).1 hW)⟩

/-- Non-vacuity of the paper's setting: a complete probability space carrying a white noise with
its augmented natural filtration exists. -/
theorem exists_augmentedWhiteNoise :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (F : Filtration ℝ≥0 m) (W : H →L[ℝ] Lp ℝ 2 P), IsAugmentedWhiteNoise P F W := by
  obtain ⟨F, W, -, -, hW, hF, -⟩ := WalshIntegral.WhiteNoise.exists_completed_whiteNoise
  have hc : WalshIntegral.WhiteNoise.completedProductGaussian.IsComplete := by
    unfold WalshIntegral.WhiteNoise.completedProductGaussian
    infer_instance
  exact ⟨_, _, _, inferInstance, F, W, ⟨hc, (isWhiteNoise_iff F W).2 hW, hF⟩⟩

/-- The headline shape in the degenerate case `ρ = 0`: the Walsh integral exists, and for every
Walsh integral a random field solution exists and every solution has `E|u(t,x)|² = J₀(t,x)²`. -/
theorem rho_zero_headline [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W) (ν : ℝ) (μ : Measure ℝ)
    [SFinite μ] :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u, IsRandomFieldSolution J ν (fun _ => 0) μ u) ∧
      ∀ u, IsRandomFieldSolution J ν (fun _ => 0) μ u →
        ∀ t > 0, ∀ x, momentFn P u 2 t x = ENNReal.ofReal (J0 ν μ t x ^ 2) :=
  ⟨exists_isWalshIntegral hW.whiteNoise, fun J _ =>
    ⟨⟨_, isRandomFieldSolution_rho_zero J ν μ⟩, fun _ hu _ ht x => momentFn_of_rho_zero hu ht x⟩⟩

end ChenDalang15.Stoch

end

end
