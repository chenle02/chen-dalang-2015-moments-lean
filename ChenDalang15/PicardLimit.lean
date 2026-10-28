module

public import WalshIntegral.LpConvergence

public import ChenDalang15.PicardDifferences
public import ChenDalang15.PicardSummability
public import ChenDalang15.PicardIteration
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Predictable limit of the actual Picard iterates

Step 3 of `T2:ExUni` at p = 2: summable successive L² differences give a
full-sequence predictable limit, with pointwise-a.s. and L² convergence and
the uniform moment bound. The limiting equation and continuity are separate.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.Picard

open MeasureTheory ProbabilityTheory Filter Set Stoch
open scoped ENNReal NNReal Topology
open WalshIntegral.Modification

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

private theorem l2_tendsto_of_summable_differences [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 P) (g : Ω → ℝ)
    (_hg : AEStronglyMeasurable g P)
    (hsum : (∑' n, eLpNorm (f (n + 1) - f n) 2 P) ≠ ⊤)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    MemLp g 2 P ∧ Tendsto (fun n => eLpNorm (f n - g) 2 P) atTop (𝓝 0) := by
  exact WalshIntegral.LpConvergence.l2_tendsto_of_summable_differences f hf g _hg hsum hae

/-- The fixed full-sequence limit is predictable and is both the a.s. and L²
limit at each positive-time space point. Its moment bound is proved, not assumed.
No simultaneous exceptional set over all time/space points is asserted. -/
theorem limit_of_iterates [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ρ : ℝ → ℝ} {C V : ℝ}
    (hgrowth : ∀ z, ρ z ^ 2 ≤ C ^ 2 * (V ^ 2 + z ^ 2))
    (hlip : ∀ a b, |ρ a - ρ b| ≤ C * |a - b|)
    (u : ℕ → ℝ → ℝ → Ω → ℝ)
    (hzero : u 0 = (fun t x _ => J0 ν μ t x))
    (hpred : ∀ n, Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => u n q.1 q.2.1 q.2.2))
    (hstep : ∀ n, PicardStep J ν ρ μ (u n) (u (n + 1)))
    (hb : ∀ n t, 0 < t → ∀ x, momentFn P (u n) 2 t x ≤ majorant ν V C μ t x) :
    Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => limitField u q.1 q.2.1 q.2.2) ∧
    ∀ t > 0, ∀ x,
      (∀ᵐ ω ∂P, Tendsto (fun n => u n t x ω) atTop (𝓝 (limitField u t x ω))) ∧
      MemLp (limitField u t x) 2 P ∧
      Tendsto (fun n => eLpNorm (u n t x - limitField u t x) 2 P) atTop (𝓝 0) ∧
      momentFn P (limitField u) 2 t x ≤ majorant ν V C μ t x := by
  classical
  have hpredlim := limitField_measurable u hpred
  refine ⟨hpredlim, ?_⟩
  intro t ht x
  have hsec (n : ℕ) : Measurable (u n t x) :=
    ((hpred n).mono (WalshIntegral.Predictable.predictableSigma_le F) le_rfl).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hseclim : Measurable (limitField u t x) :=
    (hpredlim.mono (WalshIntegral.Predictable.predictableSigma_le F) le_rfl).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hsum : (∑' n, eLpNorm (u (n + 1) t x - u n t x) 2 P) < ⊤ := by
    apply tsum_eLpNorm_two_lt_top_of_BCoeff _
      (fun n => ((hsec (n + 1)).sub (hsec n)).aestronglyMeasurable)
      (bConst_nonneg ν C) ht.le (difference_base_lt_top hT hν V C ht x)
    intro n
    exact iterate_difference_le_BCoeff hW hJ hν hgrowth hlip u hzero hstep n ht x
  have haesum := summable_norm_of_tsum_eLpNorm_ne_top
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hsum.ne
  have hae : ∀ᵐ ω ∂P, Tendsto (fun n => u n t x ω) atTop (𝓝 (limitField u t x ω)) := by
    filter_upwards [haesum] with ω hω
    have hdist : Summable (fun n => dist (u n t x ω) (u (n + 1) t x ω)) := by
      simpa only [Pi.sub_apply, dist_eq_norm, norm_sub_rev] using hω
    have hc : ∃ a : ℝ, Tendsto (fun n => u n t x ω) atTop (𝓝 a) :=
      cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
    simp only [limitField, dite_eq_left hc]
    exact Classical.choose_spec hc
  have hmem (n : ℕ) : MemLp (u n t x) 2 P := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      (hsec n).aestronglyMeasurable).mpr
    simpa only [momentFn, ENNReal.toReal_ofNat] using
      (hb n t ht x).trans_lt (majorant_lt_top hT hν V C ht x)
  obtain ⟨hmlim, hnorm⟩ := l2_tendsto_of_summable_differences
    (fun n => u n t x) hmem (limitField u t x) hseclim.aestronglyMeasurable hsum.ne hae
  refine ⟨hae, hmlim, hnorm, ?_⟩
  have hpow : ∀ᵐ ω ∂P, Tendsto (fun n => ‖u n t x ω‖ₑ ^ (2 : ℝ)) atTop
      (𝓝 (‖limitField u t x ω‖ₑ ^ (2 : ℝ))) := by
    filter_upwards [hae] with ω hω
    exact (ENNReal.continuous_rpow_const.tendsto _).comp (continuous_enorm.tendsto _ |>.comp hω)
  have heq : momentFn P (limitField u) 2 t x =
      ∫⁻ ω, liminf (fun n => ‖u n t x ω‖ₑ ^ (2 : ℝ)) atTop ∂P :=
    lintegral_congr_ae (hpow.mono fun _ h => h.liminf_eq.symm)
  rw [heq]
  refine (lintegral_liminf_le (fun n => (hsec n).enorm.pow_const (2 : ℝ))).trans ?_
  exact liminf_le_of_le (by isBoundedDefault) fun b hbl => by
    obtain ⟨n, hn⟩ := hbl.exists
    exact hn.trans (hb n t ht x)

end ChenDalang15.Picard

end
