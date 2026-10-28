module

public import ChenDalang15.GrowthTheorem
public import ChenDalang15.ExExpEnvelope

/-!
# The Bochner convolution `J₀² ⋆ 𝓚` is the genuine Lebesgue integral

`stConv f g t x = ∫ s in 0..t, ∫ y, f s y * g (t-s) (x-y)` is a Bochner integral, which Lean
sets to `0` when the integrand is not integrable. The moment hypotheses of `T2_Growth_upper`
(`E2:SecMom-Up`) and `P2_Ex_Exp` (`E2:SecMom`, `ϑ = 0`) are stated with
`stConv (fun s y => J₀(s,y)²) 𝓚`, so they say what the paper says only once that integrand is
known to be integrable. This file proves it, for every nonnegative Gaussian-tempered measure `μ`
(in particular every finite one), `ν > 0`, any `λ`, `t > 0` and `x`:

* `stConv_J0_sq_K_eq_lintegral`:
  `ofReal ((J₀² ⋆ 𝓚_λ)(t,x)) = ∫⁻_{(0,t]} ∫⁻_ℝ ofReal (J₀(s,y)² 𝓚_λ(t−s,x−y)) dy ds`;
* `lintegral_J0_sq_K_lt_top`: the right side is finite;
* `integrable_J0_sq_K`: the space-time integrand is integrable on `(0,t] × ℝ`;
* `stConv_J0_sq_K_nonneg`: `(J₀² ⋆ 𝓚_λ)(t,x) ≥ 0`.

The value of `𝓚_λ(0,·)` (at `s = t`) does not matter: `{s = t}` is Lebesgue-null.

As a consequence, the two headlines have discharge-ready variants whose moment hypotheses use
only the lower Lebesgue integral (no Bochner integral, hence no junk value):

* `T2_Growth_upper_lintegral` (from `T2_Growth_upper`);
* `P2_Ex_Exp_lintegral` (from `P2_Ex_Exp`).

Their conclusions are those of the original theorems.
-/

set_option autoImplicit false

public section

open scoped ENNReal
open Real MeasureTheory Set Filter

namespace ChenDalang15

namespace MomentBridge

open GrowthLower (integrand phiC integrand_nonneg integrable_integrand integrableOn_phiC
  stronglyMeasurable_integrand K_eq_kC)

theorem phiC_nonneg {ν : ℝ} (hν : 0 < ν) (μ : Measure ℝ) (l t x s : ℝ) :
    0 ≤ phiC ν μ l t x s :=
  integral_nonneg fun y => integrand_nonneg hν μ l t x s y

/-- For `0 < s < t`, the inner (space) Bochner integral is the genuine Lebesgue integral. -/
theorem ofReal_phiC_eq_lintegral {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (l : ℝ) {t s : ℝ}
    (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ENNReal.ofReal (phiC ν μ l t x s) =
      ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * K ν l (t - s) (x - y)) := by
  rw [phiC, ofReal_integral_eq_lintegral_ofReal (integrable_integrand hT hν hs hst)
    (Eventually.of_forall (integrand_nonneg hν μ l t x s))]
  refine lintegral_congr fun y => ?_
  rw [integrand, K_eq_kC hν (sub_pos.mpr hst)]

/-- `(J₀² ⋆ 𝓚_λ)(t,x) ≥ 0` for `t > 0`. -/
theorem stConv_J0_sq_K_nonneg {ν : ℝ} (hν : 0 < ν) (μ : Measure ℝ) (l : ℝ) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    0 ≤ stConv (fun s y => J0 ν μ s y ^ 2) (K ν l) t x := by
  rw [ExExpEnvelope.stConv_eq_integral_phiC hν μ l ht x]
  exact setIntegral_nonneg measurableSet_Ioc fun s _ => phiC_nonneg hν μ l t x s

/-- **The Bochner convolution is the Lebesgue convolution.** For a Gaussian-tempered `μ`,
`ν > 0` and `t > 0`, `(J₀² ⋆ 𝓚_λ)(t,x)` (Lean's `stConv`) equals the lower Lebesgue integral
`∫⁻_{(0,t]} ∫⁻_ℝ J₀(s,y)² 𝓚_λ(t−s,x−y) dy ds`. -/
theorem stConv_J0_sq_K_eq_lintegral {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (l : ℝ) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    ENNReal.ofReal (stConv (fun s y => J0 ν μ s y ^ 2) (K ν l) t x) =
      ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * K ν l (t - s) (x - y)) := by
  rw [ExExpEnvelope.stConv_eq_integral_phiC hν μ l ht x,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_phiC hT hν ht x)
      (Eventually.of_forall fun s => phiC_nonneg hν μ l t x s)]
  refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
  filter_upwards [ae_ne_real t] with s hst hs
  exact ofReal_phiC_eq_lintegral hT hν l hs.1 (lt_of_le_of_ne hs.2 hst) x

/-- The Lebesgue convolution `∫⁻_{(0,t]} ∫⁻_ℝ J₀(s,y)² 𝓚_λ(t−s,x−y) dy ds` is finite. -/
theorem lintegral_J0_sq_K_lt_top {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (l : ℝ) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * K ν l (t - s) (x - y)) < ⊤ := by
  rw [← stConv_J0_sq_K_eq_lintegral hT hν l ht x]
  exact ENNReal.ofReal_lt_top

/-- The space-time integrand `(s,y) ↦ J₀(s,y)² 𝓚_λ(t−s,x−y)` of `(J₀² ⋆ 𝓚_λ)(t,x)` is
integrable on `(0,t] × ℝ`. -/
theorem integrable_J0_sq_K {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (l : ℝ) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => J0 ν μ p.1 p.2 ^ 2 * K ν l (t - p.1) (x - p.2))
      ((volume.restrict (Ioc 0 t)).prod volume) := by
  have hm := stronglyMeasurable_integrand ν μ l t x
  have hae : (fun p : ℝ × ℝ => integrand ν μ l t x p.1 p.2) =ᵐ[(volume.restrict (Ioc 0 t)).prod
      volume] fun p => J0 ν μ p.1 p.2 ^ 2 * K ν l (t - p.1) (x - p.2) := by
    have hs : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) t)), s < t :=
      (ae_restrict_iff' measurableSet_Ioc).mpr
        ((ae_ne_real t).mono fun s hst hs => lt_of_le_of_ne hs.2 hst)
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs] with p hp
    rw [integrand, K_eq_kC hν (sub_pos.mpr hp)]
  refine Integrable.congr ⟨hm.aestronglyMeasurable, ?_⟩ hae
  rw [hasFiniteIntegral_iff_ofReal (f := fun p : ℝ × ℝ => integrand ν μ l t x p.1 p.2)
      (Eventually.of_forall fun p => integrand_nonneg hν μ l t x p.1 p.2),
    lintegral_prod _ hm.measurable.ennreal_ofReal.aemeasurable]
  refine lt_of_le_of_lt (le_of_eq ?_) (lintegral_J0_sq_K_lt_top hT hν l ht x)
  refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
  filter_upwards [ae_ne_real t] with s hst hs
  refine lintegral_congr fun y => ?_
  rw [integrand, K_eq_kC hν (sub_pos.mpr (lt_of_le_of_ne hs.2 hst))]

/-- `ofReal (J₀² + J₀² ⋆ 𝓚_λ) = ofReal (J₀²) + ∫⁻∫⁻ J₀² 𝓚_λ`. -/
theorem ofReal_J0_sq_add_stConv {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (l : ℝ) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    ENNReal.ofReal (J0 ν μ t x ^ 2 + stConv (fun s y => J0 ν μ s y ^ 2) (K ν l) t x) =
      ENNReal.ofReal (J0 ν μ t x ^ 2) +
        ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * K ν l (t - s) (x - y)) := by
  rw [ENNReal.ofReal_add (sq_nonneg _) (stConv_J0_sq_K_nonneg hν μ l ht x),
    stConv_J0_sq_K_eq_lintegral hT hν l ht x]

end MomentBridge

open MomentBridge

/-- **`T2:Growth(2)`, `p = 2`, with the moment hypothesis as a Lebesgue integral.** Same as
`T2_Growth_upper`, with `E2:SecMom-Up` written with the lower Lebesgue integral:
`g(t,x) ≤ J₀(t,x)² + ∫⁻_{(0,t]} ∫⁻_ℝ J₀(s,y)² 𝓚_λ(t−s,x−y) dy ds`. -/
theorem T2_Growth_upper_lintegral {μ : Measure ℝ} {ν β lam : ℝ} (hν : 0 < ν) (hβ : 0 < β)
    (hlam : lam ≠ 0) (hI : Integrable (fun y => Real.exp (β * |y|)) μ)
    {g : ℝ → ℝ → ℝ≥0∞}
    (hg : ∀ t > 0, ∀ x, g t x ≤ ENNReal.ofReal (J0 ν μ t x ^ 2) +
      ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * K ν lam (t - s) (x - y))) :
    upperGrowthIndex g ≤
      ((if β < lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
        EReal) := by
  have := GrowthUpper.isFiniteMeasure_of_integrable_exp hβ.le hI
  have hT := RoughHeatKernel.isGaussianTempered_of_isFiniteMeasure μ
  refine T2_Growth_upper hν hβ hlam hI fun t ht x => ?_
  rw [ofReal_J0_sq_add_stConv hT hν lam ht x]
  exact hg t ht x

/-- **`P2:Ex-Exp` with the second-moment formula as a Lebesgue integral.** Same as
`P2_Ex_Exp`, with `E2:SecMom` (`ϑ = 0`) written with the lower Lebesgue integral:
`f(t,x) = J₀(t,x)² + ∫⁻_{(0,t]} ∫⁻_ℝ J₀(s,y)² 𝓚_λ(t−s,x−y) dy ds`,
`μ(dx) = e^{−β|x|} dx`. -/
theorem P2_Ex_Exp_lintegral {ν lam β : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) (hβ : 0 < β)
    {f : ℝ → ℝ → ℝ≥0∞}
    (hf_eq : ∀ t > 0, ∀ x, f t x =
      ENNReal.ofReal
          (J0 ν (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-β * |x|))) t x ^ 2) +
        ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal
          (J0 ν (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-β * |x|))) s y ^ 2 *
            K ν lam (t - s) (x - y))) :
    lowerGrowthIndex f =
        ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
          EReal) ∧
      upperGrowthIndex f =
        ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
          EReal) := by
  refine P2_Ex_Exp hν hlam hβ fun t ht x => ?_
  have hT := ExExpEnvelope.isGaussianTempered_expMeasure hβ
  have h := ofReal_J0_sq_add_stConv hT hν lam ht x
  simp only [ExExpEnvelope.expMeasure] at h
  rw [hf_eq t ht x, secondMomentExpr, ← h]
  simp

end ChenDalang15

end
