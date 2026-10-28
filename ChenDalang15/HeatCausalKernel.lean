module

public import RoughHeatKernel.CausalHeatKernel

public import ChenDalang15.Kernel

/-!
# The paper's heat kernel as a WalshIntegral `CausalKernel`, at general `ν > 0`

Chen–Dalang (2015), §2: the stochastic convolution `∫₀ᵗ∫ G_ν(t-s, x-y) Φ(s,y) W(ds,dy)` uses the
causal kernel `(t,x; s,y) ↦ G_ν(t-s, x-y)` for `0 < s < t`, and `0` otherwise. This file builds
the instance `heatCausalKernel ν hν : WalshIntegral.Modification.CausalKernel`, so that
`WalshIntegral.Modification.exists_predictable_modification` applies to it.

* `lintegral_heatK_sq_Ioi`: `∫∫_{s > a} G_ν(t-s, x-y)² dy ds = √((t-a)/(πν))` for `a ≥ 0`
  (`0` when `t ≤ a`); the case `a = 0` is `lintegral_heatK_sq`.
* `heatCausalKernel`: all fields proved, including the L²-continuity field `tendsto_sq` at every
  output point, the time origin and negative times included.
* `kernelVariance_heatCausalKernel`: the kernel variance is
  `∫⁻∫⁻ G_ν(t-s,x-y)² E[Φ(s,y)²] dy ds`; for a deterministic weight `σ` it is
  `∫⁻∫⁻ G_ν(t-s,x-y)² σ(s,y)²`; for `Φ ≡ 1` it is `√(t/(πν))`; it is finite for all `(t,x)` as
  soon as the second moments of `Φ` are bounded, and it vanishes for `t ≤ 0`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Real MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ChenDalang15

namespace HeatCausalKernel

open WalshIntegral.WhiteNoise WalshIntegral.Modification

/-- The causal heat kernel `G_ν(t-s, x-y) 1_{0<s<t}`. -/
def heatK (ν t x s y : ℝ) : ℝ :=
  if 0 < s ∧ s < t then G ν (t - s) (x - y) else 0

/-- Exact causal-kernel bridge retaining the paper's diffusivity. -/
theorem heatK_eq_upstream (ν t x s y : ℝ) :
    heatK ν t x s y = RoughHeatKernel.CausalHeatKernel.heatK ν t x s y := by
  simp only [heatK, RoughHeatKernel.CausalHeatKernel.heatK, G_eq_heatKernel]

/-- The stochastic and deterministic positive-time space measures coincide. -/
theorem timeSpaceVolume_eq_upstream : WalshIntegral.WhiteNoise.timeSpaceVolume =
    RoughHeatKernel.CausalHeatKernel.positiveTimeSpaceVolume := rfl

theorem heatK_eq_heatKernel (ν t x s y : ℝ) :
    heatK ν t x s y =
      if 0 < s ∧ s < t then RoughHeatKernel.heatKernel (ν * (t - s)) (x - y) else 0 := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.heatK_eq_heatKernel ν t x s y)

theorem heatK_of_not {ν t x s y : ℝ} (h : ¬ (0 < s ∧ s < t)) : heatK ν t x s y = 0 := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.heatK_of_not h)

theorem heatK_of {ν t x s y : ℝ} (h : 0 < s ∧ s < t) :
    heatK ν t x s y = RoughHeatKernel.heatKernel (ν * (t - s)) (x - y) := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.heatK_of h)

theorem heatK_causal (ν t x s y : ℝ) (h : s ≤ 0 ∨ t ≤ s) : heatK ν t x s y = 0 := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.heatK_causal ν t x s y h)

theorem measurable_heatK (ν : ℝ) :
    Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => heatK ν q.1.1 q.1.2 q.2.1 q.2.2) := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.measurable_heatK ν)

/-! ### The closed form of the squared L² norm -/

/-- The spatial integral: `∫ G_ν(r, x-y)² dy = (4πν)^{-1/2} r^{-1/2}` (as a lower integral). -/
theorem lintegral_heatKernel_mul_sq {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (RoughHeatKernel.heatKernel (ν * r) (x - y) ^ 2) =
      ENNReal.ofReal (1 / Real.sqrt (4 * π * ν) * r ^ (-(1 / 2 : ℝ))) := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.lintegral_heatKernel_mul_sq hν hr x)

/-- The time integral `∫_a^t (4πν)^{-1/2} (t-s)^{-1/2} ds = √((t-a)/(πν))`. -/
theorem lintegral_time {ν a t : ℝ} (hν : 0 < ν) (hat : a < t) :
    ∫⁻ s in Ioo a t, ENNReal.ofReal (1 / Real.sqrt (4 * π * ν) * (t - s) ^ (-(1 / 2 : ℝ))) =
      ENNReal.ofReal (Real.sqrt ((t - a) / (π * ν))) := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.lintegral_time hν hat)

/-- Closed form of the squared L² norm of the kernel section beyond time `a ≥ 0`:
`∫∫_{s > a} G_ν(t-s, x-y)² 1_{0<s<t} dy ds = √((t-a)/(πν))`, which is `0` when `t ≤ a`
(`Real.sqrt` of a nonpositive number is `0`). -/
theorem lintegral_heatK_sq_Ioi {ν a : ℝ} (hν : 0 < ν) (ha : 0 ≤ a) (t x : ℝ) :
    ∫⁻ w, {w : ℝ × ℝ | a < w.1}.indicator
        (fun w => ENNReal.ofReal (heatK ν t x w.1 w.2 ^ 2)) w ∂timeSpaceVolume =
      ENNReal.ofReal (Real.sqrt ((t - a) / (π * ν))) := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.lintegral_heatK_sq_Ioi hν ha t x)

/-- The squared L² norm of the kernel section: `∫∫ G_ν(t-s,x-y)² 1_{0<s<t} = √(t/(πν))`
for every real `t` (`0` for `t ≤ 0`). -/
theorem lintegral_heatK_sq {ν : ℝ} (hν : 0 < ν) (t x : ℝ) :
    ∫⁻ w, ENNReal.ofReal (heatK ν t x w.1 w.2 ^ 2) ∂timeSpaceVolume =
      ENNReal.ofReal (Real.sqrt (t / (π * ν))) := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.lintegral_heatK_sq hν t x)

theorem measurable_heatK_section (ν t x : ℝ) :
    Measurable (fun w : ℝ × ℝ => heatK ν t x w.1 w.2) :=
  (measurable_heatK ν).comp ((measurable_const (a := (t, x))).prodMk measurable_id)

/-- Each kernel section is square integrable for the positive-time measure. -/
theorem memLp_heatK {ν : ℝ} (hν : 0 < ν) (t x : ℝ) :
    MemLp (fun w : ℝ × ℝ => heatK ν t x w.1 w.2) 2 timeSpaceVolume := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.memLp_heatK hν t x)

/-! ### L² continuity of the kernel in the output point -/

/-- Pointwise convergence off the diagonal time `s = t`. -/
theorem tendsto_heatK_of_ne {ν : ℝ} (hν : 0 < ν) (t x : ℝ) {s y : ℝ} (hst : s ≠ t) :
    Tendsto (fun z : ℝ × ℝ => heatK ν z.1 z.2 s y) (𝓝 (t, x)) (𝓝 (heatK ν t x s y)) := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.tendsto_heatK_of_ne hν t x hst)

/-- Domination away from the singular time: for `0 < s ≤ t - η`, `|t' - t| ≤ η/4`,
`|x' - x| ≤ 1`, `G_ν(t'-s, x'-y)² ≤ 4 e^{6/(νη)} G_{2ν}(t-s, x-y)²`. -/
theorem heatK_sq_le_local {ν t x t' x' η s y : ℝ} (hν : 0 < ν) (hη : 0 < η)
    (hs : s ≤ t - η) (ht' : |t' - t| ≤ η / 4) (hx' : |x' - x| ≤ 1) :
    heatK ν t' x' s y ^ 2 ≤ 4 * Real.exp (6 / (ν * η)) * heatK (2 * ν) t x s y ^ 2 := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.heatK_sq_le_local hν hη hs ht' hx')

/-- The squared difference restricted to `{s ≤ t - η}` tends to `0` (dominated convergence). -/
theorem tendsto_lintegral_indicator_le {ν t η : ℝ} (hν : 0 < ν) (hη : 0 < η) (x : ℝ) :
    Tendsto (fun z : ℝ × ℝ => ∫⁻ w, {w : ℝ × ℝ | w.1 ≤ t - η}.indicator
        (fun w => ENNReal.ofReal ((heatK ν z.1 z.2 w.1 w.2 - heatK ν t x w.1 w.2) ^ 2)) w
          ∂timeSpaceVolume) (𝓝 (t, x)) (𝓝 0) := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.tendsto_lintegral_indicator_le hν hη x)

/-- The real-number estimate behind the short-time tail bound. -/
theorem tail_bound_real {ν t η δ t' : ℝ} (hν : 0 < ν) (hη : 0 < η)
    (hηδ : η ≤ π * ν * δ ^ 2 / 128) (hδ : 0 < δ) (ht' : t' ≤ t + η) :
    2 * Real.sqrt ((t' - (t - η)) / (π * ν)) + 2 * Real.sqrt ((t - (t - η)) / (π * ν)) ≤
      δ / 2 := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.tail_bound_real hν hη hηδ hδ ht')

/-- **L² continuity of the heat kernel in the output point**, at every `(t,x) ∈ ℝ²`, the time
origin and negative times included: `∫∫ (G_ν(t'-s,x'-y)1_{0<s<t'} - G_ν(t-s,x-y)1_{0<s<t})²
→ 0` as `(t',x') → (t,x)`. -/
theorem tendsto_heatK_sq {ν : ℝ} (hν : 0 < ν) (z : ℝ × ℝ) :
    Tendsto (fun z' : ℝ × ℝ => ∫⁻ w : ℝ × ℝ,
      ENNReal.ofReal ((heatK ν z'.1 z'.2 w.1 w.2 - heatK ν z.1 z.2 w.1 w.2) ^ 2)
        ∂timeSpaceVolume) (𝓝 z) (𝓝 0) := by
  simpa only [heatK_eq_upstream, timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.CausalHeatKernel.tendsto_heatK_sq hν z)

end HeatCausalKernel

/-- **The paper's heat kernel as a WalshIntegral causal kernel**, at general `ν > 0`:
`K(t,x; s,y) = G_ν(t-s, x-y)` for `0 < s < t`, and `0` otherwise. -/
def heatCausalKernel (ν : ℝ) (hν : 0 < ν) : WalshIntegral.Modification.CausalKernel where
  K := HeatCausalKernel.heatK ν
  measurable := HeatCausalKernel.measurable_heatK ν
  causal := HeatCausalKernel.heatK_causal ν
  memLp := HeatCausalKernel.memLp_heatK hν
  tendsto_sq := HeatCausalKernel.tendsto_heatK_sq hν

theorem heatCausalKernel_K {ν : ℝ} (hν : 0 < ν) (t x s y : ℝ) :
    (heatCausalKernel ν hν).K t x s y = if 0 < s ∧ s < t then G ν (t - s) (x - y) else 0 :=
  rfl


/-! ### The kernel variance -/

section Variance

open WalshIntegral.WhiteNoise WalshIntegral.Modification

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `‖f‖₂² = ∫ f²` as a lower integral. -/
theorem eLpNorm_two_sq_eq_lintegral {P : Measure Ω} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) :
    eLpNorm f 2 P ^ 2 = ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
    ← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    using (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num) hf (μ := P))

/-- **The kernel variance of the heat kernel** (Itô-isometry form): for `Φ` with measurable
sections, `kernelVariance = ∫⁻∫⁻ G_ν(t-s,x-y)² 1_{0<s<t} E[Φ(s,y)²] dy ds`. -/
theorem kernelVariance_heatCausalKernel {ν : ℝ} (hν : 0 < ν) (P : Measure Ω)
    (Φ : ℝ → ℝ → Ω → ℝ) (hΦ : ∀ s y, AEStronglyMeasurable (Φ s y) P) (t x : ℝ) :
    kernelVariance P (heatCausalKernel ν hν) Φ t x =
      ∫⁻ w, ENNReal.ofReal (HeatCausalKernel.heatK ν t x w.1 w.2 ^ 2) *
        ∫⁻ ω, ENNReal.ofReal (Φ w.1 w.2 ω ^ 2) ∂P ∂timeSpaceVolume := by
  unfold kernelVariance
  refine lintegral_congr fun w => ?_
  rw [eLpNorm_two_sq_eq_lintegral (hΦ w.1 w.2)]
  rfl

/-- **Deterministic weight** (the form used by the moment argument):
`kernelVariance (fun s y _ => σ s y) = ∫⁻∫⁻ G_ν(t-s,x-y)² 1_{0<s<t} σ(s,y)²`. -/
theorem kernelVariance_heatCausalKernel_det {ν : ℝ} (hν : 0 < ν) (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℝ → ℝ → ℝ) (t x : ℝ) :
    kernelVariance P (heatCausalKernel ν hν) (fun s y _ => σ s y) t x =
      ∫⁻ w, ENNReal.ofReal (HeatCausalKernel.heatK ν t x w.1 w.2 ^ 2) *
        ENNReal.ofReal (σ w.1 w.2 ^ 2) ∂timeSpaceVolume := by
  rw [kernelVariance_heatCausalKernel hν P _ (fun _ _ => aestronglyMeasurable_const)]
  simp only [lintegral_const, measure_univ, mul_one]

/-- The deterministic-weight variance as an iterated integral over the causal region:
`∫₀ᵗ ∫_ℝ G_ν(t-s,x-y)² σ(s,y)² dy ds` (lower integrals), for Borel `σ`. -/
theorem kernelVariance_heatCausalKernel_det_iter {ν : ℝ} (hν : 0 < ν) (P : Measure Ω)
    [IsProbabilityMeasure P] {σ : ℝ → ℝ → ℝ}
    (hσ : Measurable (fun w : ℝ × ℝ => σ w.1 w.2)) (t x : ℝ) :
    kernelVariance P (heatCausalKernel ν hν) (fun s y _ => σ s y) t x =
      ∫⁻ s in Ioo 0 t, ∫⁻ y, ENNReal.ofReal (G ν (t - s) (x - y) ^ 2) *
        ENNReal.ofReal (σ s y ^ 2) := by
  rw [kernelVariance_heatCausalKernel_det hν P σ t x]
  have hm : Measurable (fun w : ℝ × ℝ =>
      ENNReal.ofReal (HeatCausalKernel.heatK ν t x w.1 w.2 ^ 2) *
        ENNReal.ofReal (σ w.1 w.2 ^ 2)) :=
    ((HeatCausalKernel.measurable_heatK_section ν t x).pow_const 2).ennreal_ofReal.mul
      (hσ.pow_const 2).ennreal_ofReal
  rw [timeSpaceVolume, lintegral_prod _ hm.aemeasurable]
  have hin : ∀ s, (∫⁻ y, ENNReal.ofReal (HeatCausalKernel.heatK ν t x s y ^ 2) *
      ENNReal.ofReal (σ s y ^ 2)) = (Ioo 0 t).indicator (fun s => ∫⁻ y,
        ENNReal.ofReal (G ν (t - s) (x - y) ^ 2) * ENNReal.ofReal (σ s y ^ 2)) s := by
    intro s
    by_cases hs : 0 < s ∧ s < t
    · rw [Set.indicator_of_mem (show s ∈ Ioo 0 t from hs)]
      simp [HeatCausalKernel.heatK, hs]
    · rw [Set.indicator_of_notMem (show s ∉ Ioo 0 t from hs)]
      simp [HeatCausalKernel.heatK_of_not hs]
  simp_rw [hin]
  rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_left.mpr (show Ioo 0 t ⊆ Ioi 0 from fun s hs => hs.1)]

/-- **Closed form**: for the constant weight `σ ≡ c`,
`kernelVariance = c² √(t/(πν))` (and `0` for `t ≤ 0`). -/
theorem kernelVariance_heatCausalKernel_const {ν : ℝ} (hν : 0 < ν) (P : Measure Ω)
    [IsProbabilityMeasure P] (c t x : ℝ) :
    kernelVariance P (heatCausalKernel ν hν) (fun _ _ _ => c) t x =
      ENNReal.ofReal (c ^ 2 * Real.sqrt (t / (π * ν))) := by
  rw [kernelVariance_heatCausalKernel_det hν P (fun _ _ => c) t x]
  simp_rw [mul_comm (ENNReal.ofReal (HeatCausalKernel.heatK ν t x _ _ ^ 2))]
  rw [lintegral_const_mul _ (((HeatCausalKernel.measurable_heatK_section ν t x).pow_const
    2).ennreal_ofReal), HeatCausalKernel.lintegral_heatK_sq hν,
    ← ENNReal.ofReal_mul (sq_nonneg c)]

/-- Causality: the kernel variance vanishes at nonpositive times, for every input. -/
theorem kernelVariance_heatCausalKernel_of_nonpos {ν : ℝ} (hν : 0 < ν) (P : Measure Ω)
    (Φ : ℝ → ℝ → Ω → ℝ) {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    kernelVariance P (heatCausalKernel ν hν) Φ t x = 0 := by
  unfold kernelVariance
  have h0 : ∀ w : ℝ × ℝ, (heatCausalKernel ν hν).K t x w.1 w.2 = 0 := fun w =>
    HeatCausalKernel.heatK_causal ν t x w.1 w.2 (by
      by_cases hs : w.1 ≤ 0
      · exact Or.inl hs
      · exact Or.inr (ht.trans (not_le.mp hs).le))
  simp [h0]

/-- **Finiteness**: if the second moments of `Φ` are bounded by `M < ∞` on `(0,t) × ℝ`, then
`kernelVariance ≤ M √(t/(πν)) < ∞`. No measurability of `Φ` is needed. -/
theorem kernelVariance_heatCausalKernel_le {ν : ℝ} (hν : 0 < ν) (P : Measure Ω)
    (Φ : ℝ → ℝ → Ω → ℝ) {t : ℝ} (x : ℝ) {M : ℝ≥0∞}
    (hM : ∀ s y, 0 < s → s < t → eLpNorm (Φ s y) 2 P ^ 2 ≤ M) :
    kernelVariance P (heatCausalKernel ν hν) Φ t x ≤
      M * ENNReal.ofReal (Real.sqrt (t / (π * ν))) := by
  unfold kernelVariance
  calc _ ≤ ∫⁻ w, M * ENNReal.ofReal (HeatCausalKernel.heatK ν t x w.1 w.2 ^ 2)
        ∂timeSpaceVolume := by
        refine lintegral_mono fun w => ?_
        by_cases hs : 0 < w.1 ∧ w.1 < t
        · rw [mul_comm]
          exact mul_le_mul_left (hM w.1 w.2 hs.1 hs.2) _
        · simp [heatCausalKernel, HeatCausalKernel.heatK_of_not hs]
    _ = _ := by
        rw [lintegral_const_mul _ (((HeatCausalKernel.measurable_heatK_section ν t x).pow_const
          2).ennreal_ofReal)]
        exact congrArg _ (HeatCausalKernel.lintegral_heatK_sq hν t x)

theorem kernelVariance_heatCausalKernel_lt_top {ν : ℝ} (hν : 0 < ν) (P : Measure Ω)
    (Φ : ℝ → ℝ → Ω → ℝ) {t : ℝ} (x : ℝ) {M : ℝ≥0∞} (hMtop : M ≠ ⊤)
    (hM : ∀ s y, 0 < s → s < t → eLpNorm (Φ s y) 2 P ^ 2 ≤ M) :
    kernelVariance P (heatCausalKernel ν hν) Φ t x < ⊤ :=
  (kernelVariance_heatCausalKernel_le hν P Φ x hM).trans_lt
    (ENNReal.mul_lt_top hMtop.lt_top ENNReal.ofReal_lt_top)

/-- Bounded deterministic weights have finite kernel variance at every output point. -/
theorem kernelVariance_heatCausalKernel_det_lt_top {ν : ℝ} (hν : 0 < ν) (P : Measure Ω)
    [IsProbabilityMeasure P] {σ : ℝ → ℝ → ℝ} {C : ℝ} (hσ : ∀ s y, |σ s y| ≤ C) (t x : ℝ) :
    kernelVariance P (heatCausalKernel ν hν) (fun s y _ => σ s y) t x < ⊤ := by
  refine kernelVariance_heatCausalKernel_lt_top hν P _ x (M := ENNReal.ofReal (C ^ 2))
    ENNReal.ofReal_ne_top fun s y _ _ => ?_
  rw [eLpNorm_two_sq_eq_lintegral aestronglyMeasurable_const, lintegral_const, measure_univ,
    mul_one]
  exact ENNReal.ofReal_le_ofReal (sq_le_sq' (abs_le.mp (hσ s y)).1 (abs_le.mp (hσ s y)).2)

/-- `WalshIntegral.Modification.exists_predictable_modification` for the heat kernel: the
stochastic convolution `∫₀ᵗ∫ G_ν(t-s,x-y) Φ(s,y) W(ds,dy)` has a predictable modification
whenever its kernel variance is finite at every output point. -/
theorem exists_predictable_modification_heat {ν : ℝ} (hν : 0 < ν)
    {F : MeasureTheory.Filtration NNReal mΩ} {P : Measure Ω}
    [IsProbabilityMeasure P] {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W)
    (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[WalshIntegral.Predictable.predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2))
    (hfin : ∀ t x, kernelVariance P (heatCausalKernel ν hν) Φ t x < ⊤) :
    ∃ Ψ : ℝ → ℝ → Ω → ℝ,
      Measurable[WalshIntegral.Predictable.predictableSigma F]
          (fun q : ℝ × ℝ × Ω => Ψ q.1 q.2.1 q.2.2) ∧
        ∀ t x, WalshIntegral.Integral.walshT hW (kernelField (heatCausalKernel ν hν) t x Φ)
          =ᵐ[P] Ψ t x :=
  exists_predictable_modification hW (heatCausalKernel ν hν) Φ hΦ hfin

end Variance

end ChenDalang15
