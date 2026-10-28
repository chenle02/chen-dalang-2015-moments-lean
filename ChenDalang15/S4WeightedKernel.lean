module

public import RoughHeatKernel.WeightedCausalHeatKernel

public import ChenDalang15.S4GaussianMargin
public import ChenDalang15.HeatCausalKernel
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Weighted positive-time heat-kernel continuity

A finite future-output variance and a finite compact bound on the input
weight imply continuity of the weighted squared kernel difference. The
weight may take the value infinity outside the active integration region.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.S4WeightedKernel

open Real MeasureTheory Filter Set HeatCausalKernel
open scoped ENNReal Topology
open WalshIntegral.WhiteNoise

theorem tendsto_weighted_sq_difference {ν t x : ℝ}
    (hν : 0 < ν) (ht : 0 < t) (w : ℝ × ℝ → ℝ≥0∞) (hw : Measurable w)
    (hfuture : (∫⁻ q : ℝ × ℝ,
      ENNReal.ofReal (heatK ν (2 * t) x q.1 q.2 ^ 2) * w q ∂timeSpaceVolume) < ⊤)
    (hcompact : ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ q ∈ Icc (t / 4) (5 * t / 4) ×ˢ
        Icc (-(|x| + 8 * (1 + ν * t))) (|x| + 8 * (1 + ν * t)), w q ≤ B) :
    Tendsto (fun z : ℝ × ℝ => ∫⁻ q : ℝ × ℝ,
      ENNReal.ofReal ((heatK ν z.1 z.2 q.1 q.2 - heatK ν t x q.1 q.2) ^ 2) * w q
        ∂timeSpaceVolume) (𝓝 (t, x)) (𝓝 0) := by
  simpa only [HeatCausalKernel.heatK_eq_upstream,
    HeatCausalKernel.timeSpaceVolume_eq_upstream] using
    (RoughHeatKernel.WeightedCausalHeatKernel.tendsto_weighted_sq_difference
      hν ht w hw (by simpa only [HeatCausalKernel.heatK_eq_upstream,
        HeatCausalKernel.timeSpaceVolume_eq_upstream] using hfuture) hcompact)

end ChenDalang15.S4WeightedKernel

end
