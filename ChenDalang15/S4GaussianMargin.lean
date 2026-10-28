module

public import RoughHeatKernel.WeightedCausalHeatKernel

public import ChenDalang15.Kernel
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A weak Gaussian margin for the S4 continuity argument

This sufficient comparison uses a later output time `2 * t` and a loose
explicit spatial radius. It does not claim the exact neighborhood or radius
of the manuscript's Proposition `P2:G-Margin`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.S4GaussianMargin

open Real

theorem G_sq_le_future_of_far {ν t t' x x' s y : ℝ}
    (hν : 0 < ν) (ht : 0 < t)
    (_ht'lo : 3 * t / 4 ≤ t') (ht'hi : t' ≤ 5 * t / 4)
    (hx : |x' - x| ≤ 1) (hslo : t / 4 ≤ s) (hshi : s < t')
    (hy : |x| + 8 * (1 + ν * t) ≤ |y|) :
    G ν (t' - s) (x' - y) ^ 2 ≤ G ν (2 * t - s) (x - y) ^ 2 := by
  simpa only [G_eq_heatKernel] using
    (RoughHeatKernel.WeightedCausalHeatKernel.heatKernel_sq_le_future_of_far
      hν ht _ht'lo ht'hi hx hslo hshi hy)

end ChenDalang15.S4GaussianMargin

end
