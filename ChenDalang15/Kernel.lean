module

public import ChenDalang15.Defs
public import RoughHeatKernel
public import WalshIntegral

/-!
# The paper's heat kernel `G_ν`

Chen–Dalang (2015), §2: `G_ν(t,x) = (2πνt)^{-1/2} exp(-x²/(2νt))`, the fundamental
solution of `∂_t − (ν/2)∂²_x`. `RoughHeatKernel.heatKernel` is the case `ν = 1`
(variance `t`). `G` itself is defined in `ChenDalang15.Defs` by the explicit formula (so the
Palomar Challenge needs only Mathlib); this module proves the bridge to `heatKernel`.
-/

set_option autoImplicit false

@[expose] public section

namespace ChenDalang15

open Real

/-- Fidelity check: `G` is literally the paper's formula
`G_ν(t,x) = (2πνt)^{-1/2} exp(-x²/(2νt))`. -/
theorem G_eq_formula (ν t x : ℝ) :
    G ν t x = 1 / Real.sqrt (2 * π * ν * t) * Real.exp (-x ^ 2 / (2 * ν * t)) := rfl

/-- The bridge to RoughHeatKernel: `G_ν(t,x) = p_{νt}(x)`, the variance-`νt` heat kernel
(for all real arguments, including Lean's junk values). -/
theorem G_eq_heatKernel (ν t x : ℝ) : G ν t x = RoughHeatKernel.heatKernel (ν * t) x := by
  unfold G RoughHeatKernel.heatKernel
  congr 2
  · ring_nf
  · ring

end ChenDalang15

end
