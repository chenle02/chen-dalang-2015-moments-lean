module

public import ChenDalang15.Phi
public import RoughHeatKernel.Erf

/-!
# Elementary facts about `erf` and `erfc`

Derivative, continuity, parity, signs and limits at `±∞` of the paper's `Erf` and `Erfc`
(`ChenDalang15.erf`, `ChenDalang15.erfc`, definitionally RoughHeatKernel's), shared by the
Appendix modules `IntGG`, `IntHG` and `IntBC`. Since RoughHeatKernel v0.11.0 each fact is the
library lemma of the same name, restated for the paper's notation.
-/

set_option autoImplicit false

public section

namespace ChenDalang15

open Real Filter Topology

theorem hasDerivAt_erf (x : ℝ) : HasDerivAt erf (2 / √π * exp (-x ^ 2)) x :=
  RoughHeatKernel.hasDerivAt_erf x

theorem continuous_erf : Continuous erf := RoughHeatKernel.continuous_erf

theorem erf_zero : erf 0 = 0 := RoughHeatKernel.erf_zero

theorem erfc_zero : erfc 0 = 1 := RoughHeatKernel.erfc_zero

theorem erf_neg (x : ℝ) : erf (-x) = -erf x := RoughHeatKernel.erf_neg x

theorem tendsto_erf_atTop : Tendsto erf atTop (𝓝 1) := RoughHeatKernel.tendsto_erf_atTop

theorem tendsto_erf_atBot : Tendsto erf atBot (𝓝 (-1)) := RoughHeatKernel.tendsto_erf_atBot

theorem tendsto_erfc_atTop : Tendsto erfc atTop (𝓝 0) := RoughHeatKernel.tendsto_erfc_atTop

theorem hasDerivAt_erfc (x : ℝ) : HasDerivAt erfc (-(2 / Real.sqrt π * Real.exp (-x ^ 2))) x :=
  RoughHeatKernel.hasDerivAt_erfc x

theorem erf_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ erf x := RoughHeatKernel.erf_nonneg hx

theorem erf_nonpos {x : ℝ} (hx : x ≤ 0) : erf x ≤ 0 := RoughHeatKernel.erf_nonpos hx

end ChenDalang15

end
