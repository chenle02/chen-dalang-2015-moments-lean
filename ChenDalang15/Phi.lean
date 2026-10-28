module

public import ChenDalang15.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import RoughHeatKernel.Erf

/-!
# The standard normal distribution function `Φ` and the error function

Chen–Dalang (2015), Section 2 (before `P2:K`):
`Φ(x) = ∫_{-∞}^x (2π)^{-1/2} e^{-y²/2} dy`, `Erf(x) = (2/√π) ∫₀ˣ e^{-y²} dy`,
`Erfc = 1 - Erf`. These are the paper's definitions, stated literally.

Mathlib (v4.35.0) has neither `erf` nor a named Gaussian distribution function. The API
(`erf`, `normalCDF`, their derivative, value at `0`, and the `erf` series) lives in
`RoughHeatKernel.Erf` (RoughHeatKernel v0.10.0). The companion keeps the paper's definitions
stated literally and bridges them definitionally: `erf_eq_erf`, `erfc_eq_erfc` and
`Phi_eq_normalCDF` are `rfl`. `erf` is written exactly as TauCeti's
`TauCeti.Analysis.SpecialFunctions.Erf.erf`, as is the library's.
-/

set_option autoImplicit false

@[expose] public section

namespace ChenDalang15

open Real MeasureTheory

-- `Phi` is defined in `ChenDalang15.Defs` (shared with the Palomar Challenge).

/-- The error function `Erf(x) = (2/√π) ∫₀ˣ e^{-y²} dy` (TauCeti's definition). -/
noncomputable def erf (x : ℝ) : ℝ :=
  2 / Real.sqrt π * ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)

/-- The complementary error function `Erfc = 1 - Erf`. -/
noncomputable def erfc (x : ℝ) : ℝ := 1 - erf x

/-- Bridge: the paper's `Erf` is `RoughHeatKernel.erf` (identical bodies). -/
theorem erf_eq_erf : erf = RoughHeatKernel.erf := rfl

/-- Bridge: the paper's `Erfc` is `RoughHeatKernel.erfc`. -/
theorem erfc_eq_erfc : erfc = RoughHeatKernel.erfc := rfl

/-- Bridge: the paper's `Φ` (`ChenDalang15.Defs`) is `RoughHeatKernel.normalCDF`
(identical bodies). -/
theorem Phi_eq_normalCDF : Phi = RoughHeatKernel.normalCDF := rfl

end ChenDalang15

end
