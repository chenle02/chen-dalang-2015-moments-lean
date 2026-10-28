module

public import ChenDalang15.Phi

/-!
# `Φ` in terms of `erf`, and the series `Σ z^k / Γ(k/2 + 1) = e^{z²}(1 + erf z)`

Chen–Dalang (2015), proof of Proposition `P2:K`. The paper uses

* `Φ(x) = (1 + Erf(x/√2))/2`, and
* `e^{x²}(1 + Erf x) = Σ_{n≥1} x^{n-1}/Γ((n+1)/2)`, citing DLMF 7.6.2 for the odd part.

Here the series is reindexed by `k = n - 1` and holds for `z ≥ 0`. The proofs were extracted to
`RoughHeatKernel.Erf` (RoughHeatKernel v0.10.0); this module restates them for the paper's
`Phi` and `erf` through the definitional bridges `Phi_eq_normalCDF` and `erf_eq_erf`
(`ChenDalang15.Phi`).
-/

set_option autoImplicit false

public section

namespace ChenDalang15

open Real
open scoped Nat

/-! ### `Φ` and `erf` -/

/-- `Φ(0) = 1/2` (`RoughHeatKernel.normalCDF_zero`). -/
theorem Phi_zero : Phi 0 = 1 / 2 := RoughHeatKernel.normalCDF_zero

/-- `Φ(x) = (1 + Erf(x/√2))/2` (`RoughHeatKernel.normalCDF_eq_erf`). -/
theorem Phi_eq_erf (x : ℝ) : Phi x = (1 + erf (x / Real.sqrt 2)) / 2 :=
  RoughHeatKernel.normalCDF_eq_erf x

/-! ### The series -/

/-- `∫₀^z (z² - u²)^m du = z^{2m+1} √π m! / (2 Γ(m + 3/2))` for `z ≥ 0`
(`RoughHeatKernel.integral_sq_sub_sq_pow`, whose arguments are ordered `hz m`). -/
theorem integral_sq_sub_sq_pow (m : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    ∫ u in (0 : ℝ)..z, (z ^ 2 - u ^ 2) ^ m =
      z ^ (2 * m + 1) * (Real.sqrt π * (m ! : ℝ) / (2 * Real.Gamma ((m : ℝ) + 3 / 2))) :=
  RoughHeatKernel.integral_sq_sub_sq_pow hz m

/-- Odd part: `Σ_m z^{2m+1}/Γ(m + 3/2) = e^{z²} erf z` for `z ≥ 0`. -/
theorem hasSum_odd_pow_div_Gamma {z : ℝ} (hz : 0 ≤ z) :
    HasSum (fun m : ℕ => z ^ (2 * m + 1) / Real.Gamma ((m : ℝ) + 3 / 2))
      (Real.exp (z ^ 2) * erf z) :=
  RoughHeatKernel.hasSum_odd_pow_div_Gamma hz

/-- Even part: `Σ_m z^{2m}/Γ(m + 1) = e^{z²}`. -/
theorem hasSum_even_pow_div_Gamma (z : ℝ) :
    HasSum (fun m : ℕ => z ^ (2 * m) / Real.Gamma ((m : ℝ) + 1)) (Real.exp (z ^ 2)) :=
  RoughHeatKernel.hasSum_even_pow_div_Gamma z

/-- `Σ_k z^k/Γ(k/2 + 1) = e^{z²}(1 + erf z)` for `z ≥ 0` (DLMF 7.6.2, reindexed;
`RoughHeatKernel.hasSum_pow_div_Gamma`). -/
theorem hasSum_pow_div_Gamma {z : ℝ} (hz : 0 ≤ z) :
    HasSum (fun k : ℕ => z ^ k / Real.Gamma ((k : ℝ) / 2 + 1))
      (Real.exp (z ^ 2) * (1 + erf z)) :=
  RoughHeatKernel.hasSum_pow_div_Gamma hz

end ChenDalang15

end
