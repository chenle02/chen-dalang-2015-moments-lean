module

public import RoughHeatKernel.Beta

/-!
# The real Beta integral on `[0, t]`

`∫₀ᵗ s^{a-1} (t - s)^{b-1} ds = t^{a+b-1} Γ(a) Γ(b) / Γ(a+b)` for `a, b, t > 0`.
This is the identity behind the induction step of Chen–Dalang (2015), Proposition `P2:K`
(their display `E2:BetaInt`, the case `a = (n+1)/2`, `b = 1/2`). The proof was extracted to
`RoughHeatKernel.integral_rpow_mul_sub_rpow` (RoughHeatKernel v0.10.0); the companion name is
kept as a wrapper because it is a claim of this package.
-/

set_option autoImplicit false

public section

namespace ChenDalang15

/-- The real Beta integral on `[0, t]` (paper `E2:BetaInt`), from
`RoughHeatKernel.integral_rpow_mul_sub_rpow`. -/
theorem integral_rpow_mul_sub_rpow {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    ∫ s in (0 : ℝ)..t, s ^ (a - 1) * (t - s) ^ (b - 1) =
      t ^ (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) :=
  RoughHeatKernel.integral_rpow_mul_sub_rpow ha hb ht

end ChenDalang15

end
