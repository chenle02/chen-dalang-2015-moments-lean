module

public import ChenDalang15.Defs

/-!
# The two-point term `𝓘` and the second-moment expression (Chen–Dalang 2015, `rd1`, `E2:SecMom`)

For `τ ≥ t > 0`, Theorem `T2:ExUni(5)` (quasi-linear case `|ρ(u)|² = λ²(ϑ² + u²)`) gives
`E[u(t,x)u(τ,y)] = J₀(t,x)J₀(τ,y) + 𝓘(t,x,τ,y)` (`E2:TP`) and
`‖u(t,x)‖₂² = J₀²(t,x) + (J₀² ⋆ 𝓚)(t,x) + ϑ²𝓗(t)` (`E2:SecMom`), with `𝓘` defined in
display `rd1`. Here `J₀` is any function of `(t,x)` (the solution of the homogeneous heat
equation with the given initial data), so the corollaries `C2:TP-Lebesgue` (`J₀ ≡ 1`) and
`C2:TP-Delta` (`J₀ = G_ν`) are deterministic identities about these expressions.

The paper's convention for `τ = t` in `rd1`, `Φ(|x − y|/0) = 1`, is written out explicitly.
-/

set_option autoImplicit false

@[expose] public section

namespace ChenDalang15

/-- `𝓗(t) = (1 ⋆ 𝓚)(t,x)` (display `E2:H`; it does not depend on `x`). -/
noncomputable def Hfun (ν lam t : ℝ) : ℝ :=
  stConv (fun _ _ => (1 : ℝ)) (K ν lam) t 0

/-- `Φ(|x − y|/√(ν(τ − t)))`, with the paper's convention `Φ(|x − y|/0) = 1` when `τ = t`. -/
noncomputable def PhiGap (ν t τ z : ℝ) : ℝ :=
  if τ = t then 1 else Phi (|z| / Real.sqrt (ν * (τ - t)))

/-- The two-point term `𝓘(t,x,τ,y;ν,ϑ,λ)` of display `rd1`:
`λ² (∫₀ᵗ ∫_ℝ […] G G dz dr) + (ϑ²-line) + (ϑ²-line)`. The parentheses around the time-space
integral are essential: `∫ x, f` extends as far right as possible, so without them both
`ϑ²`-lines would sit inside the integrals. -/
noncomputable def twoPointI (J0 : ℝ → ℝ → ℝ) (ν v lam t x τ y : ℝ) : ℝ :=
  lam ^ 2 * (∫ r in (0 : ℝ)..t, ∫ z,
      (J0 r z ^ 2 + stConv (fun s w => J0 s w ^ 2) (K ν lam) r z + v ^ 2 * Hfun ν lam r) *
        (G ν (t - r) (x - z) * G ν (τ - r) (y - z))) +
    lam ^ 2 * v ^ 2 / ν * |x - y| *
      (Phi (|x - y| / Real.sqrt (ν * (t + τ))) - PhiGap ν t τ (x - y)) +
    lam ^ 2 * v ^ 2 * ((t + τ) * G ν (t + τ) (x - y) - (τ - t) * G ν (τ - t) (x - y))

/-- The right side of `E2:SecMom`: `J₀²(t,x) + (J₀² ⋆ 𝓚)(t,x) + ϑ²𝓗(t)`. -/
noncomputable def secondMomentExpr (J0 : ℝ → ℝ → ℝ) (ν v lam t x : ℝ) : ℝ :=
  J0 t x ^ 2 + stConv (fun s w => J0 s w ^ 2) (K ν lam) t x + v ^ 2 * Hfun ν lam t

end ChenDalang15

end
