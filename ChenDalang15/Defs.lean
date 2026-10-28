module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Statement-level definitions (shared verbatim with `CD2015Challenge.lean`)

The objects of Chen–Dalang (2015) that appear in the advertised theorem statements. Palomar
requires the Challenge to import Mathlib only, so `CD2015Challenge.lean` carries a byte-identical
copy of the block between the markers below; `scripts/check-challenge-defs.py` (run by
`verify.sh`) fails if the two copies differ, and Comparator checks that the elaborated
constants agree.
-/

set_option autoImplicit false

@[expose] public section

namespace ChenDalang15

-- BEGIN SHARED DEFINITIONS (keep byte-identical with CD2015Challenge.lean)

/-- A named numeral instance keeps the shared statement layer independent of
module-local auxiliary-proof sharing when elaborating L² dictionaries. -/
instance (priority := 2000) instAtLeastTwoTwo : Nat.AtLeastTwo (1 + 1) :=
  ⟨by decide⟩

/-- The heat kernel `G_ν(t,x) = (2πνt)^{-1/2} exp(-x²/(2νt))`, the fundamental solution of
`∂_t − (ν/2)∂²_x` (paper, Section 2). For `νt ≤ 0` Lean's conventions give the value `0`,
matching the paper's convention `G_ν(t,·) ≡ 0` for `t ≤ 0` when `ν > 0`.
The heat-kernel interpretation requires `ν > 0`: if both `ν < 0` and `t < 0`,
the literal formula has `νt > 0` and need not vanish. -/
noncomputable def G (ν t x : ℝ) : ℝ :=
  1 / Real.sqrt (2 * Real.pi * ν * t) * Real.exp (-x ^ 2 / (2 * ν * t))

/-- The space-time convolution `(f ⋆ g)(t,x) = ∫₀ᵗ ∫_ℝ f(s,y) g(t-s, x-y) dy ds`. -/
noncomputable def stConv (f g : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, ∫ y, f s y * g (t - s) (x - y)

/-- The kernels `𝓛ₙ(t,x;ν,λ)` of the paper's display `E:Def-Ln`: `𝓛₀ = λ² G_ν²` and
`𝓛ₙ₊₁ = 𝓛ₙ ⋆ 𝓛₀` (the `(n+1)`-fold space-time convolution of `𝓛₀`, nested to the left). -/
noncomputable def L (ν lam : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0 => fun t x => lam ^ 2 * G ν t x ^ 2
  | n + 1 => stConv (L ν lam n) (L ν lam 0)

/-- The kernel `𝓚 = Σₙ 𝓛ₙ` of the paper's display `E:Def-K` (an unconditional `tsum`; its
convergence is part of the advertised theorem `P2K_hasSum`). -/
noncomputable def K (ν lam : ℝ) (t x : ℝ) : ℝ := ∑' n, L ν lam n t x

/-- The standard normal distribution function `Φ(x) = ∫_{-∞}^x (2π)^{-1/2} e^{-y²/2} dy`. -/
noncomputable def Phi (x : ℝ) : ℝ :=
  ∫ y in Set.Iic x, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2)

-- END SHARED DEFINITIONS

end ChenDalang15

end
