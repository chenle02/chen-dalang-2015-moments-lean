module

public import ChenDalang15.Defs

/-!
# The function `E_{a,β}` (Chen–Dalang 2015, display `E2:Eac`)

For `a > 0` and `β ∈ ℝ`,
`E_{a,β}(x) = e^{-βx} Φ((aβ − x)/√a) + e^{βx} Φ((aβ + x)/√a)`,
a smooth version of `e^{β|x|}` (Proposition `P2:E`); by `P2:E(ii)`,
`(e^{β|·|} * G_ν(t,·))(x) = e^{β²νt/2} E_{νt,β}(x)`.
-/

set_option autoImplicit false

@[expose] public section

namespace ChenDalang15

/-- `E_{a,β}(x)` of display `E2:Eac`. -/
noncomputable def Eac (a β x : ℝ) : ℝ :=
  Real.exp (-β * x) * Phi ((a * β - x) / Real.sqrt a) +
    Real.exp (β * x) * Phi ((a * β + x) / Real.sqrt a)

end ChenDalang15

end
