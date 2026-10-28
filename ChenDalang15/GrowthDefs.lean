module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup
public import ChenDalang15.Defs

/-!
# Exponential growth indices (Chen–Dalang 2015, displays `E1:GrowInd-0`, `E1:GrowInd-1`)

Following Conus–Khoshnevisan, for a moment function `f(t,x)` (in the paper
`f = E|u(t,x)|^p`) the lower and upper exponential growth indices are
```
λ̲ = sup {α > 0 : limsup_{t→∞} t⁻¹ log sup_{|x| ≥ αt} f(t,x) > 0},
λ̄ = inf {α > 0 : limsup_{t→∞} t⁻¹ log sup_{|x| ≥ αt} f(t,x) < 0}.
```
Conventions, chosen so that the paper's statements read literally:
* `f` takes values in `ℝ≥0∞` (moments are lower Lebesgue integrals, possibly infinite);
* `log` is `ENNReal.log : ℝ≥0∞ → EReal` (`log 0 = ⊥`, `log ∞ = ⊤`), so the rate lives in `EReal`;
* the indices live in `EReal`: `sup ∅ = ⊥` and `inf ∅ = ⊤`, so `λ̄ = +∞` when no `α` gives
  exponential decay, matching the paper's `λ̲(p) = λ̄(p) = +∞`.
-/

set_option autoImplicit false

@[expose] public section

-- BEGIN SHARED DEFINITIONS: GrowthDefs
open scoped ENNReal

namespace ChenDalang15

/-- `sup_{|x| ≥ αt} f(t,x)`. -/
noncomputable def tailSup (f : ℝ → ℝ → ℝ≥0∞) (α t : ℝ) : ℝ≥0∞ :=
  letI : SupSet ℝ≥0∞ :=
    @CompleteLattice.toSupSet ℝ≥0∞
      (@CompleteLinearOrder.toCompleteLattice ℝ≥0∞ ENNReal.instCompleteLinearOrder)
  ⨆ (x : ℝ) (_ : α * t ≤ |x|), f t x

/-- `limsup_{t→∞} t⁻¹ log sup_{|x| ≥ αt} f(t,x)`, valued in `EReal`. -/
noncomputable def tailRate (f : ℝ → ℝ → ℝ≥0∞) (α : ℝ) : EReal :=
  Filter.limsup (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * ENNReal.log (tailSup f α t)) Filter.atTop

/-- The lower exponential growth index `λ̲` of `f` (display `E1:GrowInd-0`). -/
noncomputable def lowerGrowthIndex (f : ℝ → ℝ → ℝ≥0∞) : EReal :=
  sSup ((fun α : ℝ => (α : EReal)) '' {α | 0 < α ∧ 0 < tailRate f α})

/-- The upper exponential growth index `λ̄` of `f` (display `E1:GrowInd-1`). -/
noncomputable def upperGrowthIndex (f : ℝ → ℝ → ℝ≥0∞) : EReal :=
  sInf ((fun α : ℝ => (α : EReal)) '' {α | 0 < α ∧ tailRate f α < 0})

/-- The `p`-th moment function `E|X(t,x)|^p` of a random field `X` under `P`. -/
noncomputable def momentFn {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (X : ℝ → ℝ → Ω → ℝ) (p : ℝ) : ℝ → ℝ → ℝ≥0∞ :=
  fun t x => ∫⁻ ω, ‖X t x ω‖ₑ ^ p ∂P

/-- The solution of the homogeneous heat equation with initial data `μ`:
`J₀(t,x) = (G_ν(t,·) * μ)(x) = ∫ G_ν(t, x − y) μ(dy)` (paper, Section 2). -/
noncomputable def J0 (ν : ℝ) (μ : MeasureTheory.Measure ℝ) (t x : ℝ) : ℝ :=
  ∫ y, G ν t (x - y) ∂μ

end ChenDalang15
-- END SHARED DEFINITIONS: GrowthDefs

end
