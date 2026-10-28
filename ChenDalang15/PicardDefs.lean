module

public import ChenDalang15.StochDefs
public import ChenDalang15.LConv

/-!
# Interfaces for Picard existence (Wave S3)

These are construction interfaces for the proof of `T2:ExUni`, Steps 1–3.
`IsRandomFieldSolution₀` omits only continuity of the integral field from the full
solution notion. It is an internal checkpoint; full `D2:Solution` still requires
Wave S4. No definition assumes existence, a moment bound or convergence.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.Stoch

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The S3 checkpoint: all clauses of `D2:Solution` except L²-continuity of the
integral field. Every clause is restricted to positive times. -/
structure IsRandomFieldSolution₀ [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (J : PredL2 F P →L[ℝ] Lp ℝ 2 P) (ν : ℝ) (ρ : ℝ → ℝ) (μ : Measure ℝ)
    (u : ℝ → ℝ → Ω → ℝ) : Prop where
  adapted : ∀ t : ℝ, 0 < t → ∀ x : ℝ, Measurable[F t.toNNReal] (u t x)
  jointlyMeasurable : Measurable (fun q : Ioi (0 : ℝ) × ℝ × Ω => u q.1 q.2.1 q.2.2)
  finite : ∀ t : ℝ, 0 < t → ∀ x : ℝ,
    ∫⁻ z in Ioo 0 t ×ˢ univ, ENNReal.ofReal (G ν (t - z.1) (x - z.2) ^ 2) *
      momentFn P (fun s y ω => ρ (u s y ω)) 2 z.1 z.2 < ∞
  integral : ∃ I : ℝ → ℝ → Lp ℝ 2 P, IsIntegralField J ν ρ u I ∧
    ∀ t : ℝ, 0 < t → ∀ x : ℝ, u t x =ᵐ[P] fun ω => J0 ν μ t x + I t x ω

/-- One genuine Picard step. The stochastic integral is driven by the input `v`;
the output `u` equals `J₀` plus that integral. `IsIntegralField` requires a
predictable square-integrable class witness for each weighted input integrand.
The construction must supply those witnesses and separately prove predictability
of the output and its moment bound; neither output property is assumed here. -/
def PicardStep [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (J : PredL2 F P →L[ℝ] Lp ℝ 2 P) (ν : ℝ) (ρ : ℝ → ℝ) (μ : Measure ℝ)
    (v u : ℝ → ℝ → Ω → ℝ) : Prop :=
  ∃ I : ℝ → ℝ → Lp ℝ 2 P, IsIntegralField J ν ρ v I ∧
    ∀ t : ℝ, 0 < t → ∀ x : ℝ, u t x =ᵐ[P] fun ω => J0 ν μ t x + I t x ω

end ChenDalang15.Stoch

namespace ChenDalang15.Picard

open MeasureTheory
open scoped ENNReal

/-- The deterministic source `V² + J₀²` of the moment majorant. -/
def source (ν V : ℝ) (μ : Measure ℝ) (t x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (V ^ 2) + ENNReal.ofReal (J0 ν μ t x ^ 2)

/-- The explicit resolvent contribution `(V² + J₀²) ⋆ 𝓚_Lip` as a lower integral.
Its finiteness must be proved from Gaussian tempering and positive diffusivity. -/
def remainder (ν V Lip : ℝ) (μ : Measure ℝ) (t x : ℝ) : ℝ≥0∞ :=
  lstConv (source ν V μ) (fun s y => ENNReal.ofReal (K ν Lip s y)) t x

/-- Candidate upper bound `J₀² + (V² + J₀²) ⋆ 𝓚_Lip` for actual Picard iterates.
This definition is not itself a moment estimate. -/
def majorant (ν V Lip : ℝ) (μ : Measure ℝ) (t x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (J0 ν μ t x ^ 2) + remainder ν V Lip μ t x

end ChenDalang15.Picard

end
