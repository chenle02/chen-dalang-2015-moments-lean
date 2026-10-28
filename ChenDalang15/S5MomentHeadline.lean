module

public import ChenDalang15.S5Headlines

/-!
# The second-moment identity with full random-field existence

The quasi-linear squared-coefficient condition gives the exact second moment
for every full solution. The theorem also supplies a Walsh integral and full
solution existence for every such integral. Its statement uses only the
Mathlib-facing stochastic definitions and explicit deterministic convolutions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.S5MomentHeadline

open MeasureTheory ProbabilityTheory Set Stoch
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The quasi-linear second-moment formula at general positive diffusivity,
with full solution existence and the formula for every solution. Both the
offset and coefficient may vanish. Gaussian integrability supplies the internal
s-finiteness bridge; no moment or solution premise is imposed on the data. -/
theorem T2_ExUni_secondMoment_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ}
    (hμ : ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) μ)
    {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) {lam θ : ℝ}
    (hρ : ∀ z : ℝ, ρ z ^ 2 = lam ^ 2 * (θ ^ 2 + z ^ 2)) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        ∀ t : ℝ, 0 < t → ∀ x : ℝ,
          momentFn P u 2 t x = ENNReal.ofReal
            (J0 ν μ t x ^ 2 +
              stConv (fun s y => J0 ν μ s y ^ 2) (K ν lam) t x +
              θ ^ 2 * stConv (fun _ _ => (1 : ℝ)) (K ν lam) t x) := by
  have hT := S1Glue.integrable_exp_neg_sq_iff.mp hμ
  let : IsLocallyFiniteMeasure μ := hT.isLocallyFiniteMeasure
  let : SigmaFinite μ := inferInstance
  obtain ⟨hJexists, hsolutions⟩ := S5Headlines.T2_ExUni_p2_headline hW hν hμ hLip
  refine ⟨hJexists, ?_⟩
  intro J hJ
  refine ⟨(hsolutions J hJ).1, ?_⟩
  intro u hu t ht x
  rw [secondMoment_eq_quasilinear_of_solution hW hJ hν hT hLip.continuous.measurable hρ hu t ht x]
  simp only [secondMomentExpr, Hfun]
  rw [(one_conv_K hν ht.le 0).trans (one_conv_K hν ht.le x).symm]

end ChenDalang15.S5MomentHeadline

end
