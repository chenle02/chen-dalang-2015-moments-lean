module

public import ChenDalang15.PicardIteration

/-!
# From a predictable Picard fixed point to the S3 solution predicate

The integral-domain finiteness clause is derived from the actual PredL2 witness
and Itô isometry. Continuity remains an independent S4 obligation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.Picard

open MeasureTheory ProbabilityTheory Set Stoch
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- A predictable fixed Picard step satisfies all solution clauses except
L²-continuity of the integral. Its finite convolution is proved, not assumed. -/
theorem solution₀_of_predictable_fixed_step [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} (hρm : Measurable ρ) {μ : Measure ℝ}
    {u : ℝ → ℝ → Ω → ℝ}
    (hu : Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => u q.1 q.2.1 q.2.2))
    (hstep : PicardStep J ν ρ μ u u) : IsRandomFieldSolution₀ J ν ρ μ u := by
  obtain ⟨I, hI, heq⟩ := hstep
  have hum : Measurable (fun q : ℝ × ℝ × Ω => u q.1 q.2.1 q.2.2) :=
    hu.mono (WalshIntegral.Predictable.predictableSigma_le F) le_rfl
  refine ⟨?_, ?_, ?_, I, hI, heq⟩
  · intro t ht x
    have h := WalshIntegral.Predictable.measurable_timeSection F hu t.toNNReal x
    simpa only [Real.coe_toNNReal t ht.le] using h
  · exact hum.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  · intro t ht x
    have hmom : Measurable (fun z : ℝ × ℝ => momentFn P (fun s y ω => ρ (u s y ω)) 2 z.1 z.2) := by
      have hm : Measurable (fun q : (ℝ × ℝ) × Ω => ‖ρ (u q.1.1 q.1.2 q.2)‖ₑ ^ (2 : ℝ)) :=
        (hρm.comp (hum.comp (measurable_fst.fst.prodMk
          (measurable_fst.snd.prodMk measurable_snd)))).enorm.pow_const _
      exact hm.lintegral_prod_right'
    have hkernel : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (G ν (t-z.1) (x-z.2) ^ 2)) := by
      unfold G
      fun_prop
    change (∫⁻ z in Ioo 0 t ×ˢ univ,
      ENNReal.ofReal (G ν (t-z.1) (x-z.2) ^ 2) *
      momentFn P (fun s y ω => ρ (u s y ω)) 2 z.1 z.2 ∂volume.prod volume) < ⊤
    rw [setLIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (s := Ioo 0 t) (t := univ)
      (fun z : ℝ × ℝ => ENNReal.ofReal (G ν (t-z.1) (x-z.2) ^ 2) *
        momentFn P (fun s y ω => ρ (u s y ω)) 2 z.1 z.2)
      (hkernel.mul hmom).aemeasurable, Measure.restrict_univ,
      ← lintegral_sq_integralField hW hJ hν hI ht x, ItoIdentity.lintegral_enorm_sq]
    exact ENNReal.pow_lt_top (by simp)

end ChenDalang15.Picard

end
