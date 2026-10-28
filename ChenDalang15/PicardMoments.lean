module

public import ChenDalang15.PicardDefs
public import ChenDalang15.PicardMajorant
public import ChenDalang15.SolutionMoments

/-!
# Itô moment identity for a Picard step

Unlike the solution renewal identity, the input and output are different fields.
This is the p = 2 calculation in Steps 1–2 of the proof of `T2:ExUni`; it does
not assume a fixed point or a moment bound for the output.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.Stoch

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The actual second moment of the output of a Picard step is the deterministic
square plus the convolution of the input coefficient's second moment with `G²`.
No existence or continuity of a fixed-point solution is assumed. -/
theorem PicardStep.momentFn_two_eq [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {μ : Measure ℝ}
    {v u : ℝ → ℝ → Ω → ℝ} (hstep : PicardStep J ν ρ μ v u)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    momentFn P u 2 t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (momentFn P (fun s y ω => ρ (v s y ω)) 2)
        (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x := by
  obtain ⟨I, hI, heq⟩ := hstep
  obtain ⟨g, -, hIg⟩ := hI t ht x
  have h0 : ∫ ω, I t x ω ∂P = 0 := by
    rw [hIg]
    exact walshMeanZero_of_isWalshIntegral hW.whiteNoise hJ g
  rw [← lintegral_sq_integralField_eq_lstConv hW hJ hν hI ht x,
    ← ItoIdentity.lintegral_sq_const_add _ _ h0, momentFn]
  simp_rw [ENNReal.rpow_two]
  exact lintegral_congr_ae ((heq t ht x).mono fun ω h => by beta_reduce at h ⊢; rw [h])

/-- Quadratic coefficient growth bounds the next iterate by convolution of the
previous iterate's moment. This estimate does not use a fixed-point solution. -/
theorem PicardStep.momentFn_two_le [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {μ : Measure ℝ} {Lip V : ℝ}
    (hρ : ∀ z, ρ z ^ 2 ≤ Lip ^ 2 * (V ^ 2 + z ^ 2))
    {v u : ℝ → ℝ → Ω → ℝ} (hstep : PicardStep J ν ρ μ v u)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    momentFn P u 2 t x ≤ ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (fun s y => ENNReal.ofReal (V ^ 2) + momentFn P v 2 s y)
        (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) t x := by
  rw [hstep.momentFn_two_eq hW hJ hν ht x]
  refine add_le_add le_rfl ?_
  unfold lstConv
  refine setLIntegral_mono' measurableSet_Ioo fun s _ => lintegral_mono fun y => ?_
  calc
    _ ≤ (ENNReal.ofReal (Lip ^ 2) *
        (ENNReal.ofReal (V ^ 2) + momentFn P v 2 s y)) *
        ENNReal.ofReal (G ν (t - s) (x - y) ^ 2) :=
      mul_le_mul_left (SolutionMoments.momentFn_rho_le hρ v s y) _
    _ = _ := by
      simp only [L, ENNReal.ofReal_mul (sq_nonneg Lip)]
      ring

/-- The explicit deterministic majorant is preserved by an actual Picard step.
The input bound is an induction hypothesis, not a fixed-point assumption. -/
theorem PicardStep.preserves_majorant [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {μ : Measure ℝ} [SFinite μ] {Lip V : ℝ}
    (hρ : ∀ z, ρ z ^ 2 ≤ Lip ^ 2 * (V ^ 2 + z ^ 2))
    {v u : ℝ → ℝ → Ω → ℝ} (hstep : PicardStep J ν ρ μ v u)
    (hv : ∀ s > 0, ∀ y, momentFn P v 2 s y ≤ Picard.majorant ν V Lip μ s y)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    momentFn P u 2 t x ≤ Picard.majorant ν V Lip μ t x := by
  calc
    _ ≤ ENNReal.ofReal (J0 ν μ t x ^ 2) +
        lstConv (fun s y => ENNReal.ofReal (V ^ 2) + momentFn P v 2 s y)
          (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) t x :=
      hstep.momentFn_two_le hW hJ hν hρ ht x
    _ ≤ ENNReal.ofReal (J0 ν μ t x ^ 2) +
        lstConv (fun s y => ENNReal.ofReal (V ^ 2) + Picard.majorant ν V Lip μ s y)
          (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) t x := by
      refine add_le_add le_rfl (lstConv_mono_left (fun s hs y => ?_) x)
      exact add_le_add le_rfl (hv s hs.1 y)
    _ = _ := by
      rw [Picard.majorant_forward_invariant hν V Lip μ t x]
      rfl

end ChenDalang15.Stoch

end
