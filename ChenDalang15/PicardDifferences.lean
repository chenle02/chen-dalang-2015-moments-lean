module

public import ChenDalang15.PicardMoments

/-!
# Successive differences of actual Picard iterates

Chen–Dalang (2015), proof of `T2:ExUni`, Step 3: the Itô identity for
two steps, the Lipschitz recurrence, and its iterated `𝓛ₙ`/`Bₙ` bounds.
The input is an actual sequence of Picard steps beginning at `J₀`, not a
fixed-point solution or an assumed bound on its differences.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.Stoch

open MeasureTheory ProbabilityTheory Set SolutionMoments
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Difference Itô identity for distinct Picard inputs and outputs. -/
theorem PicardStep.momentFn_sub_eq [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {μ : Measure ℝ}
    {v₁ v₂ u₁ u₂ : ℝ → ℝ → Ω → ℝ}
    (h₁ : PicardStep J ν ρ μ v₁ u₁) (h₂ : PicardStep J ν ρ μ v₂ u₂)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    momentFn P (fun s y ω => u₁ s y ω - u₂ s y ω) 2 t x =
      lstConv (momentFn P (fun s y ω => ρ (v₁ s y ω) - ρ (v₂ s y ω)) 2)
        (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x := by
  obtain ⟨I₁, hI₁, heq₁⟩ := h₁
  obtain ⟨I₂, hI₂, heq₂⟩ := h₂
  rw [← lintegral_sq_integralField_eq_lstConv hW hJ hν
    (isIntegralField_sub hI₁ hI₂) ht x, momentFn]
  simp_rw [ENNReal.rpow_two]
  refine lintegral_congr_ae ?_
  filter_upwards [heq₁ t ht x, heq₂ t ht x, Lp.coeFn_sub (I₁ t x) (I₂ t x)] with ω h₁ h₂ hsub
  rw [h₁, h₂, hsub, Pi.sub_apply]
  ring_nf

/-- The Lipschitz recurrence for differences of two actual steps. -/
theorem PicardStep.momentFn_sub_le [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {μ : Measure ℝ} {C : ℝ}
    (hρ : ∀ a b, |ρ a - ρ b| ≤ C * |a - b|)
    {v₁ v₂ u₁ u₂ : ℝ → ℝ → Ω → ℝ}
    (h₁ : PicardStep J ν ρ μ v₁ u₁) (h₂ : PicardStep J ν ρ μ v₂ u₂)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    momentFn P (fun s y ω => u₁ s y ω - u₂ s y ω) 2 t x ≤
      lstConv (momentFn P (fun s y ω => v₁ s y ω - v₂ s y ω) 2)
        (fun s y => ENNReal.ofReal (L ν C 0 s y)) t x := by
  rw [h₁.momentFn_sub_eq hW hJ hν h₂ ht x]
  exact MomentTheorems.lstConv_G_sq_le_lstConv_L_zero C
    (fun s _ y => momentFn_rho_sub_le hρ v₁ v₂ s y) x

/-- Subtracting `J₀` leaves exactly the step's stochastic integral. -/
theorem PicardStep.momentFn_sub_J0_eq [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {μ : Measure ℝ}
    {v u : ℝ → ℝ → Ω → ℝ} (hs : PicardStep J ν ρ μ v u)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    momentFn P (fun s y ω => u s y ω - J0 ν μ s y) 2 t x =
      lstConv (momentFn P (fun s y ω => ρ (v s y ω)) 2)
        (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x := by
  obtain ⟨I, hI, heq⟩ := hs
  rw [← lintegral_sq_integralField_eq_lstConv hW hJ hν hI ht x, momentFn]
  simp_rw [ENNReal.rpow_two]
  refine lintegral_congr_ae ?_
  filter_upwards [heq t ht x] with ω hω
  rw [hω]
  simp

/-- The first difference is controlled by growth, without a Lipschitz assumption. -/
theorem PicardStep.first_difference_le [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {μ : Measure ℝ} {C V : ℝ}
    (hρ : ∀ z, ρ z ^ 2 ≤ C ^ 2 * (V ^ 2 + z ^ 2))
    {u : ℝ → ℝ → Ω → ℝ} (hs : PicardStep J ν ρ μ (fun s y _ => J0 ν μ s y) u)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    momentFn P (fun s y ω => u s y ω - J0 ν μ s y) 2 t x ≤
      lstConv (Picard.source ν V μ) (fun s y => ENNReal.ofReal (L ν C 0 s y)) t x := by
  rw [hs.momentFn_sub_J0_eq hW hJ hν ht x]
  apply MomentTheorems.lstConv_G_sq_le_lstConv_L_zero C (x := x)
  intro s _ y
  have h := momentFn_rho_le (P := P) hρ (fun s y (_ : Ω) => J0 ν μ s y) s y
  simpa only [momentFn, enorm_rpow_two, lintegral_const, measure_univ, mul_one,
    Picard.source] using h

end ChenDalang15.Stoch

namespace ChenDalang15.Picard

open MeasureTheory ProbabilityTheory Set Stoch
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Iteration of the actual difference recurrence, manuscript Step 3. -/
theorem iterate_difference_le [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {μ : Measure ℝ} [SFinite μ] {C V : ℝ}
    (hgrowth : ∀ z, ρ z ^ 2 ≤ C ^ 2 * (V ^ 2 + z ^ 2))
    (hlip : ∀ a b, |ρ a - ρ b| ≤ C * |a - b|)
    (u : ℕ → ℝ → ℝ → Ω → ℝ) (hzero : u 0 = (fun t x _ => J0 ν μ t x))
    (hstep : ∀ n, PicardStep J ν ρ μ (u n) (u (n + 1))) :
    ∀ n t, 0 < t → ∀ x,
      momentFn P (fun s y ω => u (n + 1) s y ω - u n s y ω) 2 t x ≤
        lstConv (source ν V μ) (fun s y => ENNReal.ofReal (L ν C n s y)) t x := by
  intro n
  induction n with
  | zero =>
    intro t ht x
    have hs := hstep 0
    rw [hzero] at hs ⊢
    exact hs.first_difference_le hW hJ hν hgrowth ht x
  | succ n ih =>
    intro t ht x
    calc
      _ ≤ lstConv (momentFn P (fun s y ω => u (n + 1) s y ω - u n s y ω) 2)
          (fun s y => ENNReal.ofReal (L ν C 0 s y)) t x :=
        (hstep (n + 1)).momentFn_sub_le hW hJ hν hlip (hstep n) ht x
      _ ≤ lstConv (lstConv (source ν V μ) (fun s y => ENNReal.ofReal (L ν C n s y)))
          (fun s y => ENNReal.ofReal (L ν C 0 s y)) t x :=
        lstConv_mono_left (fun s hs y => ih s hs.1 y) x
      _ = _ := MomentTheorems.lstConv_lstConv_lL hν C (measurable_source ν V μ) n t x

/-- The summable-coefficient bound for actual successive differences. -/
theorem iterate_difference_le_BCoeff [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {μ : Measure ℝ} [SFinite μ] {C V : ℝ}
    (hgrowth : ∀ z, ρ z ^ 2 ≤ C ^ 2 * (V ^ 2 + z ^ 2))
    (hlip : ∀ a b, |ρ a - ρ b| ≤ C * |a - b|)
    (u : ℕ → ℝ → ℝ → Ω → ℝ) (hzero : u 0 = (fun t x _ => J0 ν μ t x))
    (hstep : ∀ n, PicardStep J ν ρ μ (u n) (u (n + 1)))
    (n : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    momentFn P (fun s y ω => u (n + 1) s y ω - u n s y ω) 2 t x ≤
      ENNReal.ofReal (BCoeff (bConst ν C) t n) *
        lstConv (source ν V μ) (fun s y => ENNReal.ofReal (L ν C 0 s y)) t x :=
  (iterate_difference_le hW hJ hν hgrowth hlip u hzero hstep n t ht x).trans
    (lstConv_ofReal_L_le_BCoeff_mul hν C n (source ν V μ) t x)

/-- The base convolution in the difference bound is finite for rough
Gaussian-tempered data. No division by its value is used. -/
theorem difference_base_lt_top {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν)
    (V C : ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    lstConv (source ν V μ) (fun s y => ENNReal.ofReal (L ν C 0 s y)) t x < ⊤ :=
  (lstConv_mono_right (fun r _ z => MomentTheorems.lL_zero_le_lK hν C r z) x).trans_lt
    (remainder_lt_top hT hν V C ht x)

end ChenDalang15.Picard

end
