module

public import ChenDalang15.PicardDifferences
public import ChenDalang15.PicardSummability
public import ChenDalang15.HeatCausalKernel

/-!
# Stability of actual Picard steps under pointwise L² convergence

The explicit finite majorant supplies domination for the input convolution.
No weighted convergence or fixed-point equation is assumed. Almost-sure
equalities remain separate at each positive time-space point.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ChenDalang15.Picard

open MeasureTheory ProbabilityTheory Set Filter Stoch
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Global joint measurability gives joint measurability of the second moment. -/
theorem measurable_momentFn_two [SFinite P] (v : ℝ → ℝ → Ω → ℝ)
    (hv : Measurable (fun q : ℝ × ℝ × Ω => v q.1 q.2.1 q.2.2)) :
    Measurable (Function.uncurry (momentFn P v 2)) := by
  have hm : Measurable (fun q : (ℝ × ℝ) × Ω => ‖v q.1.1 q.1.2 q.2‖ₑ ^ (2 : ℝ)) :=
    (hv.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_snd))).enorm.pow_const _
  exact hm.lintegral_prod_right'

/-- The majorant dominates a convolution limit without assuming convergence
in a weighted norm. The additive resolvent supplies its integrable envelope. -/
theorem lstConv_tendsto_zero_of_majorant {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (V C : ℝ)
    (f : ℕ → ℝ → ℝ → ℝ≥0∞)
    (hf : ∀ n, Measurable (Function.uncurry (f n)))
    (hb : ∀ n s, 0 < s → ∀ y, f n s y ≤ 4 * majorant ν V C μ s y)
    (hlim : ∀ s > 0, ∀ y, Tendsto (fun n => f n s y) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Tendsto (fun n => lstConv (f n) (fun s y => ENNReal.ofReal (L ν C 0 s y)) t x)
      atTop (𝓝 0) := by
  let l := fun s y => ENNReal.ofReal (L ν C 0 s y)
  let b := fun s y => 4 * majorant ν V C μ s y
  have hl : Measurable (Function.uncurry l) := MomentTheorems.measurable_lL hν C 0
  have hbm : Measurable (Function.uncurry b) :=
    measurable_const.mul (measurable_majorant hν V C μ)
  have hfin : lstConv b l t x < ⊤ := by
    rw [show b = fun s y => 4 * majorant ν V C μ s y from rfl,
      lstConv_const_mul_left _ _ (by norm_num)]
    apply ENNReal.mul_lt_top (by norm_num)
    apply lt_of_le_of_lt (lstConv_mono_left (fun s _ y =>
      le_add_left (le_refl (majorant ν V C μ s y))) x)
    rw [majorant_forward_invariant hν V C μ t x]
    exact remainder_lt_top hT hν V C ht x
  have heq (n : ℕ) := lstConv_eq_lconvolution (hf n) hl t x
  change Tendsto (fun n => lstConv (f n) l t x) atTop (𝓝 0)
  simp_rw [heq, lconvolution_def]
  have hbfin : (∫⁻ q : ℝ × ℝ, LConv.cut b q * LConv.cut l (-q + (t,x))) ≠ ⊤ := by
    simpa only [lstConv_eq_lconvolution hbm hl t x, lconvolution_def] using hfin.ne
  have hh := tendsto_lintegral_of_dominated_convergence
    (μ := (volume : Measure (ℝ × ℝ)))
    (fun q => LConv.cut b q * LConv.cut l (-q + (t,x)))
    (F := fun n q => LConv.cut (f n) q * LConv.cut l (-q + (t,x)))
    (f := fun _ => 0)
  apply (show (∫⁻ _ : ℝ × ℝ, (0 : ℝ≥0∞)) = 0 by simp) ▸ hh
  · intro n
    exact (LConv.measurable_cut (hf n)).mul
      ((LConv.measurable_cut hl).comp (by fun_prop))
  · intro n
    refine Eventually.of_forall fun q => ?_
    have hcut : LConv.cut (f n) q ≤ LConv.cut b q := by
      by_cases hs : 0 < q.1
      · simpa only [LConv.cut, hs, ite_true, b] using hb n q.1 hs q.2
      · simp only [LConv.cut, hs, ite_false, le_refl]
    exact mul_le_mul_left hcut _
  · exact hbfin
  · refine Eventually.of_forall fun q => ?_
    have hc : Tendsto (fun n => LConv.cut (f n) q) atTop (𝓝 0) := by
      by_cases hs : 0 < q.1
      · simpa only [LConv.cut, hs, ite_true] using hlim q.1 hs q.2
      · simp only [LConv.cut, hs, ite_false]; exact tendsto_const_nhds
    have hn : LConv.cut l (-q + (t,x)) ≠ ⊤ := by
      unfold LConv.cut l
      split_ifs <;> simp
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hc (Or.inr hn)

/-- Stability of the actual Picard map: bounded, jointly measurable inputs
converging pointwise in L² have outputs converging pointwise in L². -/
theorem step_tendsto_L2 [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ρ : ℝ → ℝ} {V C : ℝ}
    (hρ : ∀ a b, |ρ a - ρ b| ≤ C * |a - b|)
    (v w : ℕ → ℝ → ℝ → Ω → ℝ) (vlim wlim : ℝ → ℝ → Ω → ℝ)
    (hv : ∀ n, Measurable (fun q : ℝ × ℝ × Ω => v n q.1 q.2.1 q.2.2))
    (hvl : Measurable (fun q : ℝ × ℝ × Ω => vlim q.1 q.2.1 q.2.2))
    (hb : ∀ n s, 0 < s → ∀ y, momentFn P (v n) 2 s y ≤ majorant ν V C μ s y)
    (hbl : ∀ s > 0, ∀ y, momentFn P vlim 2 s y ≤ majorant ν V C μ s y)
    (hs : ∀ n, PicardStep J ν ρ μ (v n) (w n))
    (hsl : PicardStep J ν ρ μ vlim wlim)
    (hlim : ∀ s > 0, ∀ y,
      Tendsto (fun n => eLpNorm (fun ω => v n s y ω - vlim s y ω) 2 P) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Tendsto (fun n => eLpNorm (fun ω => w n t x ω - wlim t x ω) 2 P) atTop (𝓝 0) := by
  let d := fun n s y ω => v n s y ω - vlim s y ω
  have hd (n : ℕ) : Measurable (fun q : ℝ × ℝ × Ω => d n q.1 q.2.1 q.2.2) :=
    (hv n).sub hvl
  have hdsec (n : ℕ) (s y : ℝ) : AEStronglyMeasurable (d n s y) P :=
    ((hd n).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  have hmom (n : ℕ) (s y : ℝ) : momentFn P (d n) 2 s y = eLpNorm (d n s y) 2 P ^ 2 := by
    rw [eLpNorm_two_sq_eq_lintegral (hdsec n s y)]
    simp only [momentFn, SolutionMoments.enorm_rpow_two]
  have hconv := lstConv_tendsto_zero_of_majorant hT hν V C
    (fun n => momentFn P (d n) 2)
    (fun n => measurable_momentFn_two (d n) (hd n))
    (fun n s hs' y => by
      have hvm : Measurable (v n s y) :=
        (hv n).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      calc
        _ ≤ 2 * (momentFn P (v n) 2 s y + momentFn P vlim 2 s y) :=
          SolutionMoments.momentFn_sub_le_two_mul hvm
        _ ≤ 2 * (majorant ν V C μ s y + majorant ν V C μ s y) := by
          gcongr
          · exact hb n s hs' y
          · exact hbl s hs' y
        _ = 4 * majorant ν V C μ s y := by ring)
    (fun s hs' y => by
      simp_rw [hmom]
      simpa only [zero_pow two_ne_zero] using ENNReal.Tendsto.pow (n := 2) (hlim s hs' y)) ht x
  have houtmeas (n : ℕ) : AEStronglyMeasurable (fun ω => w n t x ω - wlim t x ω) P := by
    obtain ⟨I, hI, heq⟩ := hs n
    obtain ⟨Il, hIl, heql⟩ := hsl
    exact ((aestronglyMeasurable_const.add (Lp.aestronglyMeasurable (I t x))).sub
      (aestronglyMeasurable_const.add (Lp.aestronglyMeasurable (Il t x)))).congr
        ((heq t ht x).sub (heql t ht x)).symm
  have hbound (n : ℕ) := (hs n).momentFn_sub_le hW hJ hν hρ hsl ht x
  have hnorm (n : ℕ) : eLpNorm (fun ω => w n t x ω - wlim t x ω) 2 P ≤
      (lstConv (momentFn P (d n) 2) (fun s y => ENNReal.ofReal (L ν C 0 s y)) t x) ^ (1/2 : ℝ) := by
    have hh := eLpNorm_two_le_of_moment_bound (houtmeas n) (a := 1) zero_le_one
      (by simpa only [ENNReal.ofReal_one, one_mul, momentFn] using hbound n)
    simpa using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n => (lstConv (momentFn P (d n) 2)
      (fun s y => ENNReal.ofReal (L ν C 0 s y)) t x) ^ (1/2 : ℝ)) atTop (𝓝 0) from ?_)
    (fun n => bot_le) hnorm
  simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)] using
    (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).tendsto 0 |>.comp hconv

end ChenDalang15.Picard
end
