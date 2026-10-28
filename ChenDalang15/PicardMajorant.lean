module

public import ChenDalang15.PicardDefs
public import ChenDalang15.MomentTheorems

/-!
# The finite, forward-invariant Picard moment majorant

Deterministic part of Chen–Dalang (2015), proof of `T2:ExUni`, Steps 1–2,
especially `E2_:step2Mp` at `p = 2`. The resolvent identity proves that one
Picard moment estimate preserves this explicit majorant. No random field or
assumed moment bound enters these deterministic statements.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.Picard

open MeasureTheory
open scoped ENNReal

/-- The deterministic source is jointly measurable, including nonpositive times. -/
theorem measurable_source (ν V : ℝ) (μ : Measure ℝ) [SFinite μ] :
    Measurable (Function.uncurry (source ν V μ)) :=
  measurable_const.add (((Stoch.measurable_J0_uncurry ν μ).pow_const 2).ennreal_ofReal)

/-- The resolvent contribution is jointly measurable. -/
theorem measurable_remainder {ν : ℝ} (hν : 0 < ν) (V Lip : ℝ)
    (μ : Measure ℝ) [SFinite μ] :
    Measurable (Function.uncurry (remainder ν V Lip μ)) :=
  measurable_lstConv (measurable_source ν V μ) (MomentTheorems.measurable_lK hν Lip)

/-- The full candidate bound is jointly measurable. -/
theorem measurable_majorant {ν : ℝ} (hν : 0 < ν) (V Lip : ℝ)
    (μ : Measure ℝ) [SFinite μ] :
    Measurable (Function.uncurry (majorant ν V Lip μ)) :=
  (((Stoch.measurable_J0_uncurry ν μ).pow_const 2).ennreal_ofReal).add
    (measurable_remainder hν V Lip μ)

/-- The source is finite as a real-valued expression. Gaussian tempering is
needed below for the convolution, not for this literal finiteness statement. -/
theorem source_lt_top (ν V : ℝ) (μ : Measure ℝ) (t x : ℝ) :
    source ν V μ t x < ⊤ :=
  ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

/-- The candidate majorant equals the paper's second-moment expression. The
Gaussian-tempered integral bridge ensures this is not Bochner totalization. -/
theorem majorant_eq_secondMomentExpr {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν)
    (V Lip : ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    majorant ν V Lip μ t x =
      ENNReal.ofReal (secondMomentExpr (J0 ν μ) ν V Lip t x) :=
  MomentTheorems.J0_sq_add_lstConv_eq_secondMomentExpr hT hν V Lip ht x

/-- The majorant is finite for Gaussian-tempered data at positive times. -/
theorem majorant_lt_top {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν)
    (V Lip : ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    majorant ν V Lip μ t x < ⊤ := by
  rw [majorant_eq_secondMomentExpr hT hν V Lip ht x]
  exact ENNReal.ofReal_lt_top

/-- The resolvent contribution is finite for Gaussian-tempered data. -/
theorem remainder_lt_top {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν)
    (V Lip : ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    remainder ν V Lip μ t x < ⊤ :=
  (le_add_left (le_refl (remainder ν V Lip μ t x))).trans_lt
    (majorant_lt_top hT hν V Lip ht x)

/-- The additive resolvent makes the explicit majorant forward invariant.
This holds as an identity of lower integrals at every time and needs no
tempering or subtraction of potentially infinite quantities. -/
theorem majorant_forward_invariant {ν : ℝ} (hν : 0 < ν) (V Lip : ℝ)
    (μ : Measure ℝ) [SFinite μ] (t x : ℝ) :
    lstConv (fun s y => ENNReal.ofReal (V ^ 2) + majorant ν V Lip μ s y)
      (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) t x = remainder ν V Lip μ t x := by
  let k := fun s y => ENNReal.ofReal (K ν Lip s y)
  let l := fun s y => ENNReal.ofReal (L ν Lip 0 s y)
  have hk : Measurable (Function.uncurry k) := MomentTheorems.measurable_lK hν Lip
  have hl : Measurable (Function.uncurry l) := MomentTheorems.measurable_lL hν Lip 0
  have hs := measurable_source ν V μ
  have hsum : (fun s y => ENNReal.ofReal (V ^ 2) + majorant ν V Lip μ s y) =
      source ν V μ + lstConv (source ν V μ) k := by
    funext s y
    simp only [source, majorant, remainder, Pi.add_apply, k, add_assoc]
  rw [hsum, lstConv_add_left hs hl,
    lstConv_assoc hs hk hl, ← lstConv_add_right hs hl]
  have hres : l + lstConv k l = k := by
    funext s y
    exact (add_comm _ _).trans (lstConv_ofReal_K_L_zero_add hν Lip s y)
  change lstConv (source ν V μ) (l + lstConv k l) t x = _
  rw [hres]
  rfl

end ChenDalang15.Picard

end
