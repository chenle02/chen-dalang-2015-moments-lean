module

public import ChenDalang15.PicardMajorant
public import ChenDalang15.S1Glue
public import Mathlib.Topology.Order.Compact

/-!
# Compact bounds for the actual Picard majorant

The rough-data estimate `L2:InDt` bounds the explicit Picard majorant by a
continuous real envelope. Compactness then bounds this envelope on each
positive-time rectangle. No continuity of the majorant or random field is
assumed. This is one deterministic ingredient of the `P2:Picard` continuity
argument, not yet continuity of a stochastic integral.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.S4CompactMajorant

open MeasureTheory Set
open scoped ENNReal Topology

/-- An explicit real envelope for `V² + majorant`, obtained from `L2:InDt`
and the closed expression for the spatially constant resolvent term. -/
def envelope (ν V C : ℝ) (μ : Measure ℝ) (t x : ℝ) : ℝ :=
  V ^ 2 + (J0 ν μ t x ^ 2 +
    C ^ 2 * Real.sqrt (Real.pi * t / ν) *
      (1 + 2 * Real.exp (C ^ 4 * t / (4 * ν))) * J0 ν μ (2 * t) x ^ 2 +
    V ^ 2 * (2 * Real.exp (C ^ 4 * t / (4 * ν)) *
      Phi (C ^ 2 * Real.sqrt (t / (2 * ν))) - 1))

/-- The genuine Gaussian-tempered integral bridge makes this a bound on the
actual lower-integral majorant, rather than a bound on a totalized integral. -/
theorem majorant_le_envelope {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν)
    (V C : ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ENNReal.ofReal (V ^ 2) + Picard.majorant ν V C μ t x ≤
      ENNReal.ofReal (envelope ν V C μ t x) := by
  have hnonneg : 0 ≤ secondMomentExpr (J0 ν μ) ν V C t x :=
    add_nonneg
      (add_nonneg (sq_nonneg _) (MomentBridge.stConv_J0_sq_K_nonneg hν μ C ht x))
      (mul_nonneg (sq_nonneg V) (MomentTheorems.Hfun_nonneg hν C ht.le))
  rw [Picard.majorant_eq_secondMomentExpr hT hν V C ht x,
    ← ENNReal.ofReal_add (sq_nonneg V) hnonneg]
  apply ENNReal.ofReal_le_ofReal
  unfold secondMomentExpr
  rw [show Hfun ν C t =
    2 * Real.exp (C ^ 4 * t / (4 * ν)) *
      Phi (C ^ 2 * Real.sqrt (t / (2 * ν))) - 1 from one_conv_K hν ht.le 0]
  dsimp only [envelope]
  linarith [L2_InDt_stConv hT hν ht C x]

/-- Joint continuity of the actual deterministic heat flow at positive time,
with the diffusivity retained through the explicit time-scaling bridge. -/
theorem continuousAt_J0 {μ : Measure ℝ}
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν)
    (z : ℝ × ℝ) (hz : 0 < z.1) :
    ContinuousAt (fun q : ℝ × ℝ => J0 ν μ q.1 q.2) z := by
  simp_rw [GrowthLower.J0_eq_heatFlow]
  have hmap : ContinuousAt (fun q : ℝ × ℝ => (ν * q.1, q.2)) z := by fun_prop
  exact ContinuousAt.comp
    (g := fun q : ℝ × ℝ => RoughHeatKernel.heatFlow μ q.1 q.2)
    (f := fun q : ℝ × ℝ => (ν * q.1, q.2))
    (RoughHeatKernel.continuousAt_heatFlow_joint hT (ν * z.1, z.2)
      (mul_pos hν hz)) hmap

/-- The envelope is jointly continuous on the positive-time half-plane. -/
theorem continuousAt_envelope {μ : Measure ℝ}
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν)
    (V C : ℝ) (z : ℝ × ℝ) (hz : 0 < z.1) :
    ContinuousAt (fun q : ℝ × ℝ => envelope ν V C μ q.1 q.2) z := by
  have hJ := continuousAt_J0 hT hν z hz
  have hmap : ContinuousAt (fun q : ℝ × ℝ => (2 * q.1, q.2)) z := by fun_prop
  have hJ2 : ContinuousAt (fun q : ℝ × ℝ => J0 ν μ (2 * q.1) q.2) z :=
    ContinuousAt.comp (g := fun q : ℝ × ℝ => J0 ν μ q.1 q.2)
      (f := fun q : ℝ × ℝ => (2 * q.1, q.2))
      (continuousAt_J0 hT hν (2 * z.1, z.2) (by positivity)) hmap
  have hPhi : Continuous Phi := continuous_Phi
  have hfactor : Continuous (fun q : ℝ × ℝ =>
      C ^ 2 * Real.sqrt (Real.pi * q.1 / ν) *
        (1 + 2 * Real.exp (C ^ 4 * q.1 / (4 * ν)))) := by fun_prop
  have hoffset : Continuous (fun q : ℝ × ℝ =>
      V ^ 2 * (2 * Real.exp (C ^ 4 * q.1 / (4 * ν)) *
        Phi (C ^ 2 * Real.sqrt (q.1 / (2 * ν))) - 1)) := by fun_prop
  unfold envelope
  exact continuousAt_const.add
    (((hJ.pow 2).add (hfactor.continuousAt.mul (hJ2.pow 2))).add hoffset.continuousAt)

set_option maxHeartbeats 800000 in
/-- Every positive-time compact rectangle has a finite uniform bound for
`V² + majorant`. The coefficient, offset and initial measure may vanish. -/
theorem exists_bound_rect {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν)
    (V C : ℝ) {a b R : ℝ} (ha : 0 < a) (_hab : a ≤ b) (_hR : 0 ≤ R) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ t ∈ Icc a b, ∀ x ∈ Icc (-R) R,
        ENNReal.ofReal (V ^ 2) + Picard.majorant ν V C μ t x ≤ B := by
  have hc : ContinuousOn (fun q : ℝ × ℝ => envelope ν V C μ q.1 q.2)
      (Icc a b ×ˢ Icc (-R) R) := by
    intro z hz
    exact (continuousAt_envelope hT hν V C z (ha.trans_le hz.1.1)).continuousWithinAt
  have hK : IsCompact (Icc a b ×ˢ Icc (-R) R) :=
    (isCompact_Icc : IsCompact (Icc a b)).prod
      (isCompact_Icc : IsCompact (Icc (-R) R))
  have hbounded : BddAbove
      ((fun q : ℝ × ℝ => envelope ν V C μ q.1 q.2) ''
        (Icc a b ×ˢ Icc (-R) R)) := hK.bddAbove_image hc
  obtain ⟨M, hM⟩ := hbounded
  refine ⟨ENNReal.ofReal M, ENNReal.ofReal_lt_top, ?_⟩
  intro t ht x hx
  have hm : envelope ν V C μ t x ≤ M := hM ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  exact (majorant_le_envelope hT hν V C (ha.trans_le ht.1) x).trans
    (ENNReal.ofReal_le_ofReal hm)

end ChenDalang15.S4CompactMajorant

end
