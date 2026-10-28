module

public import ChenDalang15.GrowthDefs
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The exponential growth-index API (Chen–Dalang 2015, Section 5)

Tools that turn pointwise envelopes of a moment function `f(t,x)` into bounds on the growth
indices `λ̲`, `λ̄` of `ChenDalang15/GrowthDefs.lean`:

* `tailRate_antitone`: the tail rate is antitone in `α`;
* `upperGrowthIndex_le_of_envelope`: `f ≤ A e^{γt − 2β|x|}` gives `λ̄ ≤ max(γ/(2β), 0)`;
* `le_lowerGrowthIndex_of_gaussian_envelope`: `f ≥ (c/t) e^{γt} G_ξ(t,x)` gives
  `λ̲ ≥ √(2γξ)`;
* `growthIndices_eq_top_of_uniform_growth`: `f ≥ c e^{γt}` uniformly gives `λ̲ = λ̄ = +∞`;
* `L2_Growth` (paper Lemma `L2:Growth`, Conus–Khoshnevisan): both indices of `E|X|^p` are
  nondecreasing in `p`;
* `upperGrowthIndex_le_piecewise`: the final optimisation over `β` in the proof of
  Theorem `T2:Growth` (2).

Every case of the proof of Theorem `T2:Growth` (1)–(2) ends with one of these lemmas.
-/

set_option autoImplicit false

public section

open scoped ENNReal Topology
open Filter

namespace ChenDalang15

namespace GrowthIndex

variable {f : ℝ → ℝ → ℝ≥0∞}

/-- A point of the tail region bounds the tail supremum from below. -/
theorem le_tailSup {α t x : ℝ} (h : α * t ≤ |x|) : f t x ≤ tailSup f α t :=
  le_iSup₂ (f := fun x (_ : α * t ≤ |x|) => f t x) x h

/-- For `t ≥ 0` the tail supremum is antitone in `α`. -/
theorem tailSup_anti {α α' t : ℝ} (hα : α ≤ α') (ht : 0 ≤ t) :
    tailSup f α' t ≤ tailSup f α t :=
  iSup₂_le fun _ hx => le_tailSup ((mul_le_mul_of_nonneg_right hα ht).trans hx)

/-- `t⁻¹ log (ofReal y) = t⁻¹ log y` in `EReal` for `y > 0`. -/
theorem coe_inv_mul_log_ofReal {t y : ℝ} (hy : 0 < y) :
    ((t⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal y) = ((t⁻¹ * Real.log y : ℝ) : EReal) := by
  rw [ENNReal.log_ofReal_of_pos hy, ← EReal.coe_mul]

/-- Multiplication by `t⁻¹ ≥ 0` is monotone. -/
theorem inv_mul_log_le_inv_mul_log {t : ℝ} (ht : 0 < t) {a b : ℝ≥0∞} (h : a ≤ b) :
    ((t⁻¹ : ℝ) : EReal) * ENNReal.log a ≤ ((t⁻¹ : ℝ) : EReal) * ENNReal.log b :=
  mul_le_mul_of_nonneg_left (ENNReal.log_le_log h) (by exact_mod_cast (inv_pos.2 ht).le)

/-- Upper bound on the tail rate from an eventual envelope `tailSup ≤ g(t)` with
`t⁻¹ log g(t) → c`. -/
theorem tailRate_le_of_eventually {α c : ℝ} {g : ℝ → ℝ} (hpos : ∀ᶠ t in atTop, 0 < g t)
    (hle : ∀ᶠ t in atTop, tailSup f α t ≤ ENNReal.ofReal (g t))
    (hlim : Tendsto (fun t => t⁻¹ * Real.log (g t)) atTop (𝓝 c)) :
    tailRate f α ≤ c := by
  have h2 : Tendsto (fun t => ((t⁻¹ * Real.log (g t) : ℝ) : EReal)) atTop (𝓝 (c : EReal)) :=
    EReal.tendsto_coe.2 hlim
  rw [tailRate, ← h2.limsup_eq]
  refine Filter.limsup_le_limsup ?_
  filter_upwards [hpos, hle, eventually_gt_atTop 0] with t h1 h2 ht
  rw [← coe_inv_mul_log_ofReal h1]
  exact inv_mul_log_le_inv_mul_log ht h2

/-- Lower bound on the tail rate from an eventual minorant `g(t) ≤ tailSup` with
`t⁻¹ log g(t) → c`. -/
theorem le_tailRate_of_eventually {α c : ℝ} {g : ℝ → ℝ} (hpos : ∀ᶠ t in atTop, 0 < g t)
    (hle : ∀ᶠ t in atTop, ENNReal.ofReal (g t) ≤ tailSup f α t)
    (hlim : Tendsto (fun t => t⁻¹ * Real.log (g t)) atTop (𝓝 c)) :
    (c : EReal) ≤ tailRate f α := by
  have h2 : Tendsto (fun t => ((t⁻¹ * Real.log (g t) : ℝ) : EReal)) atTop (𝓝 (c : EReal)) :=
    EReal.tendsto_coe.2 hlim
  rw [tailRate, ← h2.limsup_eq]
  refine Filter.limsup_le_limsup ?_
  filter_upwards [hpos, hle, eventually_gt_atTop 0] with t h1 h2 ht
  rw [← coe_inv_mul_log_ofReal h1]
  exact inv_mul_log_le_inv_mul_log ht h2

/-- An admissible `α` lies below the lower index. -/
theorem coe_le_lowerGrowthIndex {α : ℝ} (hα : 0 < α) (h : 0 < tailRate f α) :
    (α : EReal) ≤ lowerGrowthIndex f :=
  le_sSup ⟨α, ⟨hα, h⟩, rfl⟩

/-- An admissible `α` lies above the upper index. -/
theorem upperGrowthIndex_le_coe {α : ℝ} (hα : 0 < α) (h : tailRate f α < 0) :
    upperGrowthIndex f ≤ (α : EReal) :=
  sInf_le ⟨α, ⟨hα, h⟩, rfl⟩

/-- If every `α ∈ (0, s)` has positive tail rate, then `s ≤ λ̲`. -/
theorem le_lowerGrowthIndex_of_forall {s : EReal} (hs : 0 < s)
    (h : ∀ α : ℝ, 0 < α → (α : EReal) < s → 0 < tailRate f α) : s ≤ lowerGrowthIndex f := by
  refine le_of_forall_lt_imp_le_of_dense fun a ha => ?_
  induction a using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd ha (not_lt.2 le_top)
  | coe a =>
    rcases lt_or_ge 0 a with ha0 | ha0
    · exact coe_le_lowerGrowthIndex ha0 (h a ha0 ha)
    · obtain ⟨b, hb0, hbs⟩ := EReal.lt_iff_exists_real_btwn.1 hs
      have hb0' : (0 : ℝ) < b := by exact_mod_cast hb0
      exact (EReal.coe_le_coe_iff.2 (ha0.trans hb0'.le)).trans
        (coe_le_lowerGrowthIndex hb0' (h b hb0' hbs))

/-- If every real `α > s` has negative tail rate, then `λ̄ ≤ s`. -/
theorem upperGrowthIndex_le_of_forall {s : EReal} (hs : 0 ≤ s)
    (h : ∀ α : ℝ, s < (α : EReal) → tailRate f α < 0) : upperGrowthIndex f ≤ s := by
  refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
  induction a using EReal.rec with
  | bot => exact absurd ha (not_lt.2 bot_le)
  | top => exact le_top
  | coe a =>
    have ha0 : (0 : ℝ) < a := by exact_mod_cast hs.trans_lt ha
    exact upperGrowthIndex_le_coe ha0 (h a ha)

/-- `t⁻¹ log (C e^{κ t}) → κ`. -/
theorem tendsto_inv_mul_log_mul_exp {C κ : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ => t⁻¹ * Real.log (C * Real.exp (κ * t))) atTop (𝓝 κ) := by
  have h1 : Tendsto (fun t : ℝ => t⁻¹ * Real.log C + κ) atTop (𝓝 (0 * Real.log C + κ)) :=
    (tendsto_inv_atTop_zero.mul_const _).add_const _
  rw [zero_mul, zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp]
  field_simp

/-- `log t / t → 0`, in the form `t⁻¹ * log t → 0`. -/
theorem tendsto_inv_mul_log : Tendsto (fun t : ℝ => t⁻¹ * Real.log t) atTop (𝓝 0) := by
  refine Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.congr' ?_
  filter_upwards with t
  simp [div_eq_inv_mul]

end GrowthIndex

open GrowthIndex

/-- Target 1: the tail rate `α ↦ limsup t⁻¹ log sup_{|x| ≥ αt} f(t,x)` is antitone. -/
theorem tailRate_antitone (f : ℝ → ℝ → ℝ≥0∞) : Antitone (tailRate f) := by
  intro α α' hα
  refine Filter.limsup_le_limsup ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact inv_mul_log_le_inv_mul_log ht (tailSup_anti hα ht.le)

/-- Target 2: an envelope `f(t,x) ≤ A e^{γt − 2β|x|}` (for large `t`) gives
`λ̄ ≤ max(γ/(2β), 0)`. -/
theorem upperGrowthIndex_le_of_envelope {f : ℝ → ℝ → ℝ≥0∞} {β γ A : ℝ} (hβ : 0 < β)
    (h : ∃ T₀, ∀ t ≥ T₀, ∀ x, f t x ≤ ENNReal.ofReal (A * Real.exp (γ * t - 2 * β * |x|))) :
    upperGrowthIndex f ≤ ((max (γ / (2 * β)) 0 : ℝ) : EReal) := by
  obtain ⟨T₀, hT⟩ := h
  refine upperGrowthIndex_le_of_forall (by exact_mod_cast le_max_right _ _) fun α hα => ?_
  have hα' : max (γ / (2 * β)) 0 < α := by exact_mod_cast hα
  have hα0 : 0 < α := (le_max_right _ _).trans_lt hα'
  have hκ : γ - 2 * β * α < 0 := by
    have := (le_max_left _ _).trans_lt hα'
    rw [div_lt_iff₀ (by positivity)] at this
    linarith
  have hC : (0 : ℝ) < |A| + 1 := by positivity
  have key := tailRate_le_of_eventually (f := f) (α := α)
    (g := fun t => (|A| + 1) * Real.exp ((γ - 2 * β * α) * t))
    (Eventually.of_forall fun t => by positivity) ?_ (tendsto_inv_mul_log_mul_exp hC)
  · exact key.trans_lt (by exact_mod_cast hκ)
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop 0] with t hT₀ ht
  refine iSup₂_le fun x hx => (hT t hT₀ x).trans (ENNReal.ofReal_le_ofReal ?_)
  have he : Real.exp (γ * t - 2 * β * |x|) ≤ Real.exp ((γ - 2 * β * α) * t) := by
    apply Real.exp_le_exp.2
    nlinarith
  calc A * Real.exp (γ * t - 2 * β * |x|) ≤ |A| * Real.exp (γ * t - 2 * β * |x|) :=
        mul_le_mul_of_nonneg_right (le_abs_self A) (Real.exp_pos _).le
    _ ≤ (|A| + 1) * Real.exp ((γ - 2 * β * α) * t) :=
        mul_le_mul (by linarith) he (Real.exp_pos _).le (by positivity)

/-- Target 3: a Gaussian minorant `f(t,x) ≥ (c/t) e^{γt} G_ξ(t,x)` gives `λ̲ ≥ √(2γξ)`. -/
theorem le_lowerGrowthIndex_of_gaussian_envelope {f : ℝ → ℝ → ℝ≥0∞} {γ ξ c : ℝ}
    (hγ : 0 < γ) (hξ : 0 < ξ) (hc : 0 < c)
    (h : ∃ T₀ > 0, ∀ t ≥ T₀, ∀ x,
      ENNReal.ofReal (c / t * Real.exp (γ * t) * G ξ t x) ≤ f t x) :
    ((Real.sqrt (2 * γ * ξ) : ℝ) : EReal) ≤ lowerGrowthIndex f := by
  obtain ⟨T₀, -, hT⟩ := h
  refine le_lowerGrowthIndex_of_forall (by exact_mod_cast Real.sqrt_pos.2 (by positivity))
    fun α hα0 hα => ?_
  have hα' : α < Real.sqrt (2 * γ * ξ) := by exact_mod_cast hα
  have hsq : α ^ 2 < 2 * γ * ξ := by
    have := (Real.lt_sqrt hα0.le).1 hα'
    linarith
  have hrate : 0 < γ - α ^ 2 / (2 * ξ) := by
    rw [sub_pos, div_lt_iff₀ (by positivity)]
    linarith
  set g : ℝ → ℝ := fun t => c / t * Real.exp (γ * t) * G ξ t (α * t) with hg
  have hgpos : ∀ t, 0 < t → 0 < g t := by
    intro t ht
    simp only [hg, G]
    have : 0 < Real.sqrt (2 * Real.pi * ξ * t) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hlim : Tendsto (fun t => t⁻¹ * Real.log (g t)) atTop (𝓝 (γ - α ^ 2 / (2 * ξ))) := by
    have h1 : Tendsto (fun t : ℝ => t⁻¹ * (Real.log c - Real.log (2 * Real.pi * ξ) / 2)
        - 3 / 2 * (t⁻¹ * Real.log t) + (γ - α ^ 2 / (2 * ξ))) atTop
        (𝓝 (0 * (Real.log c - Real.log (2 * Real.pi * ξ) / 2) - 3 / 2 * 0
          + (γ - α ^ 2 / (2 * ξ)))) :=
      (((tendsto_inv_atTop_zero.mul_const _).sub
        (tendsto_inv_mul_log.const_mul _)).add_const _)
    simp only [zero_mul, mul_zero, sub_zero, zero_add] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have h2 : (0 : ℝ) < 2 * Real.pi * ξ := by positivity
    have hs : 0 < Real.sqrt (2 * Real.pi * ξ * t) := Real.sqrt_pos.2 (by positivity)
    have hlog : Real.log (g t) = Real.log c - Real.log t + γ * t
        - (Real.log (2 * Real.pi * ξ) + Real.log t) / 2 - α ^ 2 / (2 * ξ) * t := by
      simp only [hg, G]
      have e1 : (0 : ℝ) < c / t := by positivity
      have e2 : (0 : ℝ) < 1 / Real.sqrt (2 * Real.pi * ξ * t) := by positivity
      rw [Real.log_mul (x := c / t * Real.exp (γ * t)) (by positivity) (by positivity),
        Real.log_mul (x := c / t) e1.ne' (Real.exp_pos _).ne',
        Real.log_mul (x := 1 / Real.sqrt (2 * Real.pi * ξ * t)) e2.ne' (Real.exp_pos _).ne',
        Real.log_div hc.ne' ht.ne', Real.log_exp, Real.log_exp, one_div, Real.log_inv,
        Real.log_sqrt (by positivity), Real.log_mul (x := 2 * Real.pi * ξ) h2.ne' ht.ne']
      field_simp
      ring
    rw [hlog]
    field_simp
    ring
  have key := le_tailRate_of_eventually (f := f) (α := α) (g := g)
    ((eventually_gt_atTop 0).mono hgpos) ?_ hlim
  · exact lt_of_lt_of_le (by exact_mod_cast hrate) key
  filter_upwards [eventually_ge_atTop T₀, eventually_gt_atTop 0] with t hT₀ ht
  exact (hT t hT₀ (α * t)).trans (le_tailSup (le_abs_self _))

/-- Target 4: uniform exponential growth `f(t,x) ≥ c e^{γt}` gives `λ̲ = λ̄ = +∞`. -/
theorem growthIndices_eq_top_of_uniform_growth {f : ℝ → ℝ → ℝ≥0∞} {c γ : ℝ}
    (hc : 0 < c) (hγ : 0 < γ)
    (h : ∃ T₀, ∀ t ≥ T₀, ∀ x, ENNReal.ofReal (c * Real.exp (γ * t)) ≤ f t x) :
    lowerGrowthIndex f = ⊤ ∧ upperGrowthIndex f = ⊤ := by
  obtain ⟨T₀, hT⟩ := h
  have hrate : ∀ α : ℝ, 0 < tailRate f α := by
    intro α
    have key := le_tailRate_of_eventually (f := f) (α := α)
      (g := fun t => c * Real.exp (γ * t)) (Eventually.of_forall fun t => by positivity) ?_
      (tendsto_inv_mul_log_mul_exp hc)
    · exact lt_of_lt_of_le (by exact_mod_cast hγ) key
    filter_upwards [eventually_ge_atTop T₀] with t hT₀
    exact (hT t hT₀ (α * t)).trans (le_tailSup (le_abs_self _))
  refine ⟨top_le_iff.1 (le_lowerGrowthIndex_of_forall (by simp) fun α _ _ => hrate α), ?_⟩
  have hempty : {α : ℝ | 0 < α ∧ tailRate f α < 0} = ∅ :=
    Set.eq_empty_of_forall_notMem fun α hα => (hrate α).not_gt hα.2
  rw [upperGrowthIndex, hempty, Set.image_empty, sInf_empty]

/-- Lyapunov's inequality `E|Y|^a ≤ (E|Y|^b)^{a/b}` for `0 < a ≤ b` under a probability
measure. -/
theorem GrowthIndex.lintegral_rpow_le_rpow_div {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : AEMeasurable Y P) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ ω, ‖Y ω‖ₑ ^ a ∂P ≤ (∫⁻ ω, ‖Y ω‖ₑ ^ b ∂P) ^ (a / b) := by
  have hb : 0 < b := ha.trans_le hab
  have h := MeasureTheory.eLpNorm'_le_eLpNorm'_of_exponent_le ha hab P hY.aestronglyMeasurable
  rw [MeasureTheory.eLpNorm'_eq_lintegral_enorm, MeasureTheory.eLpNorm'_eq_lintegral_enorm] at h
  have h2 := ENNReal.rpow_le_rpow h ha.le
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div_mul_cancel ha.ne', ENNReal.rpow_one,
    one_div_mul_eq_div] at h2

/-- The rate comparison behind `L2_Growth`: `tailRate_a ≤ (a/b) · tailRate_b`. -/
theorem GrowthIndex.tailRate_momentFn_le {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P] (X : ℝ → ℝ → Ω → ℝ)
    (hX : ∀ t x, AEMeasurable (X t x) P) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (α : ℝ) :
    tailRate (momentFn P X a) α ≤ ((a / b : ℝ) : EReal) * tailRate (momentFn P X b) α := by
  have hb : 0 < b := ha.trans_le hab
  have hr : 0 < a / b := div_pos ha hb
  rw [tailRate, tailRate, ← EReal.limsup_const_mul_of_nonneg_of_ne_top
    (by exact_mod_cast hr.le) (EReal.coe_ne_top _)]
  refine Filter.limsup_le_limsup ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hsup : tailSup (momentFn P X a) α t ≤ tailSup (momentFn P X b) α t ^ (a / b) :=
    iSup₂_le fun x hx => (lintegral_rpow_le_rpow_div (hX t x) ha hab).trans
      (ENNReal.rpow_le_rpow (le_tailSup (f := momentFn P X b) hx) hr.le)
  refine (inv_mul_log_le_inv_mul_log ht hsup).trans_eq ?_
  rw [ENNReal.log_rpow, mul_left_comm]

/-- Target 5 (paper Lemma `L2:Growth`, Conus–Khoshnevisan): for `0 < a ≤ b` both growth
indices of `E|X(t,x)|^p` are nondecreasing in `p`. -/
theorem L2_Growth {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (X : ℝ → ℝ → Ω → ℝ)
    (hX : ∀ t x, AEMeasurable (X t x) P) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    lowerGrowthIndex (momentFn P X a) ≤ lowerGrowthIndex (momentFn P X b) ∧
      upperGrowthIndex (momentFn P X a) ≤ upperGrowthIndex (momentFn P X b) := by
  have hr : (0 : EReal) < ((a / b : ℝ) : EReal) := by
    exact_mod_cast div_pos ha (ha.trans_le hab)
  have hcmp := GrowthIndex.tailRate_momentFn_le P X hX ha hab
  constructor
  · refine sSup_le_sSup (Set.image_mono fun α hα => ⟨hα.1, ?_⟩)
    by_contra hneg
    have : ((a / b : ℝ) : EReal) * tailRate (momentFn P X b) α ≤ 0 :=
      (mul_le_mul_of_nonneg_left (not_lt.1 hneg) hr.le).trans_eq (mul_zero _)
    exact (hα.2.trans_le ((hcmp α).trans this)).false
  · refine sInf_le_sInf (Set.image_mono fun α hα => ⟨hα.1, ?_⟩)
    refine (hcmp α).trans_lt ?_
    have h := hα.2
    induction h' : tailRate (momentFn P X b) α using EReal.rec with
    | bot => rw [EReal.mul_bot_of_pos hr]; exact EReal.bot_lt_zero
    | top => rw [h'] at h; exact absurd h (not_lt.2 le_top)
    | coe L =>
      rw [h'] at h
      have hL : L < 0 := by exact_mod_cast h
      exact_mod_cast mul_neg_of_pos_of_neg (div_pos ha (ha.trans_le hab)) hL

/-- Target 6: the final optimisation step of Theorem `T2:Growth` (2). If for every
`β ∈ (0, β₀]` the envelope `f ≤ A e^{(νβ² + Λ⁴/(4ν)) t − 2β|x|}` holds, then
`λ̄ ≤ β₀ν/2 + Λ⁴/(8νβ₀)` when `β₀ < Λ²/(2ν)` and `λ̄ ≤ Λ²/2` otherwise. -/
theorem upperGrowthIndex_le_piecewise {f : ℝ → ℝ → ℝ≥0∞} {ν Λ β₀ : ℝ} (hν : 0 < ν)
    (hΛ : 0 < Λ) (hβ₀ : 0 < β₀)
    (h : ∀ β, 0 < β → β ≤ β₀ → ∃ A T₀, ∀ t ≥ T₀, ∀ x,
      f t x ≤ ENNReal.ofReal (A * Real.exp ((ν * β ^ 2 + Λ ^ 4 / (4 * ν)) * t - 2 * β * |x|))) :
    upperGrowthIndex f ≤
      ((if β₀ < Λ ^ 2 / (2 * ν) then β₀ * ν / 2 + Λ ^ 4 / (8 * ν * β₀) else Λ ^ 2 / 2 : ℝ) :
        EReal) := by
  have hβ : ∀ β, 0 < β → β ≤ β₀ →
      upperGrowthIndex f ≤ ((β * ν / 2 + Λ ^ 4 / (8 * ν * β) : ℝ) : EReal) := by
    intro β hβ0 hββ₀
    obtain ⟨A, hA⟩ := h β hβ0 hββ₀
    have := upperGrowthIndex_le_of_envelope (A := A) hβ0 hA
    have heq : (ν * β ^ 2 + Λ ^ 4 / (4 * ν)) / (2 * β) = β * ν / 2 + Λ ^ 4 / (8 * ν * β) := by
      field_simp
      ring
    rwa [heq, max_eq_left (by positivity)] at this
  split_ifs with hlt
  · exact hβ β₀ hβ₀ le_rfl
  · have hstar : (0 : ℝ) < Λ ^ 2 / (2 * ν) := by positivity
    have := hβ _ hstar (not_lt.1 hlt)
    have heq : Λ ^ 2 / (2 * ν) * ν / 2 + Λ ^ 4 / (8 * ν * (Λ ^ 2 / (2 * ν))) = Λ ^ 2 / 2 := by
      field_simp
      ring
    rwa [heq] at this

end ChenDalang15

end
