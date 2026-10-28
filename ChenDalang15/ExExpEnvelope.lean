module

public import ChenDalang15.ExExpLower
public import ChenDalang15.GrowthLower
public import ChenDalang15.GrowthUpper
public import ChenDalang15.EacProps
public import ChenDalang15.TwoPoint

/-!
# Proposition `P2:Ex-Exp` from the second-moment formula (Chen–Dalang 2015, Section 5)

For `μ(dx) = e^{−β|x|} dx` (`β > 0`) and the parabolic Anderson model `ρ(u) = λu`, this file
derives the minorant assumed by `exExp_lowerIndex_of_envelope` from the right side of
`E2:SecMom` (with `ϑ = 0`), so that Proposition `P2:Ex-Exp` becomes conditional only on the
second-moment formula of Theorem `T2:ExUni(5)`:

* `J0_exp_measure`: `J₀(t,x) = e^{β²νt/2} E_{νt,−β}(x)` (`P2:E(ii)` with `−β`).
* `exExp_envelope_of_secondMoment`: if `f ≥ J₀² + J₀² ⋆ 𝓚` (`E2:SecMom`, `ϑ = 0`, as an
  inequality), then for every `c ∈ [0,1)` and every `t > 0` (so `T₀ = 1` works)
  `f(t,x) ≥ E_{νt/2,−2β}(x) e^{β²νt} Φ(−β√(ν(1−c)t))² (e^{γt} − e^{cγt})`, `γ = λ⁴/(4ν)`;
  in fact with an extra factor `4` on the right.
* `P2_Ex_Exp_lower`: the lower bound of `E2:Ex-Exp` on `λ̲(2)`.
* `P2_Ex_Exp`: under the exact formula, `λ̲(2) = λ̄(2) =` the value of `E2:Ex-Exp`.

## A false step in the paper, and the route used here

The paper's proof writes `(e^{−2β|·|} * G_ν(t − s/2, ·))(x) ≥ e^{2β²ν(t−s/2)} E_{νt/2,−2β}(x)`,
citing `P2:E(ii),(vi)`. Since `ν(t − s/2) ≥ νt/2` and `a ↦ E_{a,−2β}(x)` is nonincreasing
(`P2:E(vi)` for a negative parameter, `antitoneOn_Eac_a`), the inequality goes the other way:
`E_{ν(t−s/2),−2β} ≤ E_{νt/2,−2β}`, strictly for `s > 0`. (Example: `ν = 1.3`, `β = 0.7`,
`t = 2`, `s = 1`, `x = 0`: `E_{1.95,−1.4}(0) ≈ 0.0506 < E_{1.3,−1.4}(0) ≈ 0.1104`.)

The displayed minorant is nevertheless true. Here the `J₀`-factor is bounded below pointwise
instead of through `P2:E(iv)`: by `|w| ≤ |y| + |y − w|`,
`J₀(s,y) = ∫ e^{−β|w|} G_ν(s, y − w) dw ≥ e^{−β|y|} ∫ e^{−β|v|} G_ν(s,v) dv
= 2Φ(−β√(νs)) e^{β²νs/2} e^{−β|y|}` (`J0_exp_measure_ge`, using `E_{a,b}(0) = 2Φ(b√a)`).
Then `∫ e^{−2β|y|} G_{ν/2}(t−s, x−y) dy = e^{β²ν(t−s)} E_{ν(t−s)/2,−2β}(x)` (`P2:E(ii)`), and now
`P2:E(vi)` points the right way: `ν(t−s)/2 ≤ νt/2` gives `E_{ν(t−s)/2,−2β} ≥ E_{νt/2,−2β}`. With
`𝓚(r,·) ≥ (λ⁴/(4ν)) e^{λ⁴r/(4ν)} G_{ν/2}(r,·)` and the paper's `c`-split of the time integral
(`s ∈ (0,(1−c)t)`), this yields the minorant with the factor `4 = 2²`. No Fubini argument is
needed.

## Integrability

`stConv` is a Bochner integral, so the lower bound needs the integrand to be integrable. As in
`GrowthLower`, integrability comes from the
Chen–Dalang convolution estimate `GrowthLower.lintegral_sq_lheatFlow_mul_le`; the measure `μ`
is finite, hence Gaussian tempered.
-/

set_option autoImplicit false

public section

open scoped ENNReal
open Real MeasureTheory Set Filter

namespace ChenDalang15

namespace ExExpEnvelope

/-! ### The measure `μ(dx) = e^{−β|x|} dx` -/

/-- The initial measure `μ(dx) = e^{−β|x|} dx` of Proposition `P2:Ex-Exp`. -/
@[expose] noncomputable def expMeasure (β : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (Real.exp (-β * |x|))

instance instSFiniteExpMeasure (β : ℝ) : SFinite (expMeasure β) := by
  rw [expMeasure]; infer_instance

theorem measurable_density (β : ℝ) :
    Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-β * |x|)) :=
  (by fun_prop : Continuous fun x : ℝ => Real.exp (-β * |x|)).measurable.ennreal_ofReal

theorem toReal_density (β y : ℝ) :
    (ENNReal.ofReal (Real.exp (-β * |y|))).toReal = Real.exp (-β * |y|) :=
  ENNReal.toReal_ofReal (Real.exp_pos _).le

/-- `e^{−k|y|}` is Lebesgue integrable for `k > 0`. -/
theorem integrable_exp_neg_mul_abs {k : ℝ} (hk : 0 < k) :
    Integrable (fun y : ℝ => Real.exp (-k * |y|)) := by
  set g : ℝ → ℝ := (Ici 0).indicator (fun y => Real.exp (-k * y)) with hg_def
  have hg : Integrable g :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).2 (exp_neg_integrableOn_Ioi 0 hk)).integrable_indicator
      measurableSet_Ici
  refine Integrable.mono' (hg.add hg.comp_neg)
    (by fun_prop : Continuous fun y : ℝ => Real.exp (-k * |y|)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 : 0 ≤ g y := indicator_nonneg (fun _ _ => (Real.exp_pos _).le) y
  have h2 : 0 ≤ g (-y) := indicator_nonneg (fun _ _ => (Real.exp_pos _).le) (-y)
  simp only [Pi.add_apply]
  rcases le_total 0 y with hy | hy
  · have : g y = Real.exp (-k * |y|) := by
      rw [hg_def, indicator_of_mem (mem_Ici.2 hy), abs_of_nonneg hy]
    linarith
  · have : g (-y) = Real.exp (-k * |y|) := by
      rw [hg_def, indicator_of_mem (mem_Ici.2 (neg_nonneg.2 hy)), abs_of_nonpos hy]
    linarith

theorem integral_expMeasure (β : ℝ) (g : ℝ → ℝ) :
    ∫ y, g y ∂(expMeasure β) = ∫ y, Real.exp (-β * |y|) * g y := by
  rw [expMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_density β)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [toReal_density, smul_eq_mul]

theorem integrable_expMeasure_iff (β : ℝ) {g : ℝ → ℝ} :
    Integrable g (expMeasure β) ↔ Integrable (fun y => Real.exp (-β * |y|) * g y) := by
  rw [expMeasure, integrable_withDensity_iff_integrable_smul' (measurable_density β)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [toReal_density, smul_eq_mul]

theorem isFiniteMeasure_expMeasure {β : ℝ} (hβ : 0 < β) : IsFiniteMeasure (expMeasure β) :=
  isFiniteMeasure_withDensity_ofReal (integrable_exp_neg_mul_abs hβ).2

theorem isGaussianTempered_expMeasure {β : ℝ} (hβ : 0 < β) :
    RoughHeatKernel.IsGaussianTempered (expMeasure β) := by
  have := isFiniteMeasure_expMeasure hβ
  exact RoughHeatKernel.isGaussianTempered_of_isFiniteMeasure _

/-- For `0 < β' < β`, `∫ e^{β'|y|} μ(dy) < ∞` (`μ ∈ 𝓜^{β'}_{G,+}`). -/
theorem integrable_exp_mul_abs_expMeasure {β β' : ℝ} (hβ' : β' < β) :
    Integrable (fun y => Real.exp (β' * |y|)) (expMeasure β) := by
  rw [integrable_expMeasure_iff]
  refine (integrable_exp_neg_mul_abs (sub_pos.2 hβ')).congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [← Real.exp_add]
  congr 1
  ring

/-! ### `J₀` for `μ(dx) = e^{−β|x|} dx` -/

theorem J0_expMeasure {ν β t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : ℝ) :
    J0 ν (expMeasure β) t x = Real.exp (β ^ 2 * ν * t / 2) * Eac (ν * t) (-β) x := by
  have h := integral_exp_mul_abs_mul_G hν ht (-β) x
  rw [neg_sq] at h
  rw [J0, integral_expMeasure, h]

/-- Pointwise lower bound `J₀(s,y) ≥ 2Φ(−β√(νs)) e^{β²νs/2} e^{−β|y|}` (from
`|w| ≤ |y| + |y − w|` and `E_{a,b}(0) = 2Φ(b√a)`). -/
theorem J0_expMeasure_ge {ν β s : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β) (hs : 0 < s) (y : ℝ) :
    2 * Phi (-β * Real.sqrt (ν * s)) * Real.exp (β ^ 2 * ν * s / 2) * Real.exp (-β * |y|) ≤
      J0 ν (expMeasure β) s y := by
  have hI := integrable_exp_mul_abs_mul_G hν hs (-β) y
  have hI0 : Integrable (fun v => Real.exp (-β * |v|) * G ν s v) := by
    have := integrable_exp_mul_abs_mul_G hν hs (-β) 0
    simpa only [zero_sub, EacProps.G_neg] using this
  have hc : ∫ w, Real.exp (-β * |y - w|) * G ν s (y - w) =
      Real.exp (β ^ 2 * ν * s / 2) * (2 * Phi (-β * Real.sqrt (ν * s))) := by
    rw [integral_sub_left_eq_self (fun v => Real.exp (-β * |v|) * G ν s v) (μ := volume) y]
    have h2 := integral_exp_mul_abs_mul_G hν hs (-β) 0
    simp only [zero_sub, EacProps.G_neg] at h2
    rw [h2, Eac_zero, neg_sq]
  rw [J0, integral_expMeasure]
  calc 2 * Phi (-β * Real.sqrt (ν * s)) * Real.exp (β ^ 2 * ν * s / 2) * Real.exp (-β * |y|)
      = ∫ w, Real.exp (-β * |y|) * (Real.exp (-β * |y - w|) * G ν s (y - w)) := by
        rw [integral_const_mul, hc]; ring
    _ ≤ ∫ w, Real.exp (-β * |w|) * G ν s (y - w) := by
        refine integral_mono ((hI0.comp_sub_left y).const_mul _) hI fun w => ?_
        simp only
        rw [← mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (EacProps.G_nonneg _ _ _)
        have h := abs_sub_abs_le_abs_sub w y
        rw [abs_sub_comm] at h
        nlinarith

/-! ### Integrability of the space-time convolution

The integrand, its inner integral and their measurability and integrability are those of
`GrowthLower` (Chen–Dalang convolution estimate). -/

open GrowthLower (integrand phiC stronglyMeasurable_integrand stronglyMeasurable_phiC
  integrand_nonneg lintegral_integrand_le integrable_integrand integrableOn_phiC)

/-- `(J₀² ⋆ 𝓚)(t,x) = ∫_{(0,t]} phiC(s) ds` (closed form of `𝓚` for `s < t`). -/
theorem stConv_eq_integral_phiC {ν : ℝ} (hν : 0 < ν) (μ : Measure ℝ) (l : ℝ) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    stConv (fun s y => J0 ν μ s y ^ 2) (K ν l) t x = ∫ s in Ioc 0 t, phiC ν μ l t x s := by
  rw [stConv, intervalIntegral.integral_of_le ht.le]
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [ae_ne_real t] with s hst hs
  unfold phiC integrand
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [GrowthLower.K_eq_kC hν (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) (x - y)]

/-! ### The lower bound on `phiC` -/

/-- For `0 < s < t`:
`∫ J₀(s,y)² 𝓚(t−s,x−y) dy ≥ 4Φ(−β√(νs))² e^{β²νt} k(t−s) E_{ν(t−s)/2,−2β}(x)`. -/
theorem phiC_ge {ν β lam t x s : ℝ} (hν : 0 < ν) (hβ : 0 < β) (hs : 0 < s) (hst : s < t) :
    4 * Phi (-β * Real.sqrt (ν * s)) ^ 2 * Real.exp (β ^ 2 * ν * t) *
        (GrowthLower.kC ν lam (t - s) * Eac (ν / 2 * (t - s)) (-2 * β) x) ≤
      phiC ν (expMeasure β) lam t x s := by
  have hT := isGaussianTempered_expMeasure hβ
  have hts : 0 < t - s := sub_pos.2 hst
  set P := Phi (-β * Real.sqrt (ν * s)) with hP
  have hP0 : 0 ≤ P := EacProps.Phi_nonneg _
  set m := 2 * P * Real.exp (β ^ 2 * ν * s / 2) with hm
  have hm0 : 0 ≤ m := by positivity
  have hk0 := GrowthLower.kC_nonneg (l := lam) (r := t - s) hν
  have hle : ∫ y, (m * Real.exp (-β * |y|)) ^ 2 *
      (G (ν / 2) (t - s) (x - y) * GrowthLower.kC ν lam (t - s)) ≤
      phiC ν (expMeasure β) lam t x s := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => ?_)
      (integrable_integrand hT hν hs hst) (Eventually.of_forall fun y => ?_)
    · have := GrowthLower.G_nonneg (ν / 2) (t - s) (x - y)
      positivity
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (J0_expMeasure_ge hν hβ.le hs y) 2)
        (mul_nonneg (GrowthLower.G_nonneg _ _ _) hk0)
  have heq : ∫ y, (m * Real.exp (-β * |y|)) ^ 2 *
      (G (ν / 2) (t - s) (x - y) * GrowthLower.kC ν lam (t - s)) =
      m ^ 2 * GrowthLower.kC ν lam (t - s) *
        (Real.exp ((-2 * β) ^ 2 * (ν / 2) * (t - s) / 2) * Eac (ν / 2 * (t - s)) (-2 * β) x) := by
    rw [← integral_exp_mul_abs_mul_G (by positivity : 0 < ν / 2) hts (-2 * β) x,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have : Real.exp (-β * |y|) ^ 2 = Real.exp (-2 * β * |y|) := by
      rw [sq, ← Real.exp_add]; ring_nf
    simp only
    rw [mul_pow, this]
    ring
  have hexp : Real.exp (β ^ 2 * ν * s / 2) ^ 2 *
      Real.exp ((-2 * β) ^ 2 * (ν / 2) * (t - s) / 2) = Real.exp (β ^ 2 * ν * t) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
  calc 4 * P ^ 2 * Real.exp (β ^ 2 * ν * t) *
        (GrowthLower.kC ν lam (t - s) * Eac (ν / 2 * (t - s)) (-2 * β) x)
      = m ^ 2 * GrowthLower.kC ν lam (t - s) *
          (Real.exp ((-2 * β) ^ 2 * (ν / 2) * (t - s) / 2) *
            Eac (ν / 2 * (t - s)) (-2 * β) x) := by
        rw [← hexp, hm]; ring
    _ = _ := heq.symm
    _ ≤ _ := hle

/-- For `s ∈ (0, (1−c)t)`: `phiC(s) ≥ 4 E_{νt/2,−2β}(x) e^{β²νt} Φ(−β√(ν(1−c)t))² ·
(λ⁴/(4ν)) e^{λ⁴(t−s)/(4ν)}`. -/
theorem phiC_ge_split {ν β lam c t x s : ℝ} (hν : 0 < ν) (hβ : 0 < β) (hc0 : 0 ≤ c)
    (hc1 : c < 1) (hs : s ∈ Ioo 0 ((1 - c) * t)) :
    4 * (Eac (ν * t / 2) (-2 * β) x * Real.exp (β ^ 2 * ν * t) *
        Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2) *
        (lam ^ 4 / (4 * ν) * Real.exp (lam ^ 4 * (t - s) / (4 * ν))) ≤
      phiC ν (expMeasure β) lam t x s := by
  obtain ⟨hs0, hsT⟩ := hs
  have ht : 0 < t := by
    by_contra h
    have h' : (1 - c) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.1 h)
    linarith
  have hst : s < t := by nlinarith [mul_nonneg hc0 ht.le]
  have hts : 0 < t - s := sub_pos.2 hst
  refine le_trans ?_ (phiC_ge (lam := lam) (x := x) hν hβ hs0 hst)
  -- the three comparisons
  have hΦ : Phi (-β * Real.sqrt (ν * (1 - c) * t)) ≤ Phi (-β * Real.sqrt (ν * s)) := by
    apply GrowthLower.Phi_monotone
    have : Real.sqrt (ν * s) ≤ Real.sqrt (ν * (1 - c) * t) :=
      Real.sqrt_le_sqrt (by nlinarith)
    nlinarith
  have hΦ0 := EacProps.Phi_nonneg (-β * Real.sqrt (ν * (1 - c) * t))
  have hE : Eac (ν * t / 2) (-2 * β) x ≤ Eac (ν / 2 * (t - s)) (-2 * β) x :=
    antitoneOn_Eac_a (by linarith : -2 * β ≤ 0) x (mem_Ioi.2 (by positivity))
      (mem_Ioi.2 (by positivity)) (by nlinarith)
  have hE0 := (EacProps.Eac_pos (a := ν * t / 2) (-2 * β) x).le
  have hk := GrowthLower.kC_lower (l := lam) (r := t - s) hν
  have hk0 : 0 ≤ lam ^ 4 / (4 * ν) * Real.exp (lam ^ 4 * (t - s) / (4 * ν)) := by positivity
  have hB := (Real.exp_pos (β ^ 2 * ν * t)).le
  calc 4 * (Eac (ν * t / 2) (-2 * β) x * Real.exp (β ^ 2 * ν * t) *
        Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2) *
        (lam ^ 4 / (4 * ν) * Real.exp (lam ^ 4 * (t - s) / (4 * ν)))
      = 4 * Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2 * Real.exp (β ^ 2 * ν * t) *
          ((lam ^ 4 / (4 * ν) * Real.exp (lam ^ 4 * (t - s) / (4 * ν))) *
            Eac (ν * t / 2) (-2 * β) x) := by ring
    _ ≤ 4 * Phi (-β * Real.sqrt (ν * s)) ^ 2 * Real.exp (β ^ 2 * ν * t) *
          (GrowthLower.kC ν lam (t - s) * Eac (ν / 2 * (t - s)) (-2 * β) x) := by
        have h1 : Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2 ≤ Phi (-β * Real.sqrt (ν * s)) ^ 2 :=
          pow_le_pow_left₀ hΦ0 hΦ 2
        have h2 : (lam ^ 4 / (4 * ν) * Real.exp (lam ^ 4 * (t - s) / (4 * ν))) *
            Eac (ν * t / 2) (-2 * β) x ≤
            GrowthLower.kC ν lam (t - s) * Eac (ν / 2 * (t - s)) (-2 * β) x :=
          mul_le_mul hk hE hE0 (hk0.trans hk)
        have h3 : 0 ≤ (lam ^ 4 / (4 * ν) * Real.exp (lam ^ 4 * (t - s) / (4 * ν))) *
            Eac (ν * t / 2) (-2 * β) x := mul_nonneg hk0 hE0
        gcongr

/-- `∫_{(0,(1−c)t)} (λ⁴/(4ν)) e^{λ⁴(t−s)/(4ν)} ds = e^{γt} − e^{cγt}`, `γ = λ⁴/(4ν)`. -/
theorem integral_split {ν lam c t : ℝ} (hc1 : c < 1) (ht : 0 < t) :
    ∫ s in Ioo 0 ((1 - c) * t), lam ^ 4 / (4 * ν) * Real.exp (lam ^ 4 * (t - s) / (4 * ν)) =
      Real.exp (lam ^ 4 / (4 * ν) * t) - Real.exp (c * (lam ^ 4 / (4 * ν)) * t) := by
  have hT : 0 ≤ (1 - c) * t := mul_nonneg (by linarith) ht.le
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT]
  have hd : ∀ s ∈ uIcc 0 ((1 - c) * t),
      HasDerivAt (fun s => -1 * Real.exp (lam ^ 4 * (t - s) / (4 * ν)))
        (lam ^ 4 / (4 * ν) * Real.exp (lam ^ 4 * (t - s) / (4 * ν))) s := by
    intro s _
    have h1 : HasDerivAt (fun s => lam ^ 4 * (t - s) / (4 * ν)) (lam ^ 4 * -1 / (4 * ν)) s :=
      (((hasDerivAt_id' s).const_sub t).const_mul (lam ^ 4)).div_const (4 * ν)
    convert h1.exp.const_mul (-1) using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s =>
      lam ^ 4 / (4 * ν) * Real.exp (lam ^ 4 * (t - s) / (4 * ν))).intervalIntegrable _ _)]
  have e1 : lam ^ 4 * (t - (1 - c) * t) / (4 * ν) = c * (lam ^ 4 / (4 * ν)) * t := by ring
  have e2 : lam ^ 4 * (t - 0) / (4 * ν) = lam ^ 4 / (4 * ν) * t := by ring
  rw [e1, e2]
  ring

/-- The minorant (with the factor `4`): for `c ∈ [0,1)` and `t > 0`,
`4 E_{νt/2,−2β}(x) e^{β²νt} Φ(−β√(ν(1−c)t))² (e^{γt} − e^{cγt}) ≤ (J₀² ⋆ 𝓚)(t,x)`. -/
theorem four_mul_envelope_le_stConv {ν lam β c t : ℝ} (hν : 0 < ν) (hβ : 0 < β) (hc0 : 0 ≤ c)
    (hc1 : c < 1) (ht : 0 < t) (x : ℝ) :
    4 * (Eac (ν * t / 2) (-2 * β) x * Real.exp (β ^ 2 * ν * t) *
        Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2 *
        (Real.exp (lam ^ 4 / (4 * ν) * t) - Real.exp (c * (lam ^ 4 / (4 * ν)) * t))) ≤
      stConv (fun s y => J0 ν (expMeasure β) s y ^ 2) (K ν lam) t x := by
  have hT := isGaussianTempered_expMeasure hβ
  set C := Eac (ν * t / 2) (-2 * β) x * Real.exp (β ^ 2 * ν * t) *
    Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2 with hC
  have hint := integrableOn_phiC (l := lam) hT hν ht x
  have hsub : Ioo 0 ((1 - c) * t) ⊆ Ioc 0 t :=
    fun s hs => ⟨hs.1, by nlinarith [hs.2]⟩
  rw [stConv_eq_integral_phiC hν _ lam ht x, ← integral_split (lam := lam) (ν := ν) hc1 ht,
    ← mul_assoc, ← integral_const_mul]
  calc ∫ s in Ioo 0 ((1 - c) * t),
        4 * C * (lam ^ 4 / (4 * ν) * Real.exp (lam ^ 4 * (t - s) / (4 * ν)))
      ≤ ∫ s in Ioo 0 ((1 - c) * t), phiC ν (expMeasure β) lam t x s :=
        setIntegral_mono_on
          ((by fun_prop : Continuous fun s =>
            4 * C * (lam ^ 4 / (4 * ν) * Real.exp (lam ^ 4 * (t - s) / (4 * ν)))
            ).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
          (hint.mono_set hsub) measurableSet_Ioo
          fun s hs => phiC_ge_split hν hβ hc0 hc1 hs
    _ ≤ ∫ s in Ioc 0 t, phiC ν (expMeasure β) lam t x s :=
        setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall fun s _ =>
            integral_nonneg fun y => integrand_nonneg hν _ lam t x s y))
          hsub.eventuallyLE

end ExExpEnvelope

open ExExpEnvelope

/-- **`J₀` for `μ(dx) = e^{−β|x|} dx`** (proof of `P2:Ex-Exp`, from `E2:Eac2` = `P2:E(ii)` with
`−β`): `J₀(t,x) = e^{β²νt/2} E_{νt,−β}(x)` for `ν, t > 0` (every real `β`). -/
theorem J0_exp_measure {ν β t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : ℝ) :
    J0 ν (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-β * |x|))) t x =
      Real.exp (β ^ 2 * ν * t / 2) * Eac (ν * t) (-β) x :=
  J0_expMeasure hν ht x

/-- **The minorant of the proof of Proposition `P2:Ex-Exp`, derived from `E2:SecMom`.** For
`μ(dx) = e^{−β|x|} dx` (`β, ν > 0`), if `f(t,x) ≥ J₀²(t,x) + (J₀² ⋆ 𝓚)(t,x)` for all `t > 0`
(the right side of `E2:SecMom` with `ϑ = 0`), then for every `c ∈ [0,1)` (with `T₀ = 1`; in
fact every `t > 0` works) `f(t,x) ≥ E_{νt/2,−2β}(x) e^{β²νt} Φ(−β√(ν(1−c)t))² (e^{γt} − e^{cγt})`,
`γ = λ⁴/(4ν)`: exactly the hypothesis of `exExp_lowerIndex_of_envelope`. -/
theorem exExp_envelope_of_secondMoment {ν lam β : ℝ} (hν : 0 < ν) (hβ : 0 < β)
    {f : ℝ → ℝ → ℝ≥0∞}
    (hf : ∀ t > 0, ∀ x, ENNReal.ofReal (secondMomentExpr
      (J0 ν (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-β * |x|)))) ν 0 lam t x) ≤
        f t x) :
    ∀ c : ℝ, 0 ≤ c → c < 1 → ∃ T₀, ∀ t ≥ T₀, ∀ x,
      ENNReal.ofReal (Eac (ν * t / 2) (-2 * β) x * Real.exp (β ^ 2 * ν * t) *
          Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2 *
          (Real.exp (lam ^ 4 / (4 * ν) * t) - Real.exp (c * (lam ^ 4 / (4 * ν)) * t))) ≤ f t x := by
  intro c hc0 hc1
  refine ⟨1, fun t ht x => ?_⟩
  have ht0 : 0 < t := by linarith
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hf t ht0 x)
  set e := Eac (ν * t / 2) (-2 * β) x * Real.exp (β ^ 2 * ν * t) *
    Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2 *
    (Real.exp (lam ^ 4 / (4 * ν) * t) - Real.exp (c * (lam ^ 4 / (4 * ν)) * t)) with he
  have h4 := four_mul_envelope_le_stConv (lam := lam) hν hβ hc0 hc1 ht0 x
  have he0 : 0 ≤ e := by
    have := (EacProps.Eac_pos (a := ν * t / 2) (-2 * β) x).le
    have := EacProps.Phi_nonneg (-β * Real.sqrt (ν * (1 - c) * t))
    have : Real.exp (c * (lam ^ 4 / (4 * ν)) * t) ≤ Real.exp (lam ^ 4 / (4 * ν) * t) := by
      apply Real.exp_le_exp.2
      have : 0 ≤ lam ^ 4 / (4 * ν) * t := by positivity
      nlinarith
    have : 0 ≤ Real.exp (lam ^ 4 / (4 * ν) * t) - Real.exp (c * (lam ^ 4 / (4 * ν)) * t) := by
      linarith
    positivity
  have hJ := sq_nonneg (J0 ν (expMeasure β) t x)
  simp only [secondMomentExpr, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_mul, add_zero]
  change e ≤ J0 ν (expMeasure β) t x ^ 2 +
    stConv (fun s y => J0 ν (expMeasure β) s y ^ 2) (K ν lam) t x
  linarith

/-- **Proposition `P2:Ex-Exp`, lower bound, conditional only on `E2:SecMom`.** For
`μ(dx) = e^{−β|x|} dx` (`β > 0`), `ν > 0`, `λ ≠ 0`, and `f ≥ J₀² + J₀² ⋆ 𝓚` for `t > 0`
(`E2:SecMom` with `ϑ = 0`, as an inequality):
`λ̲(f) ≥ βν/2 + λ⁴/(8νβ)` if `β ≤ λ²/(2ν)` and `λ̲(f) ≥ λ²/2` otherwise. -/
theorem P2_Ex_Exp_lower {ν lam β : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) (hβ : 0 < β)
    {f : ℝ → ℝ → ℝ≥0∞}
    (hf : ∀ t > 0, ∀ x, ENNReal.ofReal (secondMomentExpr
      (J0 ν (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-β * |x|)))) ν 0 lam t x) ≤
        f t x) :
    ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
      EReal) ≤ lowerGrowthIndex f :=
  exExp_lowerIndex_of_envelope hν hlam hβ (exExp_envelope_of_secondMoment hν hβ hf)

/-- **Proposition `P2:Ex-Exp` (display `E2:Ex-Exp`), conditional only on `E2:SecMom`.** For
`μ(dx) = e^{−β|x|} dx` (`β > 0`), `ν > 0`, `λ ≠ 0`, if `f(t,x) = J₀²(t,x) + (J₀² ⋆ 𝓚)(t,x)` for
all `t > 0` (`E2:SecMom` with `ϑ = 0`), then
`λ̲(f) = λ̄(f) = βν/2 + λ⁴/(8νβ)` if `β ≤ λ²/(2ν)` and `= λ²/2` otherwise. The upper envelopes
for `β' < β` come from `upper_envelope_exp` (`μ ∈ 𝓜^{β'}_{G,+}`). -/
theorem P2_Ex_Exp {ν lam β : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) (hβ : 0 < β)
    {f : ℝ → ℝ → ℝ≥0∞}
    (hf_eq : ∀ t > 0, ∀ x, f t x = ENNReal.ofReal (secondMomentExpr
      (J0 ν (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-β * |x|)))) ν 0 lam t x)) :
    lowerGrowthIndex f =
        ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
          EReal) ∧
      upperGrowthIndex f =
        ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
          EReal) := by
  refine exExp_growth_eq hν hlam hβ
    (exExp_envelope_of_secondMoment hν hβ fun t ht x => (hf_eq t ht x).ge) ?_
  intro β' hβ'0 hβ'β
  obtain ⟨A, T₀, h⟩ := upper_envelope_exp (a := 1) hν hβ'0 zero_le_one hlam
    (integrable_exp_mul_abs_expMeasure hβ'β) rfl
    (f := fun t x => secondMomentExpr (J0 ν (expMeasure β)) ν 0 lam t x)
    (fun t _ x => by simp [secondMomentExpr])
  refine ⟨A, max T₀ 1, fun t ht x => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le one_pos (le_of_max_le_right ht)
  rw [hf_eq t ht0 x]
  exact ENNReal.ofReal_le_ofReal (h t (le_of_max_le_left ht) x)

end ChenDalang15

end
