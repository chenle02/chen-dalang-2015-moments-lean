module

public import ChenDalang15.MomentBridge
public import ChenDalang15.ExExpLower
public import ChenDalang15.GrowthUpper

/-!
# Wave S1 glue: `L2:InDt` at general `ν`, Gaussian-tempered bridges, conditional corollaries

Chen–Dalang (2015), Lemma `L2:InDt` and Theorem `T2:Growth` parts (1) (all `p ≥ 2`) and (3)
(`p = 2`), for nonnegative initial data `μ`.

## `L2:InDt` as a lower-integral statement

Write `J₀*(t,x) = ∫⁻ G_ν(t,x−z) μ(dz)` (`S1Glue.lJ0`, the paper's `J₀^*` for `μ ≥ 0`, valued in
`[0,∞]` and defined for every measure). For every s-finite `μ ≥ 0`, `ν > 0`, `t > 0`:

* `L2_InDt_A` (display `E2:InDt-A`): for measurable `h : ℝ → [0,∞]`,
  `∫⁻_0^t ∫⁻ J₀*(s,y)² G_{ν/2}(t−s,x−y) h(t−s) dy ds ≤ 2√t J₀*(2t,x)² ∫⁻_0^t h(t−s)/√s ds`;
* `L2_InDt_L0` (display `E2:InDt-L0`): `∫⁻∫⁻ J₀² 𝓛₀ ≤ λ²√(πt/ν) J₀*(2t,x)²`;
* `L2_InDt` (display `E2:InDt`): `∫⁻∫⁻ J₀² 𝓚 ≤ λ²√(πt/ν) (1 + 2e^{λ⁴t/(4ν)}) J₀*(2t,x)²`;
* `L2_InDt_lt_top`, `L2_InDt_tempered`: for Gaussian-tempered `μ` the right side is finite and
  equals `λ²√(πt/ν)(1 + 2e^{λ⁴t/(4ν)}) J₀(2t,x)²` with the real (Bochner) `J₀`.

The left sides are the lower-integral convolutions of `MomentBridge` (integrand
`ofReal (J₀(s,y)² 𝓚(t−s,x−y))` over `s ∈ (0,t]`), so no integrability hypothesis is needed.
The proof is the paper's: the pointwise-in-time estimate
`RoughHeatKernel.lintegral_sq_lheatFlow_mul_le` (the building block of
`RoughHeatKernel.lintegral_sq_lheatFlow_conv_le`, `ν = 1`) is applied at times `νs < νt`
through the scaling bridge `G_eq_heatKernel` (`G_ν(t,x) = p_{νt}(x)`), then integrated in `s`.
The constants follow the paper's choices of `h` (`𝓛₀ ≤ G_{ν/2} · λ²(4πνr)^{-1/2}`,
`𝓚 ≤ G_{ν/2} · hK`, `E2:ExpDivSqrt`).

## Gaussian-tempered bridges

* `integrable_exp_neg_sq_iff`: the companion's hypothesis `∀ a > 0, ∫ e^{−ay²} dμ < ∞` (Bochner
  integrability) is equivalent to `RoughHeatKernel.IsGaussianTempered μ`;
* `isGaussianTempered_of_integrable_exp`, `integrable_exp_neg_sq_of_integrable_exp`:
  `∫ e^{β|y|} dμ < ∞` (`β ≥ 0`, the class `𝓜_G^β`) implies Gaussian temperedness.

## Conditional corollaries (decision D6)

* `T2_Growth_lower_all_p`, `T2_Growth_lower_top_all_p`: `T2:Growth(1)` for every `p ≥ 2`, from
  the `p = 2` hypotheses on `E|X|²` via `L2_Growth`;
* `T2_Growth_three`, `T2_Growth_three_top`: `T2:Growth(3)`; the `ϑ = 0` part at `p = 2`
  (`λ̲(2) = λ̄(2) = λ²/2` for `β ≥ λ²/(2ν)`), the `ϑ ≠ 0` part for every `p ≥ 2`.

The moment hypotheses remain named hypotheses (`E2:SecMom-Lower`, `E2:SecMom-Up`); they are
discharged for the solution in Waves S2–S5.
-/

set_option autoImplicit false

public section

open scoped ENNReal
open Real MeasureTheory Set Filter

namespace ChenDalang15

namespace S1Glue

/-- The paper's `J₀^*(t,x) = (G_ν(t,·) * |μ|)(x)` for a nonnegative measure, as a lower
integral in `[0,∞]` (defined for every measure; no integrability hypothesis). -/
noncomputable def lJ0 (ν : ℝ) (μ : Measure ℝ) (t x : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (G ν t (x - z)) ∂μ

/-- Scaling bridge: `J₀*(t,x) = lheatFlow μ (νt) x`. -/
theorem lJ0_eq_lheatFlow (ν : ℝ) (μ : Measure ℝ) (t x : ℝ) :
    lJ0 ν μ t x = RoughHeatKernel.lheatFlow μ (ν * t) x := by
  simp only [lJ0, RoughHeatKernel.lheatFlow, G_eq_heatKernel]

theorem G_nonneg' (ν t x : ℝ) : 0 ≤ G ν t x := GrowthLower.G_nonneg ν t x

/-- `ofReal (J₀(t,x)) ≤ J₀*(t,x)` for every measure (the Bochner `J₀` is `0` when the integral
diverges). -/
theorem ofReal_J0_le_lJ0 (ν : ℝ) (μ : Measure ℝ) (t x : ℝ) :
    ENNReal.ofReal (J0 ν μ t x) ≤ lJ0 ν μ t x :=
  GrowthUpper.ofReal_integral_le_lintegral fun _ => G_nonneg' _ _ _

/-- For a Gaussian-tempered `μ`, `ν > 0`, `t > 0`: `J₀*(t,x) = ofReal (J₀(t,x))`. -/
theorem lJ0_eq_ofReal_J0 {μ : Measure ℝ} (hT : RoughHeatKernel.IsGaussianTempered μ) {ν t : ℝ}
    (hν : 0 < ν) (ht : 0 < t) (x : ℝ) : lJ0 ν μ t x = ENNReal.ofReal (J0 ν μ t x) := by
  rw [lJ0_eq_lheatFlow, GrowthLower.J0_eq_heatFlow,
    RoughHeatKernel.ofReal_heatFlow hT (mul_pos hν ht)]

theorem lJ0_lt_top {μ : Measure ℝ} (hT : RoughHeatKernel.IsGaussianTempered μ) {ν t : ℝ}
    (hν : 0 < ν) (ht : 0 < t) (x : ℝ) : lJ0 ν μ t x < ⊤ := by
  rw [lJ0_eq_ofReal_J0 hT hν ht]
  exact ENNReal.ofReal_lt_top

theorem measurable_lJ0 (ν : ℝ) (μ : Measure ℝ) [SFinite μ] (t : ℝ) :
    Measurable (lJ0 ν μ t) := by
  have hm : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (G ν t (q.1 - q.2)) := by
    have := (GrowthUpper.measurable_G ν t).comp (measurable_fst.sub measurable_snd)
    exact this.ennreal_ofReal
  exact hm.lintegral_prod_right'

/-- The pointwise-in-time step at general `ν`: for `0 < s < t`,
`∫⁻ J₀*(s,y)² G_{ν/2}(t−s,x−y) dy ≤ 2√(t/s) J₀*(2t,x)²`. -/
theorem lintegral_lJ0_sq_mul_G_le (μ : Measure ℝ) [SFinite μ] {ν s t : ℝ} (hν : 0 < ν)
    (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ∫⁻ y, lJ0 ν μ s y ^ 2 * ENNReal.ofReal (G (ν / 2) (t - s) (x - y)) ≤
      ENNReal.ofReal (2 * Real.sqrt (t / s)) * lJ0 ν μ (2 * t) x ^ 2 := by
  have h := RoughHeatKernel.lintegral_sq_lheatFlow_mul_le μ (mul_pos hν hs)
    (mul_lt_mul_of_pos_left hst hν) x
  have e1 : (ν * t - ν * s) / 2 = ν / 2 * (t - s) := by ring
  have e2 : ν * t / (ν * s) = t / s := by field_simp
  have e3 : 2 * (ν * t) = ν * (2 * t) := by ring
  rw [e1, e2, e3] at h
  simpa only [lJ0_eq_lheatFlow, G_eq_heatKernel] using h

end S1Glue

open S1Glue

/-- **Chen–Dalang (2015), Lemma `L2:InDt`, display `E2:InDt-A`, at general `ν`, lower-integral
form.** For every s-finite measure `μ ≥ 0`, `ν > 0`, `t > 0`, `x ∈ ℝ` and measurable
`h : ℝ → [0,∞]` (the kernel `K(r,z) = G_{ν/2}(r,z) h(r)`):
`∫⁻_0^t ∫⁻ J₀*(s,y)² G_{ν/2}(t−s,x−y) h(t−s) dy ds ≤ 2√t J₀*(2t,x)² ∫⁻_0^t h(t−s)/√s ds`. -/
theorem L2_InDt_A (μ : Measure ℝ) [SFinite μ] {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : ℝ)
    {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ s in Ioo 0 t, ∫⁻ y, lJ0 ν μ s y ^ 2 * ENNReal.ofReal (G (ν / 2) (t - s) (x - y)) *
        h (t - s) ≤
      ENNReal.ofReal (2 * Real.sqrt t) * lJ0 ν μ (2 * t) x ^ 2 *
        ∫⁻ s in Ioo 0 t, h (t - s) * ENNReal.ofReal (1 / Real.sqrt s) := by
  have hpt : ∀ s ∈ Ioo 0 t, ∫⁻ y, lJ0 ν μ s y ^ 2 *
      ENNReal.ofReal (G (ν / 2) (t - s) (x - y)) * h (t - s) ≤
      ENNReal.ofReal (2 * Real.sqrt t) * lJ0 ν μ (2 * t) x ^ 2 *
        (h (t - s) * ENNReal.ofReal (1 / Real.sqrt s)) := by
    intro s hs
    have hmeas : Measurable fun y => lJ0 ν μ s y ^ 2 *
        ENNReal.ofReal (G (ν / 2) (t - s) (x - y)) :=
      ((measurable_lJ0 ν μ s).pow_const 2).mul
        ((GrowthUpper.measurable_G _ _).comp (measurable_const.sub measurable_id)).ennreal_ofReal
    rw [lintegral_mul_const _ hmeas]
    calc (∫⁻ y, lJ0 ν μ s y ^ 2 * ENNReal.ofReal (G (ν / 2) (t - s) (x - y))) * h (t - s)
        ≤ ENNReal.ofReal (2 * Real.sqrt (t / s)) * lJ0 ν μ (2 * t) x ^ 2 * h (t - s) := by
          gcongr
          exact lintegral_lJ0_sq_mul_G_le μ hν hs.1 hs.2 x
      _ = _ := by
          rw [show 2 * Real.sqrt (t / s) = 2 * Real.sqrt t * (1 / Real.sqrt s) by
              rw [Real.sqrt_div ht.le]; ring,
            ENNReal.ofReal_mul (by positivity)]
          ring
  calc _ ≤ ∫⁻ s in Ioo 0 t, ENNReal.ofReal (2 * Real.sqrt t) * lJ0 ν μ (2 * t) x ^ 2 *
          (h (t - s) * ENNReal.ofReal (1 / Real.sqrt s)) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = _ := lintegral_const_mul _ (by fun_prop)

namespace S1Glue

/-- Reduction of `L2:InDt` to `L2_InDt_A` for a real kernel `k` with
`k(r,z) ≤ G_{ν/2}(r,z) h(r)` (`r > 0`), in the integrand form of `MomentBridge`. -/
theorem lintegral_conv_le_of_kernel_le (μ : Measure ℝ) [SFinite μ] {ν t : ℝ} (hν : 0 < ν)
    (ht : 0 < t) (x : ℝ) {k : ℝ → ℝ → ℝ} {hr : ℝ → ℝ}
    (hk : ∀ r, 0 < r → ∀ z, k r z ≤ G (ν / 2) r z * hr r) (hr0 : ∀ r, 0 < r → 0 ≤ hr r)
    (hrm : Measurable hr) :
    ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * k (t - s) (x - y)) ≤
      ENNReal.ofReal (2 * Real.sqrt t) * lJ0 ν μ (2 * t) x ^ 2 *
        ∫⁻ s in Ioo 0 t, ENNReal.ofReal (hr (t - s)) * ENNReal.ofReal (1 / Real.sqrt s) := by
  rw [setLIntegral_congr Ioo_ae_eq_Ioc.symm]
  refine le_trans (setLIntegral_mono' measurableSet_Ioo fun s hs => ?_)
    (L2_InDt_A μ hν ht x (h := fun r => ENNReal.ofReal (hr r)) hrm.ennreal_ofReal)
  have hts : 0 < t - s := sub_pos.mpr hs.2
  refine lintegral_mono fun y => ?_
  have hG := G_nonneg' (ν / 2) (t - s) (x - y)
  have hh := hr0 (t - s) hts
  calc ENNReal.ofReal (J0 ν μ s y ^ 2 * k (t - s) (x - y))
      ≤ ENNReal.ofReal (J0 ν μ s y ^ 2 * (G (ν / 2) (t - s) (x - y) * hr (t - s))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hk _ hts _) (sq_nonneg _))
    _ = ENNReal.ofReal (J0 ν μ s y) ^ 2 * ENNReal.ofReal (G (ν / 2) (t - s) (x - y)) *
          ENNReal.ofReal (hr (t - s)) := by
        rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul hG,
          ENNReal.ofReal_pow (GrowthLower.J0_nonneg _ _ _ _), mul_assoc]
    _ ≤ lJ0 ν μ s y ^ 2 * ENNReal.ofReal (G (ν / 2) (t - s) (x - y)) *
          ENNReal.ofReal (hr (t - s)) := by
        gcongr
        exact ofReal_J0_le_lJ0 ν μ s y

/-- `∫⁻_0^t (t−s)^{-1/2} s^{-1/2} ds = π`, in the form used for `𝓛₀`. -/
theorem lintegral_rpow_sub_mul_inv_sqrt {t : ℝ} (ht : 0 < t) (a : ℝ) (ha : 0 ≤ a) :
    ∫⁻ s in Ioo 0 t, ENNReal.ofReal (a * (t - s) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (1 / Real.sqrt s) = ENNReal.ofReal (a * π) := by
  calc ∫⁻ s in Ioo 0 t, ENNReal.ofReal (a * (t - s) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (1 / Real.sqrt s)
      = ∫⁻ s in Ioo 0 t, ENNReal.ofReal a * ENNReal.ofReal (1 / Real.sqrt (s * (t - s))) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
        have hs0 : 0 < s := hs.1
        have hts : 0 < t - s := sub_pos.mpr hs.2
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.rpow_neg hts.le, ← Real.sqrt_eq_rpow, Real.sqrt_mul hs0.le]
        field_simp
    _ = ENNReal.ofReal a * ENNReal.ofReal π := by
        rw [lintegral_const_mul _ (by fun_prop), RoughHeatKernel.lintegral_arcsine ht]
    _ = ENNReal.ofReal (a * π) := (ENNReal.ofReal_mul ha).symm

theorem L0_eq (ν lam r z : ℝ) : L ν lam 0 r z = lam ^ 2 * G ν r z ^ 2 := by simp only [L]

theorem hK_nonneg {ν lam r : ℝ} (hν : 0 < ν) : 0 ≤ GrowthUpper.hK ν lam r := by
  unfold GrowthUpper.hK
  positivity

theorem measurable_hK (ν lam : ℝ) : Measurable (GrowthUpper.hK ν lam) := by
  unfold GrowthUpper.hK
  fun_prop

end S1Glue

/-- **Chen–Dalang (2015), Lemma `L2:InDt`, display `E2:InDt-L0`, at general `ν`,
lower-integral form.** For every s-finite measure `μ ≥ 0`, `ν > 0`, `t > 0`:
`∫⁻_{(0,t]} ∫⁻ J₀(s,y)² 𝓛₀(t−s,x−y) dy ds ≤ λ²√(πt/ν) J₀*(2t,x)²`. -/
theorem L2_InDt_L0 (μ : Measure ℝ) [SFinite μ] {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (lam x : ℝ) :
    ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * L ν lam 0 (t - s) (x - y)) ≤
      ENNReal.ofReal (lam ^ 2 * Real.sqrt (π * t / ν)) * lJ0 ν μ (2 * t) x ^ 2 := by
  set a := lam ^ 2 * (1 / Real.sqrt (4 * π * ν)) with ha_def
  have ha : 0 ≤ a := by positivity
  have h := lintegral_conv_le_of_kernel_le μ hν ht x (k := L ν lam 0)
    (hr := fun r => a * r ^ (-(1 / 2 : ℝ)))
    (fun r hr z => le_of_eq (by rw [L0_eq, G_sq hν hr z]; ring))
    (fun r hr => by positivity) (by fun_prop)
  rw [lintegral_rpow_sub_mul_inv_sqrt ht a ha] at h
  refine h.trans (le_of_eq ?_)
  rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have h4 : Real.sqrt (4 * π * ν) = 2 * Real.sqrt π * Real.sqrt ν := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hd : Real.sqrt (π * t / ν) = Real.sqrt π * Real.sqrt t / Real.sqrt ν := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul Real.pi_pos.le]
  have hπ : π = Real.sqrt π * Real.sqrt π := (Real.mul_self_sqrt Real.pi_pos.le).symm
  have hν' : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hπ' : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  rw [ha_def, h4, hd]
  conv_lhs => rw [hπ]
  field_simp
  rw [Real.sqrt_sq hπ'.le]

/-- **Chen–Dalang (2015), Lemma `L2:InDt`, display `E2:InDt`, at general `ν`, lower-integral
form.** For every s-finite measure `μ ≥ 0`, `ν > 0`, `t > 0` and every `λ`:
`∫⁻_{(0,t]} ∫⁻ J₀(s,y)² 𝓚_λ(t−s,x−y) dy ds ≤ λ²√(πt/ν) (1 + 2e^{λ⁴t/(4ν)}) J₀*(2t,x)²`. -/
theorem L2_InDt (μ : Measure ℝ) [SFinite μ] {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (lam x : ℝ) :
    ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * K ν lam (t - s) (x - y)) ≤
      ENNReal.ofReal (lam ^ 2 * Real.sqrt (π * t / ν) *
        (1 + 2 * Real.exp (lam ^ 4 * t / (4 * ν)))) * lJ0 ν μ (2 * t) x ^ 2 := by
  have h := lintegral_conv_le_of_kernel_le μ hν ht x (k := K ν lam)
    (hr := GrowthUpper.hK ν lam) (fun r hr z => (GrowthUpper.K_le_G_mul_hK hν hr z).2)
    (fun r _ => hK_nonneg hν) (measurable_hK ν lam)
  refine h.trans ?_
  rcases eq_or_ne lam 0 with rfl | hlam
  · have : ∀ r, GrowthUpper.hK ν 0 r = 0 := fun r => by simp [GrowthUpper.hK]
    simp [this]
  obtain ⟨hint, hle⟩ := GrowthUpper.hK_integral hν hlam ht
  have hIoo : IntegrableOn (fun s => GrowthUpper.hK ν lam (t - s) / Real.sqrt s) (Ioo 0 t) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hint).mono_set
      Ioo_subset_Ioc_self
  have htime : ∫⁻ s in Ioo 0 t, ENNReal.ofReal (GrowthUpper.hK ν lam (t - s)) *
      ENNReal.ofReal (1 / Real.sqrt s) ≤
      ENNReal.ofReal (lam ^ 2 * Real.sqrt π / Real.sqrt ν *
        (1 / 2 + Real.exp (lam ^ 4 * t / (4 * ν)))) := by
    calc _ = ∫⁻ s in Ioo 0 t, ENNReal.ofReal (GrowthUpper.hK ν lam (t - s) / Real.sqrt s) := by
          refine lintegral_congr fun s => ?_
          rw [← ENNReal.ofReal_mul (hK_nonneg hν), mul_one_div]
      _ = ENNReal.ofReal (∫ s in Ioo 0 t, GrowthUpper.hK ν lam (t - s) / Real.sqrt s) :=
          (ofReal_integral_eq_lintegral_ofReal hIoo
            (Eventually.of_forall fun s => div_nonneg (hK_nonneg hν) (Real.sqrt_nonneg _))).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) hle)
          rw [intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]
  calc _ ≤ ENNReal.ofReal (2 * Real.sqrt t) * lJ0 ν μ (2 * t) x ^ 2 *
        ENNReal.ofReal (lam ^ 2 * Real.sqrt π / Real.sqrt ν *
          (1 / 2 + Real.exp (lam ^ 4 * t / (4 * ν)))) := by gcongr
    _ = _ := by
      rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [Real.sqrt_div (by positivity), Real.sqrt_mul Real.pi_pos.le]
      ring

/-- `L2:InDt`, finiteness (`E2:InDt`, "`< +∞`"): for a Gaussian-tempered `μ`, `ν > 0`, `t > 0`,
the lower-integral convolution `∫⁻_{(0,t]} ∫⁻ J₀² 𝓚_λ` is finite. -/
theorem L2_InDt_lt_top {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (lam x : ℝ) :
    ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * K ν lam (t - s) (x - y)) < ⊤ :=
  (L2_InDt μ hν ht lam x).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.pow_lt_top (lJ0_lt_top hT hν (by positivity) x)))

/-- `L2:InDt` (`E2:InDt-L0`), finiteness for a Gaussian-tempered `μ`. -/
theorem L2_InDt_L0_lt_top {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (lam x : ℝ) :
    ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * L ν lam 0 (t - s) (x - y)) < ⊤ :=
  (L2_InDt_L0 μ hν ht lam x).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.pow_lt_top (lJ0_lt_top hT hν (by positivity) x)))

/-- **`L2:InDt` (`E2:InDt`) for Gaussian-tempered `μ`, with the real `J₀`.** For a
Gaussian-tempered `μ ≥ 0`, `ν > 0`, `t > 0`:
`∫⁻_{(0,t]} ∫⁻ J₀² 𝓚_λ ≤ λ²√(πt/ν) (1 + 2e^{λ⁴t/(4ν)}) J₀(2t,x)²`. -/
theorem L2_InDt_tempered {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (lam x : ℝ) :
    ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * K ν lam (t - s) (x - y)) ≤
      ENNReal.ofReal (lam ^ 2 * Real.sqrt (π * t / ν) *
        (1 + 2 * Real.exp (lam ^ 4 * t / (4 * ν))) * J0 ν μ (2 * t) x ^ 2) := by
  refine (L2_InDt μ hν ht lam x).trans (le_of_eq ?_)
  rw [lJ0_eq_ofReal_J0 hT hν (by positivity), ← ENNReal.ofReal_pow (GrowthLower.J0_nonneg _ _ _ _),
    ← ENNReal.ofReal_mul (by positivity)]

/-- **`L2:InDt` (`E2:InDt`) in the paper's Bochner form**, for Gaussian-tempered `μ ≥ 0`:
`(J₀² ⋆ 𝓚_λ)(t,x) ≤ λ²√(πt/ν) (1 + 2e^{λ⁴t/(4ν)}) J₀(2t,x)²`. -/
theorem L2_InDt_stConv {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (lam x : ℝ) :
    stConv (fun s y => J0 ν μ s y ^ 2) (K ν lam) t x ≤
      lam ^ 2 * Real.sqrt (π * t / ν) * (1 + 2 * Real.exp (lam ^ 4 * t / (4 * ν))) *
        J0 ν μ (2 * t) x ^ 2 := by
  have h := L2_InDt_tempered hT hν ht lam x
  rw [← MomentBridge.stConv_J0_sq_K_eq_lintegral hT hν lam ht x] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-! ### Gaussian-tempered bridges -/

namespace S1Glue

/-- The companion's standing hypothesis on `μ` (`𝓜_H`: `∫ e^{−ay²} dμ < ∞` for all `a > 0`,
as Bochner integrability) is exactly `RoughHeatKernel.IsGaussianTempered μ`. -/
theorem integrable_exp_neg_sq_iff {μ : Measure ℝ} :
    (∀ a > 0, Integrable (fun y => Real.exp (-a * y ^ 2)) μ) ↔
      RoughHeatKernel.IsGaussianTempered μ :=
  ⟨GrowthLower.isGaussianTempered, fun hT _ ha => hT.integrable_exp_neg_mul_sq ha⟩

/-- `∫ e^{β|y|} dμ < ∞` with `β ≥ 0` (the class `𝓜_G^β`) implies Gaussian temperedness. -/
theorem isGaussianTempered_of_integrable_exp {μ : Measure ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hI : Integrable (fun y => Real.exp (β * |y|)) μ) : RoughHeatKernel.IsGaussianTempered μ :=
  haveI := GrowthUpper.isFiniteMeasure_of_integrable_exp hβ hI
  RoughHeatKernel.isGaussianTempered_of_isFiniteMeasure μ

/-- `∫ e^{β|y|} dμ < ∞` with `β ≥ 0` implies the companion's hypothesis
`∀ a > 0, ∫ e^{−ay²} dμ < ∞`. -/
theorem integrable_exp_neg_sq_of_integrable_exp {μ : Measure ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hI : Integrable (fun y => Real.exp (β * |y|)) μ) :
    ∀ a > 0, Integrable (fun y => Real.exp (-a * y ^ 2)) μ :=
  integrable_exp_neg_sq_iff.2 (isGaussianTempered_of_integrable_exp hβ hI)

end S1Glue

/-! ### Conditional corollaries of `T2:Growth` -/

/-- **`T2:Growth(1)`, `ϑ = 0`, every `p ≥ 2`**, conditional on the `p = 2` lower moment bound
(`E2:SecMom-Lower`). For a random field `X` on a probability space, a nonzero measure
`μ ∈ 𝓜_{H,+}(ℝ)`, `ν > 0`, `l ≠ 0` (`l = lip_ρ`), if `(J₀² ⋆ 𝓚_l)(t,x) ≤ E|X(t,x)|²` for all
`t > 0`, then `λ̲(p) ≥ l²/2` for every `p ≥ 2`. -/
theorem T2_Growth_lower_all_p {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ → ℝ → Ω → ℝ) (hX : ∀ t x, AEMeasurable (X t x) P)
    {μ : Measure ℝ} (hμ0 : μ ≠ 0) (hμ : ∀ a > 0, Integrable (fun y => Real.exp (-a * y ^ 2)) μ)
    {ν l : ℝ} (hν : 0 < ν) (hl : l ≠ 0)
    (hg : ∀ t > 0, ∀ x,
      ENNReal.ofReal (stConv (fun s y => J0 ν μ s y ^ 2) (K ν l) t x) ≤ momentFn P X 2 t x)
    {p : ℝ} (hp : 2 ≤ p) :
    ((l ^ 2 / 2 : ℝ) : EReal) ≤ lowerGrowthIndex (momentFn P X p) :=
  (T2_Growth_lower hμ0 hμ hν hl hg).trans (L2_Growth P X hX two_pos hp).1

/-- **`T2:Growth(1)`, `ϑ ≠ 0`, every `p ≥ 2`**, conditional on the `p = 2` lower moment bound
`ϑ² 𝓗(t) = ϑ² (1 ⋆ 𝓚_l)(t,x) ≤ E|X(t,x)|²` (`t > 0`): `λ̲(p) = λ̄(p) = +∞` for every `p ≥ 2`. -/
theorem T2_Growth_lower_top_all_p {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ → ℝ → Ω → ℝ) (hX : ∀ t x, AEMeasurable (X t x) P)
    {ν l v : ℝ} (hν : 0 < ν) (hl : l ≠ 0) (hv : v ≠ 0)
    (hg : ∀ t > 0, ∀ x,
      ENNReal.ofReal (v ^ 2 * stConv (fun _ _ => (1 : ℝ)) (K ν l) t x) ≤ momentFn P X 2 t x)
    {p : ℝ} (hp : 2 ≤ p) :
    lowerGrowthIndex (momentFn P X p) = ⊤ ∧ upperGrowthIndex (momentFn P X p) = ⊤ := by
  obtain ⟨h1, h2⟩ := T2_Growth_lower_top hν hl hv hg
  obtain ⟨m1, m2⟩ := L2_Growth P X hX two_pos hp
  exact ⟨top_le_iff.1 (h1 ▸ m1), top_le_iff.1 (h2 ▸ m2)⟩

/-- **`T2:Growth(3)`, `ϑ = 0`, `p = 2`**, conditional on the two moment bounds. Quasi-linear
`ρ` with `|ρ(u)|² = λ²u²` (so `Lip_ρ = lip_ρ = |λ|`), `λ ≠ 0`, `ν > 0`, `β ≥ λ²/(2ν)`,
a nonzero measure `μ ≥ 0` with `∫ e^{β|y|} dμ < ∞` (`μ ∈ 𝓜_{G,+}^β`). If `g(t,x)` (standing
for `E|u(t,x)|²`) satisfies, for all `t > 0`,

* `E2:SecMom-Lower`: `(J₀² ⋆ 𝓚_λ)(t,x) ≤ g(t,x)` (Bochner form, as in `T2_Growth_lower`), and
* `E2:SecMom-Up`: `g(t,x) ≤ J₀(t,x)² + ∫⁻_{(0,t]} ∫⁻ J₀² 𝓚_λ` (lower-integral form, as in
  `T2_Growth_upper_lintegral`),

then `λ̲(2) = λ̄(2) = λ²/2`. Gaussian temperedness of `μ` is derived from the exponential
moment (`S1Glue.integrable_exp_neg_sq_of_integrable_exp`). -/
theorem T2_Growth_three {μ : Measure ℝ} (hμ0 : μ ≠ 0) {ν β lam : ℝ} (hν : 0 < ν)
    (hlam : lam ≠ 0) (hβ : lam ^ 2 / (2 * ν) ≤ β)
    (hI : Integrable (fun y => Real.exp (β * |y|)) μ) {g : ℝ → ℝ → ℝ≥0∞}
    (hlow : ∀ t > 0, ∀ x,
      ENNReal.ofReal (stConv (fun s y => J0 ν μ s y ^ 2) (K ν lam) t x) ≤ g t x)
    (hup : ∀ t > 0, ∀ x, g t x ≤ ENNReal.ofReal (J0 ν μ t x ^ 2) +
      ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * K ν lam (t - s) (x - y))) :
    lowerGrowthIndex g = ((lam ^ 2 / 2 : ℝ) : EReal) ∧
      upperGrowthIndex g = ((lam ^ 2 / 2 : ℝ) : EReal) := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hlo : ((lam ^ 2 / 2 : ℝ) : EReal) ≤ lowerGrowthIndex g :=
    T2_Growth_lower hμ0 (S1Glue.integrable_exp_neg_sq_of_integrable_exp hβ0.le hI) hν hlam hlow
  have hhi : upperGrowthIndex g ≤ ((lam ^ 2 / 2 : ℝ) : EReal) := by
    have h := T2_Growth_upper_lintegral hν hβ0 hlam hI hup
    rwa [ite_eq_right_iff.2 (fun h => absurd h (not_lt.2 hβ))] at h
  have hmid := lowerGrowthIndex_le_upperGrowthIndex g
  exact ⟨le_antisymm (hmid.trans hhi) hlo, le_antisymm hhi (hlo.trans hmid)⟩

/-- **`T2:Growth(3)`, `ϑ ≠ 0`**, conditional on the `p = 2` lower moment bound. For
`|ρ(u)|² = λ²(ϑ² + u²)`, `λ ≠ 0`, `ϑ ≠ 0`, `ν > 0`: if `ϑ² 𝓗(t) = ϑ² (1 ⋆ 𝓚_λ)(t,x) ≤
E|X(t,x)|²` for all `t > 0`, then `λ̲(p) = λ̄(p) = +∞` for every `p ≥ 2` (no hypothesis on
`μ` is needed beyond what produces the moment bound). -/
theorem T2_Growth_three_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ → ℝ → Ω → ℝ) (hX : ∀ t x, AEMeasurable (X t x) P)
    {ν lam v : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) (hv : v ≠ 0)
    (hg : ∀ t > 0, ∀ x,
      ENNReal.ofReal (v ^ 2 * stConv (fun _ _ => (1 : ℝ)) (K ν lam) t x) ≤ momentFn P X 2 t x)
    {p : ℝ} (hp : 2 ≤ p) :
    lowerGrowthIndex (momentFn P X p) = ⊤ ∧ upperGrowthIndex (momentFn P X p) = ⊤ :=
  T2_Growth_lower_top_all_p P X hX hν hlam hv hg hp

end ChenDalang15

end
