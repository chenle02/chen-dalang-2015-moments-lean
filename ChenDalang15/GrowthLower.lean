module

public import ChenDalang15.H
public import ChenDalang15.GrowthDefs
public import ChenDalang15.Resolvent

/-!
# Lower bound of Theorem `T2:Growth(1)`: the deterministic analysis

Chen–Dalang (2015), Section 2, subsection `SS2:ExpInd-Low` (Lemma `L2:pLbd` and the proof of
Theorem `T2:Growth(1)`).

* `L2_pLbd`: for `μ ≠ 0` with `∫ e^{-a y²} μ(dy) < ∞` (all `a > 0`), `ε > 0`, `ξ ∈ (0, ν)`,
  there is `a > 0` with `a G_ξ(t,x) ≤ J₀(t,x)` for `t ≥ ε`. The proof is the paper's: the
  quadratic identity `x²/ξ + y²/(ν-ξ) − (x-y)²/ν = ((ν-ξ)x + ξy)²/(ξ(ν-ξ)ν)` gives
  `G_ν(t,x-y) ≥ √(ξ/ν) G_ξ(t,x) e^{-y²/(2(ν-ξ)ε)}`.
* `lower_envelope_gaussian` (case `ϑ = 0`): from the moment hypothesis
  `f ≥ J₀² ⋆ 𝓚` (consequence of `E2:SecMom-Lower`), `f(t,x) ≥ c t⁻¹ e^{λ⁴t/(4ν)} G_{ξ/2}(t,x)`
  for large `t`. `lower_envelope_gaussian'` is the stronger form without `t⁻¹`.
* `lower_envelope_uniform` (case `ϑ ≠ 0`): from `f ≥ ϑ² (1 ⋆ 𝓚) = ϑ² 𝓗`,
  `f(t,x) ≥ (ϑ²/2) e^{λ⁴t/(4ν)}` for `t ≥ 4ν/λ⁴`.

## Integrability (the "hard" direction)

`stConv` is a Bochner integral, which is `0` on non-integrable integrands, so a lower bound on
`J₀² ⋆ 𝓚` needs the integrand to be integrable. This is proved, not assumed: by the
Chen–Dalang convolution estimate (`RoughHeatKernel.lintegral_heatKernel_mul_mul_le`, applied
at time scale `ν`, `lintegral_sq_lheatFlow_mul_le`),
`∫ J₀(s,y)² G_{ν/2}(t-s,x-y) dy ≤ 2√(t/s) J₀(2t,x)²` (in `ℝ≥0∞`), and with
`k(r) ≤ (A + B√t)/√r` this is `≤ C/√(s(t-s))`, whose integral over `(0,t)` is `Cπ`
(`RoughHeatKernel.lintegral_arcsine`).

## Route to the envelope (differs from the paper only in bookkeeping)

The paper bounds the whole time integral `∫_ε^t`; here it suffices to keep `s ∈ (1, 2]`
(`ε = 1`, `t ≥ 3`), where `J₀ ≥ a G_ξ`, `𝓚(t-s,·) ≥ (λ⁴/(4ν)) e^{λ⁴(t-s)/(4ν)} G_{ν/2}(t-s,·)`
(`E:K`, `Φ ≥ 1/2`), `G_ξ² = G_{ξ/2} (4πξ)^{-1/2} s^{-1/2}` (`L2:GG`), the semigroup identity,
and `p_v(x) ≥ √(ξ/ν) p_{ξt/2}(x)` for `ξt/2 ≤ v ≤ νt/2`. This yields a lower bound
`c e^{λ⁴t/(4ν)} G_{ξ/2}(t,x)`, which is stronger than the paper's (by the factor `t`).
-/

set_option autoImplicit false

public section

namespace ChenDalang15

open Real MeasureTheory Set

namespace GrowthLower

/-- The standing hypothesis on `μ` gives `RoughHeatKernel.IsGaussianTempered μ`. -/
theorem isGaussianTempered {μ : Measure ℝ}
    (hμ : ∀ a > 0, Integrable (fun y => Real.exp (-a * y ^ 2)) μ) :
    RoughHeatKernel.IsGaussianTempered μ := fun a ha =>
  (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).mp
    (hμ a ha).2

theorem G_nonneg (ν t x : ℝ) : 0 ≤ G ν t x := by
  unfold G
  positivity

theorem J0_eq_heatFlow (ν : ℝ) (μ : Measure ℝ) (t x : ℝ) :
    J0 ν μ t x = RoughHeatKernel.heatFlow μ (ν * t) x := by
  simp only [J0, RoughHeatKernel.heatFlow, G_eq_heatKernel]

theorem J0_nonneg (ν : ℝ) (μ : Measure ℝ) (t x : ℝ) : 0 ≤ J0 ν μ t x :=
  integral_nonneg fun _ => G_nonneg _ _ _

/-- The algebraic core of `L2:pLbd`:
`x²/ξ + y²/(ν-ξ) - (x-y)²/ν = ((ν-ξ)x + ξy)² / (ξ(ν-ξ)ν) ≥ 0`. -/
theorem sq_sub_div_le {ν ξ : ℝ} (hξ : 0 < ξ) (hξν : ξ < ν) (x y : ℝ) :
    (x - y) ^ 2 / ν ≤ x ^ 2 / ξ + y ^ 2 / (ν - ξ) := by
  have hν : 0 < ν := hξ.trans hξν
  have hd : 0 < ν - ξ := sub_pos.mpr hξν
  have key : x ^ 2 / ξ + y ^ 2 / (ν - ξ) - (x - y) ^ 2 / ν =
      ((ν - ξ) * x + ξ * y) ^ 2 / (ξ * (ν - ξ) * ν) := by
    field_simp
    ring
  have : 0 ≤ ((ν - ξ) * x + ξ * y) ^ 2 / (ξ * (ν - ξ) * ν) := by positivity
  linarith

/-- Pointwise comparison behind `L2:pLbd`: for `t ≥ ε`,
`√(ξ/ν) G_ξ(t,x) e^{-y²/(2(ν-ξ)ε)} ≤ G_ν(t,x-y)`. -/
theorem G_lower_pointwise {ν ξ ε t : ℝ} (hξ : 0 < ξ) (hξν : ξ < ν) (hε : 0 < ε) (ht : ε ≤ t)
    (x y : ℝ) :
    Real.sqrt ξ / Real.sqrt ν * G ξ t x * Real.exp (-(1 / (2 * (ν - ξ) * ε)) * y ^ 2) ≤
      G ν t (x - y) := by
  have hν : 0 < ν := hξ.trans hξν
  have hd : 0 < ν - ξ := sub_pos.mpr hξν
  have ht0 : 0 < t := hε.trans_le ht
  have hpre : Real.sqrt ξ / Real.sqrt ν * (1 / Real.sqrt (2 * π * ξ * t)) =
      1 / Real.sqrt (2 * π * ν * t) := by
    rw [show 2 * π * ξ * t = ξ * (2 * π * t) by ring, show 2 * π * ν * t = ν * (2 * π * t) by ring,
      Real.sqrt_mul hξ.le, Real.sqrt_mul hν.le]
    have : 0 < Real.sqrt ξ := Real.sqrt_pos.mpr hξ
    have : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
    have : 0 < Real.sqrt (2 * π * t) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  have hexp : Real.exp (-x ^ 2 / (2 * ξ * t)) * Real.exp (-(1 / (2 * (ν - ξ) * ε)) * y ^ 2) ≤
      Real.exp (-(x - y) ^ 2 / (2 * ν * t)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 : -(1 / (2 * (ν - ξ) * ε)) * y ^ 2 ≤ -(y ^ 2 / (2 * (ν - ξ) * t)) := by
      rw [neg_mul, neg_le_neg_iff, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left (sq_nonneg y) (by positivity)
        (by nlinarith)
    have h2 := sq_sub_div_le hξ hξν x y
    have e1 : -x ^ 2 / (2 * ξ * t) = -(x ^ 2 / ξ) / (2 * t) := by field_simp
    have e2 : -(y ^ 2 / (2 * (ν - ξ) * t)) = -(y ^ 2 / (ν - ξ)) / (2 * t) := by field_simp
    have e3 : -(x - y) ^ 2 / (2 * ν * t) = -((x - y) ^ 2 / ν) / (2 * t) := by field_simp
    rw [e1, e3]
    rw [e2] at h1
    have h3 : -(x ^ 2 / ξ) / (2 * t) + -(y ^ 2 / (ν - ξ)) / (2 * t) ≤
        -((x - y) ^ 2 / ν) / (2 * t) := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  unfold G
  calc Real.sqrt ξ / Real.sqrt ν * (1 / Real.sqrt (2 * π * ξ * t) *
        Real.exp (-x ^ 2 / (2 * ξ * t))) * Real.exp (-(1 / (2 * (ν - ξ) * ε)) * y ^ 2)
      = (Real.sqrt ξ / Real.sqrt ν * (1 / Real.sqrt (2 * π * ξ * t))) *
        (Real.exp (-x ^ 2 / (2 * ξ * t)) * Real.exp (-(1 / (2 * (ν - ξ) * ε)) * y ^ 2)) := by
        ring
    _ ≤ 1 / Real.sqrt (2 * π * ν * t) * Real.exp (-(x - y) ^ 2 / (2 * ν * t)) := by
        rw [hpre]
        exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- `Φ` is monotone (its derivative is the Gaussian density). -/
theorem Phi_monotone : Monotone Phi :=
  monotone_of_deriv_nonneg (fun x => (hasDerivAt_Phi x).differentiableAt) fun x => by
    rw [(hasDerivAt_Phi x).deriv]
    unfold phiDensity
    positivity

/-- `Φ(x) ≥ Φ(0) = 1/2` for `x ≥ 0`. -/
theorem half_le_Phi {x : ℝ} (hx : 0 ≤ x) : 1 / 2 ≤ Phi x :=
  Phi_zero ▸ Phi_monotone hx

/-- `e^{γt} ≥ 2` once `γ t ≥ 1`. -/
theorem two_le_exp {u : ℝ} (hu : 1 ≤ u) : 2 ≤ Real.exp u := by
  have := Real.add_one_le_exp u
  linarith


/-! ### Measurability -/

attribute [local fun_prop] RoughHeatKernel.measurable_heatKernel

/-- The scalar factor `k(r)` of `E:K`, with the same body as `ChenDalang15.kC` (whose body
is not exposed outside `ChenDalang15.H`). -/
@[expose] noncomputable def kC (ν l r : ℝ) : ℝ :=
  l ^ 2 / Real.sqrt (4 * π * ν * r) +
    l ^ 4 / (2 * ν) * Real.exp (l ^ 4 * r / (4 * ν)) * Phi (l ^ 2 * Real.sqrt (r / (2 * ν)))

/-- `𝓚(r,z) = G_{ν/2}(r,z) k(r)` for `r > 0` (display `E:K`). -/
theorem K_eq_kC {ν l r : ℝ} (hν : 0 < ν) (hr : 0 < r) (z : ℝ) :
    K ν l r z = G (ν / 2) r z * kC ν l r :=
  K_eq hν hr z

theorem measurable_G_uncurry (ν : ℝ) : Measurable (fun p : ℝ × ℝ => G ν p.1 p.2) := by
  unfold G
  fun_prop

theorem measurable_kC (ν l : ℝ) : Measurable (kC ν l) := by
  have hΦ : Measurable Phi := continuous_Phi.measurable
  unfold kC
  fun_prop

theorem stronglyMeasurable_J0 (ν : ℝ) (μ : Measure ℝ) [SFinite μ] :
    StronglyMeasurable (fun p : ℝ × ℝ => J0 ν μ p.1 p.2) := by
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => G ν q.1.1 (q.1.2 - q.2)) :=
    (measurable_G_uncurry ν).comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'

/-- The integrand of `(J₀² ⋆ 𝓚)(t,x)` with `𝓚` in closed form (`E:K`). -/
@[expose] noncomputable def integrand (ν : ℝ) (μ : Measure ℝ) (l t x : ℝ) (s y : ℝ) : ℝ :=
  J0 ν μ s y ^ 2 * (G (ν / 2) (t - s) (x - y) * kC ν l (t - s))

/-- The inner (space) integral of `integrand`. -/
@[expose] noncomputable def phiC (ν : ℝ) (μ : Measure ℝ) (l t x : ℝ) (s : ℝ) : ℝ :=
  ∫ y, integrand ν μ l t x s y

theorem stronglyMeasurable_integrand (ν : ℝ) (μ : Measure ℝ) [SFinite μ] (l t x : ℝ) :
    StronglyMeasurable (fun p : ℝ × ℝ => integrand ν μ l t x p.1 p.2) := by
  have h1 := (stronglyMeasurable_J0 ν μ).measurable
  have h2 : Measurable (fun p : ℝ × ℝ => G (ν / 2) (t - p.1) (x - p.2)) :=
    (measurable_G_uncurry (ν / 2)).comp ((measurable_const.sub measurable_fst).prodMk
      (measurable_const.sub measurable_snd))
  have h3 : Measurable (fun p : ℝ × ℝ => kC ν l (t - p.1)) :=
    (measurable_kC ν l).comp (measurable_const.sub measurable_fst)
  exact (((h1.pow_const 2).mul (h2.mul h3))).stronglyMeasurable

theorem stronglyMeasurable_phiC (ν : ℝ) (μ : Measure ℝ) [SFinite μ] (l t x : ℝ) :
    StronglyMeasurable (phiC ν μ l t x) :=
  (stronglyMeasurable_integrand ν μ l t x).integral_prod_right'

/-! ### The scalar `k(r)` of `E:K` -/

theorem kC_nonneg {ν l r : ℝ} (hν : 0 < ν) : 0 ≤ kC ν l r := by
  have := half_le_Phi (x := l ^ 2 * Real.sqrt (r / (2 * ν))) (by positivity)
  unfold kC
  have : 0 ≤ Phi (l ^ 2 * Real.sqrt (r / (2 * ν))) := by linarith
  positivity

/-- `k(r) ≥ λ⁴/(4ν) e^{λ⁴r/(4ν)}` (drop the first term, `Φ ≥ 1/2`). -/
theorem kC_lower {ν l r : ℝ} (hν : 0 < ν) :
    l ^ 4 / (4 * ν) * Real.exp (l ^ 4 * r / (4 * ν)) ≤ kC ν l r := by
  have hΦ := half_le_Phi (x := l ^ 2 * Real.sqrt (r / (2 * ν))) (by positivity)
  have h1 : 0 ≤ l ^ 2 / Real.sqrt (4 * π * ν * r) := by positivity
  have h2 : 0 ≤ l ^ 4 / (2 * ν) * Real.exp (l ^ 4 * r / (4 * ν)) := by positivity
  unfold kC
  have : l ^ 4 / (4 * ν) * Real.exp (l ^ 4 * r / (4 * ν)) =
      l ^ 4 / (2 * ν) * Real.exp (l ^ 4 * r / (4 * ν)) * (1 / 2) := by
    field_simp
    ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left hΦ h2]

/-- `k(r) ≤ (A + B√t)/√r` for `0 < r ≤ t`. -/
theorem kC_upper {ν l r t : ℝ} (hν : 0 < ν) (hr : 0 < r) (hrt : r ≤ t) :
    kC ν l r ≤
      (l ^ 2 / Real.sqrt (4 * π * ν) + l ^ 4 / (2 * ν) * Real.exp (l ^ 4 * t / (4 * ν)) *
        Phi (l ^ 2 * Real.sqrt (t / (2 * ν))) * Real.sqrt t) / Real.sqrt r := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsrt : Real.sqrt r ≤ Real.sqrt t := Real.sqrt_le_sqrt hrt
  set B := l ^ 4 / (2 * ν) * Real.exp (l ^ 4 * t / (4 * ν)) * Phi (l ^ 2 * Real.sqrt (t / (2 * ν)))
  have hΦt := half_le_Phi (x := l ^ 2 * Real.sqrt (t / (2 * ν))) (by positivity)
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Phi (l ^ 2 * Real.sqrt (t / (2 * ν))) := by linarith
    positivity
  have hsecond : l ^ 4 / (2 * ν) * Real.exp (l ^ 4 * r / (4 * ν)) *
      Phi (l ^ 2 * Real.sqrt (r / (2 * ν))) ≤ B := by
    have hΦr := half_le_Phi (x := l ^ 2 * Real.sqrt (r / (2 * ν))) (by positivity)
    have hΦmono : Phi (l ^ 2 * Real.sqrt (r / (2 * ν))) ≤ Phi (l ^ 2 * Real.sqrt (t / (2 * ν))) :=
      Phi_monotone (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hrt (by positivity))) (by positivity))
    have hexp : Real.exp (l ^ 4 * r / (4 * ν)) ≤ Real.exp (l ^ 4 * t / (4 * ν)) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrt (by positivity)) (by positivity))
    have hc : 0 ≤ l ^ 4 / (2 * ν) := by positivity
    have hΦr0 : 0 ≤ Phi (l ^ 2 * Real.sqrt (r / (2 * ν))) := by linarith
    calc l ^ 4 / (2 * ν) * Real.exp (l ^ 4 * r / (4 * ν)) * Phi (l ^ 2 * Real.sqrt (r / (2 * ν)))
        ≤ l ^ 4 / (2 * ν) * Real.exp (l ^ 4 * t / (4 * ν)) *
            Phi (l ^ 2 * Real.sqrt (t / (2 * ν))) := by gcongr
      _ = B := rfl
  have hfirst :
      l ^ 2 / Real.sqrt (4 * π * ν * r) = l ^ 2 / Real.sqrt (4 * π * ν) / Real.sqrt r := by
    rw [Real.sqrt_mul (by positivity) r, div_div]
  have hBle : B ≤ B * Real.sqrt t / Real.sqrt r := by
    rw [le_div_iff₀ hsr]
    exact mul_le_mul_of_nonneg_left hsrt hB0
  unfold kC
  rw [hfirst, add_div]
  linarith

/-! ### The Chen–Dalang convolution estimate at a general diffusion constant -/

theorem lheatFlow_sq_eq (μ : Measure ℝ) [SFinite μ] (s y : ℝ) :
    RoughHeatKernel.lheatFlow μ s y ^ 2 = ∫⁻ q : ℝ × ℝ,
      ENNReal.ofReal (RoughHeatKernel.heatKernel s (y - q.1)) *
      ENNReal.ofReal (RoughHeatKernel.heatKernel s (y - q.2)) ∂(μ.prod μ) := by
  have hm : ∀ r, Measurable (RoughHeatKernel.heatKernel r) := RoughHeatKernel.measurable_heatKernel
  rw [sq, RoughHeatKernel.lheatFlow]
  exact (lintegral_prod_mul (μ := μ) (ν := μ)
    (f := fun z => ENNReal.ofReal (RoughHeatKernel.heatKernel s (y - z)))
    (g := fun z => ENNReal.ofReal (RoughHeatKernel.heatKernel s (y - z)))
    (((hm s).comp (by fun_prop)).ennreal_ofReal.aemeasurable)
    (((hm s).comp (by fun_prop)).ennreal_ofReal.aemeasurable)).symm

/-- For `0 < r < R`:
`∫ J(r,y)² p_{(R-r)/2}(x-y) dy ≤ 2√(R/r) J(2R,x)²` (`J = lheatFlow μ`), the pointwise-in-time
step of `RoughHeatKernel.lintegral_sq_lheatFlow_conv_le`. -/
theorem lintegral_sq_lheatFlow_mul_le (μ : Measure ℝ) [SFinite μ] {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (x : ℝ) :
    ∫⁻ y, RoughHeatKernel.lheatFlow μ r y ^ 2 *
        ENNReal.ofReal (RoughHeatKernel.heatKernel ((R - r) / 2) (x - y)) ≤
      ENNReal.ofReal (2 * Real.sqrt (R / r)) * RoughHeatKernel.lheatFlow μ (2 * R) x ^ 2 := by
  have hm : ∀ r, Measurable (RoughHeatKernel.heatKernel r) := RoughHeatKernel.measurable_heatKernel
  have hF : Measurable fun q : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (RoughHeatKernel.heatKernel r (q.1 - q.2.1)) *
        ENNReal.ofReal (RoughHeatKernel.heatKernel r (q.1 - q.2.2)) *
        ENNReal.ofReal (RoughHeatKernel.heatKernel ((R - r) / 2) (x - q.1)) := by
    fun_prop
  have hk : ∀ c : ℝ, Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal (RoughHeatKernel.heatKernel (2 * R) (x - q.1)) *
        ENNReal.ofReal (RoughHeatKernel.heatKernel (2 * R) (x - q.2)) * ENNReal.ofReal c := by
    intro c
    fun_prop
  calc ∫⁻ y, RoughHeatKernel.lheatFlow μ r y ^ 2 *
        ENNReal.ofReal (RoughHeatKernel.heatKernel ((R - r) / 2) (x - y))
      = ∫⁻ y, ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (RoughHeatKernel.heatKernel r (y - q.1)) *
          ENNReal.ofReal (RoughHeatKernel.heatKernel r (y - q.2)) *
            ENNReal.ofReal (RoughHeatKernel.heatKernel ((R - r) / 2) (x - y)) ∂(μ.prod μ) := by
        refine lintegral_congr fun y => ?_
        rw [lheatFlow_sq_eq, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ q : ℝ × ℝ, (∫⁻ y : ℝ, ENNReal.ofReal (RoughHeatKernel.heatKernel r (y - q.1)) *
          ENNReal.ofReal (RoughHeatKernel.heatKernel r (y - q.2)) *
            ENNReal.ofReal (RoughHeatKernel.heatKernel ((R - r) / 2) (x - y))) ∂(μ.prod μ) :=
        lintegral_lintegral_swap hF.aemeasurable
    _ ≤ ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (RoughHeatKernel.heatKernel (2 * R) (x - q.1)) *
          ENNReal.ofReal (RoughHeatKernel.heatKernel (2 * R) (x - q.2)) *
            ENNReal.ofReal (2 * Real.sqrt (R / r)) ∂(μ.prod μ) := by
        refine lintegral_mono fun q => ?_
        rw [mul_comm]
        exact RoughHeatKernel.lintegral_heatKernel_mul_mul_le hr hrR x q.1 q.2
    _ = ENNReal.ofReal (2 * Real.sqrt (R / r)) * RoughHeatKernel.lheatFlow μ (2 * R) x ^ 2 := by
        rw [lintegral_mul_const _ (by simpa using hk 1), lheatFlow_sq_eq, mul_comm]

/-! ### Integrability of `s ↦ ∫ J₀(s,y)² 𝓚(t-s,x-y) dy` on `(0,t)` -/

/-- The constant `2√t (A + B√t)` of the bound `2√(t/s) k(t-s) ≤ C/√(s(t-s))`. -/
noncomputable def Cup (ν l t : ℝ) : ℝ :=
  2 * Real.sqrt t * (l ^ 2 / Real.sqrt (4 * π * ν) + l ^ 4 / (2 * ν) *
    Real.exp (l ^ 4 * t / (4 * ν)) * Phi (l ^ 2 * Real.sqrt (t / (2 * ν))) * Real.sqrt t)

theorem Cup_nonneg {ν l t : ℝ} (hν : 0 < ν) : 0 ≤ Cup ν l t := by
  have hΦ := half_le_Phi (x := l ^ 2 * Real.sqrt (t / (2 * ν))) (by positivity)
  have : 0 ≤ Phi (l ^ 2 * Real.sqrt (t / (2 * ν))) := by linarith
  unfold Cup
  positivity

theorem two_sqrt_mul_kC_le {ν l s t : ℝ} (hν : 0 < ν) (hs : 0 < s) (hst : s < t) :
    2 * Real.sqrt (ν * t / (ν * s)) * kC ν l (t - s) ≤
      Cup ν l t / Real.sqrt (s * (t - s)) := by
  have hts : 0 < t - s := sub_pos.mpr hst
  have hk := kC_upper (l := l) hν hts (by linarith : t - s ≤ t)
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsts : 0 < Real.sqrt (t - s) := Real.sqrt_pos.mpr hts
  rw [show ν * t / (ν * s) = t / s by field_simp, Real.sqrt_div' t hs.le,
    Real.sqrt_mul hs.le, Cup]
  set A := l ^ 2 / Real.sqrt (4 * π * ν) + l ^ 4 / (2 * ν) * Real.exp (l ^ 4 * t / (4 * ν)) *
    Phi (l ^ 2 * Real.sqrt (t / (2 * ν))) * Real.sqrt t
  have h2 : 0 ≤ 2 * (Real.sqrt t / Real.sqrt s) := by positivity
  calc 2 * (Real.sqrt t / Real.sqrt s) * kC ν l (t - s)
      ≤ 2 * (Real.sqrt t / Real.sqrt s) * (A / Real.sqrt (t - s)) :=
        mul_le_mul_of_nonneg_left hk h2
    _ = 2 * Real.sqrt t * A / (Real.sqrt s * Real.sqrt (t - s)) := by
        field_simp

theorem integrand_nonneg {ν : ℝ} (hν : 0 < ν) (μ : Measure ℝ) (l t x s y : ℝ) :
    0 ≤ integrand ν μ l t x s y := by
  unfold integrand
  have := J0_nonneg ν μ s y
  have := G_nonneg (ν / 2) (t - s) (x - y)
  have := kC_nonneg (l := l) (r := t - s) hν
  positivity

theorem lintegral_integrand_le {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν l t x s : ℝ} (hν : 0 < ν)
    (hs : 0 < s) (hst : s < t) :
    ∫⁻ y, ENNReal.ofReal (integrand ν μ l t x s y) ≤
      RoughHeatKernel.lheatFlow μ (2 * (ν * t)) x ^ 2 *
        ENNReal.ofReal (Cup ν l t / Real.sqrt (s * (t - s))) := by
  have hνs : 0 < ν * s := mul_pos hν hs
  have hνst : ν * s < ν * t := mul_lt_mul_of_pos_left hst hν
  have hk0 := kC_nonneg (l := l) (r := t - s) hν
  have hpt : ∀ y, ENNReal.ofReal (integrand ν μ l t x s y) =
      RoughHeatKernel.lheatFlow μ (ν * s) y ^ 2 *
        ENNReal.ofReal (RoughHeatKernel.heatKernel ((ν * t - ν * s) / 2) (x - y)) *
        ENNReal.ofReal (kC ν l (t - s)) := by
    intro y
    unfold integrand
    rw [ENNReal.ofReal_mul (pow_nonneg (J0_nonneg ν μ s y) 2),
      ENNReal.ofReal_mul (G_nonneg _ _ _), ENNReal.ofReal_pow (J0_nonneg ν μ s y),
      J0_eq_heatFlow, RoughHeatKernel.ofReal_heatFlow hT hνs, G_eq_heatKernel,
      show ν / 2 * (t - s) = (ν * t - ν * s) / 2 by ring, mul_assoc]
  simp_rw [hpt]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  calc (∫⁻ y, RoughHeatKernel.lheatFlow μ (ν * s) y ^ 2 *
        ENNReal.ofReal (RoughHeatKernel.heatKernel ((ν * t - ν * s) / 2) (x - y))) *
        ENNReal.ofReal (kC ν l (t - s))
      ≤ ENNReal.ofReal (2 * Real.sqrt (ν * t / (ν * s))) *
          RoughHeatKernel.lheatFlow μ (2 * (ν * t)) x ^ 2 * ENNReal.ofReal (kC ν l (t - s)) := by
        gcongr
        exact lintegral_sq_lheatFlow_mul_le μ hνs hνst x
    _ = RoughHeatKernel.lheatFlow μ (2 * (ν * t)) x ^ 2 *
          ENNReal.ofReal (2 * Real.sqrt (ν * t / (ν * s)) * kC ν l (t - s)) := by
        rw [ENNReal.ofReal_mul (q := kC ν l (t - s)) (by positivity)]
        ring
    _ ≤ _ := by
        gcongr
        exact two_sqrt_mul_kC_le hν hs hst

theorem integrable_integrand {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν l t x s : ℝ} (hν : 0 < ν)
    (hs : 0 < s) (hst : s < t) :
    Integrable (integrand ν μ l t x s) := by
  refine ⟨((stronglyMeasurable_integrand ν μ l t x).comp_measurable
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (integrand_nonneg hν μ l t x s))]
  refine lt_of_le_of_lt (lintegral_integrand_le hT hν hs hst) ?_
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top
    (RoughHeatKernel.lheatFlow_lt_top hT (mul_pos two_pos (mul_pos hν (hs.trans hst))) x))
    ENNReal.ofReal_lt_top

theorem integrableOn_phiC {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν l t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : ℝ) :
    IntegrableOn (phiC ν μ l t x) (Ioc 0 t) := by
  refine ⟨(stronglyMeasurable_phiC ν μ l t x).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
  set L := RoughHeatKernel.lheatFlow μ (2 * (ν * t)) x
  have hbound : ∀ s ∈ Ioo 0 t, ‖phiC ν μ l t x s‖ₑ ≤
      L ^ 2 * ENNReal.ofReal (Cup ν l t) * ENNReal.ofReal (1 / Real.sqrt (s * (t - s))) := by
    intro s hs
    calc ‖phiC ν μ l t x s‖ₑ ≤ ∫⁻ y, ‖integrand ν μ l t x s y‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, ENNReal.ofReal (integrand ν μ l t x s y) := by
          refine lintegral_congr fun y => ?_
          exact Real.enorm_eq_ofReal (integrand_nonneg hν μ l t x s y)
      _ ≤ L ^ 2 * ENNReal.ofReal (Cup ν l t / Real.sqrt (s * (t - s))) :=
          lintegral_integrand_le hT hν hs.1 hs.2
      _ = _ := by
          rw [mul_assoc, ← ENNReal.ofReal_mul (Cup_nonneg hν), mul_one_div]
  calc ∫⁻ s in Ioo 0 t, ‖phiC ν μ l t x s‖ₑ
      ≤ ∫⁻ s in Ioo 0 t,
          L ^ 2 * ENNReal.ofReal (Cup ν l t) * ENNReal.ofReal (1 / Real.sqrt (s * (t - s))) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
          (Filter.Eventually.of_forall hbound))
    _ = L ^ 2 * ENNReal.ofReal (Cup ν l t) * ENNReal.ofReal π := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top
          (RoughHeatKernel.lheatFlow_lt_top hT (by positivity) x).ne) ENNReal.ofReal_ne_top),
          RoughHeatKernel.lintegral_arcsine ht]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top
          (RoughHeatKernel.lheatFlow_lt_top hT (by positivity) x)) ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top

/-! ### The lower bound on `s ∈ (1, 2]` -/

/-- The constant of `lower_envelope_gaussian`:
`a² (λ⁴/(4ν)) e^{-2λ⁴/(4ν)} (4πξ)^{-1/2} 2^{-1/2} (ν/ξ)^{-1/2}`. -/
noncomputable def cG (ν l ξ a : ℝ) : ℝ :=
  a ^ 2 * (l ^ 4 / (4 * ν)) * Real.exp (-(l ^ 4 * 2 / (4 * ν))) * (1 / Real.sqrt (4 * π * ξ)) *
    (Real.sqrt 2)⁻¹ / Real.sqrt (ν / ξ)

theorem cG_pos {ν l ξ a : ℝ} (hν : 0 < ν) (hl : l ≠ 0) (hξ : 0 < ξ) (ha : 0 < a) :
    0 < cG ν l ξ a := by
  unfold cG
  have : 0 < l ^ 4 := by positivity
  have : 0 < Real.sqrt (4 * π * ξ) := Real.sqrt_pos.mpr (by positivity)
  have : 0 < Real.sqrt (ν / ξ) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- For `s ∈ (1, 2]` and `t ≥ 3`, with `a G_ξ ≤ J₀` on `[1, ∞)`:
`∫ J₀(s,y)² 𝓚(t-s,x-y) dy ≥ c e^{λ⁴t/(4ν)} G_{ξ/2}(t,x)`. -/
theorem phiC_lower {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ν l ξ a : ℝ} (hν : 0 < ν) (hξ : 0 < ξ) (hξν : ξ < ν) (ha : 0 < a)
    (hJ : ∀ s ≥ 1, ∀ y, a * G ξ s y ≤ J0 ν μ s y) {t x s : ℝ} (ht : 3 ≤ t) (hs : s ∈ Ioc 1 2) :
    cG ν l ξ a * Real.exp (l ^ 4 * t / (4 * ν)) * G (ξ / 2) t x ≤ phiC ν μ l t x s := by
  obtain ⟨hs1, hs2⟩ := hs
  have hs0 : 0 < s := by linarith
  have hst : s < t := by linarith
  have hts : 0 < t - s := by linarith
  have ht0 : 0 < t := by linarith
  -- the minorant
  set ℓ : ℝ → ℝ := fun y => (a * G ξ s y) ^ 2 * (G (ν / 2) (t - s) (x - y) * kC ν l (t - s))
  have hk0 := kC_nonneg (l := l) (r := t - s) hν
  have hℓ_le : ∫ y, ℓ y ≤ phiC ν μ l t x s := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => ?_)
      (integrable_integrand hT hν hs0 hst) (Filter.Eventually.of_forall fun y => ?_)
    · have := G_nonneg ξ s y
      have := G_nonneg (ν / 2) (t - s) (x - y)
      positivity
    · have h1 : 0 ≤ a * G ξ s y := mul_nonneg ha.le (G_nonneg _ _ _)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h1 (hJ s hs1.le y) 2)
        (mul_nonneg (G_nonneg _ _ _) hk0)
  -- its exact value
  set v := ν / 2 * (t - s) + ξ / 2 * s
  have hℓ_eq : ∫ y, ℓ y = a ^ 2 * kC ν l (t - s) * (1 / Real.sqrt (4 * π * ξ)) *
      s ^ (-(1 / 2 : ℝ)) * RoughHeatKernel.heatKernel v x := by
    have hfun : ℓ = fun y => (a ^ 2 * kC ν l (t - s) * (1 / Real.sqrt (4 * π * ξ)) *
        s ^ (-(1 / 2 : ℝ))) * (RoughHeatKernel.heatKernel (ν / 2 * (t - s)) (x - y) *
          RoughHeatKernel.heatKernel (ξ / 2 * s) y) := by
      funext y
      simp only [ℓ]
      rw [mul_pow, G_sq hξ hs0 y]
      simp only [G_eq_heatKernel]
      ring
    rw [hfun, integral_const_mul, RoughHeatKernel.integral_heatKernel_mul_heatKernel
      (by positivity) (by positivity)]
  -- scalar lower bounds
  have hk : l ^ 4 / (4 * ν) * (Real.exp (l ^ 4 * t / (4 * ν)) *
      Real.exp (-(l ^ 4 * 2 / (4 * ν)))) ≤ kC ν l (t - s) := by
    refine le_trans ?_ (kC_lower hν)
    rw [← Real.exp_add]
    gcongr
    have : 0 ≤ l ^ 4 := by positivity
    rw [show l ^ 4 * t / (4 * ν) + -(l ^ 4 * 2 / (4 * ν)) = l ^ 4 * (t - 2) / (4 * ν) by ring]
    gcongr
  have hsr : (Real.sqrt 2)⁻¹ ≤ s ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hs0.le, ← Real.sqrt_eq_rpow]
    exact inv_anti₀ (Real.sqrt_pos.mpr hs0) (Real.sqrt_le_sqrt hs2)
  have hp : RoughHeatKernel.heatKernel (ξ / 2 * t) x / Real.sqrt (ν / ξ) ≤
      RoughHeatKernel.heatKernel v x := by
    have hle : ξ / 2 * t ≤ v := by simp only [v]; nlinarith
    have h1 := RoughHeatKernel.heatKernel_le_sqrt_div_mul (by positivity) hle x
    have h2 : Real.sqrt (v / (ξ / 2 * t)) ≤ Real.sqrt (ν / ξ) := by
      apply Real.sqrt_le_sqrt
      rw [div_le_div_iff₀ (by positivity) hξ]
      simp only [v]
      nlinarith [mul_pos (mul_pos hξ hs0) (sub_pos.mpr hξν)]
    have hpv := (RoughHeatKernel.heatKernel_pos (by positivity : 0 < v) x).le
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
    calc RoughHeatKernel.heatKernel (ξ / 2 * t) x
        ≤ Real.sqrt (v / (ξ / 2 * t)) * RoughHeatKernel.heatKernel v x := h1
      _ ≤ Real.sqrt (ν / ξ) * RoughHeatKernel.heatKernel v x :=
          mul_le_mul_of_nonneg_right h2 hpv
      _ = _ := mul_comm _ _
  have hp0 := (RoughHeatKernel.heatKernel_pos (by positivity : 0 < ξ / 2 * t) x).le
  refine le_trans ?_ (hℓ_eq ▸ hℓ_le)
  rw [G_eq_heatKernel, show ξ / 2 * t = ξ / 2 * t from rfl]
  have hA : 0 ≤ a ^ 2 * (1 / Real.sqrt (4 * π * ξ)) := by positivity
  calc cG ν l ξ a * Real.exp (l ^ 4 * t / (4 * ν)) * RoughHeatKernel.heatKernel (ξ / 2 * t) x
      = (a ^ 2 * (1 / Real.sqrt (4 * π * ξ))) *
          ((l ^ 4 / (4 * ν) * (Real.exp (l ^ 4 * t / (4 * ν)) *
            Real.exp (-(l ^ 4 * 2 / (4 * ν))))) *
          ((Real.sqrt 2)⁻¹ * (RoughHeatKernel.heatKernel (ξ / 2 * t) x / Real.sqrt (ν / ξ)))) := by
        unfold cG
        ring
    _ ≤ (a ^ 2 * (1 / Real.sqrt (4 * π * ξ))) *
          (kC ν l (t - s) * (s ^ (-(1 / 2 : ℝ)) * RoughHeatKernel.heatKernel v x)) := by
        gcongr
    _ = _ := by ring

end GrowthLower

open GrowthLower

/-- **Chen–Dalang (2015), Lemma `L2:pLbd`.** If `μ ≠ 0` is a nonnegative measure with
`∫ e^{-a y²} μ(dy) < ∞` for all `a > 0`, then for every `ε > 0` and `ξ ∈ (0, ν)` there is
`a > 0` with `a G_ξ(t,x) ≤ J₀(t,x)` for all `t ≥ ε` and `x`. -/
theorem L2_pLbd {μ : Measure ℝ} (hμ0 : μ ≠ 0)
    (hμ : ∀ a > 0, Integrable (fun y => Real.exp (-a * y ^ 2)) μ)
    {ν ε ξ : ℝ} (hν : 0 < ν) (hε : 0 < ε) (hξ : 0 < ξ) (hξν : ξ < ν) :
    ∃ a > 0, ∀ t ≥ ε, ∀ x, a * G ξ t x ≤ J0 ν μ t x := by
  have hd : 0 < ν - ξ := sub_pos.mpr hξν
  set b : ℝ := 1 / (2 * (ν - ξ) * ε) with hb_def
  have hb : 0 < b := by positivity
  have hint := hμ b hb
  have hpos : 0 < ∫ y, Real.exp (-b * y ^ 2) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hint]
    have : Function.support (fun y : ℝ => Real.exp (-b * y ^ 2)) = univ :=
      Set.eq_univ_of_forall fun _ => (Real.exp_pos _).ne'
    rw [this]
    exact Measure.measure_univ_pos.mpr hμ0
  refine ⟨Real.sqrt ξ / Real.sqrt ν * ∫ y, Real.exp (-b * y ^ 2) ∂μ,
    mul_pos (div_pos (Real.sqrt_pos.mpr hξ) (Real.sqrt_pos.mpr hν)) hpos, ?_⟩
  intro t ht x
  have ht0 : 0 < t := hε.trans_le ht
  have hT := isGaussianTempered hμ
  have hJint : Integrable (fun y => G ν t (x - y)) μ := by
    simp only [G_eq_heatKernel]
    exact hT.integrable_heatKernel_sub (mul_pos hν ht0) x
  have heq : Real.sqrt ξ / Real.sqrt ν * (∫ y, Real.exp (-b * y ^ 2) ∂μ) * G ξ t x =
      ∫ y, Real.sqrt ξ / Real.sqrt ν * G ξ t x * Real.exp (-b * y ^ 2) ∂μ := by
    rw [integral_const_mul]
    ring
  rw [J0, heq]
  refine integral_mono (hint.const_mul _) hJint fun y => ?_
  have := G_lower_pointwise hξ hξν hε ht x y
  simp only [hb_def, neg_mul] at this ⊢
  linarith [this]

/-- **Chen–Dalang (2015), proof of Theorem `T2:Growth(1)`, case `ϑ = 0` (the lower envelope).**
Let `μ ≠ 0` be a nonnegative measure with `∫ e^{-a y²} μ(dy) < ∞` for all `a > 0`, `ν > 0`,
`λ ≠ 0`, and let `f(t,x) ≥ (J₀² ⋆ 𝓚)(t,x)` for `t > 0` (a consequence of `E2:SecMom-Lower`).
Then for every `ξ ∈ (0, ν)` there are `c > 0` and `T₀ > 0` with
`c t⁻¹ e^{λ⁴t/(4ν)} G_{ξ/2}(t,x) ≤ f(t,x)` for all `t ≥ T₀` and all `x`.

The space-time convolution is a Bochner integral, so the proof establishes that its integrand
is integrable (via the Chen–Dalang convolution estimate); in fact the bound holds without the
factor `t⁻¹` (see `lower_envelope_gaussian'`). -/
theorem lower_envelope_gaussian' {μ : Measure ℝ} (hμ0 : μ ≠ 0)
    (hμ : ∀ a > 0, Integrable (fun y => Real.exp (-a * y ^ 2)) μ)
    {ν l : ℝ} (hν : 0 < ν) (hl : l ≠ 0) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t > 0, ∀ x, stConv (fun s y => J0 ν μ s y ^ 2) (K ν l) t x ≤ f t x)
    {ξ : ℝ} (hξ : 0 < ξ) (hξν : ξ < ν) :
    ∃ c > 0, ∀ t ≥ 3, ∀ x, c * Real.exp (l ^ 4 * t / (4 * ν)) * G (ξ / 2) t x ≤ f t x := by
  obtain ⟨a, ha, hJ⟩ := L2_pLbd hμ0 hμ hν one_pos hξ hξν
  have hT := isGaussianTempered hμ
  have := hT.isLocallyFiniteMeasure
  refine ⟨cG ν l ξ a, cG_pos hν hl hξ ha, fun t ht x => ?_⟩
  have ht0 : 0 < t := by linarith
  have hconv : stConv (fun s y => J0 ν μ s y ^ 2) (K ν l) t x =
      ∫ s in Ioc 0 t, phiC ν μ l t x s := by
    rw [stConv, intervalIntegral.integral_of_le ht0.le]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [ae_ne_real t] with s hst hs
    unfold phiC integrand
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [K_eq_kC hν (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) (x - y)]
  have hint := integrableOn_phiC (l := l) hT hν ht0 x
  have hsub : Ioc (1 : ℝ) 2 ⊆ Ioc 0 t := Ioc_subset_Ioc (by norm_num) (by linarith)
  calc cG ν l ξ a * Real.exp (l ^ 4 * t / (4 * ν)) * G (ξ / 2) t x
      = ∫ _ in Ioc (1 : ℝ) 2, cG ν l ξ a * Real.exp (l ^ 4 * t / (4 * ν)) * G (ξ / 2) t x := by
        rw [setIntegral_const]
        norm_num
    _ ≤ ∫ s in Ioc (1 : ℝ) 2, phiC ν μ l t x s :=
        setIntegral_mono_on (integrableOn_const (by simp)) (hint.mono_set hsub) measurableSet_Ioc
          fun s hs => phiC_lower hT hν hξ hξν ha hJ ht hs
    _ ≤ ∫ s in Ioc 0 t, phiC ν μ l t x s :=
        setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall fun s _ =>
            integral_nonneg fun y => integrand_nonneg hν μ l t x s y))
          hsub.eventuallyLE
    _ = stConv (fun s y => J0 ν μ s y ^ 2) (K ν l) t x := hconv.symm
    _ ≤ f t x := hf t ht0 x

/-- **Chen–Dalang (2015), proof of Theorem `T2:Growth(1)`, case `ϑ = 0` (the lower envelope).**
Under the hypotheses of `L2_pLbd`, `ν > 0`, `λ ≠ 0`, and `f ≥ J₀² ⋆ 𝓚` for `t > 0` (a
consequence of `E2:SecMom-Lower`): for every `ξ ∈ (0, ν)` there are `c > 0`, `T₀ > 0` with
`c t⁻¹ e^{λ⁴t/(4ν)} G_{ξ/2}(t,x) ≤ f(t,x)` for `t ≥ T₀` and all `x`. -/
theorem lower_envelope_gaussian {μ : Measure ℝ} (hμ0 : μ ≠ 0)
    (hμ : ∀ a > 0, Integrable (fun y => Real.exp (-a * y ^ 2)) μ)
    {ν l : ℝ} (hν : 0 < ν) (hl : l ≠ 0) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t > 0, ∀ x, stConv (fun s y => J0 ν μ s y ^ 2) (K ν l) t x ≤ f t x)
    {ξ : ℝ} (hξ : 0 < ξ) (hξν : ξ < ν) :
    ∃ c > 0, ∃ T₀ > 0, ∀ t ≥ T₀, ∀ x,
      c / t * Real.exp (l ^ 4 * t / (4 * ν)) * G (ξ / 2) t x ≤ f t x := by
  obtain ⟨c, hc, h⟩ := lower_envelope_gaussian' hμ0 hμ hν hl hf hξ hξν
  refine ⟨c, hc, 3, by norm_num, fun t ht x => le_trans ?_ (h t ht x)⟩
  have hct : c / t ≤ c := div_le_self hc.le (by linarith)
  have := G_nonneg (ξ / 2) t x
  gcongr

/-- **Chen–Dalang (2015), proof of Theorem `T2:Growth(1)`, case `ϑ ≠ 0`.** If
`f ≥ ϑ² 𝓗 = ϑ² (1 ⋆ 𝓚)` for `t > 0`, then `f(t,x) ≥ c e^{λ⁴t/(4ν)}` for all large `t`,
uniformly in `x` (`c = ϑ²/2`, `T₀ = 4ν/λ⁴`). -/
theorem lower_envelope_uniform {ν l v : ℝ} (hν : 0 < ν) (hl : l ≠ 0) (hv : v ≠ 0)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t > 0, ∀ x, v ^ 2 * stConv (fun _ _ => (1 : ℝ)) (K ν l) t x ≤ f t x) :
    ∃ c > 0, ∃ T₀, ∀ t ≥ T₀, ∀ x, c * Real.exp (l ^ 4 * t / (4 * ν)) ≤ f t x := by
  have hl4 : 0 < l ^ 4 := by positivity
  refine ⟨v ^ 2 / 2, by positivity, 4 * ν / l ^ 4, fun t ht x => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hγt : 1 ≤ l ^ 4 * t / (4 * ν) := by
    rw [le_div_iff₀ (by positivity), one_mul]
    rw [ge_iff_le, div_le_iff₀ hl4] at ht
    linarith
  have hE := two_le_exp hγt
  have hΦ := half_le_Phi (x := l ^ 2 * Real.sqrt (t / (2 * ν))) (by positivity)
  have hH := one_conv_K (lam := l) hν ht0.le x
  have hv2 : 0 < v ^ 2 := by positivity
  refine le_trans ?_ (hf t ht0 x)
  rw [hH]
  have : Real.exp (l ^ 4 * t / (4 * ν)) / 2 ≤
      2 * Real.exp (l ^ 4 * t / (4 * ν)) * Phi (l ^ 2 * Real.sqrt (t / (2 * ν))) - 1 := by
    nlinarith
  calc v ^ 2 / 2 * Real.exp (l ^ 4 * t / (4 * ν))
        = v ^ 2 * (Real.exp (l ^ 4 * t / (4 * ν)) / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hv2.le

end ChenDalang15

end
