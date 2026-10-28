module

public import ChenDalang15.PhiE
public import ChenDalang15.ErfFacts
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Paper `L2:IntHG-BC` and `L2:TP-Delta-BC`: Bertini–Cancrini's integrals in closed form

Chen–Dalang (2015), Appendix. These evaluate the integral formulas of Bertini–Cancrini
(1995, Cor. 2.4, 2.5) used in Remarks `R2:TP-Lebesgue` and `R2:TP-Delta`.

* `L2_IntHG_BC` (`t > 0`, `x ≠ 0`). The paper says `t ≥ 0`; at `t = 0` its right side is a
  limit, and the literal Lean reading fails (`L2_IntHG_BC_t_zero_junk`).
* `L2_TP_Delta_BC` (`t > 0`, `x ≠ y`). The paper omits `x ≠ y`, but the identity is false at
  `x = y` (`L2_TP_Delta_BC_false_of_eq`): the integrand has the factor `|x - y|`.

The paper's proofs use Laplace transforms. Here: with `c = 1/(4ν)`, `b = a²/(4ν)`, `a = |x|`,
write `Φ(√((t-r)/(2ν))) = 1/2 + ∫₀ᵗ k(s-r) ds` (`integral_bcK_sub`), swap the integrals
(`integral_bcF_mul_integral_bcK_swap`), evaluate the inner integral with the Abel-type integral
`∫₀ˢ e^{-b/r} r^{-3/2}(s-r)^{-1/2} dr = √(π/b) e^{-b/s}/√s` (`abel_integral`, substitution
`r = s/(1+su²)`), and integrate the elementary derivatives of
`E_±(s) = e^{±a/(2ν)} Erfc((a ± s)/√(4νs))` (`hasDerivAt_bcE`) with an improper endpoint at `0`
(`integral_eq_of_hasDerivAt_of_tendsto_zero`). `L2:TP-Delta-BC` then follows from
`L2:IntHG-BC` by `r = ts` and from `abel_integral` at `s = 1`.
-/

set_option autoImplicit false

public section

namespace ChenDalang15

open Real MeasureTheory Set Filter Topology

/-! ### Small helpers -/

theorem sqrt_eq_of_eq_sq {x y : ℝ} (hy : 0 ≤ y) (h : x = y ^ 2) : Real.sqrt x = y := by
  rw [h, Real.sqrt_sq hy]

/-! ### The elementary antiderivatives `e^{±a/(2ν)} Erfc((a ± s)/√(4νs))` -/

/-- The common kernel `e^{-a²/(4νs) - s/(4ν)} / (2√(πν) s^{3/2})`. -/
noncomputable def bcKer (ν a s : ℝ) : ℝ :=
  Real.exp (-a ^ 2 / (4 * ν * s) - s / (4 * ν)) / (2 * Real.sqrt (π * ν) * s * Real.sqrt s)

/-- `E_σ(s) = e^{σa/(2ν)} Erfc((a + σ s)/√(4νs))`, used for `σ = ±1`. -/
noncomputable def bcE (ν a σ s : ℝ) : ℝ :=
  Real.exp (σ * a / (2 * ν)) * erfc ((a + σ * s) / Real.sqrt (4 * ν * s))

theorem bcKer_nonneg {ν a s : ℝ} (hν : 0 < ν) (hs : 0 < s) : 0 ≤ bcKer ν a s := by
  unfold bcKer; positivity

/-- `E_σ'(s) = (a - σ s) · bcKer(s)` for `s > 0`, `σ = ±1`. -/
theorem hasDerivAt_bcE {ν a σ s : ℝ} (hν : 0 < ν) (hs : 0 < s) (hσ : σ = 1 ∨ σ = -1) :
    HasDerivAt (fun s => bcE ν a σ s) ((a - σ * s) * bcKer ν a s) s := by
  have h4 : (4 * ν * s) ≠ 0 := by positivity
  have hsq : Real.sqrt (4 * ν * s) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hz := (((hasDerivAt_id s).const_mul σ).const_add a).div
    (((hasDerivAt_id s).const_mul (4 * ν)).sqrt (by simpa using h4)) hsq
  have h := ((hasDerivAt_erfc _).comp s hz).const_mul (Real.exp (σ * a / (2 * ν)))
  unfold bcE
  convert h using 1
  · funext y; rfl
  set z := (a + σ * s) / Real.sqrt (4 * ν * s) with hzdef
  have hexp : Real.exp (σ * a / (2 * ν)) * Real.exp (-z ^ 2) =
      Real.exp (-a ^ 2 / (4 * ν * s) - s / (4 * ν)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hzdef, div_pow, Real.sq_sqrt (by positivity)]
    rcases hσ with rfl | rfl <;> field_simp <;> ring
  unfold bcKer
  rw [← hexp]
  have hS := Real.sq_sqrt hs.le
  have hN := Real.sq_sqrt hν.le
  have hP := Real.sq_sqrt Real.pi_pos.le
  have hS0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hN0 : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hP0 : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have e1 : Real.sqrt (4 * ν * s) = 2 * Real.sqrt ν * Real.sqrt s :=
    sqrt_eq_of_eq_sq (by positivity) (by rw [mul_pow, mul_pow, hS, hN]; ring)
  have e2 : Real.sqrt (π * ν) = Real.sqrt π * Real.sqrt ν :=
    sqrt_eq_of_eq_sq (by positivity) (by rw [mul_pow, hP, hN])
  simp only [id]
  rw [e1, e2]
  generalize Real.exp (σ * a / (2 * ν)) = A
  generalize Real.exp (-z ^ 2) = B
  generalize Real.sqrt s = S at hS hS0 ⊢
  generalize Real.sqrt ν = N at hN hN0 ⊢
  generalize Real.sqrt π = P at hP0 ⊢
  rw [← hS, ← hN]
  rcases hσ with rfl | rfl <;> field_simp <;> ring

/-- `E_σ(s) → 0` as `s → 0⁺` (for `a > 0`, `σ = ±1`). -/
theorem tendsto_bcE_zero {ν a σ : ℝ} (hν : 0 < ν) (ha : 0 < a) (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun s => bcE ν a σ s) (𝓝[>] 0) (𝓝 0) := by
  have hz : Tendsto (fun s => (a + σ * s) / Real.sqrt (4 * ν * s)) (𝓝[>] 0) atTop := by
    have hsq : Tendsto (fun s => Real.sqrt (4 * ν * s)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun s : ℝ => Real.sqrt (4 * ν * s)) (𝓝 0) (𝓝 (Real.sqrt (4 * ν * 0))) :=
          (by fun_prop : Continuous fun s : ℝ => Real.sqrt (4 * ν * s)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact Real.sqrt_pos.2 (by have : (0:ℝ) < s := hs; positivity)
    have hinv := (hsq.inv_tendsto_nhdsGT_zero).const_mul_atTop (show (0:ℝ) < a / 2 by positivity)
    refine tendsto_atTop_mono' _ ?_ hinv
    have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), s < a / 2 ∧ 0 < s := by
      have h1 : ∀ᶠ s in 𝓝[>] (0:ℝ), s < a / 2 :=
        nhdsWithin_le_nhds (eventually_lt_nhds (by positivity))
      filter_upwards [h1, self_mem_nhdsWithin] with s h1 h2
      exact ⟨h1, h2⟩
    filter_upwards [hev] with s ⟨hs1, hs2⟩
    have hq : 0 < Real.sqrt (4 * ν * s) := Real.sqrt_pos.2 (by positivity)
    simp only [Pi.inv_apply]
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 hq.le)
    rcases hσ with rfl | rfl <;> linarith
  have := (tendsto_erfc_atTop.comp hz).const_mul (Real.exp (σ * a / (2 * ν)))
  simpa [bcE] using this

/-- FTC with an improper left endpoint: if `E' = g ≥ 0` on `(0, ∞)` and `E(0⁺) = 0`, then
`∫₀ᵗ g = E(t)` and `g` is interval integrable on `[0, t]`. -/
theorem integral_eq_of_hasDerivAt_of_tendsto_zero {E g : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hd : ∀ s, 0 < s → HasDerivAt E (g s) s) (hg : ∀ s, 0 < s → 0 ≤ g s)
    (hlim : Tendsto E (𝓝[>] 0) (𝓝 0)) :
    IntervalIntegrable g volume 0 t ∧ ∫ s in (0 : ℝ)..t, g s = E t := by
  set E' : ℝ → ℝ := fun s => if 0 < s then E s else 0 with hE'
  have hEq : ∀ s, 0 < s → E' =ᶠ[𝓝 s] E := by
    intro s hs
    filter_upwards [eventually_gt_nhds hs] with u hu
    simp [hE', hu]
  have hd' : ∀ s, 0 < s → HasDerivAt E' (g s) s := fun s hs =>
    (hd s hs).congr_of_eventuallyEq (hEq s hs)
  have hcont : ContinuousOn E' (Icc 0 t) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · subst h0
      have h1 : ContinuousWithinAt E' (Ioi 0) 0 := by
        have : E' 0 = 0 := by simp [hE']
        rw [ContinuousWithinAt, this]
        refine hlim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with u hu
        simp [hE', show (0:ℝ) < u from hu]
      exact (continuousWithinAt_Ioi_iff_Ici.1 h1).mono Icc_subset_Ici_self
    · exact (hd' s hpos).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable g volume 0 t := by
    refine intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := E') ?_ ?_ ?_
    · simpa [uIcc_of_le ht.le] using hcont
    · intro s hs
      simp only [min_eq_left ht.le, max_eq_right ht.le] at hs
      exact hd' s hs.1
    · intro s hs
      simp only [min_eq_left ht.le, max_eq_right ht.le] at hs
      exact hg s hs.1
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.le hcont
    (fun s hs => hd' s hs.1) hint]
  simp [hE', ht]

/-- `∫₀ᵗ 2a·bcKer = E₊(t) + E₋(t)`. -/
theorem integral_bcKer_a {ν a t : ℝ} (hν : 0 < ν) (ha : 0 < a) (ht : 0 < t) :
    IntervalIntegrable (fun s => 2 * a * bcKer ν a s) volume 0 t ∧
    ∫ s in (0 : ℝ)..t, 2 * a * bcKer ν a s = bcE ν a 1 t + bcE ν a (-1) t := by
  refine integral_eq_of_hasDerivAt_of_tendsto_zero (E := fun s => bcE ν a 1 s + bcE ν a (-1) s)
    ht ?_ ?_ ?_
  · intro s hs
    convert (hasDerivAt_bcE (a := a) hν hs (Or.inl rfl)).add
      (hasDerivAt_bcE (a := a) hν hs (Or.inr rfl)) using 1
    ring
  · intro s hs; have := bcKer_nonneg (a := a) hν hs; positivity
  · simpa using (tendsto_bcE_zero hν ha (Or.inl rfl)).add (tendsto_bcE_zero hν ha (Or.inr rfl))

/-- `∫₀ᵗ 2s·bcKer = E₋(t) - E₊(t)`. -/
theorem integral_bcKer_s {ν a t : ℝ} (hν : 0 < ν) (ha : 0 < a) (ht : 0 < t) :
    IntervalIntegrable (fun s => 2 * s * bcKer ν a s) volume 0 t ∧
    ∫ s in (0 : ℝ)..t, 2 * s * bcKer ν a s = bcE ν a (-1) t - bcE ν a 1 t := by
  refine integral_eq_of_hasDerivAt_of_tendsto_zero (E := fun s => bcE ν a (-1) s - bcE ν a 1 s)
    ht ?_ ?_ ?_
  · intro s hs
    convert (hasDerivAt_bcE (a := a) hν hs (Or.inr rfl)).sub
      (hasDerivAt_bcE (a := a) hν hs (Or.inl rfl)) using 1
    ring
  · intro s hs; have := bcKer_nonneg (a := a) hν hs; positivity
  · simpa using (tendsto_bcE_zero hν ha (Or.inr rfl)).sub (tendsto_bcE_zero hν ha (Or.inl rfl))

/-! ### The Abel-type integral `∫₀ˢ e^{-b/r} r^{-3/2} (s-r)^{-1/2} dr` -/

/-- Pointwise form of the substitution `r = s/(1 + s u²)`. -/
theorem abel_subst_pointwise {b s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    |(-(2 * s ^ 2 * u) / (1 + s * u ^ 2) ^ 2)| •
        (Real.exp (-b / (s / (1 + s * u ^ 2))) /
          (Real.sqrt ((s / (1 + s * u ^ 2)) ^ 3) * Real.sqrt (s - s / (1 + s * u ^ 2)))) =
      2 * Real.exp (-b / s) / Real.sqrt s * Real.exp (-b * u ^ 2) := by
  have hQ : 0 < 1 + s * u ^ 2 := by positivity
  set Q := 1 + s * u ^ 2 with hQdef
  have hq0 : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hq2 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
  have hS0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hS2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have e1 : Real.sqrt ((s / Q) ^ 3) = s * Real.sqrt s / Real.sqrt Q ^ 3 := by
    apply sqrt_eq_of_eq_sq (by positivity)
    rw [show (s * Real.sqrt s / Real.sqrt Q ^ 3) ^ 2 =
      s ^ 2 * Real.sqrt s ^ 2 / (Real.sqrt Q ^ 2) ^ 3 by ring, hq2, hS2]
    ring_nf
  have e2 : Real.sqrt (s - s / Q) = s * u / Real.sqrt Q := by
    apply sqrt_eq_of_eq_sq (by positivity)
    rw [div_pow, hq2, mul_pow, hQdef]
    field_simp
    ring_nf
  have e3 : Real.exp (-b / (s / Q)) = Real.exp (-b / s) * Real.exp (-b * u ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    rw [hQdef]
    field_simp
    ring_nf
  have habs : |(-(2 * s ^ 2 * u) / Q ^ 2)| = 2 * s ^ 2 * u / Q ^ 2 := by
    rw [neg_div, abs_neg, abs_of_pos (by positivity)]
  rw [habs, e1, e2, e3, smul_eq_mul]
  generalize Real.sqrt Q = q at hq0 hq2 ⊢
  rw [← hq2]
  generalize Real.exp (-b / s) = A
  generalize Real.exp (-b * u ^ 2) = B
  field_simp

/-- The Abel-type integral: for `b, s > 0`,
`∫₀ˢ e^{-b/r} / (√(r³) √(s - r)) dr = √π/√b · e^{-b/s}/√s` (with integrability). -/
theorem abel_integral {b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    IntervalIntegrable (fun r => Real.exp (-b / r) / (Real.sqrt (r ^ 3) * Real.sqrt (s - r)))
      volume 0 s ∧
    ∫ r in (0 : ℝ)..s, Real.exp (-b / r) / (Real.sqrt (r ^ 3) * Real.sqrt (s - r)) =
      Real.sqrt π / Real.sqrt b * Real.exp (-b / s) / Real.sqrt s := by
  set φ : ℝ → ℝ := fun u => s / (1 + s * u ^ 2) with hφ
  set φ' : ℝ → ℝ := fun u => -(2 * s ^ 2 * u) / (1 + s * u ^ 2) ^ 2 with hφ'
  set g : ℝ → ℝ := fun r => Real.exp (-b / r) / (Real.sqrt (r ^ 3) * Real.sqrt (s - r)) with hg
  have himage : φ '' Ioi 0 = Ioo 0 s := by
    ext r
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : (0:ℝ) < u := hu
      have hQ : 1 < 1 + s * u ^ 2 := by have : 0 < s * u ^ 2 := by positivity
                                        linarith
      refine ⟨by simp only [hφ]; positivity, ?_⟩
      simp only [hφ]
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    · rintro ⟨hr0, hrs⟩
      refine ⟨Real.sqrt ((s - r) / (s * r)), Real.sqrt_pos.2 (by
        apply div_pos (by linarith) (by positivity)), ?_⟩
      simp only [hφ]
      rw [Real.sq_sqrt (div_pos (by linarith) (by positivity)).le]
      field_simp
      ring
  have hderiv : ∀ u ∈ Ioi (0:ℝ), HasDerivWithinAt φ (φ' u) (Ioi 0) u := by
    intro u _
    have hQ : (1 + s * u ^ 2) ≠ 0 := by positivity
    have h := (hasDerivAt_const u s).div (((hasDerivAt_pow 2 u).const_mul s).const_add 1) hQ
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp only [hφ']
    ring_nf
  have hinj : InjOn φ (Ioi 0) := by
    intro u hu v hv huv
    have hu' : (0:ℝ) < u := hu
    have hv' : (0:ℝ) < v := hv
    simp only [hφ] at huv
    have h1 : (1 + s * u ^ 2) ≠ 0 := by positivity
    have h2 : (1 + s * v ^ 2) ≠ 0 := by positivity
    rw [div_eq_div_iff h1 h2] at huv
    have : u ^ 2 = v ^ 2 := by
      have : s * (s * v ^ 2) = s * (s * u ^ 2) := by linarith
      have := mul_left_cancel₀ hs.ne' (mul_left_cancel₀ hs.ne' this)
      exact this.symm
    exact (pow_left_inj₀ hu'.le hv'.le two_ne_zero).1 this
  have hpt : EqOn (fun u => |φ' u| • g (φ u))
      (fun u => 2 * Real.exp (-b / s) / Real.sqrt s * Real.exp (-b * u ^ 2)) (Ioi 0) := by
    intro u hu
    exact abel_subst_pointwise (b := b) hs hu
  have hgauss : IntegrableOn
      (fun u => 2 * Real.exp (-b / s) / Real.sqrt s * Real.exp (-b * u ^ 2)) (Ioi 0) :=
    ((integrable_exp_neg_mul_sq hb).const_mul _).integrableOn
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le, integrableOn_Ioc_iff_integrableOn_Ioo,
      ← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj]
    exact hgauss.congr_fun hpt.symm measurableSet_Ioi
  · rw [intervalIntegral.integral_of_le hs.le, integral_Ioc_eq_integral_Ioo, ← himage,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj,
      setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_gaussian_Ioi,
      Real.sqrt_div Real.pi_pos.le]
    have : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
    have : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
    field_simp

/-! ### Ingredients of `L2:IntHG-BC` -/

/-- `f(r) = a e^{-a²/(4νr) - r/(4ν)} / √(πνr³)` (the paper's `f` times `e^{-r/(4ν)}`). -/
noncomputable def bcF (ν a r : ℝ) : ℝ :=
  a * Real.exp (-a ^ 2 / (4 * ν * r) - r / (4 * ν)) / Real.sqrt (π * ν * r ^ 3)

/-- `k(u) = e^{-u/(4ν)} / (4√(πνu))`, the derivative of `u ↦ Φ(√(u/(2ν)))`. -/
noncomputable def bcK (ν u : ℝ) : ℝ := Real.exp (-u / (4 * ν)) / (4 * Real.sqrt (π * ν * u))

theorem bcF_eq (ν a r : ℝ) (hν : 0 < ν) : bcF ν a r = 2 * a * bcKer ν a r := by
  unfold bcF bcKer
  rcases le_or_gt r 0 with hr | hr
  · have h1 : Real.sqrt (π * ν * r ^ 3) = 0 := Real.sqrt_eq_zero'.2 (by
      have : r ^ 3 ≤ 0 := by nlinarith [sq_nonneg r]
      have : 0 ≤ π * ν := by positivity
      nlinarith)
    have h2 : Real.sqrt r = 0 := Real.sqrt_eq_zero'.2 hr
    simp [h1, h2]
  · have e : Real.sqrt (π * ν * r ^ 3) = Real.sqrt (π * ν) * r * Real.sqrt r := by
      apply sqrt_eq_of_eq_sq (by positivity)
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hr.le]
      ring
    rw [e]
    have : 0 < Real.sqrt (π * ν) := Real.sqrt_pos.2 (by positivity)
    have : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
    field_simp

theorem bcF_nonneg {ν a r : ℝ} (ha : 0 ≤ a) : 0 ≤ bcF ν a r := by
  unfold bcF; positivity

theorem bcK_nonneg (ν u : ℝ) : 0 ≤ bcK ν u := by
  unfold bcK; positivity

theorem bcK_of_nonpos {ν u : ℝ} (hν : 0 < ν) (hu : u ≤ 0) : bcK ν u = 0 := by
  unfold bcK
  have : Real.sqrt (π * ν * u) = 0 := Real.sqrt_eq_zero'.2 (by
    have : 0 ≤ π * ν := by positivity
    nlinarith)
  simp [this]

theorem measurable_bcF (ν a : ℝ) : Measurable (bcF ν a) := by
  unfold bcF; fun_prop

theorem measurable_bcK (ν : ℝ) : Measurable (bcK ν) := by
  unfold bcK; fun_prop

theorem continuous_Phi_sqrt (ν : ℝ) : Continuous fun u : ℝ => Phi (Real.sqrt (u / (2 * ν))) := by
  have := continuous_Phi; fun_prop

theorem hasDerivAt_Phi_sqrt {ν u : ℝ} (hν : 0 < ν) (hu : 0 < u) :
    HasDerivAt (fun u => Phi (Real.sqrt (u / (2 * ν)))) (bcK ν u) u := by
  have hw : u / (2 * ν) ≠ 0 := by positivity
  have h := (hasDerivAt_Phi _).comp u (((hasDerivAt_id u).div_const (2 * ν)).sqrt hw)
  refine h.congr_deriv ?_
  unfold phiDensity bcK
  have hS := Real.sq_sqrt hu.le
  have hN := Real.sq_sqrt hν.le
  have hP := Real.sq_sqrt Real.pi_pos.le
  have hT := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hS0 : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hN0 : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hP0 : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hT0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have e1 : Real.sqrt (u / (2 * ν)) = Real.sqrt u / (Real.sqrt 2 * Real.sqrt ν) :=
    sqrt_eq_of_eq_sq (by positivity) (by rw [div_pow, mul_pow, hS, hT, hN])
  have e2 : Real.sqrt (2 * π) = Real.sqrt 2 * Real.sqrt π :=
    sqrt_eq_of_eq_sq (by positivity) (by rw [mul_pow, hT, hP])
  have e3 : Real.sqrt (π * ν * u) = Real.sqrt π * Real.sqrt ν * Real.sqrt u :=
    sqrt_eq_of_eq_sq (by positivity) (by rw [mul_pow, mul_pow, hS, hP, hN])
  have e4 : -(Real.sqrt (u / (2 * ν))) ^ 2 / 2 = -u / (4 * ν) := by
    rw [Real.sq_sqrt (by positivity)]; field_simp; ring
  simp only [id]
  rw [e4, e1, e2, e3]
  generalize Real.exp (-u / (4 * ν)) = A
  generalize Real.sqrt u = S at hS hS0 ⊢
  generalize Real.sqrt ν = N at hN hN0 ⊢
  generalize Real.sqrt π = P at hP hP0 ⊢
  generalize Real.sqrt 2 = T at hT hT0 ⊢
  rw [← hN]
  field_simp
  ring

/-- For `0 ≤ r ≤ t`: `∫₀ᵗ k(s - r) ds = Φ(√((t-r)/(2ν))) - 1/2`. -/
theorem integral_bcK_sub {ν r t : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (hrt : r ≤ t) :
    IntervalIntegrable (fun s => bcK ν (s - r)) volume 0 t ∧
    ∫ s in (0 : ℝ)..t, bcK ν (s - r) = Phi (Real.sqrt ((t - r) / (2 * ν))) - 1 / 2 := by
  rcases eq_or_lt_of_le hrt with rfl | hlt
  · have hz : EqOn (fun s => bcK ν (s - r)) (fun _ => 0) (uIcc 0 r) := by
      intro s hs
      rw [uIcc_of_le hr] at hs
      exact bcK_of_nonpos hν (by linarith [hs.2])
    refine ⟨((continuous_const : Continuous fun _ : ℝ => (0:ℝ)).intervalIntegrable 0 r).congr ?_, ?_⟩
    · intro s hs
      exact (hz (uIoc_subset_uIcc hs)).symm
    · rw [intervalIntegral.integral_congr hz]
      simp [Phi_zero]
  · have hpos : 0 < t - r := by linarith
    have hlim : Tendsto (fun u => Phi (Real.sqrt (u / (2 * ν))) - 1 / 2) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous fun u : ℝ => Phi (Real.sqrt (u / (2 * ν))) - 1 / 2 := by
        have := continuous_Phi_sqrt ν; fun_prop
      convert (hc.tendsto 0).mono_left nhdsWithin_le_nhds using 2
      simp [Phi_zero]
    obtain ⟨hI, hval⟩ := integral_eq_of_hasDerivAt_of_tendsto_zero
      (E := fun u => Phi (Real.sqrt (u / (2 * ν))) - 1 / 2) (g := bcK ν) hpos
      (fun u hu => (hasDerivAt_Phi_sqrt hν hu).sub_const _) (fun u _ => bcK_nonneg ν u) hlim
    have hz : EqOn (bcK ν) (fun _ => 0) (uIcc (-r) 0) := by
      intro u hu
      rw [uIcc_of_le (by linarith)] at hu
      exact bcK_of_nonpos hν hu.2
    have hI0 : IntervalIntegrable (bcK ν) volume (-r) 0 :=
      (continuous_const.intervalIntegrable (-r) 0).congr fun u hu => (hz (uIoc_subset_uIcc hu)).symm
    have hI' := (hI0.trans hI).comp_sub_right r
    simp only [neg_add_cancel, sub_add_cancel] at hI'
    refine ⟨hI', ?_⟩
    rw [intervalIntegral.integral_comp_sub_right (fun u => bcK ν u), zero_sub,
      ← intervalIntegral.integral_add_adjacent_intervals hI0 hI, hval,
      intervalIntegral.integral_congr hz]
    simp

/-- `bcF` is interval integrable on `[0, t]` with `∫₀ᵗ bcF = E₊(t) + E₋(t)`. -/
theorem integral_bcF {ν a t : ℝ} (hν : 0 < ν) (ha : 0 < a) (ht : 0 < t) :
    IntervalIntegrable (bcF ν a) volume 0 t ∧
    ∫ r in (0 : ℝ)..t, bcF ν a r = bcE ν a 1 t + bcE ν a (-1) t := by
  have hf : bcF ν a = fun r => 2 * a * bcKer ν a r := funext fun r => bcF_eq ν a r hν
  rw [hf]
  exact integral_bcKer_a hν ha ht

/-- Pointwise: for `0 < r < s`, `f(r) k(s-r)` is a multiple of the Abel integrand. -/
theorem bcF_mul_bcK {ν a r s : ℝ} (hν : 0 < ν) (hr : 0 < r) (hrs : r < s) :
    bcF ν a r * bcK ν (s - r) = a * Real.exp (-s / (4 * ν)) / (4 * π * ν) *
      (Real.exp (-(a ^ 2 / (4 * ν)) / r) / (Real.sqrt (r ^ 3) * Real.sqrt (s - r))) := by
  unfold bcF bcK
  have hpn : 0 ≤ π * ν := by positivity
  rw [Real.sqrt_mul hpn (r ^ 3), Real.sqrt_mul hpn (s - r)]
  have e : Real.exp (-a ^ 2 / (4 * ν * r) - r / (4 * ν)) * Real.exp (-(s - r) / (4 * ν)) =
      Real.exp (-s / (4 * ν)) * Real.exp (-(a ^ 2 / (4 * ν)) / r) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have h1 : 0 < Real.sqrt (π * ν) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < Real.sqrt (r ^ 3) := Real.sqrt_pos.2 (by positivity)
  have h3 : 0 < Real.sqrt (s - r) := Real.sqrt_pos.2 (by linarith)
  have h4 : Real.sqrt (π * ν) ^ 2 = π * ν := Real.sq_sqrt hpn
  have h4' : (4 * π * ν) = 4 * Real.sqrt (π * ν) ^ 2 := by rw [h4]; ring
  rw [h4']
  generalize Real.sqrt (π * ν) = Q at h1 ⊢
  generalize Real.sqrt (r ^ 3) = R at h2 ⊢
  generalize Real.sqrt (s - r) = W at h3 ⊢
  calc _ = a * (Real.exp (-a ^ 2 / (4 * ν * r) - r / (4 * ν)) * Real.exp (-(s - r) / (4 * ν)))
        / (4 * Q ^ 2 * R * W) := by field_simp
    _ = a * (Real.exp (-s / (4 * ν)) * Real.exp (-(a ^ 2 / (4 * ν)) / r))
        / (4 * Q ^ 2 * R * W) := by rw [e]
    _ = _ := by field_simp

/-- The inner integral after Fubini: `∫₀ᵗ f(r) k(s-r) dr = s · bcKer(s)` for `0 ≤ s ≤ t`. -/
theorem integral_bcF_mul_bcK {ν a s t : ℝ} (hν : 0 < ν) (ha : 0 < a) (hs : 0 ≤ s)
    (hst : s ≤ t) :
    ∫ r in (0 : ℝ)..t, bcF ν a r * bcK ν (s - r) = s * bcKer ν a s := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · rw [zero_mul]
    have : EqOn (fun r => bcF ν a r * bcK ν (0 - r)) (fun _ => 0) (uIcc 0 t) := by
      intro r hr
      rw [uIcc_of_le hst] at hr
      simp only
      rw [bcK_of_nonpos hν (by linarith [hr.1]), mul_zero]
    rw [intervalIntegral.integral_congr this]
    simp
  have hb : 0 < a ^ 2 / (4 * ν) := by positivity
  obtain ⟨hAI, hA⟩ := abel_integral hb hs
  set C := a * Real.exp (-s / (4 * ν)) / (4 * π * ν) with hC
  have heq : EqOn (fun r => bcF ν a r * bcK ν (s - r))
      (fun r => C * (Real.exp (-(a ^ 2 / (4 * ν)) / r) / (Real.sqrt (r ^ 3) * Real.sqrt (s - r))))
      (Ioc 0 s) := by
    intro r hr
    rcases eq_or_lt_of_le hr.2 with rfl | hlt
    · simp [bcK_of_nonpos hν (le_refl 0)]
    · exact bcF_mul_bcK hν hr.1 hlt
  have hI1 : IntervalIntegrable (fun r => bcF ν a r * bcK ν (s - r)) volume 0 s := by
    refine (hAI.const_mul C).congr ?_
    intro r hr
    rw [uIoc_of_le hs.le] at hr
    exact (heq hr).symm
  have hz : EqOn (fun r => bcF ν a r * bcK ν (s - r)) (fun _ => 0) (uIcc s t) := by
    intro r hr
    rw [uIcc_of_le hst] at hr
    simp only
    rw [bcK_of_nonpos hν (by linarith [hr.1]), mul_zero]
  have hI2 : IntervalIntegrable (fun r => bcF ν a r * bcK ν (s - r)) volume s t :=
    ((continuous_const : Continuous fun _ : ℝ => (0:ℝ)).intervalIntegrable s t).congr
      fun r hr => (hz (uIoc_subset_uIcc hr)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2,
    intervalIntegral.integral_congr hz, intervalIntegral.integral_zero, add_zero,
    intervalIntegral.integral_of_le hs.le, setIntegral_congr_fun measurableSet_Ioc heq,
    integral_const_mul, ← intervalIntegral.integral_of_le hs.le, hA, hC]
  unfold bcKer
  have hS0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hN0 : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hP0 : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hN := Real.sq_sqrt hν.le
  have hP := Real.sq_sqrt Real.pi_pos.le
  have eb : Real.sqrt (a ^ 2 / (4 * ν)) = a / (2 * Real.sqrt ν) :=
    sqrt_eq_of_eq_sq (by positivity) (by rw [div_pow, mul_pow, hN]; ring)
  have epn : Real.sqrt (π * ν) = Real.sqrt π * Real.sqrt ν :=
    sqrt_eq_of_eq_sq (by positivity) (by rw [mul_pow, hP, hN])
  have ee : Real.exp (-s / (4 * ν)) * Real.exp (-(a ^ 2 / (4 * ν)) / s) =
      Real.exp (-a ^ 2 / (4 * ν * s) - s / (4 * ν)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [eb, epn, ← ee]
  generalize Real.exp (-s / (4 * ν)) = A
  generalize Real.exp (-(a ^ 2 / (4 * ν)) / s) = B
  generalize Real.sqrt ν = N at hN hN0 ⊢
  generalize Real.sqrt π = P at hP hP0 ⊢
  rw [← hN, ← hP]
  field_simp
  ring

/-- Fubini on `[0,t]²` for `f(r) k(s - r)`. -/
theorem integral_bcF_mul_integral_bcK_swap {ν a t : ℝ} (hν : 0 < ν) (ha : 0 < a) (ht : 0 < t) :
    ∫ r in (0 : ℝ)..t, bcF ν a r * ∫ s in (0 : ℝ)..t, bcK ν (s - r) =
      ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..t, bcF ν a r * bcK ν (s - r) := by
  set μ : Measure ℝ := volume.restrict (Ioc 0 t) with hμ
  have hFI := (integral_bcF hν ha ht).1
  -- integrability of `r ↦ f(r) (Φ(√((t-r)/(2ν))) - 1/2)`
  have hH : IntervalIntegrable
      (fun r => bcF ν a r * (Phi (Real.sqrt ((t - r) / (2 * ν))) - 1 / 2)) volume 0 t := by
    refine hFI.mul_continuousOn ?_
    have hc : Continuous fun r : ℝ => Phi (Real.sqrt ((t - r) / (2 * ν))) - 1 / 2 := by
      have := continuous_Phi; fun_prop
    exact hc.continuousOn
  have hmeas : Measurable (Function.uncurry fun r s => bcF ν a r * bcK ν (s - r)) :=
    ((measurable_bcF ν a).comp measurable_fst).mul
      ((measurable_bcK ν).comp (measurable_snd.sub measurable_fst))
  have hint : Integrable (Function.uncurry fun r s => bcF ν a r * bcK ν (s - r)) (μ.prod μ) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    constructor
    · rw [hμ, ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun r hr => ?_
      have := ((integral_bcK_sub hν hr.1.le hr.2).1.const_mul (bcF ν a r))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).1 this
    · have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).1 hH
      refine h1.congr_fun_ae ?_
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun r hr => ?_
      simp only [Function.uncurry_apply_pair]
      have hn : ∀ s, ‖bcF ν a r * bcK ν (s - r)‖ = bcF ν a r * bcK ν (s - r) := fun s =>
        Real.norm_of_nonneg (mul_nonneg (bcF_nonneg ha.le) (bcK_nonneg ν _))
      simp only [hn, hμ]
      rw [integral_const_mul, ← intervalIntegral.integral_of_le ht.le,
        (integral_bcK_sub hν hr.1.le hr.2).2]
  have hswap := integral_integral_swap hint
  simp only [intervalIntegral.integral_of_le ht.le]
  rw [← hswap]
  refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
  rw [integral_const_mul]

/-- **Paper `L2:IntHG-BC`** (Chen–Dalang 2015, Appendix): for `ν > 0`, `t > 0` and `x ≠ 0`,
`∫₀ᵗ |x| e^{-x²/(4νr) + (t-r)/(4ν)} / √(πνr³) · Φ(√((t-r)/(2ν))) dr
  = exp((t - 2|x|)/(4ν)) · Erfc((|x| - t)/√(4νt))`.

The paper states `t ≥ 0`; at `t = 0` the right side contains `(|x| - 0)/√0`, which the paper
reads as the limit `Erfc(+∞) = 0` but which is `Erfc(0) = 1` in Lean
(`L2_IntHG_BC_t_zero_junk`). Hence `t > 0` here. -/
theorem L2_IntHG_BC {ν t x : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx : x ≠ 0) :
    ∫ r in (0 : ℝ)..t, |x| * Real.exp (-x ^ 2 / (4 * ν * r) + (t - r) / (4 * ν)) /
        Real.sqrt (π * ν * r ^ 3) * Phi (Real.sqrt ((t - r) / (2 * ν))) =
      Real.exp ((t - 2 * |x|) / (4 * ν)) * erfc ((|x| - t) / Real.sqrt (4 * ν * t)) := by
  set a := |x| with ha_def
  have ha : 0 < a := abs_pos.2 hx
  have hx2 : x ^ 2 = a ^ 2 := (sq_abs x).symm
  -- Step 1: pull out `e^{t/(4ν)}`
  have h1 : ∀ r, a * Real.exp (-x ^ 2 / (4 * ν * r) + (t - r) / (4 * ν)) /
      Real.sqrt (π * ν * r ^ 3) * Phi (Real.sqrt ((t - r) / (2 * ν))) =
      Real.exp (t / (4 * ν)) * (bcF ν a r * Phi (Real.sqrt ((t - r) / (2 * ν)))) := by
    intro r
    unfold bcF
    rw [hx2, show -a ^ 2 / (4 * ν * r) + (t - r) / (4 * ν) =
      t / (4 * ν) + (-a ^ 2 / (4 * ν * r) - r / (4 * ν)) by ring, Real.exp_add]
    ring
  simp only [h1, intervalIntegral.integral_const_mul]
  -- Step 2: `Φ(√((t-r)/(2ν))) = 1/2 + ∫₀ᵗ k(s - r) ds`
  obtain ⟨hFI, hFval⟩ := integral_bcF hν ha ht
  have hH : IntervalIntegrable
      (fun r => bcF ν a r * (Phi (Real.sqrt ((t - r) / (2 * ν))) - 1 / 2)) volume 0 t := by
    refine hFI.mul_continuousOn ?_
    have hc : Continuous fun r : ℝ => Phi (Real.sqrt ((t - r) / (2 * ν))) - 1 / 2 := by
      have := continuous_Phi; fun_prop
    exact hc.continuousOn
  have h2 : ∫ r in (0 : ℝ)..t, bcF ν a r * Phi (Real.sqrt ((t - r) / (2 * ν))) =
      ∫ r in (0 : ℝ)..t, (bcF ν a r * (Phi (Real.sqrt ((t - r) / (2 * ν))) - 1 / 2) +
        1 / 2 * bcF ν a r) := by
    congr 1; funext r; ring
  rw [h2, intervalIntegral.integral_add hH (hFI.const_mul _), intervalIntegral.integral_const_mul,
    hFval]
  have h3 : ∫ r in (0 : ℝ)..t, bcF ν a r * (Phi (Real.sqrt ((t - r) / (2 * ν))) - 1 / 2) =
      ∫ r in (0 : ℝ)..t, bcF ν a r * ∫ s in (0 : ℝ)..t, bcK ν (s - r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht.le] at hr
    rw [(integral_bcK_sub hν hr.1 hr.2).2]
  rw [h3, integral_bcF_mul_integral_bcK_swap hν ha ht]
  -- Step 3: the inner integrals
  have h4 : ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..t, bcF ν a r * bcK ν (s - r) =
      ∫ s in (0 : ℝ)..t, 1 / 2 * (2 * s * bcKer ν a s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.le] at hs
    rw [integral_bcF_mul_bcK hν ha hs.1 hs.2]
    ring
  rw [h4, intervalIntegral.integral_const_mul, (integral_bcKer_s hν ha ht).2]
  -- Step 4: algebra
  unfold bcE
  have he : Real.exp (t / (4 * ν)) * Real.exp (-1 * a / (2 * ν)) =
      Real.exp ((t - 2 * a) / (4 * ν)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [← he, show a + -1 * t = a - t by ring]
  ring

/-- The integrand of `L2:IntHG-BC` is interval integrable on `[0, t]`. -/
theorem L2_IntHG_BC_integrable {ν t x : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx : x ≠ 0) :
    IntervalIntegrable (fun r => |x| * Real.exp (-x ^ 2 / (4 * ν * r) + (t - r) / (4 * ν)) /
        Real.sqrt (π * ν * r ^ 3) * Phi (Real.sqrt ((t - r) / (2 * ν)))) volume 0 t := by
  set a := |x| with ha_def
  have ha : 0 < a := abs_pos.2 hx
  have hx2 : x ^ 2 = a ^ 2 := (sq_abs x).symm
  obtain ⟨hFI, -⟩ := integral_bcF hν ha ht
  have hH : IntervalIntegrable
      (fun r => bcF ν a r * (Phi (Real.sqrt ((t - r) / (2 * ν))) - 1 / 2)) volume 0 t := by
    refine hFI.mul_continuousOn ?_
    have hc : Continuous fun r : ℝ => Phi (Real.sqrt ((t - r) / (2 * ν))) - 1 / 2 := by
      have := continuous_Phi; fun_prop
    exact hc.continuousOn
  have h := (hH.add (hFI.const_mul (1 / 2))).const_mul (Real.exp (t / (4 * ν)))
  refine h.congr fun r _ => ?_
  simp only [bcF]
  rw [hx2, show -a ^ 2 / (4 * ν * r) + (t - r) / (4 * ν) =
    t / (4 * ν) + (-a ^ 2 / (4 * ν * r) - r / (4 * ν)) by ring, Real.exp_add]
  ring

/-- At `t = 0` the transcribed identity of `L2:IntHG-BC` fails with Lean's conventions
(`√0 = 0`, `y/0 = 0`): the left side is `0`, the right side is `e^{-|x|/(2ν)} Erfc(0) > 0`.
The paper's `t ≥ 0` relies on reading `Erfc(|x|/0)` as `Erfc(+∞) = 0`. -/
theorem L2_IntHG_BC_t_zero_junk {ν x : ℝ} :
    ¬ (∫ r in (0 : ℝ)..0, |x| * Real.exp (-x ^ 2 / (4 * ν * r) + (0 - r) / (4 * ν)) /
        Real.sqrt (π * ν * r ^ 3) * Phi (Real.sqrt ((0 - r) / (2 * ν))) =
      Real.exp ((0 - 2 * |x|) / (4 * ν)) * erfc ((|x| - 0) / Real.sqrt (4 * ν * 0))) := by
  intro h
  simp only [intervalIntegral.integral_same, mul_zero, Real.sqrt_zero, div_zero, erfc,
    erf_zero, sub_zero, mul_one] at h
  exact (Real.exp_pos _).ne' h.symm

/-- **Paper `L2:TP-Delta-BC`** (Chen–Dalang 2015, Appendix): Bertini–Cancrini's integral
`E2:TP-Delta-BC` equals
`G_ν(t,x) G_ν(t,y) + (1/(4ν)) G_{ν/2}(t,(x+y)/2) e^{(t-2|x-y|)/(4ν)} Erfc((|x-y|-t)/√(4νt))`,
for `ν > 0`, `t > 0` and `x ≠ y`.

The hypothesis `x ≠ y` is not in the paper's statement, but it is necessary: at `x = y` the
integrand carries the factor `|x - y| = 0`, so the left side is `0` while the right side is
positive (`L2_TP_Delta_BC_false_of_eq`). The paper's proof itself assumes `x ≠ y`. -/
theorem L2_TP_Delta_BC {ν t x y : ℝ} (hν : 0 < ν) (ht : 0 < t) (hxy : x ≠ y) :
    1 / (2 * π * ν * t) * Real.exp (-(x ^ 2 + y ^ 2) / (2 * ν * t)) *
      ∫ s in (0 : ℝ)..1, |x - y| / Real.sqrt (4 * π * ν * t) * (1 / Real.sqrt (s ^ 3 * (1 - s))) *
        Real.exp (-(x - y) ^ 2 / (4 * ν * t) * ((1 - s) / s)) *
        (1 + Real.sqrt (π * t * (1 - s) / ν) * Real.exp (t / (2 * ν) * ((1 - s) / 2)) *
          Phi (Real.sqrt (t * (1 - s) / (2 * ν)))) =
    G ν t x * G ν t y + 1 / (4 * ν) * G (ν / 2) t ((x + y) / 2) *
      Real.exp ((t - 2 * |x - y|) / (4 * ν)) * erfc ((|x - y| - t) / Real.sqrt (4 * ν * t)) := by
  have hxy' : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hL := L2_IntHG_BC hν ht hxy'
  have hLI := L2_IntHG_BC_integrable hν ht hxy'
  set a := |x - y| with ha_def
  have ha : 0 < a := abs_pos.2 hxy'
  have hD : (x - y) ^ 2 = a ^ 2 := (sq_abs _).symm
  set L : ℝ → ℝ := fun r => a * Real.exp (-(x - y) ^ 2 / (4 * ν * r) + (t - r) / (4 * ν)) /
      Real.sqrt (π * ν * r ^ 3) * Phi (Real.sqrt ((t - r) / (2 * ν))) with hLdef
  set β := a ^ 2 / (4 * ν * t) with hβ
  have hβ0 : 0 < β := by positivity
  obtain ⟨hAI, hA⟩ := abel_integral hβ0 one_pos
  set c1 := a / Real.sqrt (4 * π * ν * t) * Real.exp β with hc1
  set κ := Real.exp β * π * t ^ 2 / (2 * Real.sqrt (π * ν * t)) with hκ
  -- pointwise split of the integrand on `(0, 1)`
  have hsplit : EqOn (fun s => a / Real.sqrt (4 * π * ν * t) * (1 / Real.sqrt (s ^ 3 * (1 - s))) *
        Real.exp (-(x - y) ^ 2 / (4 * ν * t) * ((1 - s) / s)) *
        (1 + Real.sqrt (π * t * (1 - s) / ν) * Real.exp (t / (2 * ν) * ((1 - s) / 2)) *
          Phi (Real.sqrt (t * (1 - s) / (2 * ν)))))
      (fun s => c1 * (Real.exp (-β / s) / (Real.sqrt (s ^ 3) * Real.sqrt (1 - s))) +
        κ * L (t * s)) (uIoo 0 1) := by
    intro s hs
    rw [uIoo, min_eq_left zero_le_one, max_eq_right zero_le_one] at hs
    obtain ⟨hs0, hs1⟩ := hs
    have h1s : 0 < 1 - s := by linarith
    simp only [hLdef, hc1, hκ]
    rw [show (t - t * s) = t * (1 - s) by ring]
    have hS := Real.sq_sqrt hs0.le
    have hU := Real.sq_sqrt h1s.le
    have hT := Real.sq_sqrt ht.le
    have hN := Real.sq_sqrt hν.le
    have hP := Real.sq_sqrt Real.pi_pos.le
    have hS0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
    have hU0 : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.2 h1s
    have hT0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hN0 : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
    have hP0 : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
    have r1 : Real.sqrt (s ^ 3 * (1 - s)) = Real.sqrt s ^ 3 * Real.sqrt (1 - s) :=
      sqrt_eq_of_eq_sq (by positivity) (by
        rw [mul_pow, ← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, hS, hU])
    have r2 : Real.sqrt (s ^ 3) = Real.sqrt s ^ 3 :=
      sqrt_eq_of_eq_sq (by positivity) (by rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, hS])
    have r3 : Real.sqrt (π * t * (1 - s) / ν) =
        Real.sqrt π * Real.sqrt t * Real.sqrt (1 - s) / Real.sqrt ν :=
      sqrt_eq_of_eq_sq (by positivity) (by rw [div_pow, mul_pow, mul_pow, hP, hT, hU, hN])
    have r4 : Real.sqrt (4 * π * ν * t) = 2 * Real.sqrt π * Real.sqrt ν * Real.sqrt t :=
      sqrt_eq_of_eq_sq (by positivity) (by rw [mul_pow, mul_pow, mul_pow, hP, hT, hN]; ring)
    have r5 : Real.sqrt (π * ν * t) = Real.sqrt π * Real.sqrt ν * Real.sqrt t :=
      sqrt_eq_of_eq_sq (by positivity) (by rw [mul_pow, mul_pow, hP, hT, hN])
    have r6 : Real.sqrt (π * ν * (t * s) ^ 3) =
        Real.sqrt π * Real.sqrt ν * Real.sqrt t ^ 3 * Real.sqrt s ^ 3 :=
      sqrt_eq_of_eq_sq (by positivity) (by
        rw [show (Real.sqrt π * Real.sqrt ν * Real.sqrt t ^ 3 * Real.sqrt s ^ 3) ^ 2 =
          Real.sqrt π ^ 2 * Real.sqrt ν ^ 2 * (Real.sqrt t ^ 2) ^ 3 * (Real.sqrt s ^ 2) ^ 3 by ring,
          hP, hT, hN, hS]; ring)
    have x1 : Real.exp (-(x - y) ^ 2 / (4 * ν * t) * ((1 - s) / s)) =
        Real.exp β * Real.exp (-β / s) := by
      rw [← Real.exp_add, hβ, hD]; congr 1; field_simp; ring
    have x2 : Real.exp (-(x - y) ^ 2 / (4 * ν * (t * s)) + t * (1 - s) / (4 * ν)) =
        Real.exp (-β / s) * Real.exp (t / (2 * ν) * ((1 - s) / 2)) := by
      rw [← Real.exp_add, hβ, hD]; congr 1; field_simp; ring
    rw [r1, r2, r3, r4, r5, r6, x1, x2]
    generalize Real.exp β = Eb
    generalize Real.exp (-β / s) = Es
    generalize Real.exp (t / (2 * ν) * ((1 - s) / 2)) = E2
    generalize Phi (Real.sqrt (t * (1 - s) / (2 * ν))) = Φv
    generalize Real.sqrt s = S at hS hS0 ⊢
    generalize Real.sqrt (1 - s) = U at hU hU0 ⊢
    generalize Real.sqrt t = T at hT hT0 ⊢
    generalize Real.sqrt ν = N at hN hN0 ⊢
    generalize Real.sqrt π = P at hP hP0 ⊢
    rw [← hT, ← hP]
    field_simp
  have hBI : IntervalIntegrable (fun s => L (t * s)) volume 0 1 := by
    have := hLI.comp_mul_left (c := t)
    simpa [zero_div, div_self ht.ne'] using this
  rw [intervalIntegral.integral_congr_uIoo hsplit,
    intervalIntegral.integral_add (hAI.const_mul c1) (hBI.const_mul κ),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hA,
    intervalIntegral.integral_comp_mul_left (fun r => L r) ht.ne', mul_zero, mul_one]
  have hLt : ∫ r in (0 : ℝ)..t, L r =
      Real.exp ((t - 2 * a) / (4 * ν)) * erfc ((a - t) / Real.sqrt (4 * ν * t)) := hL
  rw [hLt, smul_eq_mul]
  -- the two constants
  have hN := Real.sq_sqrt hν.le
  have hP := Real.sq_sqrt Real.pi_pos.le
  have hT := Real.sq_sqrt ht.le
  have hN0 : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hP0 : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hT0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hA1 : c1 * (Real.sqrt π / Real.sqrt β * Real.exp (-β / 1) / Real.sqrt 1) = 1 := by
    have eβ : Real.sqrt β = a / (2 * Real.sqrt ν * Real.sqrt t) :=
      sqrt_eq_of_eq_sq (by positivity) (by rw [hβ, div_pow, mul_pow, mul_pow, hN, hT]; ring)
    have r4 : Real.sqrt (4 * π * ν * t) = 2 * Real.sqrt π * Real.sqrt ν * Real.sqrt t :=
      sqrt_eq_of_eq_sq (by positivity) (by rw [mul_pow, mul_pow, mul_pow, hP, hT, hN]; ring)
    have ee : Real.exp β * Real.exp (-β / 1) = 1 := by
      rw [← Real.exp_add, div_one, add_neg_cancel, Real.exp_zero]
    rw [hc1, eβ, r4, Real.sqrt_one]
    calc _ = a / (2 * √π * √ν * √t) * √π / (a / (2 * √ν * √t)) * (Real.exp β * Real.exp (-β / 1)) := by
          ring
      _ = 1 := by rw [ee]; field_simp
  have hGG : 1 / (2 * π * ν * t) * Real.exp (-(x ^ 2 + y ^ 2) / (2 * ν * t)) =
      G ν t x * G ν t y := by
    unfold G
    have h2 : 0 < 2 * π * ν * t := by positivity
    have hs := Real.sq_sqrt h2.le
    have hs0 : 0 < Real.sqrt (2 * π * ν * t) := Real.sqrt_pos.2 h2
    have ee : Real.exp (-x ^ 2 / (2 * ν * t)) * Real.exp (-y ^ 2 / (2 * ν * t)) =
        Real.exp (-(x ^ 2 + y ^ 2) / (2 * ν * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← ee]
    generalize Real.sqrt (2 * π * ν * t) = Q at hs hs0 ⊢
    rw [← hs]
    field_simp
  have hB1 : 1 / (2 * π * ν * t) * Real.exp (-(x ^ 2 + y ^ 2) / (2 * ν * t)) * κ * t⁻¹ =
      1 / (4 * ν) * G (ν / 2) t ((x + y) / 2) := by
    unfold G
    rw [hκ, show 2 * π * (ν / 2) * t = π * ν * t by ring]
    have ee : Real.exp (-(x ^ 2 + y ^ 2) / (2 * ν * t)) * Real.exp β =
        Real.exp (-((x + y) / 2) ^ 2 / (2 * (ν / 2) * t)) := by
      rw [← Real.exp_add, hβ, ← hD]; congr 1; field_simp; ring
    have h2 : 0 < π * ν * t := by positivity
    have hs := Real.sq_sqrt h2.le
    have hs0 : 0 < Real.sqrt (π * ν * t) := Real.sqrt_pos.2 h2
    rw [← ee]
    generalize Real.exp (-(x ^ 2 + y ^ 2) / (2 * ν * t)) = E1
    generalize Real.exp β = E2
    generalize Real.sqrt (π * ν * t) = Q at hs hs0 ⊢
    have : π = Q ^ 2 / (ν * t) := by rw [hs]; field_simp
    rw [this]
    field_simp
    ring
  calc _ = 1 / (2 * π * ν * t) * Real.exp (-(x ^ 2 + y ^ 2) / (2 * ν * t)) *
        (c1 * (Real.sqrt π / Real.sqrt β * Real.exp (-β / 1) / Real.sqrt 1)) +
      1 / (2 * π * ν * t) * Real.exp (-(x ^ 2 + y ^ 2) / (2 * ν * t)) * κ * t⁻¹ *
        (Real.exp ((t - 2 * a) / (4 * ν)) * erfc ((a - t) / Real.sqrt (4 * ν * t))) := by ring
    _ = _ := by rw [hA1, hB1, hGG]; ring

/-- **No-go at `x = y`** for the paper's `L2:TP-Delta-BC` as stated (without `x ≠ y`): for every
`ν > 0`, `t > 0` and `x`, Bertini–Cancrini's integral `E2:TP-Delta-BC` at `y = x` is `0`
(its integrand carries the factor `|x - y|`), while the claimed closed form is positive. -/
theorem L2_TP_Delta_BC_false_of_eq {ν t x : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    ¬ (1 / (2 * π * ν * t) * Real.exp (-(x ^ 2 + x ^ 2) / (2 * ν * t)) *
      ∫ s in (0 : ℝ)..1, |x - x| / Real.sqrt (4 * π * ν * t) * (1 / Real.sqrt (s ^ 3 * (1 - s))) *
        Real.exp (-(x - x) ^ 2 / (4 * ν * t) * ((1 - s) / s)) *
        (1 + Real.sqrt (π * t * (1 - s) / ν) * Real.exp (t / (2 * ν) * ((1 - s) / 2)) *
          Phi (Real.sqrt (t * (1 - s) / (2 * ν)))) =
    G ν t x * G ν t x + 1 / (4 * ν) * G (ν / 2) t ((x + x) / 2) *
      Real.exp ((t - 2 * |x - x|) / (4 * ν)) * erfc ((|x - x| - t) / Real.sqrt (4 * ν * t))) := by
  intro h
  simp only [sub_self, abs_zero, zero_div, zero_mul, intervalIntegral.integral_zero,
    mul_zero] at h
  have hG : 0 < G ν t x := by unfold G; positivity
  have hG2 : 0 < G (ν / 2) t ((x + x) / 2) := by unfold G; positivity
  have herfc : 0 < erfc ((0 - t) / Real.sqrt (4 * ν * t)) := by
    unfold erfc
    have : erf ((0 - t) / Real.sqrt (4 * ν * t)) ≤ 0 :=
      erf_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _))
    linarith
  have : 0 < G ν t x * G ν t x + 1 / (4 * ν) * G (ν / 2) t ((x + x) / 2) *
      Real.exp ((t - 2 * 0) / (4 * ν)) * erfc ((0 - t) / Real.sqrt (4 * ν * t)) := by
    have : 0 < 1 / (4 * ν) := by positivity
    positivity
  linarith

end ChenDalang15

end
