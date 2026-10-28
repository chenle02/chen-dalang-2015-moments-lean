module

public import ChenDalang15.KClosed
public import ChenDalang15.PhiE

/-!
# The function `𝓗 = 1 ⋆ 𝓚` (Chen–Dalang 2015, display `E2:H`)

For `ν > 0`, `t ≥ 0` and every `x`,
`𝓗(t;ν,λ) := (1 ⋆ 𝓚)(t,x) = 2 e^{λ⁴t/(4ν)} Φ(λ² √(t/(2ν))) − 1`.

Route (the paper cites `LA:Phi-E`): the space integral of `𝓚(r, x − y) = G_{ν/2}(r, x − y) k(r)`
is `k(r)` (heat kernel of mass one), so `(1 ⋆ 𝓚)(t,x) = ∫₀ᵗ k(r) dr` with
`k(r) = λ²/√(4πνr) + λ⁴/(2ν) e^{λ⁴r/(4ν)} Φ(λ²√(r/(2ν)))` (`E:K`). With `b = λ²/√(4πν)`, the
first term integrates to `2b√t`, and `LA:Phi-E` (valid for `b > 0`, i.e. `λ ≠ 0`) gives the
second as `2 e^{λ⁴t/(4ν)} Φ(·) − 1 − 2b√t`. The case `λ = 0` is direct (`𝓚 = 0`, `Φ(0) = 1/2`).
-/

set_option autoImplicit false

public section

namespace ChenDalang15

open Real MeasureTheory intervalIntegral

/-- The scalar factor of `𝓚(r, ·)` in `E:K`. -/
noncomputable def kClosed (ν lam r : ℝ) : ℝ :=
  lam ^ 2 / Real.sqrt (4 * π * ν * r) +
    lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))

/-- The space integral of `𝓚(r, x − y)` is `k(r)` for `r > 0`. -/
theorem integral_K_sub {ν lam r : ℝ} (hν : 0 < ν) (hr : 0 < r) (x : ℝ) :
    ∫ y, (1 : ℝ) * K ν lam r (x - y) = kClosed ν lam r := by
  have hfun : (fun y => (1 : ℝ) * K ν lam r (x - y)) =
      fun y => kClosed ν lam r * G (ν / 2) r (x - y) := by
    funext y
    rw [K_eq hν hr (x - y), kClosed]
    ring
  rw [hfun, MeasureTheory.integral_const_mul,
    integral_sub_left_eq_self (fun y => G (ν / 2) r y) (volume : Measure ℝ) x]
  simp only [G_eq_heatKernel]
  rw [RoughHeatKernel.integral_heatKernel (mul_pos (half_pos hν) hr), mul_one]

/-- `(1 ⋆ 𝓚)(t,x) = ∫₀ᵗ k(r) dr`. -/
theorem one_conv_K_eq_integral {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    stConv (fun _ _ => (1 : ℝ)) (K ν lam) t x = ∫ r in (0 : ℝ)..t, kClosed ν lam r := by
  have hcongr : ∫ s in (0 : ℝ)..t, ∫ y, (1 : ℝ) * K ν lam (t - s) (x - y) =
      ∫ s in (0 : ℝ)..t, kClosed ν lam (t - s) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_real t] with s hst hs
    rw [Set.uIoc_of_le ht] at hs
    exact integral_K_sub hν (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) x
  rw [stConv, hcongr, intervalIntegral.integral_comp_sub_left (fun r => kClosed ν lam r) t]
  simp

/-- `∫₀ᵗ λ²/√(4πνr) dr = 2 b √t` with `b = λ²/√(4πν)`. -/
theorem integral_first_term {ν lam t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    ∫ r in (0 : ℝ)..t, lam ^ 2 / Real.sqrt (4 * π * ν * r) =
      2 * bConst ν lam * Real.sqrt t := by
  have hcongr : ∫ r in (0 : ℝ)..t, lam ^ 2 / Real.sqrt (4 * π * ν * r) =
      ∫ r in (0 : ℝ)..t, bConst ν lam * r ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le ht] at hr
    rw [bConst, Real.sqrt_mul (by positivity) r, Real.rpow_neg hr.1, ← Real.sqrt_eq_rpow]
    by_cases h0 : r = 0
    · simp [h0]
    · field_simp
  rw [hcongr, intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
    Real.sqrt_eq_rpow]
  norm_num [Real.zero_rpow]
  ring

/-- `b² = λ⁴/(4πν)`. -/
theorem bConst_sq {ν lam : ℝ} (hν : 0 < ν) : bConst ν lam ^ 2 = lam ^ 4 / (4 * π * ν) := by
  rw [bConst, div_pow, Real.sq_sqrt (by positivity)]
  ring

/-- `√(2πb²r) = λ²√(r/(2ν))`. -/
theorem sqrt_two_pi_bConst_sq {ν lam r : ℝ} (hν : 0 < ν) :
    Real.sqrt (2 * π * bConst ν lam ^ 2 * r) = lam ^ 2 * Real.sqrt (r / (2 * ν)) := by
  rw [bConst_sq hν, show 2 * π * (lam ^ 4 / (4 * π * ν)) * r = (lam ^ 2) ^ 2 * (r / (2 * ν)) by
    field_simp; ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]

/-- `πb²r = λ⁴r/(4ν)`. -/
theorem pi_bConst_sq_mul {ν lam r : ℝ} (hν : 0 < ν) :
    π * bConst ν lam ^ 2 * r = lam ^ 4 * r / (4 * ν) := by
  rw [bConst_sq hν]
  field_simp

/-- The second term of `k` in the variables of `LA:Phi-E`. -/
theorem second_term_eq {ν lam r : ℝ} (hν : 0 < ν) :
    lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (r / (2 * ν))) =
      2 * bConst ν lam ^ 2 *
        (π * (Real.exp (π * bConst ν lam ^ 2 * r) *
          Phi (Real.sqrt (2 * π * bConst ν lam ^ 2 * r)))) := by
  rw [sqrt_two_pi_bConst_sq hν, pi_bConst_sq_mul hν, bConst_sq hν]
  field_simp
  ring

/-- **Chen–Dalang (2015), display `E2:H`.** For `ν > 0`, `t ≥ 0` and every `x`,
`(1 ⋆ 𝓚)(t,x) = 2 e^{λ⁴t/(4ν)} Φ(λ² √(t/(2ν))) − 1`. -/
theorem one_conv_K {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    stConv (fun _ _ => (1 : ℝ)) (K ν lam) t x =
      2 * Real.exp (lam ^ 4 * t / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (t / (2 * ν))) - 1 := by
  rw [one_conv_K_eq_integral hν ht x]
  by_cases hlam : lam = 0
  · subst hlam
    simp [kClosed, Phi_zero]
  have hb : 0 < bConst ν lam := by
    unfold bConst
    have : 0 < lam ^ 2 := by positivity
    positivity
  -- Split `k` into its two terms.
  have hI1 : IntervalIntegrable (fun r => lam ^ 2 / Real.sqrt (4 * π * ν * r)) volume 0 t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
      (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (bConst ν lam)
    refine h.congr fun r hr => ?_
    rw [Set.uIoc_of_le ht] at hr
    show bConst ν lam * r ^ (-(1 / 2 : ℝ)) = lam ^ 2 / Real.sqrt (4 * π * ν * r)
    rw [bConst, Real.sqrt_mul (by positivity) r, Real.rpow_neg hr.1.le, ← Real.sqrt_eq_rpow]
    field_simp
  have hI2 : IntervalIntegrable (fun r => lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) *
      Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))) volume 0 t := by
    have hΦ : Continuous Phi := continuous_Phi
    apply Continuous.intervalIntegrable
    fun_prop
  have hsplit : (fun r => kClosed ν lam r) = fun r => lam ^ 2 / Real.sqrt (4 * π * ν * r) +
      lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) *
        Phi (lam ^ 2 * Real.sqrt (r / (2 * ν))) := by
    funext r; rfl
  rw [hsplit, intervalIntegral.integral_add hI1 hI2, integral_first_term hν ht]
  -- Second term via `LA:Phi-E`.
  have hcongr : ∫ r in (0 : ℝ)..t, lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) *
        Phi (lam ^ 2 * Real.sqrt (r / (2 * ν))) =
      ∫ r in (0 : ℝ)..t, 2 * bConst ν lam ^ 2 *
        (π * (Real.exp (π * bConst ν lam ^ 2 * r) *
          Phi (Real.sqrt (2 * π * bConst ν lam ^ 2 * r)))) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le ht] at hr
    exact second_term_eq hν
  rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_exp_mul_Phi hb ht, pi_bConst_sq_mul hν, sqrt_two_pi_bConst_sq hν]
  have hb0 : bConst ν lam ≠ 0 := hb.ne'
  field_simp
  ring

end ChenDalang15

end
