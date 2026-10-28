module

public import ChenDalang15.Phi
public import ChenDalang15.ErfSeries
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Paper `LA:Phi-E`: `π ∫₀ᵗ e^{πb²u} Φ(√(2πb²u)) du`

Chen–Dalang (2015), Appendix, Lemma `LA:Phi-E`:
`π ∫₀ᵗ e^{πb²u} Φ(√(2πb²u)) du = e^{πb²t}Φ(√(2πb²t))/b² − 1/(2b²) − √t/b`, stated for `b ≠ 0`.

The paper's proof differentiates `√(2πb²u)` as `b/√(2u)·√π`, i.e. it writes `b` for `|b|`.
The identity holds for `b > 0` (`integral_exp_mul_Phi`, the case used in the paper,
`b = λ²/√(4πν)`) and fails for `b < 0` (`integral_exp_mul_Phi_false_of_neg`), where the last
term must be `−√t/|b|`.

Helpers: `Phi` has derivative the standard Gaussian density (`hasDerivAt_Phi`) and
`Phi 0 = 1/2` (`Phi_zero`, from `ChenDalang15.ErfSeries`); both come from
`RoughHeatKernel.Erf` (v0.10.0) through the definitional bridges `Phi_eq_normalCDF` and
`phiDensity_eq_normalDensity`.
-/

set_option autoImplicit false

public section

namespace ChenDalang15

open Real MeasureTheory Set

/-- The standard Gaussian density `(2π)^{-1/2} e^{-y²/2}`, the integrand of `Phi`. -/
@[expose] noncomputable def phiDensity (y : ℝ) : ℝ :=
  (Real.sqrt (2 * π))⁻¹ * Real.exp (-y ^ 2 / 2)

/-- Bridge: `phiDensity` is `RoughHeatKernel.normalDensity` (identical bodies). -/
theorem phiDensity_eq_normalDensity : phiDensity = RoughHeatKernel.normalDensity := rfl

theorem continuous_phiDensity : Continuous phiDensity := RoughHeatKernel.continuous_normalDensity

theorem integrable_phiDensity : Integrable phiDensity := RoughHeatKernel.integrable_normalDensity

theorem Phi_eq_integral_phiDensity (x : ℝ) : Phi x = ∫ y in Iic x, phiDensity y := rfl

theorem Phi_eq_Phi_zero_add (x : ℝ) : Phi x = Phi 0 + ∫ y in (0 : ℝ)..x, phiDensity y :=
  RoughHeatKernel.normalCDF_eq_add_integral x

/-- `Φ'(x) = (2π)^{-1/2} e^{-x²/2}` (`RoughHeatKernel.hasDerivAt_normalCDF`). -/
theorem hasDerivAt_Phi (x : ℝ) : HasDerivAt Phi (phiDensity x) x :=
  RoughHeatKernel.hasDerivAt_normalCDF x

theorem continuous_Phi : Continuous Phi := RoughHeatKernel.continuous_normalCDF

/-- Paper LA:Phi-E, for `b > 0` (the case the paper uses: `b = λ²/√(4πν)`). -/
theorem integral_exp_mul_Phi {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    Real.pi * ∫ u in (0 : ℝ)..t, Real.exp (Real.pi * b ^ 2 * u) * Phi (Real.sqrt (2 * Real.pi * b ^ 2 * u)) =
      Real.exp (Real.pi * b ^ 2 * t) * Phi (Real.sqrt (2 * Real.pi * b ^ 2 * t)) / b ^ 2
        - 1 / (2 * b ^ 2) - Real.sqrt t / b := by
  set G : ℝ → ℝ := fun u => Real.exp (Real.pi * b ^ 2 * u) *
    Phi (Real.sqrt (2 * Real.pi * b ^ 2 * u)) / b ^ 2 - Real.sqrt u / b with hG
  have hGc : Continuous G := by
    have := continuous_Phi
    rw [hG]; fun_prop (disch := exact hb.ne')
  have hcont : Continuous fun u => Real.pi * (Real.exp (Real.pi * b ^ 2 * u) *
      Phi (Real.sqrt (2 * Real.pi * b ^ 2 * u))) := by
    have := continuous_Phi
    fun_prop
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) t, HasDerivAt G (Real.pi * (Real.exp (Real.pi * b ^ 2 * u) *
      Phi (Real.sqrt (2 * Real.pi * b ^ 2 * u)))) u := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hlin : 0 < 2 * Real.pi * b ^ 2 * u := by positivity
    have hs := ((hasDerivAt_id' u).const_mul (2 * Real.pi * b ^ 2)).sqrt hlin.ne'
    have hP := (hasDerivAt_Phi _).comp u hs
    have hE := ((hasDerivAt_id' u).const_mul (Real.pi * b ^ 2)).exp
    have hR := (Real.hasDerivAt_sqrt hu0.ne').div_const b
    have hall := ((hE.mul hP).div_const (b ^ 2)).sub hR
    convert hall using 1
    · funext x; rfl
    have hdens : phiDensity (Real.sqrt (2 * Real.pi * b ^ 2 * u)) =
        (Real.sqrt (2 * π))⁻¹ * Real.exp (-(Real.pi * b ^ 2 * u)) := by
      simp only [phiDensity]
      rw [Real.sq_sqrt hlin.le]
      congr 2
      ring
    have hsplit : Real.sqrt (2 * Real.pi * b ^ 2 * u) =
        Real.sqrt (2 * π) * b * Real.sqrt u := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hb.le]
    simp only [Function.comp_apply]
    rw [hdens, Real.exp_neg]
    rw [hsplit]
    have hA : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
    have hApos : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
    have hS : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
    have hSpos : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
    have hEpos : 0 < Real.exp (Real.pi * b ^ 2 * u) := Real.exp_pos _
    generalize Real.exp (Real.pi * b ^ 2 * u) = E at hEpos ⊢
    generalize Phi (Real.sqrt (2 * π) * b * Real.sqrt u) = P
    generalize Real.sqrt (2 * π) = A at hA hApos ⊢
    generalize Real.sqrt u = S at hS hSpos ⊢
    have hπ : Real.pi = A ^ 2 / 2 := by linarith
    rw [hπ]
    have hb0 : b ≠ 0 := hb.ne'
    field_simp
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hGc.continuousOn hderiv
    (hcont.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul] at hint
  rw [hint, hG]
  simp only [mul_zero, Real.exp_zero, Real.sqrt_zero, Phi_zero, zero_div, sub_zero, one_mul]
  ring

/-- The paper's hypothesis `b ≠ 0` is too weak: the identity fails for `b = -1`, `t = 1`. -/
theorem integral_exp_mul_Phi_false_of_neg :
    ¬ (Real.pi * ∫ u in (0 : ℝ)..1, Real.exp (Real.pi * (-1 : ℝ) ^ 2 * u) * Phi (Real.sqrt (2 * Real.pi * (-1 : ℝ) ^ 2 * u)) =
      Real.exp (Real.pi * (-1 : ℝ) ^ 2 * 1) * Phi (Real.sqrt (2 * Real.pi * (-1 : ℝ) ^ 2 * 1)) / (-1 : ℝ) ^ 2
        - 1 / (2 * (-1 : ℝ) ^ 2) - Real.sqrt 1 / (-1 : ℝ)) := by
  intro H
  have h1 := integral_exp_mul_Phi (b := 1) (t := 1) one_pos zero_le_one
  simp only [neg_one_sq, one_pow, mul_one, Real.sqrt_one, div_one, div_neg] at H h1
  linarith

end ChenDalang15

end
