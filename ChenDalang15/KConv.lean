module

public import ChenDalang15.KernelK
public import ChenDalang15.Summability

/-!
# The resolvent identity `𝓚 ⋆ 𝓛₀ = 𝓚 − 𝓛₀` of Chen–Dalang (2015), `E:KS-Kn-K0`

The paper (Proposition `P2:K`) calls `(𝓚 ⋆ 𝓛₀)(t,x) = 𝓚(t,x) − 𝓛₀(t,x)` "a direct
consequence of `E:Def-K`". Formally it needs an interchange of the time integral with the
series `𝓚 = Σₙ 𝓛ₙ`. For `0 < s < t` the inner space integral factorizes
(`K_eq_G_mul_kSeries`, `L_zero_eq`, semigroup property at `ν/2`) into
`Σₙ G_{ν/2}(t,x) lCoeffₙ b · s^{(n+1)/2-1} (t-s)^{1/2-1}`; every term is nonnegative and
integrable (Beta integrand), and its integral is `𝓛ₙ₊₁(t,x)`, which is summable. The
interchange is `MeasureTheory.integral_tsum_of_summable_integral_norm`.
-/

set_option autoImplicit false

public section

namespace ChenDalang15

open Real MeasureTheory intervalIntegral

/-- `b = λ²/√(4πν) ≥ 0`. -/
theorem bConst_nonneg (ν lam : ℝ) : 0 ≤ bConst ν lam := by
  unfold bConst
  positivity

/-- `(b√π)^{n+1}/Γ((n+1)/2) ≥ 0`. -/
theorem lCoeff_nonneg (ν lam : ℝ) (n : ℕ) : 0 ≤ lCoeff ν lam n := by
  unfold lCoeff
  have hΓ := Real.Gamma_pos_of_pos (show 0 < ((n : ℝ) + 1) / 2 by positivity)
  have hb := bConst_nonneg ν lam
  positivity

/-- For `t > 0`, the series `Σₙ 𝓛ₙ(t,x)` defining `𝓚(t,x)` is summable. -/
theorem summable_L {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun n => L ν lam n t x) := by
  have h := (summable_BCoeff_rpow (bConst_nonneg ν lam) ht.le (m := 1) one_pos).mul_left
    (L ν lam 0 t x)
  refine h.congr fun n => ?_
  rw [L_eq_L_zero_mul_BCoeff hν n ht x]
  simp

/-- The Beta integrand `s^{a-1} (t-s)^{b-1}` is interval integrable on `[0, t]` for
`a, b, t > 0`, from `RoughHeatKernel.intervalIntegrable_rpow_mul_sub_rpow`. -/
theorem intervalIntegrable_rpow_mul_sub_rpow {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) :
    IntervalIntegrable (fun s => s ^ (a - 1) * (t - s) ^ (b - 1)) volume 0 t :=
  RoughHeatKernel.intervalIntegrable_rpow_mul_sub_rpow ha hb ht

/-- The `n`-th time integrand of `𝓛ₙ ⋆ 𝓛₀` integrates to `𝓛ₙ₊₁(t,x)`. -/
theorem integral_L_succ_integrand {ν lam : ℝ} (hν : 0 < ν) (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    ∫ s in (0 : ℝ)..t, G (ν / 2) t x * (lCoeff ν lam n * bConst ν lam) *
        (s ^ (((n : ℝ) + 1) / 2 - 1) * (t - s) ^ ((1 / 2 : ℝ) - 1)) =
      L ν lam (n + 1) t x := by
  have ha : 0 < ((n : ℝ) + 1) / 2 := by positivity
  have hGa : Real.Gamma (((n : ℝ) + 1) / 2) ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  rw [intervalIntegral.integral_const_mul,
    integral_rpow_mul_sub_rpow ha (by norm_num : (0 : ℝ) < 1 / 2) ht, Real.Gamma_one_half_eq,
    L_eq hν (n + 1) ht x]
  simp only [lCoeff]
  have e3 : ((n : ℝ) + 1) / 2 + 1 / 2 - 1 = (((n + 1 : ℕ) : ℝ) - 1) / 2 := by push_cast; ring
  have e4 : ((n : ℝ) + 1) / 2 + 1 / 2 = (((n + 1 : ℕ) : ℝ) + 1) / 2 := by push_cast; ring
  rw [e3, e4]
  field_simp
  ring

/-- **Chen–Dalang (2015), Proposition `P2:K`, display `E:KS-Kn-K0`:**
`(𝓚 ⋆ 𝓛₀)(t,x) = 𝓚(t,x) − 𝓛₀(t,x)`. -/
theorem K_conv_L_zero {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    stConv (K ν lam) (L ν lam 0) t x = K ν lam t x - L ν lam 0 t x := by
  have hν2 : 0 < ν / 2 := half_pos hν
  set F : ℕ → ℝ → ℝ := fun n s => G (ν / 2) t x * (lCoeff ν lam n * bConst ν lam) *
      (s ^ (((n : ℝ) + 1) / 2 - 1) * (t - s) ^ ((1 / 2 : ℝ) - 1)) with hF
  have hsum := summable_L (lam := lam) hν ht x
  -- Right side: `𝓚 − 𝓛₀ = Σₙ 𝓛ₙ₊₁`.
  have hRHS : K ν lam t x - L ν lam 0 t x = ∑' n, L ν lam (n + 1) t x := by
    rw [K, hsum.tsum_eq_zero_add]
    ring
  -- Inner space integral at `0 < s < t`.
  have hinner : ∀ s, 0 < s → s < t →
      ∫ y, K ν lam s y * L ν lam 0 (t - s) (x - y) = ∑' n, F n s := by
    intro s hs hst
    have hts : 0 < t - s := sub_pos.mpr hst
    have hfun : (fun y => K ν lam s y * L ν lam 0 (t - s) (x - y)) = fun y =>
        (kSeries ν lam s * bConst ν lam * (t - s) ^ (-(1 / 2 : ℝ))) *
          (G (ν / 2) (t - s) (x - y) * G (ν / 2) s y) := by
      funext y
      rw [K_eq_G_mul_kSeries hν hs y, L_zero_eq hν hts (x - y)]
      ring
    rw [hfun, MeasureTheory.integral_const_mul, integral_G_mul_G hν2 hs hst x]
    have hterm : ∀ n : ℕ, F n s = (G (ν / 2) t x * bConst ν lam * (t - s) ^ (-(1 / 2 : ℝ))) *
        (lCoeff ν lam n * s ^ (((n : ℝ) - 1) / 2)) := by
      intro n
      have e1 : ((n : ℝ) + 1) / 2 - 1 = ((n : ℝ) - 1) / 2 := by ring
      have e2 : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
      simp only [hF]
      rw [e1, e2]
      ring
    rw [tsum_congr hterm, tsum_mul_left, kSeries]
    ring
  -- Left side as a time integral of the series.
  have hLHS : stConv (K ν lam) (L ν lam 0) t x = ∫ s in (0 : ℝ)..t, ∑' n, F n s := by
    unfold stConv
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_real t] with s hst hs
    rw [Set.uIoc_of_le ht.le] at hs
    exact hinner s hs.1 (lt_of_le_of_ne hs.2 hst)
  have hint : ∀ n, ∫ s in (0 : ℝ)..t, F n s = L ν lam (n + 1) t x := fun n =>
    integral_L_succ_integrand hν n ht x
  have hFint : ∀ n, IntervalIntegrable (F n) volume 0 t := fun n =>
    (intervalIntegrable_rpow_mul_sub_rpow (by positivity : (0 : ℝ) < ((n : ℝ) + 1) / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) ht).const_mul _
  have hnonneg : ∀ n, ∀ s ∈ Set.Ioc 0 t, 0 ≤ F n s := by
    intro n s hs
    have hG : 0 ≤ G (ν / 2) t x := by
      rw [G_eq_heatKernel]
      exact (RoughHeatKernel.heatKernel_pos (mul_pos hν2 ht) x).le
    have hl := lCoeff_nonneg ν lam n
    have hb := bConst_nonneg ν lam
    have h1 : 0 ≤ s ^ (((n : ℝ) + 1) / 2 - 1) := Real.rpow_nonneg hs.1.le _
    have h2 : 0 ≤ (t - s) ^ ((1 / 2 : ℝ) - 1) := Real.rpow_nonneg (sub_nonneg.mpr hs.2) _
    simp only [hF]
    positivity
  have hnorm : ∀ n, ∫ s in Set.Ioc 0 t, ‖F n s‖ = L ν lam (n + 1) t x := by
    intro n
    rw [← hint n, intervalIntegral.integral_of_le ht.le]
    exact setIntegral_congr_fun measurableSet_Ioc fun s hs => Real.norm_of_nonneg (hnonneg n s hs)
  have hint' : ∀ n, ∫ s in Set.Ioc 0 t, F n s = L ν lam (n + 1) t x := fun n => by
    rw [← hint n, intervalIntegral.integral_of_le ht.le]
  rw [hLHS, hRHS, intervalIntegral.integral_of_le ht.le, ← tsum_congr hint']
  refine (integral_tsum_of_summable_integral_norm (fun n => (hFint n).1) ?_).symm
  simp_rw [hnorm]
  exact (summable_nat_add_iff 1).2 hsum

end ChenDalang15

end
