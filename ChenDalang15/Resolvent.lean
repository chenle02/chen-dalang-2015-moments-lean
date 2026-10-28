module

public import ChenDalang15.Kernel
public import ChenDalang15.Beta

/-!
# The resolvent kernels `𝓛ₙ` of Chen–Dalang (2015), Proposition `P2:K`

Notation of the paper (`E:Def-Ln`): for `ν > 0` and `λ` (written `lam`, since `λ` is a Lean
keyword),
`𝓛₀(t,x) = λ² G_ν(t,x)²` and `𝓛ₙ = 𝓛₀ ⋆ ⋯ ⋆ 𝓛₀` (`n + 1` factors), where `⋆` is the
space-time convolution `(f ⋆ g)(t,x) = ∫₀ᵗ ∫_ℝ f(s,y) g(t-s, x-y) dy ds`.
The paper's proof uses the left nesting `𝓛ₙ₊₁ = 𝓛ₙ ⋆ 𝓛₀`; that is the definition here.

This file proves the closed form `E:KS-LB`:
`𝓛ₙ(t,x) = G_{ν/2}(t,x) (b√π)^{n+1} t^{(n-1)/2} / Γ((n+1)/2)`, `b = λ²/√(4πν)`.
-/

set_option autoImplicit false

@[expose] public section

namespace ChenDalang15

open Real MeasureTheory intervalIntegral

-- `stConv` and `L` are defined in `ChenDalang15.Defs` (shared with the Palomar Challenge).

/-- The constant `b = λ²/√(4πν)` of `P2:K`. -/
noncomputable def bConst (ν lam : ℝ) : ℝ := lam ^ 2 / Real.sqrt (4 * π * ν)

/-- The coefficient `(b√π)^{n+1} / Γ((n+1)/2)` in the closed form of `𝓛ₙ`. -/
noncomputable def lCoeff (ν lam : ℝ) (n : ℕ) : ℝ :=
  (bConst ν lam * Real.sqrt π) ^ (n + 1) / Real.Gamma (((n : ℝ) + 1) / 2)

/-! ### Kernel facts at general `ν` -/

/-- At time zero the kernel takes Lean's junk value `0` (the paper's convention `G ≡ 0`, `t ≤ 0`). -/
theorem G_time_zero (ν x : ℝ) : G ν 0 x = 0 := by
  simp [G_eq_heatKernel, RoughHeatKernel.heatKernel]

/-- `G_ν(t,x)² = G_{ν/2}(t,x) · (4πν)^{-1/2} · t^{-1/2}` (paper `L2:GG`, first part), from
`RoughHeatKernel.heatKernel_mul_sq_eq` via `G_eq_heatKernel`. -/
theorem G_sq {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : ℝ) :
    G ν t x ^ 2 = G (ν / 2) t x * (1 / Real.sqrt (4 * π * ν)) * t ^ (-(1 / 2 : ℝ)) := by
  simp only [G_eq_heatKernel]
  exact RoughHeatKernel.heatKernel_mul_sq_eq hν ht x

/-- The semigroup property at general `ν`: `∫ G_ν(t-s, x-y) G_ν(s, y) dy = G_ν(t, x)`, from
`RoughHeatKernel.integral_heatKernel_mul_sub_mul` via `G_eq_heatKernel`. -/
theorem integral_G_mul_G {ν s t : ℝ} (hν : 0 < ν) (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ∫ y, G ν (t - s) (x - y) * G ν s y = G ν t x := by
  simp only [G_eq_heatKernel]
  exact RoughHeatKernel.integral_heatKernel_mul_sub_mul hν hs hst x

/-! ### The closed form of `𝓛ₙ` (`E:KS-LB`) -/

/-- Every `𝓛ₙ` vanishes at time zero (junk value of `G`, empty time integral). -/
theorem L_time_zero (ν lam : ℝ) (n : ℕ) (x : ℝ) : L ν lam n 0 x = 0 := by
  cases n with
  | zero => simp [L, G_time_zero]
  | succ n => simp [L, stConv]

/-- `𝓛₀(t,x) = G_{ν/2}(t,x) · b · t^{-1/2}` with `b = λ²/√(4πν)`. -/
theorem L_zero_eq {ν lam t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : ℝ) :
    L ν lam 0 t x = G (ν / 2) t x * bConst ν lam * t ^ (-(1 / 2 : ℝ)) := by
  simp only [L, bConst]
  rw [G_sq hν ht x]
  ring

/-- Almost every time differs from a given one. -/
theorem ae_ne_real (t : ℝ) : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
  rw [ae_iff]
  simp

/-- **Chen–Dalang (2015), Proposition `P2:K`, display `E:KS-LB`.** For `ν > 0` and `t > 0`,
`𝓛ₙ(t,x) = G_{ν/2}(t,x) · (b√π)^{n+1} / Γ((n+1)/2) · t^{(n-1)/2}`. -/
theorem L_eq {ν lam : ℝ} (hν : 0 < ν) (n : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    L ν lam n t x = G (ν / 2) t x * lCoeff ν lam n * t ^ (((n : ℝ) - 1) / 2) := by
  have hν2 : 0 < ν / 2 := half_pos hν
  induction n generalizing t x with
  | zero =>
    have hpi : Real.sqrt π ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
    rw [L_zero_eq hν ht x, lCoeff, show (((0 : ℕ) : ℝ) + 1) / 2 = 1 / 2 by norm_num,
      Real.Gamma_one_half_eq, show (((0 : ℕ) : ℝ) - 1) / 2 = -(1 / 2) by norm_num, zero_add,
      pow_one, mul_div_assoc, div_self hpi, mul_one]
  | succ n ih =>
    -- Inner integral at each `s ∈ (0, t)`.
    have hinner : ∀ s, 0 < s → s < t →
        ∫ y, L ν lam n s y * L ν lam 0 (t - s) (x - y) =
          G (ν / 2) t x * (lCoeff ν lam n * bConst ν lam) *
            (s ^ (((n : ℝ) + 1) / 2 - 1) * (t - s) ^ ((1 / 2 : ℝ) - 1)) := by
      intro s hs hst
      have hts : 0 < t - s := sub_pos.mpr hst
      have hfun : (fun y => L ν lam n s y * L ν lam 0 (t - s) (x - y)) = fun y =>
          (lCoeff ν lam n * s ^ (((n : ℝ) - 1) / 2) * bConst ν lam * (t - s) ^ (-(1 / 2 : ℝ))) *
            (G (ν / 2) (t - s) (x - y) * G (ν / 2) s y) := by
        funext y
        rw [ih hs y, L_zero_eq hν hts (x - y)]
        ring
      rw [hfun, MeasureTheory.integral_const_mul, integral_G_mul_G hν2 hs hst x]
      have e1 : ((n : ℝ) + 1) / 2 - 1 = ((n : ℝ) - 1) / 2 := by ring
      have e2 : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
      rw [e1, e2]
      ring
    have hcongr : ∫ s in (0 : ℝ)..t, ∫ y, L ν lam n s y * L ν lam 0 (t - s) (x - y) =
        ∫ s in (0 : ℝ)..t, G (ν / 2) t x * (lCoeff ν lam n * bConst ν lam) *
          (s ^ (((n : ℝ) + 1) / 2 - 1) * (t - s) ^ ((1 / 2 : ℝ) - 1)) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [ae_ne_real t] with s hst hs
      rw [Set.uIoc_of_le ht.le] at hs
      exact hinner s hs.1 (lt_of_le_of_ne hs.2 hst)
    have ha : 0 < ((n : ℝ) + 1) / 2 := by positivity
    have hGa : Real.Gamma (((n : ℝ) + 1) / 2) ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    rw [L.eq_2, stConv, hcongr, intervalIntegral.integral_const_mul,
      integral_rpow_mul_sub_rpow ha (by norm_num : (0 : ℝ) < 1 / 2) ht, Real.Gamma_one_half_eq]
    simp only [lCoeff]
    have e3 : ((n : ℝ) + 1) / 2 + 1 / 2 - 1 = (((n + 1 : ℕ) : ℝ) - 1) / 2 := by push_cast; ring
    have e4 : ((n : ℝ) + 1) / 2 + 1 / 2 = (((n + 1 : ℕ) : ℝ) + 1) / 2 := by push_cast; ring
    rw [e3, e4]
    field_simp
    ring

end ChenDalang15

end
