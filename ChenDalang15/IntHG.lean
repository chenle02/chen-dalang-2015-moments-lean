module

public import ChenDalang15.H
public import ChenDalang15.ErfFacts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Paper `L2:IntHG`: `∫₀ᵗ (𝓗(r) + 1) G_{2ν}(t − r, x) dr`

Chen–Dalang (2015), Appendix, Lemma `L2:IntHG` (used for Corollary `C2:TP-Lebesgue`):
for `t > 0`,
`∫₀ᵗ (𝓗(r) + 1) G_{2ν}(t − r, x) dr
   = λ⁻² (e^{(λ⁴t − 2λ²|x|)/(4ν)} Erfc((|x| − λ²t)/(2√(νt))) − Erfc(|x|/(2√(νt))))`,
with `𝓗(r) + 1 = 2 e^{λ⁴r/(4ν)} Φ(λ²√(r/(2ν)))` (display `E2:H`).

The paper inverts a Laplace transform (Erdélyi tables). Mathlib has no Laplace inversion, so
the proof here is elementary. Write `c = λ²/(2√ν) > 0`, `α = |x|/(2√ν)`,
`f(r) = e^{c²r}(1 + erf(c√r)) = 𝓗(r) + 1` and `k(s) = e^{-α²/s}/√(πs)`, so that
`G_{2ν}(s, x) = k(s)/(2√ν)`.

1. (`integral_Ioi_fpt`) For `r > 0`, `c f(r) = ∫_{z>0} (e^{cz} − 1) (z/r) g_r(z) dz`, where
   `g_r(z) = e^{-z²/(4r)}/√(4πr)` (an explicit antiderivative and FTC on `(0, ∞)`).
2. (`integral_fpt_mul_k`) For `z > 0`, the time convolution of the first-passage density
   `(z/r) g_r(z)` with `k` is `∫₀ᵗ (z/r) g_r(z) k(t − r) dr = e^{-(z+2α)²/(4t)}/√(πt)`.
   Antiderivative in `r` (with `p = z√(t−r)/(2√t√r)`, `q = α√r/(√t√(t−r))`):
   `−(e^{-(z+2α)²/(4t)} erf(p − q) + e^{-(z−2α)²/(4t)} erf(p + q))/(2√(πt))`.
3. Fubini–Tonelli (nonnegative integrands) exchanges the `r`- and `z`-integrals.
4. (`integral_Ioi_gauss_tail`) `∫_{z>0} (e^{cz} − 1) e^{-(z+2α)²/(4t)}/√(πt) dz`
   `= e^{c²t−2cα} Erfc(α/√t − c√t) − Erfc(α/√t)`.

The paper states `t ≥ 0`; at `t = 0` the right side contains `|x|/√0`, a limit in the paper and
a junk value in Lean, so the Lean statements assume `t > 0`.
-/

set_option autoImplicit false

public section

namespace ChenDalang15

open Real MeasureTheory Set Filter Topology intervalIntegral

/-! ### `erf` facts -/

/-- `d/dx [C · erf (g x)] = 2/√π · (C · e^{-(g x)²}) · g'`. -/
theorem hasDerivAt_const_mul_erf {g : ℝ → ℝ} {g' x : ℝ} (C : ℝ) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => C * erf (g y))
      (2 / Real.sqrt π * (C * Real.exp (-(g x) ^ 2)) * g') x := by
  have := ((hasDerivAt_erf (g x)).comp x hg).const_mul C
  convert this using 1
  · rfl
  · ring

/-! ### FTC on an open interval with a nonnegative derivative -/

/-- FTC on `(a, b)` with one-sided limits at both ends and a nonnegative derivative; the
derivative is then automatically interval integrable. -/
theorem integral_eq_sub_of_tendsto_of_nonneg {f f' : ℝ → ℝ} {a b fa fb : ℝ} (hab : a < b)
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ Ioo a b, 0 ≤ f' x)
    (ha : Tendsto f (𝓝[>] a) (𝓝 fa)) (hb : Tendsto f (𝓝[<] b) (𝓝 fb)) :
    IntervalIntegrable f' volume a b ∧ ∫ y in a..b, f' y = fb - fa := by
  set F : ℝ → ℝ := Function.update (Function.update f a fa) b fb
  have Fderiv : ∀ x ∈ Ioo a b, HasDerivAt F (f' x) x := by
    refine fun x hx => (hderiv x hx).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with _ hy
    unfold F
    rw [Function.update_of_ne hy.2.ne, Function.update_of_ne hy.1.ne']
  have hcont : ContinuousOn F (Icc a b) := by
    rw [continuousOn_update_iff, continuousOn_update_iff, Icc_sdiff_right, Ico_sdiff_left]
    refine ⟨⟨fun z hz => (hderiv z hz).continuousAt.continuousWithinAt, ?_⟩, ?_⟩
    · exact fun _ => ha.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self)
    · rintro -
      refine (hb.congr' ?_).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
      filter_upwards [Ioo_mem_nhdsLT hab] with _ hz
        using (Function.update_of_ne hz.1.ne' _ _).symm
  have hint : IntervalIntegrable f' volume a b := by
    refine intervalIntegrable_deriv_of_nonneg (g := F) ?_ ?_ ?_
    · rwa [uIcc_of_le hab.le]
    · simpa [min_eq_left hab.le, max_eq_right hab.le] using Fderiv
    · simpa [min_eq_left hab.le, max_eq_right hab.le] using hpos
  exact ⟨hint, integral_eq_sub_of_hasDerivAt_of_tendsto hab hderiv hint ha hb⟩

/-- `(z + m)/(2√t) → ∞` as `z → ∞`. -/
theorem tendsto_add_div_atTop (m : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun z : ℝ => (z + m) / (2 * Real.sqrt t)) atTop atTop := by
  apply Tendsto.atTop_div_const (by positivity)
  exact tendsto_atTop_add_const_right atTop m tendsto_id

/-- `((w)/(2√t))² = w²/(4t)`. -/
theorem div_two_sqrt_sq (w : ℝ) {t : ℝ} (ht : 0 < t) :
    (w / (2 * Real.sqrt t)) ^ 2 = w ^ 2 / (4 * t) := by
  rw [div_pow, mul_pow, Real.sq_sqrt ht.le]
  ring

/-! ### Step 4: the Gaussian tail integral -/

/-- `∫_{z>0} (e^{cz} − 1) e^{-(z+2α)²/(4t)}/√(πt) dz = e^{c²t−2cα} Erfc(α/√t − c√t) − Erfc(α/√t)`,
with integrability. -/
theorem integral_Ioi_gauss_tail {c α t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    IntegrableOn (fun z => (Real.exp (c * z) - 1) *
        (Real.exp (-(z + 2 * α) ^ 2 / (4 * t)) / Real.sqrt (π * t))) (Ioi 0) ∧
    ∫ z in Ioi 0, (Real.exp (c * z) - 1) *
        (Real.exp (-(z + 2 * α) ^ 2 / (4 * t)) / Real.sqrt (π * t)) =
      Real.exp (c ^ 2 * t - 2 * c * α) * (1 - erf (α / Real.sqrt t - c * Real.sqrt t))
        - (1 - erf (α / Real.sqrt t)) := by
  set C := Real.exp (c ^ 2 * t - 2 * c * α) with hC
  set F : ℝ → ℝ := fun z => C * erf ((z + (2 * α - 2 * c * t)) / (2 * Real.sqrt t)) -
    1 * erf ((z + 2 * α) / (2 * Real.sqrt t)) with hF
  have hT : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hderiv : ∀ z ∈ Ici (0 : ℝ), HasDerivAt F ((Real.exp (c * z) - 1) *
      (Real.exp (-(z + 2 * α) ^ 2 / (4 * t)) / Real.sqrt (π * t))) z := by
    intro z _
    have h1 := hasDerivAt_const_mul_erf C
      (((hasDerivAt_id' z).add_const (2 * α - 2 * c * t)).div_const (2 * Real.sqrt t))
    have h2 := hasDerivAt_const_mul_erf 1 (((hasDerivAt_id' z).add_const (2 * α)).div_const
      (2 * Real.sqrt t))
    convert h1.sub h2 using 1
    have e1 : C * Real.exp (-((z + (2 * α - 2 * c * t)) / (2 * Real.sqrt t)) ^ 2) =
        Real.exp (c * z) * Real.exp (-(z + 2 * α) ^ 2 / (4 * t)) := by
      rw [hC, ← Real.exp_add, ← Real.exp_add, div_two_sqrt_sq _ ht]
      congr 1
      field_simp
      ring
    have e2 : 1 * Real.exp (-((z + 2 * α) / (2 * Real.sqrt t)) ^ 2) =
        Real.exp (-(z + 2 * α) ^ 2 / (4 * t)) := by
      rw [one_mul, div_two_sqrt_sq _ ht]
      congr 1
      ring
    rw [e1, e2, Real.sqrt_mul Real.pi_pos.le]
    have hP : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
    field_simp
  have hpos : ∀ z ∈ Ioi (0 : ℝ), 0 ≤ (Real.exp (c * z) - 1) *
      (Real.exp (-(z + 2 * α) ^ 2 / (4 * t)) / Real.sqrt (π * t)) := by
    intro z hz
    have : 1 ≤ Real.exp (c * z) := Real.one_le_exp (by have := hz.out; positivity)
    have : 0 ≤ Real.exp (c * z) - 1 := by linarith
    positivity
  have hlim : Tendsto F atTop (𝓝 (C * 1 - 1 * 1)) :=
    ((tendsto_erf_atTop.comp (tendsto_add_div_atTop _ ht)).const_mul C).sub
      ((tendsto_erf_atTop.comp (tendsto_add_div_atTop _ ht)).const_mul 1)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim, hF]
  have a1 : (0 + (2 * α - 2 * c * t)) / (2 * Real.sqrt t) =
      α / Real.sqrt t - c * Real.sqrt t := by
    have hT2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
    field_simp
    rw [hT2]
    ring
  have a2 : (0 + 2 * α) / (2 * Real.sqrt t) = α / Real.sqrt t := by
    rw [zero_add, mul_div_mul_left _ _ two_ne_zero]
  simp only
  rw [a1, a2]
  ring

/-- `e^{c²r} e^{-((z − 2cr)/(2√r))²} = e^{cz} e^{-z²/(4r)}` (completing the square). -/
theorem exp_complete_sq (c z : ℝ) {r : ℝ} (hr : 0 < r) :
    Real.exp (c ^ 2 * r) * Real.exp (-((z + -2 * c * r) / (2 * Real.sqrt r)) ^ 2) =
      Real.exp (c * z) * Real.exp (-z ^ 2 / (4 * r)) := by
  rw [← Real.exp_add, ← Real.exp_add, div_two_sqrt_sq _ hr]
  congr 1
  field_simp
  ring

/-! ### Step 1: `c f(r)` as an integral against the first-passage density -/

/-- For `r > 0`: `∫_{z>0} (e^{cz} − 1)(z/r) e^{-z²/(4r)}/√(4πr) dz = c e^{c²r}(1 + erf(c√r))`,
with integrability. -/
theorem integral_Ioi_fpt {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    IntegrableOn (fun z => (Real.exp (c * z) - 1) *
        (z / r * (Real.exp (-z ^ 2 / (4 * r)) / Real.sqrt (4 * π * r)))) (Ioi 0) ∧
    ∫ z in Ioi 0, (Real.exp (c * z) - 1) *
        (z / r * (Real.exp (-z ^ 2 / (4 * r)) / Real.sqrt (4 * π * r))) =
      c * (Real.exp (c ^ 2 * r) * (1 + erf (c * Real.sqrt r))) := by
  set C := c * Real.exp (c ^ 2 * r) with hC
  set g : ℝ → ℝ := fun z => (Real.exp (c * z) - 1) *
    (Real.exp (-z ^ 2 / (4 * r)) / Real.sqrt (4 * π * r)) with hg
  set F : ℝ → ℝ := fun z => -2 * g z + C * erf ((z + -2 * c * r) / (2 * Real.sqrt r)) with hF
  have hR : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hP : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have h4 : Real.sqrt (4 * π * r) = 2 * Real.sqrt π * Real.sqrt r := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hderiv : ∀ z ∈ Ici (0 : ℝ), HasDerivAt F ((Real.exp (c * z) - 1) *
      (z / r * (Real.exp (-z ^ 2 / (4 * r)) / Real.sqrt (4 * π * r)))) z := by
    intro z _
    have hE := (((hasDerivAt_pow 2 z).neg).div_const (4 * r)).exp
    have hX := ((hasDerivAt_id' z).const_mul c).exp
    have hgd := ((hX.sub_const 1).mul (hE.div_const (Real.sqrt (4 * π * r)))).const_mul (-2)
    have h1 := hasDerivAt_const_mul_erf C
      (((hasDerivAt_id' z).add_const (-2 * c * r)).div_const (2 * Real.sqrt r))
    convert hgd.add h1 using 1
    have e1 : C * Real.exp (-((z + -2 * c * r) / (2 * Real.sqrt r)) ^ 2) =
        c * (Real.exp (c * z) * Real.exp (-z ^ 2 / (4 * r))) := by
      rw [hC, mul_assoc, exp_complete_sq c z hr]
    rw [e1, h4]
    simp only [Pi.neg_apply, Nat.cast_ofNat, mul_one]
    norm_num
    field_simp
    ring
  have hpos : ∀ z ∈ Ioi (0 : ℝ), 0 ≤ (Real.exp (c * z) - 1) *
      (z / r * (Real.exp (-z ^ 2 / (4 * r)) / Real.sqrt (4 * π * r))) := by
    intro z hz
    have hz0 : 0 < z := hz
    have : 1 ≤ Real.exp (c * z) := Real.one_le_exp (by positivity)
    have : 0 ≤ Real.exp (c * z) - 1 := by linarith
    positivity
  have hgexp : ∀ z, g z = (Real.exp (c ^ 2 * r) *
      Real.exp (-((z + -2 * c * r) / (2 * Real.sqrt r)) ^ 2) -
      Real.exp (-(z / (2 * Real.sqrt r)) ^ 2)) / Real.sqrt (4 * π * r) := by
    intro z
    rw [exp_complete_sq c z hr, div_two_sqrt_sq _ hr, hg]
    ring_nf
  have hexp0 : ∀ m : ℝ, Tendsto (fun z : ℝ => Real.exp (-((z + m) / (2 * Real.sqrt r)) ^ 2))
      atTop (𝓝 0) := fun m =>
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_pow_atTop two_ne_zero).comp (tendsto_add_div_atTop m hr))
  have hglim : Tendsto g atTop (𝓝 0) := by
    have h := ((((hexp0 (-2 * c * r)).const_mul (Real.exp (c ^ 2 * r))).sub
      (hexp0 0)).div_const (Real.sqrt (4 * π * r)))
    simp only [mul_zero, sub_zero, zero_div, add_zero] at h
    refine h.congr fun z => ?_
    rw [hgexp z]
  have hlim : Tendsto F atTop (𝓝 (-2 * 0 + C * 1)) :=
    (hglim.const_mul (-2)).add
      ((tendsto_erf_atTop.comp (tendsto_add_div_atTop _ hr)).const_mul C)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim, hF]
  have a1 : (0 + -2 * c * r) / (2 * Real.sqrt r) = -(c * Real.sqrt r) := by
    have hR2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
    field_simp
    rw [hR2]
    ring
  simp only [hg, a1, erf_neg, mul_zero, Real.exp_zero, sub_self, zero_mul]
  rw [hC]
  ring

/-! ### Step 2: time convolution of the first-passage density with `k` -/

theorem hasDerivAt_pfun {z t r : ℝ} (ht : 0 < t) (hr0 : 0 < r) (hrt : r < t) :
    HasDerivAt (fun r => z * Real.sqrt (t - r) / (2 * Real.sqrt t * Real.sqrt r))
      (-(z * Real.sqrt t) / (4 * r * Real.sqrt r * Real.sqrt (t - r))) r := by
  have hU := ((hasDerivAt_id' r).const_sub t).sqrt (by linarith : t - r ≠ 0)
  have hS := Real.hasDerivAt_sqrt hr0.ne'
  have hT : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hSp : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hUp : 0 < Real.sqrt (t - r) := Real.sqrt_pos.2 (by linarith)
  have h := (hU.const_mul z).div (hS.const_mul (2 * Real.sqrt t)) (by positivity)
  convert h using 1
  have hS2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
  have hU2 : Real.sqrt (t - r) ^ 2 = t - r := Real.sq_sqrt (by linarith)
  have hT2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  generalize Real.sqrt r = S at *
  generalize Real.sqrt (t - r) = U at *
  generalize Real.sqrt t = T at *
  subst hS2 hT2
  field_simp
  linear_combination 4 * z * hU2

theorem hasDerivAt_qfun {α t r : ℝ} (ht : 0 < t) (hr0 : 0 < r) (hrt : r < t) :
    HasDerivAt (fun r => α * Real.sqrt r / (Real.sqrt t * Real.sqrt (t - r)))
      (α * Real.sqrt t / (2 * Real.sqrt r * (t - r) * Real.sqrt (t - r))) r := by
  have hU := ((hasDerivAt_id' r).const_sub t).sqrt (by linarith : t - r ≠ 0)
  have hS := Real.hasDerivAt_sqrt hr0.ne'
  have hT : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hSp : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hUp : 0 < Real.sqrt (t - r) := Real.sqrt_pos.2 (by linarith)
  have h := (hS.const_mul α).div (hU.const_mul (Real.sqrt t)) (by positivity)
  convert h using 1
  have hS2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
  have hU2 : Real.sqrt (t - r) ^ 2 = t - r := Real.sq_sqrt (by linarith)
  have hT2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  generalize Real.sqrt r = S at *
  generalize Real.sqrt (t - r) = U at *
  generalize Real.sqrt t = T at *
  subst hS2 hT2
  have hU0 : T ^ 2 - S ^ 2 ≠ 0 := by rw [← hU2]; positivity
  field_simp
  linear_combination α * S ^ 2 * hU2

/-- Exponent bookkeeping for step 2: with `p = z√(t−r)/(2√t√r)` and `q = α√r/(√t√(t−r))`,
`(z ± 2α)²/(4t) + (p ∓ q)² = z²/(4r) + α²/(t−r)`. -/
theorem exp_pq {z α t r : ℝ} (ht : 0 < t) (hr0 : 0 < r) (hrt : r < t) (s : ℝ)
    (hs : s = 1 ∨ s = -1) :
    Real.exp (-(z + s * 2 * α) ^ 2 / (4 * t)) *
        Real.exp (-(z * Real.sqrt (t - r) / (2 * Real.sqrt t * Real.sqrt r) -
          s * (α * Real.sqrt r / (Real.sqrt t * Real.sqrt (t - r)))) ^ 2) =
      Real.exp (-z ^ 2 / (4 * r)) * Real.exp (-α ^ 2 / (t - r)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hS2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
  have hU2 : Real.sqrt (t - r) ^ 2 = t - r := Real.sq_sqrt (by linarith)
  have hT2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hT : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hSp : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hUp : 0 < Real.sqrt (t - r) := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  generalize Real.sqrt r = S at *
  generalize Real.sqrt (t - r) = U at *
  generalize Real.sqrt t = T at *
  subst hS2 hT2
  have hU0 : T ^ 2 - S ^ 2 ≠ 0 := by rw [← hU2]; positivity
  field_simp
  rw [hU2]
  linear_combination (-16 * (T ^ 2 - S ^ 2) * T ^ 2 * α ^ 2 * S ^ 2) * hs2

theorem tendsto_sqrt_nhdsGT_zero : Tendsto Real.sqrt (𝓝[>] 0) (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨(Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero).mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun _ hr => Real.sqrt_pos.2 hr⟩

theorem tendsto_inv_sqrt_nhdsGT_zero :
    Tendsto (fun r => (Real.sqrt r)⁻¹) (𝓝[>] 0) atTop :=
  tendsto_inv_nhdsGT_zero.comp tendsto_sqrt_nhdsGT_zero

theorem tendsto_sub_nhdsLT {t : ℝ} : Tendsto (fun r => t - r) (𝓝[<] t) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun r => t - r) (𝓝 t) (𝓝 (t - t)) := tendsto_const_nhds.sub tendsto_id
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun r hr => sub_pos.2 hr

/-- **Step 2.** For `z > 0`, `α ≥ 0`, `t > 0`:
`∫₀ᵗ (z/r) e^{-z²/(4r)}/√(4πr) · e^{-α²/(t−r)}/√(π(t−r)) dr = e^{-(z+2α)²/(4t)}/√(πt)`,
with interval integrability. -/
theorem integral_fpt_mul_k {z α t : ℝ} (hz : 0 < z) (hα : 0 ≤ α) (ht : 0 < t) :
    IntervalIntegrable (fun r => z / r * (Real.exp (-z ^ 2 / (4 * r)) / Real.sqrt (4 * π * r)) *
        (Real.exp (-α ^ 2 / (t - r)) / Real.sqrt (π * (t - r)))) volume 0 t ∧
    ∫ r in (0 : ℝ)..t, z / r * (Real.exp (-z ^ 2 / (4 * r)) / Real.sqrt (4 * π * r)) *
        (Real.exp (-α ^ 2 / (t - r)) / Real.sqrt (π * (t - r))) =
      Real.exp (-(z + 2 * α) ^ 2 / (4 * t)) / Real.sqrt (π * t) := by
  set P : ℝ → ℝ := fun r => z * Real.sqrt (t - r) / (2 * Real.sqrt t * Real.sqrt r) with hP
  set Q : ℝ → ℝ := fun r => α * Real.sqrt r / (Real.sqrt t * Real.sqrt (t - r)) with hQ
  set A1 := -Real.exp (-(z + 1 * 2 * α) ^ 2 / (4 * t)) / (2 * Real.sqrt (π * t)) with hA1
  set A2 := -Real.exp (-(z + -1 * 2 * α) ^ 2 / (4 * t)) / (2 * Real.sqrt (π * t)) with hA2
  set F : ℝ → ℝ := fun r => A1 * erf (P r - 1 * Q r) + A2 * erf (P r - -1 * Q r) with hF
  have hT : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hPi : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hderiv : ∀ r ∈ Ioo (0 : ℝ) t, HasDerivAt F (z / r *
      (Real.exp (-z ^ 2 / (4 * r)) / Real.sqrt (4 * π * r)) *
        (Real.exp (-α ^ 2 / (t - r)) / Real.sqrt (π * (t - r)))) r := by
    rintro r ⟨hr0, hrt⟩
    have hp := hasDerivAt_pfun (z := z) ht hr0 hrt
    have hq := hasDerivAt_qfun (α := α) ht hr0 hrt
    have h := (hasDerivAt_const_mul_erf A1 (hp.sub (hq.const_mul 1))).add
      (hasDerivAt_const_mul_erf A2 (hp.sub (hq.const_mul (-1))))
    convert h using 1
    have k1 : A1 * Real.exp (-(P r - 1 * Q r) ^ 2) =
        -(Real.exp (-z ^ 2 / (4 * r)) * Real.exp (-α ^ 2 / (t - r))) /
          (2 * Real.sqrt (π * t)) := by
      rw [hA1, ← exp_pq ht hr0 hrt 1 (Or.inl rfl)]
      ring
    have k2 : A2 * Real.exp (-(P r - -1 * Q r) ^ 2) =
        -(Real.exp (-z ^ 2 / (4 * r)) * Real.exp (-α ^ 2 / (t - r))) /
          (2 * Real.sqrt (π * t)) := by
      rw [hA2, ← exp_pq ht hr0 hrt (-1) (Or.inr rfl)]
      ring
    simp only [hP, hQ] at k1 k2
    simp only [Pi.sub_apply]
    rw [k1, k2]
    have hSp : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
    have hUp : 0 < Real.sqrt (t - r) := Real.sqrt_pos.2 (by linarith)
    have hr' : 0 < t - r := by linarith
    rw [show (4 : ℝ) * π * r = 2 ^ 2 * π * r by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num), Real.sqrt_mul Real.pi_pos.le, Real.sqrt_mul Real.pi_pos.le]
    generalize Real.exp (-z ^ 2 / (4 * r)) = E1
    generalize Real.exp (-α ^ 2 / (t - r)) = E2
    field_simp
    ring
  have hpos : ∀ r ∈ Ioo (0 : ℝ) t, 0 ≤ z / r *
      (Real.exp (-z ^ 2 / (4 * r)) / Real.sqrt (4 * π * r)) *
        (Real.exp (-α ^ 2 / (t - r)) / Real.sqrt (π * (t - r))) := by
    rintro r ⟨hr0, -⟩
    positivity
  -- Limits at the endpoints.
  have hnum : ∀ (C : ℝ) (g : ℝ → ℝ), Continuous g → ∀ r₀ : ℝ,
      Tendsto (fun r => C * Real.sqrt (g r)) (𝓝 r₀) (𝓝 (C * Real.sqrt (g r₀))) := by
    intro C g hg r₀
    exact ((hg.sqrt.const_mul C).tendsto r₀)
  have hPt : Tendsto P (𝓝[<] t) (𝓝 0) := by
    have h := (hnum z (fun r => t - r) (by fun_prop) t).div
      (((by fun_prop : Continuous fun r => 2 * Real.sqrt t * Real.sqrt r)).tendsto t)
      (by positivity)
    simp only [sub_self, Real.sqrt_zero, mul_zero, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hQ0 : Tendsto Q (𝓝[>] 0) (𝓝 0) := by
    have h := (hnum α id continuous_id 0).div
      (((by fun_prop : Continuous fun r => Real.sqrt t * Real.sqrt (t - r))).tendsto 0)
      (by simp only [sub_zero]; positivity)
    simp only [id, Real.sqrt_zero, mul_zero, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hP0 : Tendsto P (𝓝[>] 0) atTop := by
    have h1 : Tendsto (fun r => z * Real.sqrt (t - r) / (2 * Real.sqrt t)) (𝓝[>] 0)
        (𝓝 (z * Real.sqrt (t - 0) / (2 * Real.sqrt t))) :=
      ((by fun_prop : Continuous fun r => z * Real.sqrt (t - r) / (2 * Real.sqrt t)).tendsto
        0).mono_left nhdsWithin_le_nhds
    rw [sub_zero] at h1
    refine (h1.pos_mul_atTop (by positivity) tendsto_inv_sqrt_nhdsGT_zero).congr fun r => ?_
    simp only [hP, div_eq_mul_inv, mul_inv]
    ring
  have hlim0 : Tendsto F (𝓝[>] 0) (𝓝 (A1 * 1 + A2 * 1)) := by
    have hm : Tendsto (fun r => P r - 1 * Q r) (𝓝[>] 0) atTop := by
      refine (hP0.atTop_add (hQ0.const_mul (-1))).congr fun r => ?_
      ring
    have hp' : Tendsto (fun r => P r - -1 * Q r) (𝓝[>] 0) atTop := by
      refine (hP0.atTop_add (hQ0.const_mul 1)).congr fun r => ?_
      ring
    exact ((tendsto_erf_atTop.comp hm).const_mul A1).add
      ((tendsto_erf_atTop.comp hp').const_mul A2)
  have hlimt : Tendsto F (𝓝[<] t) (𝓝 (A1 * (-1) + A2 * 1)) := by
    rcases hα.lt_or_eq with hα' | hα'
    · have hQt : Tendsto Q (𝓝[<] t) atTop := by
        have h1 : Tendsto (fun r => α * Real.sqrt r / Real.sqrt t) (𝓝[<] t)
            (𝓝 (α * Real.sqrt t / Real.sqrt t)) :=
          ((by fun_prop : Continuous fun r => α * Real.sqrt r / Real.sqrt t).tendsto
            t).mono_left nhdsWithin_le_nhds
        refine (h1.pos_mul_atTop (by positivity)
          (tendsto_inv_nhdsGT_zero.comp (tendsto_sqrt_nhdsGT_zero.comp tendsto_sub_nhdsLT))).congr
          fun r => ?_
        simp only [hQ, Function.comp, div_eq_mul_inv, mul_inv]
        ring
      have hm : Tendsto (fun r => P r - 1 * Q r) (𝓝[<] t) atBot := by
        refine (hPt.add_atBot (tendsto_neg_atTop_atBot.comp hQt)).congr fun r => ?_
        simp only [Function.comp]
        ring
      have hp' : Tendsto (fun r => P r - -1 * Q r) (𝓝[<] t) atTop := by
        refine (hPt.add_atTop hQt).congr fun r => ?_
        ring
      exact ((tendsto_erf_atBot.comp hm).const_mul A1).add
        ((tendsto_erf_atTop.comp hp').const_mul A2)
    · subst hα'
      have hA : A1 = A2 := by rw [hA1, hA2]; ring_nf
      have hF0 : ∀ r, F r = (A1 + A2) * erf (P r) := by
        intro r; simp only [hF, hQ]; ring_nf
      have h := ((continuous_erf.tendsto 0).comp hPt).const_mul (A1 + A2)
      rw [erf_zero] at h
      convert h.congr (fun r => (hF0 r).symm) using 2
      rw [hA]; ring
  obtain ⟨hint, hval⟩ := integral_eq_sub_of_tendsto_of_nonneg ht hderiv hpos hlim0 hlimt
  refine ⟨hint, ?_⟩
  rw [hval, hA1]
  ring_nf

/-! ### Step 3: Fubini–Tonelli and the normalized identity -/

/-- The normalized form of `L2:IntHG`: for `c > 0`, `α ≥ 0`, `t > 0`,
`∫₀ᵗ e^{c²r}(1 + erf(c√r)) e^{-α²/(t−r)}/√(π(t−r)) dr
  = c⁻¹ (e^{c²t−2cα} Erfc(α/√t − c√t) − Erfc(α/√t))`. -/
theorem integral_f_mul_k {c α t : ℝ} (hc : 0 < c) (hα : 0 ≤ α) (ht : 0 < t) :
    ∫ r in (0 : ℝ)..t, Real.exp (c ^ 2 * r) * (1 + erf (c * Real.sqrt r)) *
        (Real.exp (-α ^ 2 / (t - r)) / Real.sqrt (π * (t - r))) =
      1 / c * (Real.exp (c ^ 2 * t - 2 * c * α) * (1 - erf (α / Real.sqrt t - c * Real.sqrt t))
        - (1 - erf (α / Real.sqrt t))) := by
  set H : ℝ → ℝ → ℝ := fun z r => (Real.exp (c * z) - 1) *
    (z / r * (Real.exp (-z ^ 2 / (4 * r)) / Real.sqrt (4 * π * r))) *
      (Real.exp (-α ^ 2 / (t - r)) / Real.sqrt (π * (t - r))) with hH
  have hHz : ∀ z r, H z r = (Real.exp (c * z) - 1) *
      (z / r * (Real.exp (-z ^ 2 / (4 * r)) / Real.sqrt (4 * π * r)) *
        (Real.exp (-α ^ 2 / (t - r)) / Real.sqrt (π * (t - r)))) := by
    intro z r; simp only [hH]; ring
  -- Step a/b: insert the representation of `f`.
  have hstep1 : ∫ r in (0 : ℝ)..t, Real.exp (c ^ 2 * r) * (1 + erf (c * Real.sqrt r)) *
        (Real.exp (-α ^ 2 / (t - r)) / Real.sqrt (π * (t - r))) =
      1 / c * ∫ r in Ioc (0 : ℝ) t, ∫ z in Ioi (0 : ℝ), H z r := by
    rw [intervalIntegral.integral_of_le ht.le, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have h1 := (integral_Ioi_fpt hc hr.1).2
    simp only [hH]
    rw [MeasureTheory.integral_mul_const, h1]
    field_simp
  -- Step c: integrability on the product and the swap.
  have hmeas : Measurable (Function.uncurry H) := by
    simp only [hH]
    fun_prop
  have hinner : ∀ z ∈ Ioi (0 : ℝ), IntegrableOn (H z) (Ioc 0 t) ∧
      ∫ r in Ioc (0 : ℝ) t, H z r = (Real.exp (c * z) - 1) *
        (Real.exp (-(z + 2 * α) ^ 2 / (4 * t)) / Real.sqrt (π * t)) := by
    intro z hz
    obtain ⟨hi, hv⟩ := integral_fpt_mul_k (α := α) hz hα ht
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le] at hi
    rw [intervalIntegral.integral_of_le ht.le] at hv
    have hfun : H z = fun r => (Real.exp (c * z) - 1) *
        (z / r * (Real.exp (-z ^ 2 / (4 * r)) / Real.sqrt (4 * π * r)) *
          (Real.exp (-α ^ 2 / (t - r)) / Real.sqrt (π * (t - r)))) := funext (hHz z)
    rw [hfun, MeasureTheory.integral_const_mul, hv]
    exact ⟨hi.const_mul _, rfl⟩
  have hHnn : ∀ z ∈ Ioi (0 : ℝ), ∀ r ∈ Ioc (0 : ℝ) t, 0 ≤ H z r := by
    intro z hz r hr
    have hz0 : 0 < z := hz
    have hr0 : 0 < r := hr.1
    have : 1 ≤ Real.exp (c * z) := Real.one_le_exp (by positivity)
    have : 0 ≤ Real.exp (c * z) - 1 := by linarith
    simp only [hH]
    positivity
  have hint : Integrable (Function.uncurry H)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) t))) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun z hz => (hinner z hz).1
    · refine (integral_Ioi_gauss_tail (α := α) hc ht).1.congr_fun_ae ?_
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun z hz => ?_
      rw [← (hinner z hz).2]
      refine (setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_).symm
      simp only [Function.uncurry_apply_pair]
      exact Real.norm_of_nonneg (hHnn z hz r hr)
  have hswap := integral_integral_swap hint
  rw [hstep1, ← hswap]
  have hcongr : ∫ z in Ioi (0 : ℝ), ∫ r in Ioc (0 : ℝ) t, H z r =
      ∫ z in Ioi (0 : ℝ), (Real.exp (c * z) - 1) *
        (Real.exp (-(z + 2 * α) ^ 2 / (4 * t)) / Real.sqrt (π * t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun z hz => (hinner z hz).2
  rw [hcongr, (integral_Ioi_gauss_tail (α := α) hc ht).2]

/-! ### The paper's statement -/

/-- Paper L2:IntHG, with `𝓗(r) + 1 = 2 e^{λ⁴r/(4ν)} Φ(λ²√(r/(2ν)))` (display E2:H). -/
theorem integral_H_add_one_mul_G {ν lam t : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) (ht : 0 < t) (x : ℝ) :
    ∫ r in (0 : ℝ)..t,
        (2 * Real.exp (lam ^ 4 * r / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))) *
          G (2 * ν) (t - r) x =
      1 / lam ^ 2 * (Real.exp ((lam ^ 4 * t - 2 * lam ^ 2 * |x|) / (4 * ν)) *
          erfc ((|x| - lam ^ 2 * t) / (2 * Real.sqrt (ν * t)))
        - erfc (|x| / (2 * Real.sqrt (ν * t)))) := by
  have hN : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hN2 : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt hν.le
  have hl2 : 0 < lam ^ 2 := by positivity
  set c := lam ^ 2 / (2 * Real.sqrt ν) with hc
  set α := |x| / (2 * Real.sqrt ν) with hα
  have hc0 : 0 < c := by positivity
  have hα0 : 0 ≤ α := by positivity
  have hpt : ∀ r : ℝ,
      (2 * Real.exp (lam ^ 4 * r / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))) *
          G (2 * ν) (t - r) x =
        1 / (2 * Real.sqrt ν) * (Real.exp (c ^ 2 * r) * (1 + erf (c * Real.sqrt r)) *
          (Real.exp (-α ^ 2 / (t - r)) / Real.sqrt (π * (t - r)))) := by
    intro r
    have e1 : lam ^ 2 * Real.sqrt (r / (2 * ν)) / Real.sqrt 2 = c * Real.sqrt r := by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by norm_num), hc]
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h2p : 0 < Real.sqrt 2 := by positivity
      field_simp
      rw [h2]
    have e2 : lam ^ 4 * r / (4 * ν) = c ^ 2 * r := by
      rw [hc, div_pow, mul_pow, hN2]
      ring
    have e3 : G (2 * ν) (t - r) x =
        1 / (2 * Real.sqrt ν) * (Real.exp (-α ^ 2 / (t - r)) / Real.sqrt (π * (t - r))) := by
      have ex : -x ^ 2 / (2 * (2 * ν) * (t - r)) = -α ^ 2 / (t - r) := by
        rw [hα, div_pow, sq_abs, mul_pow, hN2]
        simp only [neg_div, div_div]
        congr 2
        ring
      rw [G, ex, show 2 * π * (2 * ν) * (t - r) = (2 * Real.sqrt ν) ^ 2 * (π * (t - r)) by
          rw [mul_pow, hN2]; ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      ring
    rw [Phi_eq_erf, e1, e2, e3]
    ring
  rw [intervalIntegral.integral_congr (fun r _ => hpt r), intervalIntegral.integral_const_mul,
    integral_f_mul_k hc0 hα0 ht]
  have hT : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hT2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have a1 : (lam ^ 4 * t - 2 * lam ^ 2 * |x|) / (4 * ν) = c ^ 2 * t - 2 * c * α := by
    rw [hc, hα]
    generalize Real.sqrt ν = N at *
    subst hN2
    field_simp
    ring
  have a2 : (|x| - lam ^ 2 * t) / (2 * Real.sqrt (ν * t)) =
      α / Real.sqrt t - c * Real.sqrt t := by
    rw [Real.sqrt_mul hν.le, hc, hα]
    field_simp
    rw [hT2]
  have a3 : |x| / (2 * Real.sqrt (ν * t)) = α / Real.sqrt t := by
    rw [Real.sqrt_mul hν.le, hα]
    field_simp
  rw [a1, a2, a3, erfc, erfc, hc]
  field_simp

/-- The same identity stated with the paper's `𝓗(r) = (1 ⋆ 𝓚)(r, x)` (via `one_conv_K`). -/
theorem integral_one_conv_K_add_one_mul_G {ν lam t : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) (ht : 0 < t)
    (x : ℝ) :
    ∫ r in (0 : ℝ)..t, (stConv (fun _ _ => (1 : ℝ)) (K ν lam) r x + 1) * G (2 * ν) (t - r) x =
      1 / lam ^ 2 * (Real.exp ((lam ^ 4 * t - 2 * lam ^ 2 * |x|) / (4 * ν)) *
          erfc ((|x| - lam ^ 2 * t) / (2 * Real.sqrt (ν * t)))
        - erfc (|x| / (2 * Real.sqrt (ν * t)))) := by
  rw [← integral_H_add_one_mul_G hν hlam ht x]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le ht.le] at hr
  rw [one_conv_K hν hr.1 x]
  ring

end ChenDalang15

end
