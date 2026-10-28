module

public import ChenDalang15.TwoPoint
public import ChenDalang15.IntHG
public import ChenDalang15.IntGG
public import ChenDalang15.Resolvent

/-!
# Corollary `C2:TP-Lebesgue` (constant initial data), deterministic part

Chen–Dalang (2015), Corollary `C2:TP-Lebesgue`: with `J₀ ≡ 1` (Lebesgue initial data),
the right sides of `E2:SecMom` and `E2:TP` become

* `E2:SecMom-Lebesgue`: `J₀² + J₀² ⋆ 𝓚 + ϑ²𝓗 = 1 + (1 + ϑ²)𝓗(t)` (`C2_SecMom_Lebesgue`);
* for `τ ≥ t > 0`, with `t̄ = (t + τ)/2` and `w = x − y`,
  `1 + 𝓘(t,x,τ,y) = 1 + λ²(1 + ϑ²) ∫₀ᵗ (𝓗(r) + 1) G_{2ν}(t̄ − r, w) dr`
  (`C2_TP_Lebesgue_integral`; the paper's displayed intermediate step, which is correct).

**Paper erratum (`τ > t`).** The paper evaluates the last integral "by Lemma `L2:IntHG`", but
that lemma integrates over `r ∈ [0, t̄]`, not `[0, t]`; the ranges agree only when `τ = t`.
For `τ > t` the integrand is strictly positive on `(t, t̄)`, so the printed closed form
`E2:TP-Lebesgue` strictly overestimates `1 + 𝓘` (`C2_TP_Lebesgue_lt`) and the statement
"for all `τ ≥ t > 0`" is false (`C2_TP_Lebesgue_false`). Example: `ν = λ = t = 1`,
`τ = 2`, `ϑ = 1/2`, `|x − y| = 0.3`: true value `1.564823…`, printed formula `2.288116…`.
The printed formula is correct at `τ = t` (`C2_TP_Lebesgue_diag`).

Junk values: `stConv` at time `0` is an empty interval integral `= 0`, which agrees with
`𝓗(0) = 2Φ(0) − 1 = 0`; `G` at nonpositive time is `0`, and at `r = t` the factor
`G_ν(t − r, ·)` is `0`, which only affects a null set of `r`. Neither matters for the
statements, which assume `t > 0`.
-/

set_option autoImplicit false

@[expose] public section

namespace ChenDalang15

namespace TPLebesgue

open Real MeasureTheory Set intervalIntegral

/-- `𝓗(r)` in closed form (`E2:H`) for `r ≥ 0`. -/
theorem Hfun_eq {ν lam r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    Hfun ν lam r =
      2 * Real.exp (lam ^ 4 * r / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (r / (2 * ν))) - 1 :=
  one_conv_K hν hr 0

/-- `(1 ⋆ 𝓚)(r, z) = 𝓗(r)` at every point `z` (for `r ≥ 0`). -/
theorem one_conv_K_eq_Hfun {ν lam r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (z : ℝ) :
    stConv (fun _ _ => (1 : ℝ)) (K ν lam) r z = Hfun ν lam r := by
  rw [one_conv_K hν hr z, Hfun_eq hν hr]

/-- The `J₀²` of `J₀ ≡ 1`, as a function. -/
theorem one_sq_fun : (fun _ _ => (1 : ℝ) ^ 2 : ℝ → ℝ → ℝ) = fun _ _ => 1 := by
  funext s w
  simp

theorem continuous_Hfun_closed (ν lam : ℝ) :
    Continuous fun r : ℝ =>
      2 * Real.exp (lam ^ 4 * r / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (r / (2 * ν))) - 1 := by
  have hΦ : Continuous Phi := continuous_Phi
  fun_prop

theorem continuousOn_Hfun {ν lam a b : ℝ} (hν : 0 < ν) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ContinuousOn (fun r => Hfun ν lam r) (uIcc a b) := by
  refine (continuous_Hfun_closed ν lam).continuousOn.congr fun r hr => ?_
  have : 0 ≤ r := le_trans (le_min ha hb) hr.1
  exact Hfun_eq hν this

theorem Phi_pos_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 < Phi x := by
  rw [Phi_eq_erf]
  have := erf_nonneg (div_nonneg hx (Real.sqrt_nonneg 2))
  linarith

/-- `𝓗(r) + 1 > 0` for `r ≥ 0`. -/
theorem Hfun_add_one_pos {ν lam r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) : 0 < Hfun ν lam r + 1 := by
  rw [Hfun_eq hν hr, sub_add_cancel]
  have := Phi_pos_of_nonneg (x := lam ^ 2 * Real.sqrt (r / (2 * ν))) (by positivity)
  positivity

theorem G_pos {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (w : ℝ) : 0 < G ν s w := by
  rw [G_eq_heatKernel]
  exact RoughHeatKernel.heatKernel_pos (mul_pos hν hs) w

/-- `G_ν(t + τ − 2r, w) = G_{2ν}((t + τ)/2 − r, w)`. -/
theorem G_two_nu (ν t τ r w : ℝ) : G ν (t + τ - 2 * r) w = G (2 * ν) ((t + τ) / 2 - r) w := by
  unfold G
  congr 3 <;> ring

/-- `r ↦ G_σ(T − r, w)` is integrable on `[0, T]` (singularity `(T − r)^{-1/2}` at most). -/
theorem intervalIntegrable_G_sub {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) (w : ℝ) :
    IntervalIntegrable (fun r => G σ (T - r) w) volume 0 T := by
  set C := 1 / Real.sqrt (2 * π * σ)
  have h0 : IntervalIntegrable (fun s => C * s ^ (-(1 / 2 : ℝ))) volume T 0 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul C
  have h1 : IntervalIntegrable (fun r => C * (T - r) ^ (-(1 / 2 : ℝ))) volume 0 T := by
    have := h0.comp_sub_left T
    simp only [sub_self, sub_zero] at this
    exact this
  refine h1.mono_fun ?_ ?_
  · have : Measurable fun r => G σ (T - r) w := by unfold G; fun_prop
    exact this.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun r hr => ?_)
    rw [uIoc_of_le hT] at hr
    have hs : 0 ≤ T - r := by linarith [hr.2]
    show ‖G σ (T - r) w‖ ≤ ‖C * (T - r) ^ (-(1 / 2 : ℝ))‖
    rw [Real.norm_of_nonneg (G_nonneg' σ (T - r) w), Real.norm_of_nonneg (by positivity)]
    rcases hs.lt_or_eq with hs | hs
    · rw [Real.rpow_neg hs.le, ← Real.sqrt_eq_rpow]
      unfold G
      have hE : Real.exp (-w ^ 2 / (2 * σ * (T - r))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ w ^ 2 / (2 * σ * (T - r)) := by positivity
        rw [neg_div]; linarith
      have hsq : Real.sqrt (2 * π * σ * (T - r)) = Real.sqrt (2 * π * σ) * Real.sqrt (T - r) :=
        Real.sqrt_mul (by positivity) _
      rw [hsq]
      have hp : 0 < Real.sqrt (2 * π * σ) * Real.sqrt (T - r) := by positivity
      calc 1 / (Real.sqrt (2 * π * σ) * Real.sqrt (T - r)) *
            Real.exp (-w ^ 2 / (2 * σ * (T - r)))
          ≤ 1 / (Real.sqrt (2 * π * σ) * Real.sqrt (T - r)) * 1 := by gcongr
        _ = C * (Real.sqrt (T - r))⁻¹ := by simp only [C]; field_simp
    · rw [← hs, G_time_zero]
      positivity
where
  G_nonneg' (σ s w : ℝ) : 0 ≤ G σ s w := by unfold G; positivity

/-- `r ↦ f(r) G_σ(T − r, w)` is integrable on `[0, T]` for `f` continuous on `[0, T]`. -/
theorem intervalIntegrable_mul_G_sub {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) (w : ℝ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (uIcc 0 T)) :
    IntervalIntegrable (fun r => f r * G σ (T - r) w) volume 0 T :=
  (intervalIntegrable_G_sub hσ hT w).continuousOn_mul hf

/-- The space integral in `rd1` with `J₀ ≡ 1`, for `0 < r < t ≤ τ`. -/
theorem inner_integral {ν v lam t τ r : ℝ} (hν : 0 < ν) (hr0 : 0 ≤ r) (hrt : r < t)
    (htτ : t ≤ τ) (x y : ℝ) :
    ∫ z, ((1 : ℝ) ^ 2 +
        stConv (fun _ _ => (1 : ℝ) ^ 2) (K ν lam) r z + v ^ 2 * Hfun ν lam r) *
        (G ν (t - r) (x - z) * G ν (τ - r) (y - z)) =
      (1 + (1 + v ^ 2) * Hfun ν lam r) * G (2 * ν) ((t + τ) / 2 - r) (x - y) := by
  have hc : ∀ z, ((1 : ℝ) ^ 2 +
        stConv (fun _ _ => (1 : ℝ) ^ 2) (K ν lam) r z + v ^ 2 * Hfun ν lam r) =
      1 + (1 + v ^ 2) * Hfun ν lam r := by
    intro z
    rw [one_sq_fun, one_conv_K_eq_Hfun hν hr0 z]
    ring
  simp_rw [hc]
  rw [MeasureTheory.integral_const_mul,
    IntGG.integral_G_mul_G_space hν (by linarith) (by linarith), ← G_two_nu]
  congr 2
  ring

/-- The same with `J₀ ≡ 1` replaced by the plain double integral of `G G`. -/
theorem inner_integral_GG {ν t τ r : ℝ} (hν : 0 < ν) (hrt : r < t) (htτ : t ≤ τ) (x y : ℝ) :
    ∫ z, G ν (t - r) (x - z) * G ν (τ - r) (y - z) = G (2 * ν) ((t + τ) / 2 - r) (x - y) := by
  rw [IntGG.integral_G_mul_G_space hν (by linarith) (by linarith), ← G_two_nu]
  congr 1
  ring

/-- The last two lines of `rd1` (the `ϑ²`-terms), by `L:IntIntGG`. -/
theorem v_lines_eq {ν v lam t τ : ℝ} (hν : 0 < ν) (ht : 0 < t) (htτ : t ≤ τ) (x y : ℝ) :
    lam ^ 2 * v ^ 2 / ν * |x - y| *
        (Phi (|x - y| / Real.sqrt (ν * (t + τ))) - PhiGap ν t τ (x - y)) +
      lam ^ 2 * v ^ 2 * ((t + τ) * G ν (t + τ) (x - y) - (τ - t) * G ν (τ - t) (x - y)) =
      lam ^ 2 * v ^ 2 * ∫ r in (0 : ℝ)..t, G (2 * ν) ((t + τ) / 2 - r) (x - y) := by
  have hcongr : ∫ r in (0 : ℝ)..t, ∫ z, G ν (t - r) (x - z) * G ν (τ - r) (y - z) =
      ∫ r in (0 : ℝ)..t, G (2 * ν) ((t + τ) / 2 - r) (x - y) := by
    rw [intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_of_le ht.le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun r hr => inner_integral_GG hν hr.2 htτ x y
  rw [← hcongr]
  rcases htτ.lt_or_eq with hlt | heq
  · rw [integral_integral_G_mul_G hν ht hlt x y, PhiGap,
      ite_eq_right_of_eq_false _ _ (eq_false hlt.ne'),
      add_comm τ t]
    ring
  · subst heq
    rw [integral_integral_G_mul_G_diag hν ht x y, PhiGap,
      ite_eq_left_of_eq_true _ _ (eq_self t), sub_self,
      zero_mul,
      sub_zero, ← two_mul]
    ring

end TPLebesgue

open Real MeasureTheory Set intervalIntegral TPLebesgue

/-- **Chen–Dalang (2015), `E2:SecMom-Lebesgue`.** With `J₀ ≡ 1`,
`J₀² + J₀² ⋆ 𝓚 + ϑ²𝓗 = 1 + (1 + ϑ²)𝓗(t)`. -/
theorem C2_SecMom_Lebesgue {ν v lam : ℝ} (hν : 0 < ν) :
    ∀ t > 0, ∀ x, secondMomentExpr (fun _ _ => 1) ν v lam t x = 1 + (1 + v ^ 2) * Hfun ν lam t := by
  intro t ht x
  rw [secondMomentExpr, one_sq_fun, one_conv_K_eq_Hfun hν ht.le x]
  ring

/-- **Chen–Dalang (2015), proof of `C2:TP-Lebesgue`, displayed step (correct).** For
`τ ≥ t > 0`, with `J₀ ≡ 1`,
`1 + 𝓘(t,x,τ,y) = 1 + λ²(1 + ϑ²) ∫₀ᵗ (𝓗(r) + 1) G_{2ν}((t + τ)/2 − r, x − y) dr`. -/
theorem C2_TP_Lebesgue_integral {ν v lam : ℝ} (hν : 0 < ν) :
    ∀ t τ, 0 < t → t ≤ τ → ∀ x y,
      1 * 1 + twoPointI (fun _ _ => 1) ν v lam t x τ y =
        1 + lam ^ 2 * (1 + v ^ 2) *
          ∫ r in (0 : ℝ)..t, (Hfun ν lam r + 1) * G (2 * ν) ((t + τ) / 2 - r) (x - y) := by
  intro t τ ht htτ x y
  set g : ℝ → ℝ := fun r => G (2 * ν) ((t + τ) / 2 - r) (x - y) with hg
  have hT : 0 ≤ (t + τ) / 2 := by linarith
  have htT : t ≤ (t + τ) / 2 := by linarith
  have hsub : uIcc 0 t ⊆ uIcc 0 ((t + τ) / 2) := by
    rw [uIcc_of_le ht.le, uIcc_of_le hT]
    exact Icc_subset_Icc_right htT
  have hgi : IntervalIntegrable g volume 0 t :=
    (intervalIntegrable_G_sub (by positivity) hT (x - y)).mono_set hsub
  have hfi : IntervalIntegrable (fun r => (1 + (1 + v ^ 2) * Hfun ν lam r) * g r) volume 0 t :=
    hgi.continuousOn_mul (continuousOn_const.add
      (continuousOn_const.mul (continuousOn_Hfun hν le_rfl ht.le)))
  have hfirst : ∫ r in (0 : ℝ)..t, ∫ z,
      ((1 : ℝ) ^ 2 +
        stConv (fun _ _ => (1 : ℝ) ^ 2) (K ν lam) r z + v ^ 2 * Hfun ν lam r) *
        (G ν (t - r) (x - z) * G ν (τ - r) (y - z)) =
      ∫ r in (0 : ℝ)..t, (1 + (1 + v ^ 2) * Hfun ν lam r) * g r := by
    rw [intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_of_le ht.le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun r hr =>
      inner_integral hν hr.1.le hr.2 htτ x y
  have hA : twoPointI (fun _ _ => 1) ν v lam t x τ y =
      lam ^ 2 * (∫ r in (0 : ℝ)..t, (1 + (1 + v ^ 2) * Hfun ν lam r) * g r) +
        lam ^ 2 * v ^ 2 * ∫ r in (0 : ℝ)..t, g r := by
    have hv := v_lines_eq (v := v) (lam := lam) hν ht htτ x y
    unfold twoPointI
    beta_reduce
    rw [hfirst, ← hv]
    ring
  rw [hA, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hfi.const_mul _) (hgi.const_mul _),
    ← intervalIntegral.integral_const_mul]
  congr 1
  · ring
  · refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [hg]
    ring

/-- The printed right side of `E2:TP-Lebesgue` is `1 + λ²(1 + ϑ²) ∫₀^{t̄} (𝓗 + 1) G_{2ν}(t̄ − r)`
(Lemma `L2:IntHG` at time `t̄`), i.e. the `r`-range `[0, t̄]` instead of `[0, t]`. -/
theorem TPLebesgue.paper_rhs_eq {ν v lam : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) {tb : ℝ}
    (htb : 0 < tb) (w : ℝ) :
    1 + (1 + v ^ 2) *
        (Real.exp ((lam ^ 4 * tb - 2 * lam ^ 2 * |w|) / (4 * ν)) *
            erfc ((|w| - lam ^ 2 * tb) / (2 * √(ν * tb))) -
          erfc (|w| / (2 * √(ν * tb)))) =
      1 + lam ^ 2 * (1 + v ^ 2) *
        ∫ r in (0 : ℝ)..tb, (Hfun ν lam r + 1) * G (2 * ν) (tb - r) w := by
  have hcongr : ∫ r in (0 : ℝ)..tb, (Hfun ν lam r + 1) * G (2 * ν) (tb - r) w =
      ∫ r in (0 : ℝ)..tb,
        (stConv (fun _ _ => (1 : ℝ)) (K ν lam) r w + 1) * G (2 * ν) (tb - r) w := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le htb.le] at hr
    rw [one_conv_K_eq_Hfun hν hr.1 w]
  rw [hcongr, integral_one_conv_K_add_one_mul_G hν hlam htb w]
  have hl : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
  field_simp

/-- **Chen–Dalang (2015), `E2:TP-Lebesgue` at `τ = t`** (where the printed formula is
correct), with `t̄ = (t + t)/2 = t`. -/
theorem C2_TP_Lebesgue_diag {ν v lam : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) :
    ∀ t, 0 < t → ∀ x y,
      1 * 1 + twoPointI (fun _ _ => 1) ν v lam t x t y =
        1 + (1 + v ^ 2) *
          (Real.exp ((lam ^ 4 * ((t + t) / 2) - 2 * lam ^ 2 * |x - y|) / (4 * ν)) *
              erfc ((|x - y| - lam ^ 2 * ((t + t) / 2)) / (2 * √(ν * ((t + t) / 2)))) -
            erfc (|x - y| / (2 * √(ν * ((t + t) / 2))))) := by
  intro t ht x y
  rw [TPLebesgue.paper_rhs_eq hν hlam (by linarith : 0 < (t + t) / 2) (x - y),
    C2_TP_Lebesgue_integral hν t t ht le_rfl x y, show (t + t) / 2 = t by ring]

/-- **Erratum to `E2:TP-Lebesgue` (`τ > t`).** For `τ > t > 0` the printed closed form strictly
exceeds `1 + 𝓘(t,x,τ,y)`: the difference is
`λ²(1 + ϑ²) ∫ₜ^{t̄} (𝓗(r) + 1) G_{2ν}(t̄ − r, x − y) dr > 0`. -/
theorem C2_TP_Lebesgue_lt {ν v lam : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) :
    ∀ t τ, 0 < t → t < τ → ∀ x y,
      1 * 1 + twoPointI (fun _ _ => 1) ν v lam t x τ y <
        1 + (1 + v ^ 2) *
          (Real.exp ((lam ^ 4 * ((t + τ) / 2) - 2 * lam ^ 2 * |x - y|) / (4 * ν)) *
              erfc ((|x - y| - lam ^ 2 * ((t + τ) / 2)) / (2 * √(ν * ((t + τ) / 2)))) -
            erfc (|x - y| / (2 * √(ν * ((t + τ) / 2))))) := by
  intro t τ ht htτ x y
  set tb := (t + τ) / 2 with htb_def
  have htb : 0 < tb := by rw [htb_def]; linarith
  have httb : t < tb := by rw [htb_def]; linarith
  rw [C2_TP_Lebesgue_integral hν t τ ht htτ.le x y, paper_rhs_eq hν hlam htb (x - y)]
  set f : ℝ → ℝ := fun r => (Hfun ν lam r + 1) * G (2 * ν) (tb - r) (x - y) with hf
  have hfi : IntervalIntegrable f volume 0 tb :=
    intervalIntegrable_mul_G_sub (by positivity) htb.le (x - y)
      ((continuousOn_Hfun hν le_rfl htb.le).add continuousOn_const)
  have hfi1 : IntervalIntegrable f volume 0 t :=
    hfi.mono_set (by rw [uIcc_of_le ht.le, uIcc_of_le htb.le]; exact Icc_subset_Icc_right httb.le)
  have hfi2 : IntervalIntegrable f volume t tb :=
    hfi.mono_set (by
      rw [uIcc_of_le httb.le, uIcc_of_le htb.le]; exact Icc_subset_Icc_left ht.le)
  rw [← intervalIntegral.integral_add_adjacent_intervals hfi1 hfi2]
  have hpos : 0 < ∫ r in t..tb, f r :=
    intervalIntegral_pos_of_pos_on hfi2 (fun r hr => mul_pos
      (Hfun_add_one_pos hν (by linarith [hr.1])) (G_pos (by positivity) (by linarith [hr.2]) _))
      httb
  have hc : 0 < lam ^ 2 * (1 + v ^ 2) := by positivity
  nlinarith [mul_pos hc hpos]

namespace TPLebesgue

/-- `𝓘` with `J₀ ≡ 1` is nonnegative. -/
theorem twoPointI_one_nonneg {ν v lam t τ : ℝ} (hν : 0 < ν) (ht : 0 < t) (htτ : t ≤ τ)
    (x y : ℝ) : 0 ≤ twoPointI (fun _ _ => 1) ν v lam t x τ y := by
  have h := C2_TP_Lebesgue_integral (v := v) (lam := lam) hν t τ ht htτ x y
  have hI : 0 ≤ ∫ r in (0 : ℝ)..t, (Hfun ν lam r + 1) * G (2 * ν) ((t + τ) / 2 - r) (x - y) :=
    intervalIntegral.integral_nonneg ht.le fun r hr =>
      mul_nonneg (Hfun_add_one_pos hν hr.1).le (IntGG.G_nonneg _ _ _)
  have : 0 ≤ lam ^ 2 * (1 + v ^ 2) *
      ∫ r in (0 : ℝ)..t, (Hfun ν lam r + 1) * G (2 * ν) ((t + τ) / 2 - r) (x - y) := by
    positivity
  linarith

end TPLebesgue

/-- **`E2:TP-Lebesgue` as printed (all `τ ≥ t > 0`) is false**, for every `ν > 0`, `λ ≠ 0`
and `ϑ`: it fails at `t = 1`, `τ = 2`, `x = y = 0` (indeed at every `τ > t`,
`C2_TP_Lebesgue_lt`). -/
theorem C2_TP_Lebesgue_false {ν v lam : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) :
    ¬ ∀ t τ, 0 < t → t ≤ τ → ∀ x y,
      1 * 1 + twoPointI (fun _ _ => 1) ν v lam t x τ y =
        1 + (1 + v ^ 2) *
          (Real.exp ((lam ^ 4 * ((t + τ) / 2) - 2 * lam ^ 2 * |x - y|) / (4 * ν)) *
              erfc ((|x - y| - lam ^ 2 * ((t + τ) / 2)) / (2 * √(ν * ((t + τ) / 2)))) -
            erfc (|x - y| / (2 * √(ν * ((t + τ) / 2))))) := by
  intro h
  have h1 := h 1 2 one_pos (by norm_num) 0 0
  have h2 := C2_TP_Lebesgue_lt (v := v) hν hlam 1 2 one_pos (by norm_num) 0 0
  rw [h1] at h2
  exact lt_irrefl _ h2

end ChenDalang15

end
