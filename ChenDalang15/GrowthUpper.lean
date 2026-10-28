module

public import ChenDalang15.H
public import ChenDalang15.GrowthDefs

/-!
# The deterministic analysis behind the upper bound of `T2:Growth(2)` (Chen–Dalang 2015)

* `L2_MaxGGE`, `L2_MaxGGE_cases`: Lemma `L2:MaxGGE` (display `E2:Hxbts` and the two-case bound).
* `L2_InDt_G_J0`, `L2_InDt_G_conv`: Lemma `L2:InDt-G` (`E2:J0Bd-G`, `E2:J0KBd-G`), for a
  nonnegative initial measure `μ` with `∫ e^{β|y|} μ(dy) < ∞`.
* `upper_envelope`: the displayed bound on `f` in the proof of `T2:Growth(2)`, with the
  constants generalised (`a = 1`, `Λ = Lip_ρ` for `p = 2`; `a = 2`, `Λ = √2 z_p Lip_ρ` for even
  `p`).
* `upper_envelope_exp`: the corollary `f(t,x) ≤ A e^{(νβ² + Λ⁴/(4ν)) t − 2β|x|}` for large `t`.

Route for the convolution bound (as in the paper): write `J₀²` as a double integral, apply the
product formula `L2:GG` and the semigroup property in `y` (display `E2:InDt-Mid`), then
`L2:MaxGGE`. Everything is nonnegative, so the computation runs in lower Lebesgue integrals
(Tonelli), and the Bochner integrals of the statement are bounded through
`‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ`; no integrability of the left-hand sides is assumed or proved.
-/

set_option autoImplicit false

public section

namespace ChenDalang15

open Real MeasureTheory Set
open scoped ENNReal

namespace GrowthUpper

theorem G_nonneg (ν t x : ℝ) : 0 ≤ G ν t x := by
  unfold G
  positivity

theorem continuous_G (ν t : ℝ) : Continuous (G ν t) := by
  have : G ν t = RoughHeatKernel.heatKernel (ν * t) := funext (G_eq_heatKernel ν t)
  rw [this]
  exact RoughHeatKernel.continuous_heatKernel _

theorem measurable_G (ν t : ℝ) : Measurable (G ν t) := (continuous_G ν t).measurable

/-- The prefactor identity: `G_{2ν}(s,Δ) G_{ν/2}(t,y)` as one exponential. -/
theorem G_two_mul_G_half {ν t s : ℝ} (hν : 0 < ν) (ht : 0 < t) (hs : 0 < s) (Δ y : ℝ) :
    G (2 * ν) s Δ * G (ν / 2) t y =
      1 / (2 * π * ν * √(t * s)) * exp (-Δ ^ 2 / (4 * ν * s) - y ^ 2 / (ν * t)) := by
  unfold G
  have h1 : √(2 * π * (2 * ν) * s) * √(2 * π * (ν / 2) * t) = 2 * π * ν * √(t * s) := by
    rw [← Real.sqrt_mul (by positivity),
      show 2 * π * (2 * ν) * s * (2 * π * (ν / 2) * t) = (2 * π * ν) ^ 2 * (t * s) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [show -Δ ^ 2 / (4 * ν * s) - y ^ 2 / (ν * t) =
      -Δ ^ 2 / (2 * (2 * ν) * s) + -y ^ 2 / (2 * (ν / 2) * t) by
    field_simp; ring, Real.exp_add, ← h1]
  field_simp

/-- The scalar minimisation behind `L2:MaxGGE`: `(x-w)²/p + 2β|w| ≥ 2β|x| − pβ²`. -/
theorem quad_abs_ge {p β : ℝ} (hp : 0 < p) (hβ : 0 ≤ β) (x w : ℝ) :
    2 * β * |x| - p * β ^ 2 ≤ (x - w) ^ 2 / p + 2 * β * |w| := by
  have hxw : |x| ≤ |x - w| + |w| := by
    have := abs_sub_abs_le_abs_sub x w
    linarith
  have key : p * (2 * β * |x - w| - p * β ^ 2) ≤ (x - w) ^ 2 := by
    nlinarith [sq_nonneg (|x - w| - p * β), sq_abs (x - w)]
  have : 2 * β * |x - w| - p * β ^ 2 ≤ (x - w) ^ 2 / p := by
    rw [le_div_iff₀ hp]; linarith
  nlinarith

/-- The first case of `L2:MaxGGE`: `(x-w)²/p + 2β|w| ≥ x²/p` when `|x| ≤ pβ`. -/
theorem quad_abs_ge_case1 {p β : ℝ} (hp : 0 < p) {x : ℝ} (hx : |x| ≤ p * β) (w : ℝ) :
    x ^ 2 / p ≤ (x - w) ^ 2 / p + 2 * β * |w| := by
  have hxw : x * w ≤ |x| * |w| := by rw [← abs_mul]; exact le_abs_self _
  have : x ^ 2 ≤ (x - w) ^ 2 + p * (2 * β * |w|) := by
    nlinarith [abs_nonneg w, sq_nonneg w, mul_le_mul_of_nonneg_right hx (abs_nonneg w)]
  rw [div_add' _ _ _ hp.ne', div_le_div_iff_of_pos_right hp]
  linarith

theorem abs_add_le_half {z₁ z₂ : ℝ} : 2 * |(z₁ + z₂) / 2| ≤ |z₁| + |z₂| := by
  rw [abs_div, abs_two]
  have := abs_add_le z₁ z₂
  linarith

end GrowthUpper

open GrowthUpper

/-- **Chen–Dalang (2015), Lemma `L2:MaxGGE`, display `E2:Hxbts`.** For `ν, t, s, β > 0` and all
`x, z₁, z₂`,
`G_{2ν}(s, z₂ − z₁) G_{ν/2}(t, x − (z₁+z₂)/2) e^{−β|z₁| − β|z₂|} ≤ (2πν√(ts))⁻¹ e^{−2β|x| + νβ²t}`. -/
theorem L2_MaxGGE {ν t s β : ℝ} (hν : 0 < ν) (ht : 0 < t) (hs : 0 < s) (hβ : 0 < β)
    (x z₁ z₂ : ℝ) :
    G (2 * ν) s (z₂ - z₁) * G (ν / 2) t (x - (z₁ + z₂) / 2) * exp (-β * |z₁| - β * |z₂|) ≤
      1 / (2 * π * ν * √(t * s)) * exp (-2 * β * |x| + ν * β ^ 2 * t) := by
  rw [G_two_mul_G_half hν ht hs, mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hp : 0 < ν * t := mul_pos hν ht
  have h1 := quad_abs_ge (β := β) hp hβ.le x ((z₁ + z₂) / 2)
  have h2 : -(z₂ - z₁) ^ 2 / (4 * ν * s) ≤ 0 := by
    rw [neg_div]; exact neg_nonpos.mpr (by positivity)
  have h3 := mul_le_mul_of_nonneg_left (abs_add_le_half (z₁ := z₁) (z₂ := z₂)) hβ.le
  linarith

/-- **Chen–Dalang (2015), Lemma `L2:MaxGGE`, the two-case bound.** With the same hypotheses,
the product is at most `(2πν√(ts))⁻¹ e^{−x²/(νt)}` if `|x| ≤ νβt`, and at most
`(2πν√(ts))⁻¹ e^{−2β|x| + νβ²t}` otherwise. -/
theorem L2_MaxGGE_cases {ν t s β : ℝ} (hν : 0 < ν) (ht : 0 < t) (hs : 0 < s) (hβ : 0 < β)
    (x z₁ z₂ : ℝ) :
    G (2 * ν) s (z₂ - z₁) * G (ν / 2) t (x - (z₁ + z₂) / 2) * exp (-β * |z₁| - β * |z₂|) ≤
      1 / (2 * π * ν * √(t * s)) *
        (if |x| ≤ ν * β * t then exp (-x ^ 2 / (ν * t)) else exp (-2 * β * |x| + ν * β ^ 2 * t)) := by
  split_ifs with hx
  · rw [G_two_mul_G_half hν ht hs, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have hp : 0 < ν * t := mul_pos hν ht
    have h1 := quad_abs_ge_case1 (β := β) hp (x := x) (by linarith) ((z₁ + z₂) / 2)
    have h2 : 0 ≤ (z₂ - z₁) ^ 2 / (4 * ν * s) := by positivity
    have h3 := mul_le_mul_of_nonneg_left (abs_add_le_half (z₁ := z₁) (z₂ := z₂)) hβ.le
    rw [neg_div, neg_div]
    linarith
  · exact L2_MaxGGE hν ht hs hβ x z₁ z₂

namespace GrowthUpper

/-- Pointwise envelope of `G_ν(t, x − y)` against `e^{β|y|}`:
`G_ν(t,x−y) ≤ (2πνt)^{-1/2} e^{−β|x| + νβ²t/2} e^{β|y|}`. -/
theorem G_sub_le {ν t β : ℝ} (hν : 0 < ν) (ht : 0 < t) (hβ : 0 ≤ β) (x y : ℝ) :
    G ν t (x - y) ≤ 1 / √(2 * π * ν * t) * exp (-β * |x| + ν * β ^ 2 * t / 2) * exp (β * |y|) := by
  unfold G
  rw [mul_assoc _ (exp _) (exp _), ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hp : 0 < 2 * ν * t := by positivity
  have h1 := quad_abs_ge (β := β / 2) hp (by positivity) x y
  rw [neg_div]
  nlinarith

/-- A measure integrating `e^{β|y|}` (`β ≥ 0`) is finite. -/
theorem isFiniteMeasure_of_integrable_exp {μ : Measure ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hI : Integrable (fun y => exp (β * |y|)) μ) : IsFiniteMeasure μ := by
  refine ⟨?_⟩
  calc μ univ = ∫⁻ _, 1 ∂μ := by simp
    _ ≤ ∫⁻ y, ‖exp (β * |y|)‖ₑ ∂μ := by
        refine lintegral_mono fun y => ?_
        rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))
    _ < ⊤ := hI.2

theorem J0_nonneg (ν : ℝ) (μ : Measure ℝ) (t x : ℝ) : 0 ≤ J0 ν μ t x :=
  integral_nonneg fun _ => G_nonneg _ _ _

/-- `J₀(t,x) ≤ C (2πνt)^{-1/2} e^{−β|x| + νβ²t/2}`. -/
theorem J0_le {ν t β : ℝ} (hν : 0 < ν) (ht : 0 < t) (hβ : 0 ≤ β) {μ : Measure ℝ}
    (hI : Integrable (fun y => exp (β * |y|)) μ) (x : ℝ) :
    J0 ν μ t x ≤ 1 / √(2 * π * ν * t) * exp (-β * |x| + ν * β ^ 2 * t / 2) *
      ∫ y, exp (β * |y|) ∂μ := by
  rw [J0, ← integral_const_mul]
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => G_nonneg _ _ _)
    (hI.const_mul _) (Filter.Eventually.of_forall fun y => G_sub_le hν ht hβ x y)

/-- `ENNReal.ofReal (∫ f) ≤ ∫⁻ ENNReal.ofReal f` for nonnegative `f`, with no integrability
hypothesis (a non-integrable `f` has Bochner integral `0`). -/
theorem ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  calc ENNReal.ofReal (∫ a, f a ∂μ) ≤ ‖∫ a, f a ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ a, ‖f a‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ a, ENNReal.ofReal (f a) ∂μ :=
        lintegral_congr fun a => Real.enorm_eq_ofReal (hf a)

end GrowthUpper

/-- **Chen–Dalang (2015), Lemma `L2:InDt-G`, display `E2:J0Bd-G`.** For a nonnegative measure
`μ` with `C = ∫ e^{β|y|} μ(dy) < ∞`, `ν, β, t > 0` and every `x`,
`J₀(t,x)² ≤ C²/(2πνt) · e^{−2β|x| + νβ²t}`. -/
theorem L2_InDt_G_J0 {ν β t : ℝ} (hν : 0 < ν) (hβ : 0 < β) (ht : 0 < t) {μ : Measure ℝ}
    (hI : Integrable (fun y => exp (β * |y|)) μ) {C : ℝ} (hC : C = ∫ y, exp (β * |y|) ∂μ)
    (x : ℝ) :
    J0 ν μ t x ^ 2 ≤ C ^ 2 / (2 * π * ν * t) * exp (-2 * β * |x| + ν * β ^ 2 * t) := by
  have h := J0_le hν ht hβ.le hI x
  rw [← hC] at h
  calc J0 ν μ t x ^ 2
      ≤ (1 / √(2 * π * ν * t) * exp (-β * |x| + ν * β ^ 2 * t / 2) * C) ^ 2 :=
        pow_le_pow_left₀ (J0_nonneg ν μ t x) h 2
    _ = C ^ 2 / (2 * π * ν * t) * exp (-2 * β * |x| + ν * β ^ 2 * t) := by
        have hsq : √(2 * π * ν * t) ^ 2 = 2 * π * ν * t := Real.sq_sqrt (by positivity)
        have hexp : exp (-β * |x| + ν * β ^ 2 * t / 2) ^ 2 =
            exp (-2 * β * |x| + ν * β ^ 2 * t) := by
          rw [sq, ← Real.exp_add]; ring_nf
        rw [mul_pow, mul_pow, div_pow, one_pow, hsq, hexp]
        ring

namespace GrowthUpper

attribute [local fun_prop] measurable_G

/-- `L2:GG`, product form: `G_ν(s,y−z₁) G_ν(s,y−z₂) = G_{2ν}(s,z₂−z₁) G_{ν/2}(s, y − (z₁+z₂)/2)`. -/
theorem G_mul_G_eq {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (y z₁ z₂ : ℝ) :
    G ν s (y - z₁) * G ν s (y - z₂) = G (2 * ν) s (z₂ - z₁) * G (ν / 2) s (y - (z₁ + z₂) / 2) := by
  simp only [G_eq_heatKernel]
  rw [RoughHeatKernel.heatKernel_mul_heatKernel_eq (mul_pos hν hs), ← RoughHeatKernel.heatKernel_neg
    (2 * ν * s), neg_sub]
  ring_nf

/-- The semigroup property in the shifted form `∫ G_{ν/2}(s, y − m) G_{ν/2}(r, x − y) dy`. -/
theorem integrable_G_sub_mul_G_sub {ν s r : ℝ} (hν : 0 < ν) (hs : 0 < s) (hr : 0 < r)
    (x m : ℝ) : Integrable (fun y => G ν s (y - m) * G ν r (x - y)) := by
  simp only [G_eq_heatKernel]
  have h := (RoughHeatKernel.integrable_heatKernel_sub_mul_heatKernel (mul_pos hν hs)
    (mul_pos hν hr) (x - m)).comp_sub_right m
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [show x - m - (y - m) = x - y by ring, mul_comm]

theorem integral_G_sub_mul_G_sub {ν s r : ℝ} (hν : 0 < ν) (hs : 0 < s) (hr : 0 < r)
    (x m : ℝ) : ∫ y, G ν s (y - m) * G ν r (x - y) = G ν (s + r) (x - m) := by
  have h := integral_G_mul_G hν hs (show s < s + r by linarith) (x - m)
  rw [← integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => G ν (s + r - s) (x - m - y) * G ν s y) m] at h
  rw [← h]
  congr 1
  ext y
  rw [show x - m - (y - m) = x - y by ring, show s + r - s = r by ring, mul_comm]

/-- Display `E2:InDt-Mid` at the level of the `y`-integral (Tonelli form):
`∫ G_ν(s,y−z₁) G_ν(s,y−z₂) G_{ν/2}(r,x−y) dy = G_{2ν}(s,z₂−z₁) G_{ν/2}(s+r, x − (z₁+z₂)/2)`. -/
theorem lintegral_G_G_G {ν s r : ℝ} (hν : 0 < ν) (hs : 0 < s) (hr : 0 < r) (x z₁ z₂ : ℝ) :
    ∫⁻ y, ENNReal.ofReal (G ν s (y - z₁)) * ENNReal.ofReal (G ν s (y - z₂)) *
        ENNReal.ofReal (G (ν / 2) r (x - y)) =
      ENNReal.ofReal (G (2 * ν) s (z₂ - z₁) * G (ν / 2) (s + r) (x - (z₁ + z₂) / 2)) := by
  have hν2 : 0 < ν / 2 := half_pos hν
  have e : ∀ y, ENNReal.ofReal (G ν s (y - z₁)) * ENNReal.ofReal (G ν s (y - z₂)) *
      ENNReal.ofReal (G (ν / 2) r (x - y)) =
      ENNReal.ofReal (G (2 * ν) s (z₂ - z₁)) *
        ENNReal.ofReal (G (ν / 2) s (y - (z₁ + z₂) / 2) * G (ν / 2) r (x - y)) := by
    intro y
    rw [← ENNReal.ofReal_mul (G_nonneg _ _ _), ← ENNReal.ofReal_mul (G_nonneg _ _ _),
      ← ENNReal.ofReal_mul (mul_nonneg (G_nonneg _ _ _) (G_nonneg _ _ _)), G_mul_G_eq hν hs]
    ring_nf
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_G_sub_mul_G_sub hν2 hs hr x _)
      (Filter.Eventually.of_forall fun y => mul_nonneg (G_nonneg _ _ _) (G_nonneg _ _ _)),
    integral_G_sub_mul_G_sub hν2 hs hr, ← ENNReal.ofReal_mul (G_nonneg _ _ _)]

/-- `L2:MaxGGE` rearranged: the kernel product is at most
`(2πν√(ts))⁻¹ e^{−2β|x|+νβ²t} e^{β|z₁|} e^{β|z₂|}`. -/
theorem GG_le_mul_exp {ν t s β : ℝ} (hν : 0 < ν) (ht : 0 < t) (hs : 0 < s) (hβ : 0 < β)
    (x z₁ z₂ : ℝ) :
    G (2 * ν) s (z₂ - z₁) * G (ν / 2) t (x - (z₁ + z₂) / 2) ≤
      1 / (2 * π * ν * √(t * s)) * exp (-2 * β * |x| + ν * β ^ 2 * t) *
        (exp (β * |z₁|) * exp (β * |z₂|)) := by
  have h := mul_le_mul_of_nonneg_right (L2_MaxGGE hν ht hs hβ x z₁ z₂)
    (Real.exp_pos (β * |z₁| + β * |z₂|)).le
  rw [mul_assoc _ (exp _) (exp _), ← Real.exp_add,
    show -β * |z₁| - β * |z₂| + (β * |z₁| + β * |z₂|) = 0 by ring, Real.exp_zero,
    mul_one, Real.exp_add (β * |z₁|) (β * |z₂|)] at h
  exact h

/-- The core Tonelli estimate behind `E2:J0KBd-G`, for `s, r > 0`:
`∫ J₀(s,y)² G_{ν/2}(r,x−y) dy ≤ C²/(2πν√((s+r)s)) e^{−2β|x| + νβ²(s+r)}` (in `[0,∞]`). -/
theorem lintegral_J0_sq_mul_G_le {ν β s r : ℝ} (hν : 0 < ν) (hβ : 0 < β) (hs : 0 < s)
    (hr : 0 < r) {μ : Measure ℝ} (hI : Integrable (fun y => exp (β * |y|)) μ) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (J0 ν μ s y) ^ 2 * ENNReal.ofReal (G (ν / 2) r (x - y)) ≤
      ENNReal.ofReal (1 / (2 * π * ν * √((s + r) * s)) *
        exp (-2 * β * |x| + ν * β ^ 2 * (s + r))) *
        ENNReal.ofReal (∫ y, exp (β * |y|) ∂μ) ^ 2 := by
  have := isFiniteMeasure_of_integrable_exp hβ.le hI
  set M := 1 / (2 * π * ν * √((s + r) * s)) * exp (-2 * β * |x| + ν * β ^ 2 * (s + r))
  have hM : 0 ≤ M := by positivity
  have hsq : ∀ y, ENNReal.ofReal (J0 ν μ s y) ^ 2 ≤ ∫⁻ q : ℝ × ℝ,
      ENNReal.ofReal (G ν s (y - q.1)) * ENNReal.ofReal (G ν s (y - q.2)) ∂(μ.prod μ) := by
    intro y
    rw [lintegral_prod_mul (f := fun z => ENNReal.ofReal (G ν s (y - z)))
      (g := fun z => ENNReal.ofReal (G ν s (y - z))) (by fun_prop) (by fun_prop), sq]
    exact mul_le_mul' (ofReal_integral_le_lintegral fun _ => G_nonneg _ _ _)
      (ofReal_integral_le_lintegral fun _ => G_nonneg _ _ _)
  have hF : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (G ν s (p.1 - p.2.1)) * ENNReal.ofReal (G ν s (p.1 - p.2.2)) *
        ENNReal.ofReal (G (ν / 2) r (x - p.1)) := by fun_prop
  calc ∫⁻ y, ENNReal.ofReal (J0 ν μ s y) ^ 2 * ENNReal.ofReal (G (ν / 2) r (x - y))
      ≤ ∫⁻ y, ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (G ν s (y - q.1)) * ENNReal.ofReal (G ν s (y - q.2)) *
          ENNReal.ofReal (G (ν / 2) r (x - y)) ∂(μ.prod μ) := by
        refine lintegral_mono fun y => ?_
        rw [lintegral_mul_const _ (by fun_prop)]
        exact mul_le_mul_left (hsq y) _
    _ = ∫⁻ q : ℝ × ℝ, (∫⁻ y, ENNReal.ofReal (G ν s (y - q.1)) *
          ENNReal.ofReal (G ν s (y - q.2)) * ENNReal.ofReal (G (ν / 2) r (x - y))) ∂(μ.prod μ) :=
        lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (G (2 * ν) s (q.2 - q.1) *
          G (ν / 2) (s + r) (x - (q.1 + q.2) / 2)) ∂(μ.prod μ) :=
        lintegral_congr fun q => lintegral_G_G_G hν hs hr x q.1 q.2
    _ ≤ ∫⁻ q : ℝ × ℝ, ENNReal.ofReal M *
          (ENNReal.ofReal (exp (β * |q.1|)) * ENNReal.ofReal (exp (β * |q.2|))) ∂(μ.prod μ) := by
        refine lintegral_mono fun q => ?_
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hM]
        exact ENNReal.ofReal_le_ofReal (GG_le_mul_exp hν (by linarith) hs hβ x q.1 q.2)
    _ = ENNReal.ofReal M * ENNReal.ofReal (∫ y, exp (β * |y|) ∂μ) ^ 2 := by
        rw [lintegral_const_mul _ (by fun_prop),
          lintegral_prod_mul (f := fun z => ENNReal.ofReal (exp (β * |z|)))
            (g := fun z => ENNReal.ofReal (exp (β * |z|))) (by fun_prop) (by fun_prop),
          ofReal_integral_eq_lintegral_ofReal hI
            (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le), sq]

/-- The real form of the inner estimate, for any kernel dominated by `G_{ν/2}(r,·) h(r)`:
`∫ J₀(s,y)² 𝒦(r,x−y) dy ≤ C²/(2πν√((s+r)s)) e^{−2β|x| + νβ²(s+r)} h(r)`. -/
theorem integral_J0_sq_mul_le {ν β s r : ℝ} (hν : 0 < ν) (hβ : 0 < β) (hs : 0 < s)
    (hr : 0 < r) {μ : Measure ℝ} (hI : Integrable (fun y => exp (β * |y|)) μ)
    {Kf : ℝ → ℝ → ℝ} {hr' : ℝ} (hK : ∀ z, 0 ≤ Kf r z ∧ Kf r z ≤ G (ν / 2) r z * hr')
    (x : ℝ) :
    ∫ y, J0 ν μ s y ^ 2 * Kf r (x - y) ≤
      1 / (2 * π * ν * √((s + r) * s)) * exp (-2 * β * |x| + ν * β ^ 2 * (s + r)) *
        (∫ y, exp (β * |y|) ∂μ) ^ 2 * hr' := by
  have hh0 : 0 ≤ hr' := by
    have h := (hK 0).1.trans (hK 0).2
    have hG : 0 < G (ν / 2) r 0 := by
      rw [G_eq_heatKernel]; exact RoughHeatKernel.heatKernel_pos (by positivity) _
    exact nonneg_of_mul_nonneg_right h hG
  have hC0 : 0 ≤ ∫ y, exp (β * |y|) ∂μ := integral_nonneg fun _ => (Real.exp_pos _).le
  have hB : 0 ≤ 1 / (2 * π * ν * √((s + r) * s)) * exp (-2 * β * |x| + ν * β ^ 2 * (s + r)) *
      (∫ y, exp (β * |y|) ∂μ) ^ 2 * hr' := by positivity
  rw [← ENNReal.ofReal_le_ofReal_iff hB]
  calc ENNReal.ofReal (∫ y, J0 ν μ s y ^ 2 * Kf r (x - y))
      ≤ ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * Kf r (x - y)) :=
        ofReal_integral_le_lintegral fun y => mul_nonneg (sq_nonneg _) (hK _).1
    _ ≤ ∫⁻ y, ENNReal.ofReal (J0 ν μ s y) ^ 2 * ENNReal.ofReal (G (ν / 2) r (x - y)) *
          ENNReal.ofReal hr' := by
        refine lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_pow (J0_nonneg _ _ _ _), ← ENNReal.ofReal_mul (sq_nonneg _),
          ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (G_nonneg _ _ _)), mul_assoc]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hK _).2 (sq_nonneg _))
    _ = (∫⁻ y, ENNReal.ofReal (J0 ν μ s y) ^ 2 * ENNReal.ofReal (G (ν / 2) r (x - y))) *
          ENNReal.ofReal hr' := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (1 / (2 * π * ν * √((s + r) * s)) *
          exp (-2 * β * |x| + ν * β ^ 2 * (s + r))) *
          ENNReal.ofReal (∫ y, exp (β * |y|) ∂μ) ^ 2 * ENNReal.ofReal hr' :=
        mul_le_mul_left (lintegral_J0_sq_mul_G_le hν hβ hs hr hI x) _
    _ = _ := by
        rw [← ENNReal.ofReal_pow hC0, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]

/-- The convolution estimate `E2:J0KBd-G` for any kernel `𝒦` with
`0 ≤ 𝒦(r,z) ≤ G_{ν/2}(r,z) h(r)` for `r > 0`. -/
theorem stConv_J0_sq_le {ν β t : ℝ} (hν : 0 < ν) (hβ : 0 < β) (ht : 0 < t) {μ : Measure ℝ}
    (hI : Integrable (fun y => exp (β * |y|)) μ) {Kf : ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hK : ∀ r, 0 < r → ∀ z, 0 ≤ Kf r z ∧ Kf r z ≤ G (ν / 2) r z * h r)
    (hh : IntervalIntegrable (fun s => h (t - s) / √s) volume 0 t) (x : ℝ) :
    stConv (fun s y => J0 ν μ s y ^ 2) Kf t x ≤
      (∫ y, exp (β * |y|) ∂μ) ^ 2 / (2 * π * ν * √t) * exp (-2 * β * |x| + ν * β ^ 2 * t) *
        ∫ s in (0 : ℝ)..t, h (t - s) / √s := by
  set c := (∫ y, exp (β * |y|) ∂μ) ^ 2 / (2 * π * ν * √t) * exp (-2 * β * |x| + ν * β ^ 2 * t)
  rw [stConv, intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_of_le ht.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ ((hh.1.mono_set Ioo_subset_Ioc_self).const_mul c) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact integral_nonneg fun y =>
      mul_nonneg (sq_nonneg _) (hK (t - s) (by linarith [hs.2]) _).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hts : 0 < t - s := by linarith [hs.2]
    have h1 := integral_J0_sq_mul_le hν hβ hs.1 hts hI (hK (t - s) hts) x
    rw [show s + (t - s) = t by ring] at h1
    refine h1.trans (le_of_eq ?_)
    have hst : √(t * s) = √t * √s := Real.sqrt_mul ht.le s
    have h2 : 0 < √t := Real.sqrt_pos.mpr ht
    have h3 : 0 < √s := Real.sqrt_pos.mpr hs.1
    simp only [c, hst]
    field_simp

end GrowthUpper

/-- **Chen–Dalang (2015), Lemma `L2:InDt-G`, display `E2:J0KBd-G`.** For a nonnegative measure
`μ` with `C = ∫ e^{β|y|} μ(dy) < ∞`, `ν, β, t > 0`, and `h ≥ 0` with
`s ↦ h(t−s)/√s` integrable on `[0,t]`,
`(J₀² ⋆ G_{ν/2} h)(t,x) ≤ C²/(2πν√t) · e^{−2β|x| + νβ²t} · ∫₀ᵗ h(t−s)/√s ds`. -/
theorem L2_InDt_G_conv {ν β t : ℝ} (hν : 0 < ν) (hβ : 0 < β) (ht : 0 < t) {μ : Measure ℝ}
    (hI : Integrable (fun y => exp (β * |y|)) μ) {C : ℝ} (hC : C = ∫ y, exp (β * |y|) ∂μ)
    {h : ℝ → ℝ} (h0 : 0 ≤ h) (hh : IntervalIntegrable (fun s => h (t - s) / √s) volume 0 t)
    (x : ℝ) :
    stConv (fun s y => J0 ν μ s y ^ 2) (fun s y => G (ν / 2) s y * h s) t x ≤
      C ^ 2 / (2 * π * ν * √t) * exp (-2 * β * |x| + ν * β ^ 2 * t) *
        ∫ s in (0 : ℝ)..t, h (t - s) / √s := by
  rw [hC]
  exact stConv_J0_sq_le hν hβ ht hI
    (fun r _ z => ⟨mul_nonneg (G_nonneg _ _ _) (h0 r), le_rfl⟩) hh x

namespace GrowthUpper

theorem Phi_nonneg (x : ℝ) : 0 ≤ Phi x :=
  setIntegral_nonneg measurableSet_Iic fun y _ => by positivity

theorem Phi_le_one (x : ℝ) : Phi x ≤ 1 := by
  have hint : ∫ y, phiDensity y = 1 := by
    have h := RoughHeatKernel.integral_heatKernel (t := 1) one_pos
    rw [← h]
    congr 1
    ext y
    simp only [phiDensity, RoughHeatKernel.heatKernel]
    rw [mul_one, one_div]
    congr 2
    ring
  rw [Phi_eq_integral_phiDensity, ← hint]
  exact setIntegral_le_integral integrable_phiDensity
    (Filter.Eventually.of_forall fun y => by unfold phiDensity; positivity)

/-- The majorant `h(r) = Λ²/√(4πνr) + Λ⁴/(2ν) e^{Λ⁴r/(4ν)}` of `k(r)` (proof of `T2:Growth(2)`,
using `Φ ≤ 1` in `E:K`). -/
@[expose] noncomputable def hK (ν lam r : ℝ) : ℝ :=
  lam ^ 2 / √(4 * π * ν * r) + lam ^ 4 / (2 * ν) * exp (lam ^ 4 * r / (4 * ν))

/-- `0 ≤ 𝓚(r,z) ≤ G_{ν/2}(r,z) h(r)` for `r > 0` (from `E:K` and `0 ≤ Φ ≤ 1`). -/
theorem K_le_G_mul_hK {ν lam : ℝ} (hν : 0 < ν) {r : ℝ} (hr : 0 < r) (z : ℝ) :
    0 ≤ K ν lam r z ∧ K ν lam r z ≤ G (ν / 2) r z * hK ν lam r := by
  rw [K_eq hν hr z, hK]
  have hG := G_nonneg (ν / 2) r z
  have hA : 0 ≤ lam ^ 2 / √(4 * π * ν * r) := by positivity
  have hB : 0 ≤ lam ^ 4 / (2 * ν) * exp (lam ^ 4 * r / (4 * ν)) := by positivity
  have h0 := Phi_nonneg (lam ^ 2 * √(r / (2 * ν)))
  have h1 := Phi_le_one (lam ^ 2 * √(r / (2 * ν)))
  refine ⟨by positivity, mul_le_mul_of_nonneg_left ?_ hG⟩
  have := mul_le_mul_of_nonneg_left h1 hB
  linarith

/-- Display `E2:ExpDivSqrt` (in the form used): `∫₀ᵗ e^{a(t−s)} s^{−1/2} ds ≤ √(π/a) e^{at}`,
here as `e^{at} ∫₀ᵗ s^{−1/2} e^{−as} ds ≤ e^{at} (1/a)^{1/2} Γ(1/2)`. -/
theorem integral_rpow_mul_exp_le {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, s ^ ((1 / 2 : ℝ) - 1) * exp (-(a * s)) ≤
      (1 / a) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2) := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2) ha,
    intervalIntegral.integral_of_le ht]
  refine setIntegral_mono_set ?_ ?_ (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
  · have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 / 2 : ℝ) - 1) (p := 1) (b := a)
      (by norm_num) one_pos ha
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hs) _) (Real.exp_pos _).le

/-- The time integral in the proof of `T2:Growth(2)`:
`∫₀ᵗ h(t−s)/√s ds ≤ Λ²√π/√ν · (1/2 + e^{Λ⁴t/(4ν)})`, together with its integrability. -/
theorem hK_integral {ν lam t : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) (ht : 0 < t) :
    IntervalIntegrable (fun s => hK ν lam (t - s) / √s) volume 0 t ∧
      ∫ s in (0 : ℝ)..t, hK ν lam (t - s) / √s ≤
        lam ^ 2 * √π / √ν * (1 / 2 + exp (lam ^ 4 * t / (4 * ν))) := by
  have hl2 : 0 < lam ^ 2 := by positivity
  set a := lam ^ 4 / (4 * ν) with ha_def
  have ha : 0 < a := by positivity
  set c1 := lam ^ 2 / √(4 * π * ν)
  set c2 := lam ^ 4 / (2 * ν)
  set g : ℝ → ℝ := fun s => c1 * (s ^ ((1 / 2 : ℝ) - 1) * (t - s) ^ ((1 / 2 : ℝ) - 1)) +
    c2 * exp (a * t) * (s ^ ((1 / 2 : ℝ) - 1) * exp (-(a * s)))
  have e12 : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
  have heq : EqOn (fun s => hK ν lam (t - s) / √s) g (uIoo 0 t) := by
    intro s hs
    rw [uIoo_of_le ht.le] at hs
    have hs0 : 0 < s := hs.1
    have hts : 0 < t - s := by linarith [hs.2]
    simp only [g, hK, c1, c2, e12]
    rw [Real.rpow_neg hs0.le, Real.rpow_neg hts.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 * π * ν) (t - s),
      show lam ^ 4 * (t - s) / (4 * ν) = a * t + -(a * s) by rw [ha_def]; ring, Real.exp_add]
    have : 0 < √s := Real.sqrt_pos.mpr hs0
    have : 0 < √(t - s) := Real.sqrt_pos.mpr hts
    have : 0 < √(4 * π * ν) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  have hg1 : IntervalIntegrable (fun s => s ^ ((1 / 2 : ℝ) - 1) * (t - s) ^ ((1 / 2 : ℝ) - 1))
      volume 0 t := RoughHeatKernel.intervalIntegrable_rpow_mul_sub_rpow (by norm_num) (by norm_num) ht
  have hg2 : IntervalIntegrable (fun s => s ^ ((1 / 2 : ℝ) - 1) * exp (-(a * s))) volume 0 t :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).mul_continuousOn
      (by fun_prop)
  have hgi : IntervalIntegrable g volume 0 t := (hg1.const_mul c1).add (hg2.const_mul _)
  refine ⟨hgi.congr_uIoo heq.symm, ?_⟩
  have hint : ∫ s in (0 : ℝ)..t, hK ν lam (t - s) / √s = ∫ s in (0 : ℝ)..t, g s :=
    intervalIntegral.integral_congr_uIoo heq
  rw [hint, intervalIntegral.integral_add (hg1.const_mul c1) (hg2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rpow_mul_sub_rpow (by norm_num) (by norm_num) ht]
  have hbound := integral_rpow_mul_exp_le ha ht.le
  have hc2 : 0 ≤ c2 * exp (a * t) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hbound hc2
  refine (add_le_add le_rfl hstep).trans (le_of_eq ?_)
  -- identify the constants
  have hG1 : Real.Gamma ((1 / 2 : ℝ) + 1 / 2) = 1 := by norm_num
  have hsa : (1 / a) ^ (1 / 2 : ℝ) = 2 * √ν / lam ^ 2 := by
    rw [← Real.sqrt_eq_rpow]
    have : 1 / a = (2 * √ν / lam ^ 2) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hν.le, ha_def]
      field_simp
      ring
    rw [this, Real.sqrt_sq (by positivity)]
  have hpi : √(4 * π * ν) = 2 * √π * √ν := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hG1, show (1 / 2 : ℝ) + 1 / 2 - 1 = 0 by norm_num, Real.rpow_zero, Real.Gamma_one_half_eq,
    hsa, ha_def]
  simp only [c1, c2, hpi]
  have : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have : 0 < √ν := Real.sqrt_pos.mpr hν
  have hpp : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hνν : √ν * √ν = ν := Real.mul_self_sqrt hν.le
  field_simp
  rw [Real.sq_sqrt hν.le]
  ring

end GrowthUpper

/-- **The upper envelope in the proof of Chen–Dalang (2015), Theorem `T2:Growth(2)`** (the
display after "By Lemma `L2:InDt-G`, `E2:BetaInt` and `E2:ExpDivSqrt`"), with the constants
generalised: if `f(t,x) ≤ a J₀²(t,x) + (J₀² ⋆ 𝓚_Λ)(t,x)` for all `t > 0` (`E2:SecMom-Up` with
`ϑ = 0`; `a = 1`, `Λ = Lip_ρ` for `p = 2`; `a = 2`, `Λ = √2 z_p Lip_ρ` for even `p`), then
`f(t,x) ≤ (aC²/(2πνt) + C²Λ²/(2√π ν^{3/2} √t) (1/2 + e^{Λ⁴t/(4ν)})) e^{−2β|x| + νβ²t}`. -/
theorem upper_envelope {ν β a lam : ℝ} (hν : 0 < ν) (hβ : 0 < β) (ha : 0 ≤ a) (hlam : lam ≠ 0)
    {μ : Measure ℝ} (hI : Integrable (fun y => exp (β * |y|)) μ) {C : ℝ}
    (hC : C = ∫ y, exp (β * |y|) ∂μ) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t > 0, ∀ x, f t x ≤
      a * J0 ν μ t x ^ 2 + stConv (fun s y => J0 ν μ s y ^ 2) (K ν lam) t x) :
    ∀ t > 0, ∀ x, f t x ≤
      (a * C ^ 2 / (2 * π * ν * t) + C ^ 2 * lam ^ 2 / (2 * √π * ν ^ (3 / 2 : ℝ) * √t) *
        (1 / 2 + exp (lam ^ 4 * t / (4 * ν)))) * exp (-2 * β * |x| + ν * β ^ 2 * t) := by
  intro t ht x
  obtain ⟨hint, hle⟩ := hK_integral hν hlam ht
  have h1 := L2_InDt_G_J0 hν hβ ht hI hC x
  have h2 := stConv_J0_sq_le hν hβ ht hI (fun r hr z => K_le_G_mul_hK (lam := lam) hν hr z)
    hint x
  rw [← hC] at h2
  have hE := Real.exp_pos (-2 * β * |x| + ν * β ^ 2 * t)
  have hν32 : ν ^ (3 / 2 : ℝ) = ν * √ν := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hν, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  calc f t x ≤ a * J0 ν μ t x ^ 2 + stConv (fun s y => J0 ν μ s y ^ 2) (K ν lam) t x := hf t ht x
    _ ≤ a * (C ^ 2 / (2 * π * ν * t) * exp (-2 * β * |x| + ν * β ^ 2 * t)) +
          C ^ 2 / (2 * π * ν * √t) * exp (-2 * β * |x| + ν * β ^ 2 * t) *
            ∫ s in (0 : ℝ)..t, hK ν lam (t - s) / √s :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) h2
    _ ≤ a * (C ^ 2 / (2 * π * ν * t) * exp (-2 * β * |x| + ν * β ^ 2 * t)) +
          C ^ 2 / (2 * π * ν * √t) * exp (-2 * β * |x| + ν * β ^ 2 * t) *
            (lam ^ 2 * √π / √ν * (1 / 2 + exp (lam ^ 4 * t / (4 * ν)))) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hle (by positivity))
    _ = _ := by
        rw [hν32]
        have : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
        have : 0 < √ν := Real.sqrt_pos.mpr hν
        have : 0 < √t := Real.sqrt_pos.mpr ht
        have hpp : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
        field_simp
        linear_combination (C ^ 2 * t * lam ^ 2 * (1 + 2 * exp (t * lam ^ 4 / (ν * 4)))) * hpp

/-- **Exponential form of the upper envelope** (input for the upper growth index): under the
hypotheses of `upper_envelope`, there are `A` and `T₀` with
`f(t,x) ≤ A e^{(νβ² + Λ⁴/(4ν)) t − 2β|x|}` for all `t ≥ T₀` and all `x`. -/
theorem upper_envelope_exp {ν β a lam : ℝ} (hν : 0 < ν) (hβ : 0 < β) (ha : 0 ≤ a)
    (hlam : lam ≠ 0) {μ : Measure ℝ} (hI : Integrable (fun y => exp (β * |y|)) μ) {C : ℝ}
    (hC : C = ∫ y, exp (β * |y|) ∂μ) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t > 0, ∀ x, f t x ≤
      a * J0 ν μ t x ^ 2 + stConv (fun s y => J0 ν μ s y ^ 2) (K ν lam) t x) :
    ∃ A T₀ : ℝ, ∀ t ≥ T₀, ∀ x,
      f t x ≤ A * exp ((ν * β ^ 2 + lam ^ 4 / (4 * ν)) * t - 2 * β * |x|) := by
  set D := C ^ 2 * lam ^ 2 / (2 * √π * ν ^ (3 / 2 : ℝ))
  refine ⟨a * C ^ 2 / (2 * π * ν) + D * (3 / 2), 1, fun t ht x => ?_⟩
  have ht0 : 0 < t := by linarith
  have hD : 0 ≤ D := by positivity
  have hb : 1 ≤ exp (lam ^ 4 * t / (4 * ν)) := Real.one_le_exp (by positivity)
  have hst : 1 ≤ √t := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt ht
  have hE := Real.exp_pos (-2 * β * |x| + ν * β ^ 2 * t)
  refine (upper_envelope hν hβ ha hlam hI hC hf t ht0 x).trans ?_
  have hsplit : exp ((ν * β ^ 2 + lam ^ 4 / (4 * ν)) * t - 2 * β * |x|) =
      exp (lam ^ 4 * t / (4 * ν)) * exp (-2 * β * |x| + ν * β ^ 2 * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hE.le
  have hT1 : a * C ^ 2 / (2 * π * ν * t) ≤ a * C ^ 2 / (2 * π * ν) * exp (lam ^ 4 * t / (4 * ν)) :=
    calc a * C ^ 2 / (2 * π * ν * t) ≤ a * C ^ 2 / (2 * π * ν) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (le_mul_of_one_le_right (by positivity) ht)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hb
  have hT2 : C ^ 2 * lam ^ 2 / (2 * √π * ν ^ (3 / 2 : ℝ) * √t) *
      (1 / 2 + exp (lam ^ 4 * t / (4 * ν))) ≤ D * (3 / 2) * exp (lam ^ 4 * t / (4 * ν)) := by
    have h1 : C ^ 2 * lam ^ 2 / (2 * √π * ν ^ (3 / 2 : ℝ) * √t) ≤ D := by
      rw [← div_div]
      exact div_le_self hD hst
    calc C ^ 2 * lam ^ 2 / (2 * √π * ν ^ (3 / 2 : ℝ) * √t) *
          (1 / 2 + exp (lam ^ 4 * t / (4 * ν)))
        ≤ D * (3 / 2 * exp (lam ^ 4 * t / (4 * ν))) :=
          mul_le_mul h1 (by linarith) (by positivity) hD
      _ = _ := by ring
  linarith

end ChenDalang15

end
