module

public import ChenDalang15.Eac
public import ChenDalang15.PhiE
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Properties of `E_{a,β}` (Chen–Dalang 2015, Proposition `P2:E`) and Lemma `L2:LogRel`

`E_{a,β}(x) = e^{-βx} Φ((aβ − x)/√a) + e^{βx} Φ((aβ + x)/√a)` (`Eac`, display `E2:Eac`).

Route. Everything comparative is reduced to the one Gaussian half-line integral
`∫_{(-∞,0]} e^{cy} G_ν(t, x − y) dy = e^{cx + c²νt/2} Φ(−(x + νt c)/√(νt))`
(`EacProps.integral_Iic_exp_mul_G_sub`: complete the square, translate, rescale). This gives

* (ii) the convolution identity, splitting `ℝ = (-∞,0] ∪ (0,∞)`;
* (iv), `β ≤ 0`: `e^{β²a/2}(e^{βx} − E_{a,β}(x)) = ∫_{y≤0} (e^{βy} − e^{−βy}) G_a(1,x−y) dy ≥ 0`
  (this replaces the paper's l'Hôpital limit argument);
* (v): `E'_{a,β}(x) = β (e^{βx}Φ(u₊) − e^{−βx}Φ(u₋))` and the bracket has the sign of `x`
  because `G` is radially nonincreasing (the paper's convolution argument).

(iii) and (vi) are direct differentiation, using
`e^{∓βx} φ((aβ ∓ x)/√a) = (2π)^{-1/2} e^{−(a²β²+x²)/(2a)}`.

Findings recorded here:
* (v), `β < 0`: the paper states `E''_{a,β}(0) ≤ 0`; it is in fact `< 0`
  (`Eac_deriv2_zero_neg`, via the Mills-type inequality `φ(z) + zΦ(z) > 0`, itself derived from
  the paper's `≤ 0` and the strict monotonicity of `φ(z) + zΦ(z)`).
* (i) holds for every `a`; the strict upper bound in (iv) holds for every `a, β`.
* `L2:LogRel`: the claim `inf_{s∈[0,a)} f = lim_{s→a} f = (b−a) log(b−a)` is FALSE; the limit and
  the infimum are `0` (`logRel_tendsto`, `logRel_sInf`; refutations `logRel_inf_claim_false`,
  `logRel_lim_claim_false` at `a = 1, b = 3`). The paper uses only the supremum
  (Proposition `P2:G-Margin`), which is correct (`logRel_isGreatest`).
-/

set_option autoImplicit false

public section

namespace ChenDalang15

open Real MeasureTheory Set Filter Topology

namespace EacProps

/-! ### `Φ` -/

theorem phiDensity_neg (y : ℝ) : phiDensity (-y) = phiDensity y := by
  simp [phiDensity]

theorem phiDensity_pos (y : ℝ) : 0 < phiDensity y := by
  unfold phiDensity; positivity

theorem Phi_nonneg (x : ℝ) : 0 ≤ Phi x := by
  rw [Phi_eq_integral_phiDensity]
  exact setIntegral_nonneg measurableSet_Iic fun y _ => (phiDensity_pos y).le

theorem strictMono_Phi : StrictMono Phi :=
  strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_Phi x).deriv]; exact phiDensity_pos x

theorem monotone_Phi : Monotone Phi := strictMono_Phi.monotone

theorem Phi_pos (x : ℝ) : 0 < Phi x :=
  lt_of_le_of_lt (Phi_nonneg (x - 1)) (strictMono_Phi (by linarith))

/-- `∫_{(c,∞)} φ = Φ(-c)`. -/
theorem integral_Ioi_phiDensity (c : ℝ) : ∫ y in Ioi c, phiDensity y = Phi (-c) := by
  rw [Phi_eq_integral_phiDensity, ← integral_comp_neg_Ioi]
  simp only [phiDensity_neg]

/-- `∫_ℝ φ = 1`. -/
theorem integral_phiDensity : ∫ y, phiDensity y = 1 := by
  have h := integral_gaussian (1 / 2)
  have hc : ∀ y : ℝ, phiDensity y = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2) * y ^ 2) := by
    intro y; simp only [phiDensity]; congr 2; ring
  simp_rw [hc]
  rw [integral_const_mul, h, show π / (1 / 2) = 2 * π by ring]
  have : 0 < Real.sqrt (2 * π) := by positivity
  field_simp

/-- `Φ(x) + Φ(-x) = 1`. -/
theorem Phi_add_Phi_neg (x : ℝ) : Phi x + Phi (-x) = 1 := by
  have h := intervalIntegral.integral_Iic_add_Ioi (b := x)
    integrable_phiDensity.integrableOn integrable_phiDensity.integrableOn
  rw [← Phi_eq_integral_phiDensity, integral_Ioi_phiDensity] at h
  rw [h, integral_phiDensity]

/-! ### The heat kernel as a scaled Gaussian density -/

theorem G_eq_phiDensity {ν t : ℝ} (h : 0 < ν * t) (w : ℝ) :
    G ν t w = (Real.sqrt (ν * t))⁻¹ * phiDensity ((Real.sqrt (ν * t))⁻¹ * w) := by
  have hs : 0 < Real.sqrt (ν * t) := Real.sqrt_pos.mpr h
  have hs2 : Real.sqrt (ν * t) ^ 2 = ν * t := Real.sq_sqrt h.le
  unfold G phiDensity
  rw [show 2 * π * ν * t = (2 * π) * (ν * t) by ring,
    Real.sqrt_mul (by positivity) (ν * t)]
  have he : -((Real.sqrt (ν * t))⁻¹ * w) ^ 2 / 2 = -w ^ 2 / (2 * ν * t) := by
    rw [mul_pow, inv_pow, hs2]
    field_simp
  rw [he]
  field_simp

theorem G_nonneg (ν t w : ℝ) : 0 ≤ G ν t w := by
  unfold G; positivity

theorem integrable_G {ν t : ℝ} (h : 0 < ν * t) : Integrable (G ν t) := by
  have hb : 0 < 1 / (2 * ν * t) := by
    have : 0 < 2 * ν * t := by nlinarith
    positivity
  refine ((integrable_exp_neg_mul_sq hb).const_mul (1 / Real.sqrt (2 * π * ν * t))).congr
    (Eventually.of_forall fun w => ?_)
  simp only [G]
  congr 2
  ring

/-- `∫_{(m,∞)} G_ν(t,w) dw = Φ(-m/√(νt))`. -/
theorem integral_Ioi_G {ν t : ℝ} (h : 0 < ν * t) (m : ℝ) :
    ∫ w in Ioi m, G ν t w = Phi (-(m / Real.sqrt (ν * t))) := by
  have hs : 0 < Real.sqrt (ν * t) := Real.sqrt_pos.mpr h
  simp_rw [G_eq_phiDensity h]
  rw [integral_const_mul, integral_comp_mul_left_Ioi phiDensity m (inv_pos.mpr hs),
    smul_eq_mul, integral_Ioi_phiDensity, inv_inv, ← mul_assoc, inv_mul_cancel₀ hs.ne',
    one_mul, inv_mul_eq_div]

/-- `∫_{(-∞,0]} G_ν(t, m − y) dy = Φ(-m/√(νt))`. -/
theorem integral_Iic_G_sub {ν t : ℝ} (h : 0 < ν * t) (m : ℝ) :
    ∫ y in Iic (0 : ℝ), G ν t (m - y) = Phi (-(m / Real.sqrt (ν * t))) := by
  rw [← integral_indicator measurableSet_Iic]
  have hind : (Iic (0 : ℝ)).indicator (fun y => G ν t (m - y)) =
      fun y => (Ici m).indicator (G ν t) (m - y) := by
    funext y
    by_cases hy : y ≤ 0
    · have : m - y ∈ Ici m := by simp only [mem_Ici]; linarith
      simp [indicator_of_mem (show y ∈ Iic (0 : ℝ) from hy), indicator_of_mem this]
    · have : m - y ∉ Ici m := by simp only [mem_Ici]; linarith
      simp [indicator_of_notMem (show y ∉ Iic (0 : ℝ) from hy), indicator_of_notMem this]
  rw [hind, integral_sub_left_eq_self (fun w => (Ici m).indicator (G ν t) w),
    integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_Ioi_G h]

/-- Completing the square: `e^{cy} G_ν(t, x−y) = e^{cx + c²νt/2} G_ν(t, x + νt c − y)`. -/
theorem exp_mul_G_sub {ν t : ℝ} (h : 0 < ν * t) (c x y : ℝ) :
    Real.exp (c * y) * G ν t (x - y) =
      Real.exp (c * x + c ^ 2 * (ν * t) / 2) * G ν t (x + ν * t * c - y) := by
  unfold G
  have hν : ν ≠ 0 := left_ne_zero_of_mul h.ne'
  have ht : t ≠ 0 := right_ne_zero_of_mul h.ne'
  rw [mul_left_comm, mul_left_comm (Real.exp _), ← Real.exp_add, ← Real.exp_add]
  congr 2
  field_simp
  ring

theorem integrable_exp_mul_G_sub {ν t : ℝ} (h : 0 < ν * t) (c x : ℝ) :
    Integrable (fun y => Real.exp (c * y) * G ν t (x - y)) := by
  simp_rw [exp_mul_G_sub h c x]
  exact ((integrable_G h).comp_sub_left (x + ν * t * c)).const_mul _

/-- The basic half-line integral:
`∫_{(-∞,0]} e^{cy} G_ν(t, x − y) dy = e^{cx + c²νt/2} Φ(−(x + νt c)/√(νt))`. -/
theorem integral_Iic_exp_mul_G_sub {ν t : ℝ} (h : 0 < ν * t) (c x : ℝ) :
    ∫ y in Iic (0 : ℝ), Real.exp (c * y) * G ν t (x - y) =
      Real.exp (c * x + c ^ 2 * (ν * t) / 2) *
        Phi (-((x + ν * t * c) / Real.sqrt (ν * t))) := by
  simp_rw [exp_mul_G_sub h c x]
  rw [integral_const_mul, integral_Iic_G_sub h]

theorem G_neg (ν t w : ℝ) : G ν t (-w) = G ν t w := by
  simp [G]

/-- `G_ν(t,·)` is radially nonincreasing. -/
theorem G_le_G_of_sq_le {ν t : ℝ} (h : 0 < ν * t) {w₁ w₂ : ℝ} (hw : w₁ ^ 2 ≤ w₂ ^ 2) :
    G ν t w₂ ≤ G ν t w₁ := by
  unfold G
  have h2 : 0 < 2 * ν * t := by nlinarith
  gcongr

/-! ### The three half-line integrals behind `E_{a,β}` (with `a = νt`) -/

/-- `∫_{(-∞,0]} e^{-βy} G(x−y) dy = e^{β²a/2} e^{-βx} Φ((aβ − x)/√a)`. -/
theorem integral_Iic_A {ν t : ℝ} (h : 0 < ν * t) (β x : ℝ) :
    ∫ y in Iic (0 : ℝ), Real.exp (-β * y) * G ν t (x - y) =
      Real.exp (β ^ 2 * (ν * t) / 2) *
        (Real.exp (-β * x) * Phi ((ν * t * β - x) / Real.sqrt (ν * t))) := by
  rw [integral_Iic_exp_mul_G_sub h, neg_sq, Real.exp_add]
  rw [show -((x + ν * t * -β) / Real.sqrt (ν * t)) = (ν * t * β - x) / Real.sqrt (ν * t) by ring]
  ring

/-- `∫_{(-∞,0]} e^{-βy} G(−x−y) dy = e^{β²a/2} e^{βx} Φ((aβ + x)/√a)`. -/
theorem integral_Iic_B {ν t : ℝ} (h : 0 < ν * t) (β x : ℝ) :
    ∫ y in Iic (0 : ℝ), Real.exp (-β * y) * G ν t (-x - y) =
      Real.exp (β ^ 2 * (ν * t) / 2) *
        (Real.exp (β * x) * Phi ((ν * t * β + x) / Real.sqrt (ν * t))) := by
  rw [integral_Iic_exp_mul_G_sub h, neg_sq, Real.exp_add]
  rw [show -((-x + ν * t * -β) / Real.sqrt (ν * t)) = (ν * t * β + x) / Real.sqrt (ν * t) by ring,
    show -β * -x = β * x by ring]
  ring

/-- `∫_{(-∞,0]} e^{βy} G(x−y) dy = e^{β²a/2} e^{βx} (1 − Φ((aβ + x)/√a))`. -/
theorem integral_Iic_C {ν t : ℝ} (h : 0 < ν * t) (β x : ℝ) :
    ∫ y in Iic (0 : ℝ), Real.exp (β * y) * G ν t (x - y) =
      Real.exp (β ^ 2 * (ν * t) / 2) *
        (Real.exp (β * x) * (1 - Phi ((ν * t * β + x) / Real.sqrt (ν * t)))) := by
  rw [integral_Iic_exp_mul_G_sub h, Real.exp_add]
  have := Phi_add_Phi_neg ((ν * t * β + x) / Real.sqrt (ν * t))
  rw [show -((x + ν * t * β) / Real.sqrt (ν * t)) = -((ν * t * β + x) / Real.sqrt (ν * t)) by
    ring, show 1 - Phi ((ν * t * β + x) / Real.sqrt (ν * t)) =
      Phi (-((ν * t * β + x) / Real.sqrt (ν * t))) by linarith]
  ring

theorem integrable_exp_mul_abs_G_sub {ν t : ℝ} (h : 0 < ν * t) (β x : ℝ) :
    Integrable (fun y => Real.exp (β * |y|) * G ν t (x - y)) := by
  refine Integrable.mono' ((integrable_exp_mul_G_sub h β x).add
    (integrable_exp_mul_G_sub h (-β) x)) ?_ (Eventually.of_forall fun y => ?_)
  · exact (Continuous.aestronglyMeasurable (by unfold G; fun_prop))
  · have hG := G_nonneg ν t (x - y)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      nlinarith [Real.exp_pos (-β * y)]
    · rw [abs_of_nonpos hy, show β * -y = -β * y by ring]
      nlinarith [Real.exp_pos (β * y)]

end EacProps

/-- **Proposition `P2:E`(i)**: `E_{a,0} ≡ 1` (true for every `a`; the paper assumes `a > 0`). -/
theorem Eac_zero_beta (a x : ℝ) : Eac a 0 x = 1 := by
  unfold Eac
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, mul_zero, zero_sub, zero_add]
  rw [neg_div, add_comm]
  exact EacProps.Phi_add_Phi_neg _

/-- **Proposition `P2:E`(ii)**, integrability part: `y ↦ e^{β|y|} G_ν(t, x − y)` is integrable
for every `β`. -/
theorem integrable_exp_mul_abs_mul_G {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (β x : ℝ) :
    Integrable (fun y => Real.exp (β * |y|) * G ν t (x - y)) :=
  EacProps.integrable_exp_mul_abs_G_sub (mul_pos hν ht) β x

/-- **Proposition `P2:E`(ii)**: `(e^{β|·|} * G_ν(t,·))(x) = e^{β²νt/2} E_{νt,β}(x)`. -/
theorem integral_exp_mul_abs_mul_G {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (β x : ℝ) :
    ∫ y, Real.exp (β * |y|) * G ν t (x - y) =
      Real.exp (β ^ 2 * ν * t / 2) * Eac (ν * t) β x := by
  have h := mul_pos hν ht
  have hI := EacProps.integrable_exp_mul_abs_G_sub h β x
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hI.integrableOn hI.integrableOn]
  have h1 : ∫ y in Iic (0 : ℝ), Real.exp (β * |y|) * G ν t (x - y) =
      ∫ y in Iic (0 : ℝ), Real.exp (-β * y) * G ν t (x - y) := by
    refine setIntegral_congr_fun measurableSet_Iic fun y hy => ?_
    rw [abs_of_nonpos hy, show β * -y = -β * y by ring]
  have h2 : ∫ y in Ioi (0 : ℝ), Real.exp (β * |y|) * G ν t (x - y) =
      ∫ y in Ioi (0 : ℝ), Real.exp (-β * -y) * G ν t (-x - -y) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    rw [abs_of_pos hy, show -x - -y = -(x - y) by ring, EacProps.G_neg,
      show -β * -y = β * y by ring]
  have h3 := integral_comp_neg_Ioi (0 : ℝ) (fun z => Real.exp (-β * z) * G ν t (-x - z))
  rw [h1, h2, h3, neg_zero, EacProps.integral_Iic_A h,
    EacProps.integral_Iic_B h]
  unfold Eac
  rw [show β ^ 2 * ν * t / 2 = β ^ 2 * (ν * t) / 2 by ring]
  ring

end ChenDalang15

namespace ChenDalang15.EacProps

open Real MeasureTheory Set Filter Topology

/-! ### Comparison results via the half-line integrals (with `ν = a`, `t = 1`) -/

theorem integrable_exp_mul_G_sub' {a : ℝ} (ha : 0 < a) (c x : ℝ) :
    IntegrableOn (fun y => Real.exp (c * y) * G a 1 (x - y)) (Iic 0) :=
  (integrable_exp_mul_G_sub (by simpa using ha) c x).integrableOn

/-- For `β ≤ 0`: `E_{a,β}(x) ≤ e^{βx}` for every `x` (the half-line integral of
`(e^{βy} − e^{−βy}) G_a(1, x − y) ≥ 0` over `y ≤ 0`). -/
theorem Eac_le_exp_of_nonpos {a β : ℝ} (ha : 0 < a) (hβ : β ≤ 0) (x : ℝ) :
    Eac a β x ≤ Real.exp (β * x) := by
  have h : 0 < a * 1 := by simpa using ha
  have hA := integral_Iic_A h β x
  have hC := integral_Iic_C h β x
  simp only [mul_one] at hA hC
  have hsub := integral_sub (integrable_exp_mul_G_sub' ha β x)
    (integrable_exp_mul_G_sub' ha (-β) x)
  rw [hA, hC] at hsub
  have hnn : 0 ≤ ∫ y in Iic (0 : ℝ),
      (Real.exp (β * y) * G a 1 (x - y) - Real.exp (-β * y) * G a 1 (x - y)) := by
    refine setIntegral_nonneg measurableSet_Iic fun y hy => ?_
    have hy : y ≤ 0 := hy
    have : Real.exp (-β * y) ≤ Real.exp (β * y) := Real.exp_le_exp.mpr (by nlinarith)
    have hG := G_nonneg a 1 (x - y)
    nlinarith
  rw [hsub] at hnn
  have hE : 0 < Real.exp (β ^ 2 * a / 2) := Real.exp_pos _
  unfold Eac
  nlinarith

/-- For every `β` and `x ≥ 0`: `e^{−βx} Φ((aβ − x)/√a) ≤ e^{βx} Φ((aβ + x)/√a)` (the heat kernel
is radially nonincreasing). -/
theorem exp_neg_mul_Phi_le {a : ℝ} (ha : 0 < a) (β : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-β * x) * Phi ((a * β - x) / Real.sqrt a) ≤
      Real.exp (β * x) * Phi ((a * β + x) / Real.sqrt a) := by
  have h : 0 < a * 1 := by simpa using ha
  have hA := integral_Iic_A h β x
  have hB := integral_Iic_B h β x
  simp only [mul_one] at hA hB
  have hle : ∫ y in Iic (0 : ℝ), Real.exp (-β * y) * G a 1 (x - y) ≤
      ∫ y in Iic (0 : ℝ), Real.exp (-β * y) * G a 1 (-x - y) :=
    setIntegral_mono_on (integrable_exp_mul_G_sub' ha (-β) x)
      (integrable_exp_mul_G_sub' ha (-β) (-x)) measurableSet_Iic fun y hy => by
        have hy : y ≤ 0 := hy
        have := G_le_G_of_sq_le h (w₁ := -x - y) (w₂ := x - y) (by nlinarith)
        exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
  rw [hA, hB] at hle
  exact le_of_mul_le_mul_left hle (Real.exp_pos _)

theorem Eac_neg (a β x : ℝ) : Eac a β (-x) = Eac a β x := by
  unfold Eac
  rw [show -β * -x = β * x by ring, show β * -x = -β * x by ring, sub_neg_eq_add,
    ← sub_eq_add_neg]
  ring

theorem Eac_pos {a : ℝ} (β x : ℝ) : 0 < Eac a β x := by
  unfold Eac
  have := Phi_pos ((a * β - x) / Real.sqrt a)
  have := Phi_pos ((a * β + x) / Real.sqrt a)
  positivity

/-- `E_{a,β}(x) + E_{a,−β}(x) = e^{βx} + e^{−βx}`. -/
theorem Eac_add_Eac_neg (a β x : ℝ) :
    Eac a β x + Eac a (-β) x = Real.exp (β * x) + Real.exp (-β * x) := by
  unfold Eac
  have h1 := Phi_add_Phi_neg ((a * β - x) / Real.sqrt a)
  have h2 := Phi_add_Phi_neg ((a * β + x) / Real.sqrt a)
  rw [show (a * -β - x) / Real.sqrt a = -((a * β + x) / Real.sqrt a) by ring,
    show (a * -β + x) / Real.sqrt a = -((a * β - x) / Real.sqrt a) by ring, neg_neg]
  linear_combination Real.exp (-β * x) * h1 + Real.exp (β * x) * h2

end ChenDalang15.EacProps

namespace ChenDalang15.EacProps

open Real MeasureTheory Set Filter Topology

/-! ### Derivatives in `x` -/

/-- `e^{∓βx} φ((aβ ∓ x)/√a) = (2π)^{-1/2} e^{-(a²β²+x²)/(2a)}`. -/
theorem exp_mul_phiDensity {a : ℝ} (ha : 0 < a) (β x s : ℝ) (hs : s = 1 ∨ s = -1) :
    Real.exp (-(s * β) * x) * phiDensity ((a * β - s * x) / Real.sqrt a) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-(a ^ 2 * β ^ 2 + x ^ 2) / (2 * a)) := by
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hs0 : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  unfold phiDensity
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  rw [div_pow, hsa]
  field_simp
  linear_combination (-(x ^ 2)) * hs2

theorem exp_neg_mul_phiDensity_sub {a : ℝ} (ha : 0 < a) (β x : ℝ) :
    Real.exp (-β * x) * phiDensity ((a * β - x) / Real.sqrt a) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-(a ^ 2 * β ^ 2 + x ^ 2) / (2 * a)) := by
  simpa using exp_mul_phiDensity ha β x 1 (Or.inl rfl)

theorem exp_mul_phiDensity_add {a : ℝ} (ha : 0 < a) (β x : ℝ) :
    Real.exp (β * x) * phiDensity ((a * β + x) / Real.sqrt a) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-(a ^ 2 * β ^ 2 + x ^ 2) / (2 * a)) := by
  simpa [sub_eq_add_neg] using exp_mul_phiDensity ha β x (-1) (Or.inr rfl)

theorem hasDerivAt_Phi_sub (a β x : ℝ) :
    HasDerivAt (fun x => Phi ((a * β - x) / Real.sqrt a))
      (phiDensity ((a * β - x) / Real.sqrt a) * (-1 / Real.sqrt a)) x :=
  (hasDerivAt_Phi _).comp x (((hasDerivAt_id x).const_sub (a * β)).div_const _)

theorem hasDerivAt_Phi_add (a β x : ℝ) :
    HasDerivAt (fun x => Phi ((a * β + x) / Real.sqrt a))
      (phiDensity ((a * β + x) / Real.sqrt a) * (1 / Real.sqrt a)) x :=
  (hasDerivAt_Phi _).comp x (((hasDerivAt_id x).const_add (a * β)).div_const _)

theorem hasDerivAt_exp_mul (c x : ℝ) :
    HasDerivAt (fun x => Real.exp (c * x)) (Real.exp (c * x) * c) x := by
  simpa using ((hasDerivAt_id x).const_mul c).exp

/-- `2 (2π)^{-1/2}/√a = √(2/(πa))`. -/
theorem sqrt_two_div_pi_mul {a : ℝ} (ha : 0 < a) :
    Real.sqrt (2 / (π * a)) = 2 * (Real.sqrt (2 * π))⁻¹ / Real.sqrt a := by
  rw [show 2 / (π * a) = 2 ^ 2 / ((2 * π) * a) by field_simp,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by norm_num),
    Real.sqrt_mul (by positivity)]
  field_simp

end ChenDalang15.EacProps

namespace ChenDalang15

open Real Set Filter Topology

/-- **Proposition `P2:E`(iii)**, first derivative:
`E'_{a,β}(x) = −β e^{−βx} Φ((aβ − x)/√a) + β e^{βx} Φ((aβ + x)/√a)`. -/
theorem Eac_hasDerivAt {a : ℝ} (ha : 0 < a) (β x : ℝ) :
    HasDerivAt (Eac a β)
      (-β * Real.exp (-β * x) * Phi ((a * β - x) / Real.sqrt a) +
        β * Real.exp (β * x) * Phi ((a * β + x) / Real.sqrt a)) x := by
  have h := ((EacProps.hasDerivAt_exp_mul (-β) x).mul (EacProps.hasDerivAt_Phi_sub a β x)).add
    ((EacProps.hasDerivAt_exp_mul β x).mul (EacProps.hasDerivAt_Phi_add a β x))
  have h1 := EacProps.exp_neg_mul_phiDensity_sub ha β x
  have h2 := EacProps.exp_mul_phiDensity_add ha β x
  convert h using 1
  · funext y
    simp only [Eac, Pi.add_apply, Pi.mul_apply]
  · linear_combination (1 / Real.sqrt a) * h1 - (1 / Real.sqrt a) * h2

/-- **Proposition `P2:E`(iii)**, second derivative:
`E''_{a,β}(x) = β √(2/(πa)) e^{−(a²β²+x²)/(2a)} + β² E_{a,β}(x)`. -/
theorem Eac_hasDerivAt_deriv {a : ℝ} (ha : 0 < a) (β x : ℝ) :
    HasDerivAt
      (fun x => -β * Real.exp (-β * x) * Phi ((a * β - x) / Real.sqrt a) +
        β * Real.exp (β * x) * Phi ((a * β + x) / Real.sqrt a))
      (β * Real.sqrt (2 / (π * a)) * Real.exp (-(a ^ 2 * β ^ 2 + x ^ 2) / (2 * a)) +
        β ^ 2 * Eac a β x) x := by
  have h := (((EacProps.hasDerivAt_exp_mul (-β) x).mul
    (EacProps.hasDerivAt_Phi_sub a β x)).const_mul (-β)).add
    (((EacProps.hasDerivAt_exp_mul β x).mul (EacProps.hasDerivAt_Phi_add a β x)).const_mul β)
  have h1 := EacProps.exp_neg_mul_phiDensity_sub ha β x
  have h2 := EacProps.exp_mul_phiDensity_add ha β x
  rw [EacProps.sqrt_two_div_pi_mul ha]
  convert h using 1
  · funext y
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  · unfold Eac
    linear_combination (-β / Real.sqrt a) * h1 + (-β / Real.sqrt a) * h2

namespace EacProps

/-- `E_{a,β}` has `x`-derivative `β (e^{βx}Φ(u₊) − e^{−βx}Φ(u₋))`, in a factored form. -/
theorem deriv_Eac {a : ℝ} (ha : 0 < a) (β : ℝ) :
    deriv (Eac a β) = fun x => β * (Real.exp (β * x) * Phi ((a * β + x) / Real.sqrt a) -
      Real.exp (-β * x) * Phi ((a * β - x) / Real.sqrt a)) := by
  funext x
  rw [(Eac_hasDerivAt ha β x).deriv]
  ring

theorem differentiable_Eac {a : ℝ} (ha : 0 < a) (β : ℝ) : Differentiable ℝ (Eac a β) :=
  fun x => (Eac_hasDerivAt ha β x).differentiableAt

theorem continuous_Eac {a : ℝ} (ha : 0 < a) (β : ℝ) : Continuous (Eac a β) :=
  (differentiable_Eac ha β).continuous

/-- The bracket `e^{βx}Φ(u₊) − e^{−βx}Φ(u₋)` is `≥ 0` for `x ≥ 0`. -/
theorem bracket_nonneg {a : ℝ} (ha : 0 < a) (β : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.exp (β * x) * Phi ((a * β + x) / Real.sqrt a) -
      Real.exp (-β * x) * Phi ((a * β - x) / Real.sqrt a) :=
  sub_nonneg.mpr (exp_neg_mul_Phi_le ha β hx)

/-- The bracket is `≤ 0` for `x ≤ 0`. -/
theorem bracket_nonpos {a : ℝ} (ha : 0 < a) (β : ℝ) {x : ℝ} (hx : x ≤ 0) :
    Real.exp (β * x) * Phi ((a * β + x) / Real.sqrt a) -
      Real.exp (-β * x) * Phi ((a * β - x) / Real.sqrt a) ≤ 0 := by
  have h := exp_neg_mul_Phi_le ha β (x := -x) (by linarith)
  rw [show -β * -x = β * x by ring, show β * -x = -β * x by ring, sub_neg_eq_add,
    ← sub_eq_add_neg] at h
  linarith

theorem monotoneOn_Ici_of_nonneg {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β) :
    MonotoneOn (Eac a β) (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (continuous_Eac ha β).continuousOn
    (differentiable_Eac ha β).differentiableOn fun x hx => ?_
  rw [interior_Ici] at hx
  rw [deriv_Eac ha]
  exact mul_nonneg hβ (bracket_nonneg ha β (le_of_lt hx))

theorem antitoneOn_Iic_of_nonneg {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β) :
    AntitoneOn (Eac a β) (Iic 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Iic 0) (continuous_Eac ha β).continuousOn
    (differentiable_Eac ha β).differentiableOn fun x hx => ?_
  rw [interior_Iic] at hx
  rw [deriv_Eac ha]
  exact mul_nonpos_of_nonneg_of_nonpos hβ (bracket_nonpos ha β (le_of_lt hx))

theorem antitoneOn_Ici_of_nonpos {a β : ℝ} (ha : 0 < a) (hβ : β ≤ 0) :
    AntitoneOn (Eac a β) (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (continuous_Eac ha β).continuousOn
    (differentiable_Eac ha β).differentiableOn fun x hx => ?_
  rw [interior_Ici] at hx
  rw [deriv_Eac ha]
  exact mul_nonpos_of_nonpos_of_nonneg hβ (bracket_nonneg ha β (le_of_lt hx))

theorem monotoneOn_Iic_of_nonpos {a β : ℝ} (ha : 0 < a) (hβ : β ≤ 0) :
    MonotoneOn (Eac a β) (Iic 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Iic 0) (continuous_Eac ha β).continuousOn
    (differentiable_Eac ha β).differentiableOn fun x hx => ?_
  rw [interior_Iic] at hx
  rw [deriv_Eac ha]
  exact mul_nonneg_of_nonpos_of_nonpos hβ (bracket_nonpos ha β (le_of_lt hx))

/-- For `β ≤ 0`: `E_{a,β}(x) ≤ e^{−|βx|}`. -/
theorem Eac_le_exp_neg_abs {a β : ℝ} (ha : 0 < a) (hβ : β ≤ 0) (x : ℝ) :
    Eac a β x ≤ Real.exp (-|β * x|) := by
  rcases le_total 0 (β * x) with h | h
  · rw [abs_of_nonneg h, ← Eac_neg]
    have := Eac_le_exp_of_nonpos ha hβ (-x)
    rwa [show β * -x = -(β * x) by ring] at this
  · rw [abs_of_nonpos h, neg_neg]
    exact Eac_le_exp_of_nonpos ha hβ x

theorem a_beta_div_sqrt (a β : ℝ) : a * β / Real.sqrt a = Real.sqrt a * β := by
  rw [mul_comm a β, mul_div_assoc, Real.div_sqrt, mul_comm]

/-- `E_{a,β}(x) ≥ e^{−|βx|} Φ((aβ + |x|)/√a)` for `β ≤ 0`. -/
theorem exp_neg_abs_mul_Phi_le_Eac {a β : ℝ} (hβ : β ≤ 0) (x : ℝ) :
    Real.exp (-|β * x|) * Phi ((a * β + |x|) / Real.sqrt a) ≤ Eac a β x := by
  unfold Eac
  have h1 := mul_nonneg (Real.exp_pos (-β * x)).le (Phi_nonneg ((a * β - x) / Real.sqrt a))
  have h2 := mul_nonneg (Real.exp_pos (β * x)).le (Phi_nonneg ((a * β + x) / Real.sqrt a))
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hβ hx), neg_neg]
    linarith
  · rw [abs_of_nonpos hx, abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos hβ hx),
      show -(β * x) = -β * x by ring, ← sub_eq_add_neg]
    linarith

/-- `φ' (z) = −z φ(z)`. -/
theorem hasDerivAt_phiDensity (z : ℝ) : HasDerivAt phiDensity (-z * phiDensity z) z := by
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-z) z := by
    have := ((hasDerivAt_pow 2 z).div_const 2).neg
    convert this using 1
    · funext y; simp only [Pi.neg_apply]; ring
    · simp
  have h := h1.exp.const_mul (Real.sqrt (2 * π))⁻¹
  convert h using 1
  · rfl
  · simp only [phiDensity]
    ring

/-- `h(z) = φ(z) + zΦ(z)` is strictly increasing (`h' = Φ > 0`). -/
theorem strictMono_phiDensity_add_mul_Phi : StrictMono fun z => phiDensity z + z * Phi z := by
  refine strictMono_of_deriv_pos fun z => ?_
  have h := (hasDerivAt_phiDensity z).add ((hasDerivAt_id z).mul (hasDerivAt_Phi z))
  rw [show (fun z => phiDensity z + z * Phi z) = phiDensity + id * Phi from rfl, h.deriv]
  simp only [id]
  linarith [Phi_pos z]

end EacProps

/-- **Proposition `P2:E`(iv)**, `β > 0`, lower bound: `e^{β|x|} ≤ E_{a,β}(x)`. -/
theorem exp_mul_abs_le_Eac {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : ℝ) :
    Real.exp (β * |x|) ≤ Eac a β x := by
  have h1 := EacProps.Eac_add_Eac_neg a β x
  have h2 := EacProps.Eac_le_exp_neg_abs ha (neg_nonpos.mpr hβ.le) x
  rw [show -β * x = -(β * x) by ring, abs_neg] at h2
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    rw [abs_of_nonneg (mul_nonneg hβ.le hx)] at h2
    have : Real.exp (-β * x) = Real.exp (-(β * x)) := by ring_nf
    linarith
  · rw [abs_of_nonpos hx]
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hβ.le hx), neg_neg] at h2
    rw [show β * -x = -β * x by ring]
    linarith

/-- **Proposition `P2:E`(iv)**, `β > 0`, strict upper bound `E_{a,β}(x) < e^{βx} + e^{−βx}`
(it holds for every `a` and `β`, since `E_{a,−β} > 0`). -/
theorem Eac_lt_exp_add_exp (a β x : ℝ) :
    Eac a β x < Real.exp (β * x) + Real.exp (-β * x) := by
  have h1 := EacProps.Eac_add_Eac_neg a β x
  have h2 := EacProps.Eac_pos (a := a) (-β) x
  linarith

/-- **Proposition `P2:E`(iv)**, `β < 0`, upper bound `E_{a,β}(x) ≤ e^{−|βx|}`
(proved for `β ≤ 0`). -/
theorem Eac_le_exp_neg_abs {a β : ℝ} (ha : 0 < a) (hβ : β < 0) (x : ℝ) :
    Eac a β x ≤ Real.exp (-|β * x|) :=
  EacProps.Eac_le_exp_neg_abs ha hβ.le x

/-- **Proposition `P2:E`(iv)**, `β < 0`, lower bound `Φ(√a β) E_{a,2β}(x)^{1/2} ≤ E_{a,β}(x)`
(proved for `β ≤ 0`). -/
theorem Phi_mul_sqrt_Eac_two_mul_le_Eac {a β : ℝ} (ha : 0 < a) (hβ : β < 0) (x : ℝ) :
    Phi (Real.sqrt a * β) * Real.sqrt (Eac a (2 * β) x) ≤ Eac a β x := by
  have hup := EacProps.Eac_le_exp_neg_abs ha (by linarith : 2 * β ≤ 0) x
  have hsq : Real.sqrt (Eac a (2 * β) x) ≤ Real.exp (-|β * x|) := by
    rw [Real.sqrt_le_left (Real.exp_pos _).le, ← Real.exp_nat_mul]
    · convert hup using 2
      rw [show 2 * β * x = 2 * (β * x) by ring, abs_mul]
      push_cast
      norm_num
  have hPhi : Phi (Real.sqrt a * β) ≤ Phi ((a * β + |x|) / Real.sqrt a) := by
    apply EacProps.monotone_Phi
    rw [← EacProps.a_beta_div_sqrt a β]
    gcongr
    exact le_add_of_nonneg_right (abs_nonneg x)
  have hlow := EacProps.exp_neg_abs_mul_Phi_le_Eac (a := a) hβ.le x
  have hP0 := EacProps.Phi_nonneg (Real.sqrt a * β)
  calc Phi (Real.sqrt a * β) * Real.sqrt (Eac a (2 * β) x)
      ≤ Phi (Real.sqrt a * β) * Real.exp (-|β * x|) := mul_le_mul_of_nonneg_left hsq hP0
    _ ≤ Phi ((a * β + |x|) / Real.sqrt a) * Real.exp (-|β * x|) :=
        mul_le_mul_of_nonneg_right hPhi (Real.exp_pos _).le
    _ ≤ Eac a β x := by rw [mul_comm]; exact hlow

/-! ### Proposition `P2:E`(v) -/

/-- `E_{a,β}(0) = 2Φ(β√a)` (any `a`, `β`). -/
theorem Eac_zero (a β : ℝ) : Eac a β 0 = 2 * Phi (β * Real.sqrt a) := by
  unfold Eac
  simp only [mul_zero, Real.exp_zero, one_mul, sub_zero, add_zero]
  rw [EacProps.a_beta_div_sqrt, mul_comm (Real.sqrt a)]
  ring

/-- **Proposition `P2:E`(v)**, `β > 0`: `x ↦ E_{a,β}(x)` is strictly convex on `ℝ`. -/
theorem strictConvexOn_Eac {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    StrictConvexOn ℝ univ (Eac a β) := by
  refine strictConvexOn_univ_of_deriv2_pos (EacProps.continuous_Eac ha β) fun x => ?_
  have hd : deriv (Eac a β) = fun x => -β * Real.exp (-β * x) * Phi ((a * β - x) / Real.sqrt a) +
      β * Real.exp (β * x) * Phi ((a * β + x) / Real.sqrt a) :=
    funext fun y => (Eac_hasDerivAt ha β y).deriv
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, hd,
    (Eac_hasDerivAt_deriv ha β x).deriv]
  have := EacProps.Eac_pos (a := a) β x
  positivity

/-- **Proposition `P2:E`(v)**, `β > 0`: the infimum of `E_{a,β}` is attained at `0`. -/
theorem Eac_zero_le {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : ℝ) : Eac a β 0 ≤ Eac a β x := by
  rcases le_total 0 x with hx | hx
  · exact EacProps.monotoneOn_Ici_of_nonneg ha hβ.le (show (0 : ℝ) ∈ Ici 0 from le_refl 0) hx hx
  · exact EacProps.antitoneOn_Iic_of_nonneg ha hβ.le hx (show (0 : ℝ) ∈ Iic 0 from le_refl 0) hx

/-- **Proposition `P2:E`(v)**, `β > 0`: `inf_x E_{a,β}(x) = E_{a,β}(0)`. -/
theorem isLeast_Eac_zero {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    IsLeast (range (Eac a β)) (Eac a β 0) :=
  ⟨⟨0, rfl⟩, by rintro _ ⟨x, rfl⟩; exact Eac_zero_le ha hβ x⟩

/-- **Proposition `P2:E`(v)**, `β > 0`: `E_{a,β}(0) = 2Φ(β√a) > 1`. -/
theorem one_lt_Eac_zero {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) : 1 < Eac a β 0 := by
  rw [Eac_zero]
  have := EacProps.strictMono_Phi (show (0 : ℝ) < β * Real.sqrt a by
    have := Real.sqrt_pos.mpr ha; positivity)
  rw [Phi_zero] at this
  linarith

/-- **Proposition `P2:E`(v)**, `β < 0`: `E_{a,β}` is nonincreasing on `[0,∞)`. -/
theorem antitoneOn_Eac_Ici {a β : ℝ} (ha : 0 < a) (hβ : β < 0) : AntitoneOn (Eac a β) (Ici 0) :=
  EacProps.antitoneOn_Ici_of_nonpos ha hβ.le

/-- **Proposition `P2:E`(v)**, `β < 0`: `E_{a,β}` is nondecreasing on `(−∞,0]`. -/
theorem monotoneOn_Eac_Iic {a β : ℝ} (ha : 0 < a) (hβ : β < 0) : MonotoneOn (Eac a β) (Iic 0) :=
  EacProps.monotoneOn_Iic_of_nonpos ha hβ.le

/-- **Proposition `P2:E`(v)**, `β < 0`: the supremum of `E_{a,β}` is attained at `0`. -/
theorem Eac_le_Eac_zero {a β : ℝ} (ha : 0 < a) (hβ : β < 0) (x : ℝ) : Eac a β x ≤ Eac a β 0 := by
  rcases le_total 0 x with hx | hx
  · exact antitoneOn_Eac_Ici ha hβ (show (0 : ℝ) ∈ Ici 0 from le_refl 0) hx hx
  · exact monotoneOn_Eac_Iic ha hβ hx (show (0 : ℝ) ∈ Iic 0 from le_refl 0) hx

theorem isGreatest_Eac_zero {a β : ℝ} (ha : 0 < a) (hβ : β < 0) :
    IsGreatest (range (Eac a β)) (Eac a β 0) :=
  ⟨⟨0, rfl⟩, by rintro _ ⟨x, rfl⟩; exact Eac_le_Eac_zero ha hβ x⟩

/-- **Proposition `P2:E`(v)**, `β < 0`: `E_{a,β}(0) = 2Φ(β√a) < 1`. -/
theorem Eac_zero_lt_one {a β : ℝ} (ha : 0 < a) (hβ : β < 0) : Eac a β 0 < 1 := by
  rw [Eac_zero]
  have := EacProps.strictMono_Phi (show β * Real.sqrt a < 0 from
    mul_neg_of_neg_of_pos hβ (Real.sqrt_pos.mpr ha))
  rw [Phi_zero] at this
  linarith

/-- **Proposition `P2:E`(v)**: `E''_{a,β}(0) = β √(2/(πa)) e^{−β²a/2} + 2β² Φ(β√a)`. -/
theorem Eac_hasDerivAt_deriv_zero {a : ℝ} (ha : 0 < a) (β : ℝ) :
    HasDerivAt
      (fun x => -β * Real.exp (-β * x) * Phi ((a * β - x) / Real.sqrt a) +
        β * Real.exp (β * x) * Phi ((a * β + x) / Real.sqrt a))
      (β * Real.sqrt (2 / (π * a)) * Real.exp (-(β ^ 2 * a) / 2) +
        2 * β ^ 2 * Phi (β * Real.sqrt a)) 0 := by
  convert Eac_hasDerivAt_deriv ha β 0 using 1
  rw [Eac_zero, show -(a ^ 2 * β ^ 2 + (0 : ℝ) ^ 2) / (2 * a) = -(β ^ 2 * a) / 2 by
    field_simp; ring]
  ring

/-- **Proposition `P2:E`(v)**, `β > 0`: `E''_{a,β}(0) > 0`. -/
theorem Eac_deriv2_zero_pos {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    0 < β * Real.sqrt (2 / (π * a)) * Real.exp (-(β ^ 2 * a) / 2) +
      2 * β ^ 2 * Phi (β * Real.sqrt a) := by
  have := EacProps.Phi_pos (β * Real.sqrt a)
  have : 0 < Real.sqrt (2 / (π * a)) := Real.sqrt_pos.mpr (by positivity)
  positivity

namespace EacProps

/-- The paper's argument for `β ≤ 0`: `E'` vanishes at `0` and is `≤ 0` on `(0,∞)`, so
`E''(0) ≤ 0`. -/
theorem Eac_deriv2_zero_nonpos {a β : ℝ} (ha : 0 < a) (hβ : β ≤ 0) :
    β * Real.sqrt (2 / (π * a)) * Real.exp (-(β ^ 2 * a) / 2) +
      2 * β ^ 2 * Phi (β * Real.sqrt a) ≤ 0 := by
  have hd := Eac_hasDerivAt_deriv_zero ha β
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have hd' := hd.mono_left (nhdsWithin_mono _ (fun x (hx : x ∈ Ioi (0 : ℝ)) =>
    (show x ≠ 0 from hx.ne')))
  apply le_of_tendsto hd'
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [slope_def_field]
  apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
  have hb := bracket_nonneg ha β hx.le
  simp only [mul_zero, Real.exp_zero, sub_zero, add_zero]
  have hm := mul_nonpos_of_nonpos_of_nonneg hβ hb
  linarith

theorem deriv2_zero_eq {a : ℝ} (ha : 0 < a) (β : ℝ) :
    β * Real.sqrt (2 / (π * a)) * Real.exp (-(β ^ 2 * a) / 2) +
      2 * β ^ 2 * Phi (β * Real.sqrt a) =
    2 * β / Real.sqrt a *
      (phiDensity (β * Real.sqrt a) + β * Real.sqrt a * Phi (β * Real.sqrt a)) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  rw [sqrt_two_div_pi_mul ha]
  unfold phiDensity
  rw [mul_pow, hsa]
  field_simp

/-- Mills-ratio inequality: `φ(z) + zΦ(z) > 0` for `z < 0` (in fact for every `z`). -/
theorem phiDensity_add_mul_Phi_pos {z : ℝ} (hz : z < 0) : 0 < phiDensity z + z * Phi z := by
  have h1 := Eac_deriv2_zero_nonpos (a := 1) (β := z - 1) one_pos (by linarith)
  rw [deriv2_zero_eq one_pos, Real.sqrt_one, mul_one, div_one] at h1
  have h2 : 0 ≤ phiDensity (z - 1) + (z - 1) * Phi (z - 1) := by
    by_contra hc
    have hc' := lt_of_not_ge hc
    nlinarith
  exact lt_of_le_of_lt h2 (strictMono_phiDensity_add_mul_Phi (by linarith))

end EacProps

/-- **Proposition `P2:E`(v)**, `β < 0`: `E''_{a,β}(0) < 0` (strict; the paper states `≤ 0`). -/
theorem Eac_deriv2_zero_neg {a β : ℝ} (ha : 0 < a) (hβ : β < 0) :
    β * Real.sqrt (2 / (π * a)) * Real.exp (-(β ^ 2 * a) / 2) +
      2 * β ^ 2 * Phi (β * Real.sqrt a) < 0 := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  rw [EacProps.deriv2_zero_eq ha]
  have := EacProps.phiDensity_add_mul_Phi_pos (mul_neg_of_neg_of_pos hβ hs)
  have : 2 * β / Real.sqrt a < 0 := div_neg_of_neg_of_pos (by linarith) hs
  nlinarith

/-- **Proposition `P2:E`(v)**, `β < 0`, the paper's form: `E''_{a,β}(0) ≤ 0`. -/
theorem Eac_deriv2_zero_nonpos {a β : ℝ} (ha : 0 < a) (hβ : β < 0) :
    β * Real.sqrt (2 / (π * a)) * Real.exp (-(β ^ 2 * a) / 2) +
      2 * β ^ 2 * Phi (β * Real.sqrt a) ≤ 0 :=
  (Eac_deriv2_zero_neg ha hβ).le

/-! ### Proposition `P2:E`(vi): the derivative in `a` -/

namespace EacProps

theorem hasDerivAt_sub_div_sqrt {a : ℝ} (ha : 0 < a) (β x : ℝ) :
    HasDerivAt (fun a => (a * β - x) / Real.sqrt a) ((a * β + x) / (2 * a * Real.sqrt a)) a := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have h := (((hasDerivAt_id a).mul_const β).sub_const x).div (Real.hasDerivAt_sqrt ha.ne') hs.ne'
  convert h using 1
  · funext y; simp only [Pi.div_apply, id]
  simp only [id]
  rw [hsa]
  field_simp
  linear_combination (-2 * β) * hsa

theorem hasDerivAt_add_div_sqrt {a : ℝ} (ha : 0 < a) (β x : ℝ) :
    HasDerivAt (fun a => (a * β + x) / Real.sqrt a) ((a * β - x) / (2 * a * Real.sqrt a)) a := by
  have := hasDerivAt_sub_div_sqrt ha β (-x)
  simpa [sub_eq_add_neg] using this

end EacProps

/-- **Proposition `P2:E`(vi)**: `∂E_{a,β}(x)/∂a = β/√(2πa) · exp(−(a²β²+x²)/(2a))`. -/
theorem Eac_hasDerivAt_a {a : ℝ} (ha : 0 < a) (β x : ℝ) :
    HasDerivAt (fun a => Eac a β x)
      (β / Real.sqrt (2 * π * a) * Real.exp (-(a ^ 2 * β ^ 2 + x ^ 2) / (2 * a))) a := by
  have h := (((hasDerivAt_Phi _).comp a (EacProps.hasDerivAt_sub_div_sqrt ha β x)).const_mul
    (Real.exp (-β * x))).add
    (((hasDerivAt_Phi _).comp a (EacProps.hasDerivAt_add_div_sqrt ha β x)).const_mul
    (Real.exp (β * x)))
  have h1 := EacProps.exp_neg_mul_phiDensity_sub ha β x
  have h2 := EacProps.exp_mul_phiDensity_add ha β x
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hkey : (a * β + x) / (2 * a * Real.sqrt a) + (a * β - x) / (2 * a * Real.sqrt a) =
      β / Real.sqrt a := by
    field_simp
    ring
  convert h using 1
  · funext y; simp only [Eac, Pi.add_apply, Function.comp]
  rw [Real.sqrt_mul (by positivity)]
  linear_combination (-((a * β + x) / (2 * a * Real.sqrt a))) * h1 +
    (-((a * β - x) / (2 * a * Real.sqrt a))) * h2 -
    (Real.sqrt (2 * π))⁻¹ * Real.exp (-(a ^ 2 * β ^ 2 + x ^ 2) / (2 * a)) * hkey

/-- **Proposition `P2:E`(vi)**: for `β > 0` (indeed `β ≥ 0`), `a ↦ E_{a,β}(x)` is nondecreasing
on `(0,∞)`. -/
theorem monotoneOn_Eac_a {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) :
    MonotoneOn (fun a => Eac a β x) (Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun a ha => (Eac_hasDerivAt_a ha β x).continuousAt.continuousWithinAt)
    (fun a ha =>
      (Eac_hasDerivAt_a (interior_subset ha) β x).differentiableAt.differentiableWithinAt)
    fun a ha => ?_
  rw [interior_Ioi] at ha
  rw [(Eac_hasDerivAt_a ha β x).deriv]
  positivity

/-- **Proposition `P2:E`(vi)**: for `β < 0` (indeed `β ≤ 0`), `a ↦ E_{a,β}(x)` is nonincreasing
on `(0,∞)`. -/
theorem antitoneOn_Eac_a {β : ℝ} (hβ : β ≤ 0) (x : ℝ) :
    AntitoneOn (fun a => Eac a β x) (Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun a ha => (Eac_hasDerivAt_a ha β x).continuousAt.continuousWithinAt)
    (fun a ha =>
      (Eac_hasDerivAt_a (interior_subset ha) β x).differentiableAt.differentiableWithinAt)
    fun a ha => ?_
  rw [interior_Ioi] at ha
  rw [(Eac_hasDerivAt_a ha β x).deriv]
  have : 0 ≤ 1 / Real.sqrt (2 * π * a) * Real.exp (-(a ^ 2 * β ^ 2 + x ^ 2) / (2 * a)) := by
    positivity
  rw [div_mul_eq_mul_div, mul_div_assoc] at *
  nlinarith

/-! ### Lemma `L2:LogRel` -/

/-- **Lemma `L2:LogRel`**, display `E2:log`: `log(b/a)/(b − a) ≥ 1/b` for `0 < a < b`. -/
theorem one_div_le_log_div_div_sub {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    1 / b ≤ Real.log (b / a) / (b - a) := by
  have hb : 0 < b := ha.trans hab
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [inv_div] at h
  rw [div_le_div_iff₀ hb (by linarith)]
  have : 1 - a / b = (b - a) / b := by field_simp
  rw [this, div_le_iff₀ hb] at h
  linarith

namespace EacProps

/-- `f(s) = (a−s)(b−s)(log(b−s) − log(a−s))`, which equals `L2:LogRel`'s
`(a−s)(b−s) log((b−s)/(a−s))` for `s < a`. -/
noncomputable def logRelAux (a b s : ℝ) : ℝ :=
  (b - s) * ((a - s) * Real.log (b - s) - (a - s) * Real.log (a - s))

theorem logRel_eq_aux {a b s : ℝ} (hab : a < b) (hs : s < a) :
    (a - s) * (b - s) * Real.log ((b - s) / (a - s)) = logRelAux a b s := by
  unfold logRelAux
  rw [Real.log_div (by linarith) (by linarith)]
  ring

theorem hasDerivAt_logRelAux {a b s : ℝ} (hab : a < b) (hs : s < a) :
    HasDerivAt (logRelAux a b)
      ((b - a) - (a + b - 2 * s) * (Real.log (b - s) - Real.log (a - s))) s := by
  have h1 : HasDerivAt (fun s => Real.log (b - s)) (-1 / (b - s)) s :=
    ((hasDerivAt_id s).const_sub b).log (by simp; linarith)
  have h2 : HasDerivAt (fun s => Real.log (a - s)) (-1 / (a - s)) s :=
    ((hasDerivAt_id s).const_sub a).log (by simp; linarith)
  have hb : HasDerivAt (fun s => b - s) (-1) s := by simpa using (hasDerivAt_id s).const_sub b
  have ha : HasDerivAt (fun s => a - s) (-1) s := by simpa using (hasDerivAt_id s).const_sub a
  have h := hb.mul ((ha.mul h1).sub (ha.mul h2))
  have hbs : b - s ≠ 0 := by linarith
  have has : a - s ≠ 0 := by linarith
  convert h using 1
  · funext y; simp only [logRelAux, Pi.mul_apply, Pi.sub_apply]
  simp only [Pi.mul_apply, Pi.sub_apply]
  field_simp
  ring

theorem continuous_logRelAux_at {a b : ℝ} (hab : a < b) :
    ContinuousAt (logRelAux a b) a := by
  unfold logRelAux
  have hl : ContinuousAt (fun s => Real.log (b - s)) a :=
    (continuous_const.sub continuous_id).continuousAt.log (by simp; linarith)
  have hm : Continuous (fun s : ℝ => (a - s) * Real.log (a - s)) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  exact (continuous_const.sub continuous_id).continuousAt.mul
    (((continuous_const.sub continuous_id).continuousAt.mul hl).sub hm.continuousAt)

end EacProps

/-- **Lemma `L2:LogRel`**: `f(s) = (a−s)(b−s) log((b−s)/(a−s))` is nonincreasing on `[0,a)`. -/
theorem logRel_antitoneOn {a b : ℝ} (_ha : 0 < a) (hab : a < b) :
    AntitoneOn (fun s => (a - s) * (b - s) * Real.log ((b - s) / (a - s))) (Ico 0 a) := by
  have hg : AntitoneOn (EacProps.logRelAux a b) (Ico 0 a) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ico 0 a)
      (fun s hs => (EacProps.hasDerivAt_logRelAux hab hs.2).continuousAt.continuousWithinAt)
      (fun s hs => (EacProps.hasDerivAt_logRelAux hab
        (interior_subset hs).2).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Ico] at hs
    rw [(EacProps.hasDerivAt_logRelAux hab hs.2).deriv]
    have hbs : 0 < b - s := by linarith [hs.2]
    have has : 0 < a - s := by linarith [hs.2]
    have hL := Real.one_sub_inv_le_log_of_pos (div_pos hbs has)
    rw [Real.log_div hbs.ne' has.ne', inv_div] at hL
    have h1 : 1 - (a - s) / (b - s) = (b - a) / (b - s) := by field_simp; ring
    rw [h1] at hL
    have h2 : (b - a) ≤ (a + b - 2 * s) * ((b - a) / (b - s)) := by
      rw [mul_div_assoc', le_div_iff₀ hbs]
      nlinarith
    have h3 : 0 ≤ a + b - 2 * s := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hL h3]
  intro s hs t ht hst
  simp only
  rw [EacProps.logRel_eq_aux hab hs.2, EacProps.logRel_eq_aux hab ht.2]
  exact hg hs ht hst

/-- **Lemma `L2:LogRel`**: `f > 0` on `[0,a)`. -/
theorem logRel_pos {a b s : ℝ} (hab : a < b) (hs : s < a) :
    0 < (a - s) * (b - s) * Real.log ((b - s) / (a - s)) := by
  have has : 0 < a - s := by linarith
  have hbs : 0 < b - s := by linarith
  have : 0 < Real.log ((b - s) / (a - s)) :=
    Real.log_pos ((one_lt_div has).mpr (by linarith))
  positivity

/-- **Lemma `L2:LogRel`**: `sup_{s∈[0,a)} f(s) = f(0) = ab log(b/a)` (attained). -/
theorem logRel_isGreatest {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsGreatest ((fun s => (a - s) * (b - s) * Real.log ((b - s) / (a - s))) '' Ico 0 a)
      (a * b * Real.log (b / a)) := by
  have h0 : (0 : ℝ) ∈ Ico 0 a := ⟨le_refl 0, ha⟩
  refine ⟨⟨0, h0, by simp⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have := logRel_antitoneOn ha hab h0 hs hs.1
  simpa using this

/-- **Lemma `L2:LogRel`**, corrected limit: `f(s) → 0` as `s → a⁻` (not `(b−a) log(b−a)`). -/
theorem logRel_tendsto {a b : ℝ} (hab : a < b) :
    Tendsto (fun s => (a - s) * (b - s) * Real.log ((b - s) / (a - s))) (𝓝[<] a) (𝓝 0) := by
  have hc := EacProps.continuous_logRelAux_at hab
  have h0 : EacProps.logRelAux a b a = 0 := by simp [EacProps.logRelAux]
  rw [ContinuousAt, h0] at hc
  refine (tendsto_nhdsWithin_of_tendsto_nhds hc).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : s < a)
  exact (EacProps.logRel_eq_aux hab hs).symm

/-- **Lemma `L2:LogRel`**, corrected infimum: `inf_{s∈[0,a)} f(s) = 0` (not attained). -/
theorem logRel_isGLB {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsGLB ((fun s => (a - s) * (b - s) * Real.log ((b - s) / (a - s))) '' Ico 0 a) 0 := by
  refine ⟨?_, fun lb hlb => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (logRel_pos hab hs.2).le
  · refine ge_of_tendsto (logRel_tendsto hab) ?_
    filter_upwards [Ioo_mem_nhdsLT ha] with s hs
    exact hlb ⟨s, ⟨hs.1.le, hs.2⟩, rfl⟩

theorem logRel_sInf {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    sInf ((fun s => (a - s) * (b - s) * Real.log ((b - s) / (a - s))) '' Ico 0 a) = 0 :=
  (logRel_isGLB ha hab).csInf_eq ⟨_, 0, ⟨le_refl 0, ha⟩, rfl⟩

/-- **Paper error in `L2:LogRel`**: the claim `inf_{s∈[0,a)} f(s) = (b−a) log(b−a)` is false
(`a = 1`, `b = 3`: the infimum is `0`, while `(b−a) log(b−a) = 2 log 2 > 0`). -/
theorem logRel_inf_claim_false :
    ¬ ∀ a b : ℝ, 0 < a → a < b →
      sInf ((fun s => (a - s) * (b - s) * Real.log ((b - s) / (a - s))) '' Ico 0 a) =
        (b - a) * Real.log (b - a) := by
  intro h
  have h1 := h 1 3 one_pos (by norm_num)
  rw [logRel_sInf one_pos (by norm_num)] at h1
  norm_num at h1

/-- **Paper error in `L2:LogRel`**: the claim `lim_{s→a} f(s) = (b−a) log(b−a)` is false
(`a = 1`, `b = 3`). -/
theorem logRel_lim_claim_false :
    ¬ ∀ a b : ℝ, 0 < a → a < b →
      Tendsto (fun s => (a - s) * (b - s) * Real.log ((b - s) / (a - s))) (𝓝[<] a)
        (𝓝 ((b - a) * Real.log (b - a))) := by
  intro h
  have h1 := tendsto_nhds_unique (h 1 3 one_pos (by norm_num)) (logRel_tendsto (by norm_num))
  norm_num at h1

end ChenDalang15

end
