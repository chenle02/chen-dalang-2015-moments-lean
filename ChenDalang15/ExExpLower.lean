module

public import ChenDalang15.GrowthIndex
public import ChenDalang15.Eac
public import ChenDalang15.PhiE

/-!
# Proposition `P2:Ex-Exp`, lower bound (Chen–Dalang 2015, Section 5)

For the parabolic Anderson model `ρ(u) = λu` with initial data `μ(dx) = e^{-β|x|} dx`
(`β > 0`), the proof of Proposition `P2:Ex-Exp` reduces the second moment `f(t,x) = E u(t,x)²`
to the explicit minorant (for every `c ∈ [0,1)` and large `t`)
```
f(t,x) ≥ E_{νt/2,−2β}(x) e^{β²νt} Φ(−β√(ν(1−c)t))² (e^{γt} − e^{cγt}),   γ = λ⁴/(4ν).
```
This file proves, from that minorant alone:

* `exExp_rate_point` (paper display before "We now consider two cases"): the tail rate at
  `α` is at least `cβ²ν + γ − 2βα` if `α ≥ βν` and `(c−1)β²ν + γ − α²/ν` if `α < βν`.
  The second bound in fact holds for every `α` (`ExExpLower.quadratic_le_tailRate`).
* `exExp_lowerIndex_of_envelope`: `λ̲ ≥ βν/2 + λ⁴/(8νβ)` if `β ≤ λ²/(2ν)` and `λ̲ ≥ λ²/2`
  otherwise (the `c → 1` limit of the paper's two cases).
* `lowerGrowthIndex_le_upperGrowthIndex`: `λ̲ ≤ λ̄` for every `f` (from the antitonicity of
  the tail rate).
* `exExp_growth_eq`: with the upper envelopes of Theorem `T2:Growth` for every `β' < β`
  (as a named hypothesis), `λ̲(2) = λ̄(2) =` the piecewise value of display `E2:Ex-Exp`.

Gaussian tail input: only the crude bound `Φ(w) ≥ φ(|w| + 1)` (`ExExpLower.phiDensity_le_Phi`),
turned into `Φ(w) ≥ K_δ e^{−(1+δ)w²/2}` for every `δ > 0`.
-/

set_option autoImplicit false

public section

open scoped ENNReal Topology
open Filter

namespace ChenDalang15

namespace ExExpLower

/-! ### Gaussian lower bounds -/

theorem phiDensity_nonneg (y : ℝ) : 0 ≤ phiDensity y := by
  unfold phiDensity; positivity

theorem Phi_nonneg (x : ℝ) : 0 ≤ Phi x := by
  rw [Phi_eq_integral_phiDensity]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Iic fun y _ => phiDensity_nonneg y

/-- `Φ(w) ≥ 1/2` for `w ≥ 0`. -/
theorem half_le_Phi {w : ℝ} (hw : 0 ≤ w) : 1 / 2 ≤ Phi w := by
  rw [Phi_eq_Phi_zero_add, Phi_zero]
  have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hw fun y _ => phiDensity_nonneg y
  linarith

/-- The crude Gaussian lower bound `Φ(w) ≥ φ(|w| + 1)`, valid for every real `w`:
`Φ(w) ≥ ∫_{w−1}^w φ ≥ min_{[w−1,w]} φ`. -/
theorem phiDensity_le_Phi (w : ℝ) : phiDensity (|w| + 1) ≤ Phi w := by
  have hi := continuous_phiDensity.intervalIntegrable (μ := MeasureTheory.volume)
  have hsub : Phi w - Phi (w - 1) = ∫ y in (w - 1)..w, phiDensity y := by
    rw [Phi_eq_Phi_zero_add w, Phi_eq_Phi_zero_add (w - 1), add_sub_add_left_eq_sub]
    exact intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)
  have hmono : ∫ _ in (w - 1)..w, phiDensity (|w| + 1) ≤ ∫ y in (w - 1)..w, phiDensity y := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const (hi _ _) ?_
    intro y hy
    have h1 : -(|w| + 1) ≤ y := by linarith [neg_abs_le w, hy.1]
    have h2 : y ≤ |w| + 1 := by linarith [le_abs_self w, hy.2]
    have hsq : y ^ 2 ≤ (|w| + 1) ^ 2 := sq_le_sq' h1 h2
    unfold phiDensity
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have := Phi_nonneg (w - 1)
  nlinarith

/-- The constant `K_δ = (2π)^{-1/2} e^{-(1+δ⁻¹)/2}`. -/
noncomputable def K (δ : ℝ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 + δ⁻¹) / 2)

theorem K_pos (δ : ℝ) : 0 < K δ := by
  unfold K
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- Quadratic Gaussian lower bound: for `δ > 0`, `Φ(w) ≥ K_δ e^{−(1+δ)w²/2}`. -/
theorem K_mul_exp_le_Phi {δ : ℝ} (hδ : 0 < δ) (w : ℝ) :
    K δ * Real.exp (-(1 + δ) * w ^ 2 / 2) ≤ Phi w := by
  refine le_trans ?_ (phiDensity_le_Phi w)
  have hd : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
  have hkey : δ * w ^ 2 + δ⁻¹ - 2 * |w| = δ⁻¹ * (δ * |w| - 1) ^ 2 := by
    rw [← sq_abs w]
    linear_combination (-(δ * |w| ^ 2 - 2 * |w|)) * hd
  have hq : (|w| + 1) ^ 2 ≤ (1 + δ) * w ^ 2 + (1 + δ⁻¹) := by
    have : 0 ≤ δ⁻¹ * (δ * |w| - 1) ^ 2 := by positivity
    have hw : |w| ^ 2 = w ^ 2 := sq_abs w
    nlinarith
  unfold K phiDensity
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)

/-! ### The function `E_{νt/2,−2β}` at `x = αt` -/

theorem Eac_nonneg (a β x : ℝ) : 0 ≤ Eac a β x := by
  unfold Eac
  have := Phi_nonneg ((a * β - x) / Real.sqrt a)
  have := Phi_nonneg ((a * β + x) / Real.sqrt a)
  positivity

/-- First term of `E_{νt/2,−2β}(αt)`: for `t > 0`, `δ > 0`,
`E_{νt/2,−2β}(αt) ≥ K_δ e^{(2βα − (1+δ)(βν+α)²/ν) t}` (valid for every real `α`). -/
theorem Eac_ge_first {ν β α δ t : ℝ} (hν : 0 < ν) (hδ : 0 < δ) (ht : 0 < t) :
    K δ * Real.exp ((2 * β * α - (1 + δ) * (β * ν + α) ^ 2 / ν) * t) ≤
      Eac (ν * t / 2) (-2 * β) (α * t) := by
  unfold Eac
  set w := (ν * t / 2 * (-2 * β) - α * t) / Real.sqrt (ν * t / 2) with hw
  have ha : 0 < ν * t / 2 := by positivity
  have hw2 : w ^ 2 = 2 * (β * ν + α) ^ 2 / ν * t := by
    rw [hw, div_pow, Real.sq_sqrt ha.le]
    field_simp
    ring
  have h1 := K_mul_exp_le_Phi hδ w
  have h2 := Phi_nonneg ((ν * t / 2 * (-2 * β) + α * t) / Real.sqrt (ν * t / 2))
  have h3 : K δ * Real.exp ((2 * β * α - (1 + δ) * (β * ν + α) ^ 2 / ν) * t) =
      Real.exp (-(-2 * β) * (α * t)) * (K δ * Real.exp (-(1 + δ) * w ^ 2 / 2)) := by
    rw [hw2, mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [h3]
  have h4 : 0 ≤ Real.exp (-2 * β * (α * t)) *
      Phi ((ν * t / 2 * (-2 * β) + α * t) / Real.sqrt (ν * t / 2)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(-2 * β) * (α * t))).le]

/-- Second term of `E_{νt/2,−2β}(αt)`: for `t > 0` and `α ≥ βν`,
`E_{νt/2,−2β}(αt) ≥ ½ e^{−2βαt}` (the `Φ` argument is `≥ 0`). -/
theorem Eac_ge_second {ν β α t : ℝ} (ht : 0 < t) (hα : β * ν ≤ α) :
    1 / 2 * Real.exp ((-2 * β * α) * t) ≤ Eac (ν * t / 2) (-2 * β) (α * t) := by
  unfold Eac
  have harg : 0 ≤ (ν * t / 2 * (-2 * β) + α * t) / Real.sqrt (ν * t / 2) := by
    apply div_nonneg _ (Real.sqrt_nonneg _)
    nlinarith
  have h1 := half_le_Phi harg
  have h2 := Phi_nonneg ((ν * t / 2 * (-2 * β) - α * t) / Real.sqrt (ν * t / 2))
  have h0 : 0 ≤ Real.exp (-(-2 * β) * (α * t)) *
      Phi ((ν * t / 2 * (-2 * β) - α * t) / Real.sqrt (ν * t / 2)) := by positivity
  have he : Real.exp ((-2 * β * α) * t) = Real.exp (-2 * β * (α * t)) := by ring_nf
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-2 * β * (α * t))).le]

/-! ### The minorant and its exponential rate -/

/-- The minorant `E_{νt/2,−2β}(x) e^{β²νt} Φ(−β√(ν(1−c)t))² (e^{γt} − e^{cγt})` of the proof
of Proposition `P2:Ex-Exp`. -/
@[expose] noncomputable def envelope (ν β γ c t x : ℝ) : ℝ :=
  Eac (ν * t / 2) (-2 * β) x * Real.exp (β ^ 2 * ν * t) *
    Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2 * (Real.exp (γ * t) - Real.exp (c * γ * t))

/-- `Φ(−β√(ν(1−c)t))² ≥ K_δ² e^{−(1+δ)β²ν(1−c)t}`. -/
theorem Phi_sq_ge {ν β c δ t : ℝ} (hν : 0 < ν) (hc : c ≤ 1) (hδ : 0 < δ) (ht : 0 ≤ t) :
    K δ ^ 2 * Real.exp (-(1 + δ) * β ^ 2 * ν * (1 - c) * t) ≤
      Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2 := by
  have h0 : 0 ≤ ν * (1 - c) * t := by
    have : 0 ≤ 1 - c := by linarith
    exact mul_nonneg (mul_nonneg hν.le this) ht
  have h1 := K_mul_exp_le_Phi hδ (-β * Real.sqrt (ν * (1 - c) * t))
  have hw : (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2 = β ^ 2 * (ν * (1 - c) * t) := by
    rw [mul_pow, neg_sq, Real.sq_sqrt h0]
  rw [hw] at h1
  have h2 := pow_le_pow_left₀ (by have := K_pos δ; positivity) h1 2
  refine le_trans (le_of_eq ?_) h2
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- `e^{γt} − e^{cγt} ≥ (1 − e^{−(1−c)γ}) e^{γt}` for `t ≥ 1`. -/
theorem exp_sub_exp_ge {γ c t : ℝ} (hγ : 0 < γ) (hc : c < 1) (ht : 1 ≤ t) :
    (1 - Real.exp (-(1 - c) * γ)) * Real.exp (γ * t) ≤
      Real.exp (γ * t) - Real.exp (c * γ * t) := by
  have h1 : Real.exp (c * γ * t) = Real.exp (γ * t) * Real.exp (-(1 - c) * γ * t) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-(1 - c) * γ * t) ≤ Real.exp (-(1 - c) * γ) := by
    apply Real.exp_le_exp.2
    have : 0 < (1 - c) * γ := mul_pos (by linarith) hγ
    nlinarith
  rw [h1]
  nlinarith [Real.exp_pos (γ * t)]

/-- Combination: an exponential lower bound `A e^{at} ≤ E_{νt/2,−2β}(αt)` (for `t ≥ 1`) gives
`C e^{(a + β²ν − (1+δ)β²ν(1−c) + γ)t} ≤` minorant at `x = αt`. -/
theorem envelope_ge {ν β γ c α δ A a : ℝ} (hν : 0 < ν) (hγ : 0 < γ) (hc1 : c < 1)
    (hδ : 0 < δ) (hA : 0 < A)
    (hE : ∀ t, 1 ≤ t → A * Real.exp (a * t) ≤ Eac (ν * t / 2) (-2 * β) (α * t)) :
    ∃ C > 0, ∀ t, 1 ≤ t →
      C * Real.exp ((a + β ^ 2 * ν - (1 + δ) * β ^ 2 * ν * (1 - c) + γ) * t) ≤
        envelope ν β γ c t (α * t) := by
  have hD : 0 < 1 - Real.exp (-(1 - c) * γ) := by
    have : Real.exp (-(1 - c) * γ) < 1 := by
      rw [Real.exp_lt_one_iff]
      have : 0 < (1 - c) * γ := mul_pos (by linarith) hγ
      linarith
    linarith
  refine ⟨A * K δ ^ 2 * (1 - Real.exp (-(1 - c) * γ)), by have := K_pos δ; positivity, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := by linarith
  have e1 := hE t ht
  have e2 := Phi_sq_ge (β := β) hν hc1.le hδ ht0
  have e3 := exp_sub_exp_ge hγ hc1 ht
  have hsplit : A * K δ ^ 2 * (1 - Real.exp (-(1 - c) * γ)) *
      Real.exp ((a + β ^ 2 * ν - (1 + δ) * β ^ 2 * ν * (1 - c) + γ) * t) =
      A * Real.exp (a * t) * Real.exp (β ^ 2 * ν * t) *
        (K δ ^ 2 * Real.exp (-(1 + δ) * β ^ 2 * ν * (1 - c) * t)) *
        ((1 - Real.exp (-(1 - c) * γ)) * Real.exp (γ * t)) := by
    have : (a + β ^ 2 * ν - (1 + δ) * β ^ 2 * ν * (1 - c) + γ) * t =
        a * t + β ^ 2 * ν * t + (-(1 + δ) * β ^ 2 * ν * (1 - c) * t) + γ * t := by ring
    rw [this, Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  rw [hsplit, envelope]
  have hK := K_pos δ
  have hEn := Eac_nonneg (ν * t / 2) (-2 * β) (α * t)
  apply mul_le_mul _ e3 (by positivity) (by positivity)
  apply mul_le_mul _ e2 (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le

/-- A minorant `C e^{Rt} ≤ envelope(t, αt)` (for `t ≥ 1`) of `f` gives `R ≤ tailRate f α`. -/
theorem le_tailRate_of_envelope {f : ℝ → ℝ → ℝ≥0∞} {ν β γ c α C R : ℝ}
    (hf : ∃ T₀, ∀ t ≥ T₀, ∀ x, ENNReal.ofReal (envelope ν β γ c t x) ≤ f t x) (hC : 0 < C)
    (hlow : ∀ t, 1 ≤ t → C * Real.exp (R * t) ≤ envelope ν β γ c t (α * t)) :
    (R : EReal) ≤ tailRate f α := by
  obtain ⟨T₀, hT⟩ := hf
  refine GrowthIndex.le_tailRate_of_eventually (g := fun t => C * Real.exp (R * t))
    (Eventually.of_forall fun t => by positivity) ?_ (GrowthIndex.tendsto_inv_mul_log_mul_exp hC)
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop 1] with t hT₀ ht
  exact (ENNReal.ofReal_le_ofReal (hlow t ht)).trans
    ((hT t hT₀ (α * t)).trans (GrowthIndex.le_tailSup (le_abs_self _)))

/-- Letting `δ → 0`: if `R − δM ≤ r` for every `δ > 0` (`M ≥ 0`), then `R ≤ r`. -/
theorem le_of_forall_sub_mul_le {R M : ℝ} {r : EReal} (hM : 0 ≤ M)
    (h : ∀ δ : ℝ, 0 < δ → ((R - δ * M : ℝ) : EReal) ≤ r) : (R : EReal) ≤ r := by
  refine le_of_forall_lt_imp_le_of_dense fun a ha => ?_
  induction a using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd ha (not_lt.2 le_top)
  | coe a =>
    have ha' : a < R := by exact_mod_cast ha
    have hδ : 0 < (R - a) / (M + 1) := div_pos (by linarith) (by linarith)
    refine le_trans ?_ (h _ hδ)
    have : (R - a) / (M + 1) * M ≤ R - a := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    exact_mod_cast (by linarith : a ≤ R - (R - a) / (M + 1) * M)

/-- The rate bound `(c−1)β²ν + γ − α²/ν ≤ tailRate f α`, valid for every `α` (first term of
`E`). -/
theorem quadratic_le_tailRate {f : ℝ → ℝ → ℝ≥0∞} {ν β γ c : ℝ} (hν : 0 < ν) (hγ : 0 < γ)
    (hc1 : c < 1)
    (hf : ∃ T₀, ∀ t ≥ T₀, ∀ x, ENNReal.ofReal (envelope ν β γ c t x) ≤ f t x) (α : ℝ) :
    (((c - 1) * β ^ 2 * ν + γ - α ^ 2 / ν : ℝ) : EReal) ≤ tailRate f α := by
  have hM : 0 ≤ (β * ν + α) ^ 2 / ν + β ^ 2 * ν * (1 - c) := by
    have : 0 ≤ 1 - c := by linarith
    positivity
  refine le_of_forall_sub_mul_le hM fun δ hδ => ?_
  obtain ⟨C, hC, hlow⟩ := envelope_ge (β := β) (α := α) hν hγ hc1 hδ (K_pos δ)
    (a := 2 * β * α - (1 + δ) * (β * ν + α) ^ 2 / ν)
    (fun t ht => Eac_ge_first hν hδ (by linarith))
  have key := le_tailRate_of_envelope hf hC hlow
  have heq : 2 * β * α - (1 + δ) * (β * ν + α) ^ 2 / ν + β ^ 2 * ν -
      (1 + δ) * β ^ 2 * ν * (1 - c) + γ =
      (c - 1) * β ^ 2 * ν + γ - α ^ 2 / ν - δ * ((β * ν + α) ^ 2 / ν + β ^ 2 * ν * (1 - c)) := by
    field_simp
    ring
  rwa [heq] at key

/-- The rate bound `cβ²ν + γ − 2βα ≤ tailRate f α` for `α ≥ βν` (second term of `E`). -/
theorem linear_le_tailRate {f : ℝ → ℝ → ℝ≥0∞} {ν β γ c α : ℝ} (hν : 0 < ν) (hγ : 0 < γ)
    (hc1 : c < 1)
    (hf : ∃ T₀, ∀ t ≥ T₀, ∀ x, ENNReal.ofReal (envelope ν β γ c t x) ≤ f t x)
    (hα : β * ν ≤ α) :
    ((c * β ^ 2 * ν + γ - 2 * β * α : ℝ) : EReal) ≤ tailRate f α := by
  have hM : 0 ≤ β ^ 2 * ν * (1 - c) := by
    have : 0 ≤ 1 - c := by linarith
    positivity
  refine le_of_forall_sub_mul_le hM fun δ hδ => ?_
  obtain ⟨C, hC, hlow⟩ := envelope_ge (β := β) (α := α) hν hγ hc1 hδ (by norm_num : (0 : ℝ) < 1 / 2)
    (a := -2 * β * α) (fun t ht => Eac_ge_second (by linarith) hα)
  have key := le_tailRate_of_envelope hf hC hlow
  have heq : -2 * β * α + β ^ 2 * ν - (1 + δ) * β ^ 2 * ν * (1 - c) + γ =
      c * β ^ 2 * ν + γ - 2 * β * α - δ * (β ^ 2 * ν * (1 - c)) := by ring
  rwa [heq] at key

/-- Choice of `c ∈ [0,1)` close to `1`: if `D > 0` and `B > 0`, some `c ∈ [0,1)` has
`D − (1 − c)B > 0`. -/
theorem exists_c {D B : ℝ} (hD : 0 < D) (hB : 0 < B) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ 0 < D - (1 - c) * B := by
  refine ⟨1 - D / (2 * B + D), ?_, ?_, ?_⟩
  · rw [sub_nonneg, div_le_one (by positivity)]; linarith
  · have : 0 < D / (2 * B + D) := by positivity
    linarith
  · rw [sub_sub_cancel, div_mul_eq_mul_div, sub_pos, div_lt_iff₀ (by positivity)]
    nlinarith

end ExExpLower

open ExExpLower

/-- Paper display before "We now consider two cases" (proof of `P2:Ex-Exp`): if, for a fixed
`c ∈ [0,1)`, `f(t,x) ≥ E_{νt/2,−2β}(x) e^{β²νt} Φ(−β√(ν(1−c)t))² (e^{γt} − e^{cγt})` for large
`t`, with `γ = λ⁴/(4ν)`, then the tail rate at `α` is at least `cβ²ν + γ − 2βα` if
`α ≥ βν` and `(c−1)β²ν + γ − α²/ν` if `α < βν`. The paper's side conditions `α > 0`,
`β > 0`, `c ≥ 0` are not needed. -/
theorem exExp_rate_point {f : ℝ → ℝ → ℝ≥0∞} {ν lam β c α : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0)
    (hc1 : c < 1)
    (hf : ∃ T₀, ∀ t ≥ T₀, ∀ x,
      ENNReal.ofReal (Eac (ν * t / 2) (-2 * β) x * Real.exp (β ^ 2 * ν * t) *
          Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2 *
          (Real.exp (lam ^ 4 / (4 * ν) * t) - Real.exp (c * (lam ^ 4 / (4 * ν)) * t))) ≤ f t x) :
    ((if β * ν ≤ α then c * β ^ 2 * ν + lam ^ 4 / (4 * ν) - 2 * β * α
        else (c - 1) * β ^ 2 * ν + lam ^ 4 / (4 * ν) - α ^ 2 / ν : ℝ) : EReal) ≤
      tailRate f α := by
  have hγ : 0 < lam ^ 4 / (4 * ν) := by positivity
  split_ifs with h
  · exact linear_le_tailRate hν hγ hc1 hf h
  · exact quadratic_le_tailRate hν hγ hc1 hf α

/-- Proposition `P2:Ex-Exp`, lower bound, from the minorant of its proof (for every
`c ∈ [0,1)`): `λ̲ ≥ βν/2 + λ⁴/(8νβ)` if `β ≤ λ²/(2ν)` and `λ̲ ≥ λ²/2` otherwise. -/
theorem exExp_lowerIndex_of_envelope {f : ℝ → ℝ → ℝ≥0∞} {ν lam β : ℝ} (hν : 0 < ν)
    (hlam : lam ≠ 0) (hβ : 0 < β)
    (hf : ∀ c : ℝ, 0 ≤ c → c < 1 → ∃ T₀, ∀ t ≥ T₀, ∀ x,
      ENNReal.ofReal (Eac (ν * t / 2) (-2 * β) x * Real.exp (β ^ 2 * ν * t) *
          Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2 *
          (Real.exp (lam ^ 4 / (4 * ν) * t) - Real.exp (c * (lam ^ 4 / (4 * ν)) * t))) ≤ f t x) :
    ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
      EReal) ≤ lowerGrowthIndex f := by
  have hL : 0 < lam ^ 2 := by positivity
  have hγ : 0 < lam ^ 4 / (4 * ν) := by positivity
  have hB : 0 < β ^ 2 * ν := by positivity
  have h4 : lam ^ 4 = (lam ^ 2) ^ 2 := by ring
  -- the real inequalities behind the two cases
  have caseB : ∀ α : ℝ, β * ν ≤ α → (α : EReal) <
      ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
        EReal) → 0 < β ^ 2 * ν + lam ^ 4 / (4 * ν) - 2 * β * α := by
    intro α hαβ hαs
    have hαs' : α < (if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β)
        else lam ^ 2 / 2) := by exact_mod_cast hαs
    split_ifs at hαs' with hb
    · have : 2 * β * α < β ^ 2 * ν + lam ^ 4 / (4 * ν) := by
        have e : 2 * β * (β * ν / 2 + lam ^ 4 / (8 * ν * β)) = β ^ 2 * ν + lam ^ 4 / (4 * ν) := by
          field_simp; ring
        rw [← e]
        exact mul_lt_mul_of_pos_left hαs' (by positivity)
      linarith
    · exfalso
      rw [not_le, div_lt_iff₀ (by positivity)] at hb
      nlinarith
  have caseA : ∀ α : ℝ, 0 < α → α < β * ν → (α : EReal) <
      ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
        EReal) → 0 < lam ^ 4 / (4 * ν) - α ^ 2 / ν := by
    intro α hα0 hαβ hαs
    have hαs' : α < (if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β)
        else lam ^ 2 / 2) := by exact_mod_cast hαs
    have hα2 : α < lam ^ 2 / 2 := by
      split_ifs at hαs' with hb
      · rw [le_div_iff₀ (by positivity)] at hb
        nlinarith
      · exact hαs'
    have hsq : α ^ 2 < (lam ^ 2 / 2) ^ 2 := by nlinarith
    have e : lam ^ 4 / (4 * ν) - α ^ 2 / ν = ((lam ^ 2 / 2) ^ 2 - α ^ 2) / ν := by
      rw [h4]; field_simp; ring
    rw [e]
    exact div_pos (by linarith) hν
  have hs : (0 : EReal) <
      ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
        EReal) := by
    have : (0 : ℝ) <
        (if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2) := by
      split_ifs <;> positivity
    exact_mod_cast this
  refine GrowthIndex.le_lowerGrowthIndex_of_forall hs fun α hα0 hαs => ?_
  by_cases hαβ : β * ν ≤ α
  · obtain ⟨c, hc0, hc1, hpos⟩ := exists_c (caseB α hαβ hαs) hB
    refine lt_of_lt_of_le ?_ (linear_le_tailRate hν hγ hc1 (hf c hc0 hc1) hαβ)
    have : 0 < c * β ^ 2 * ν + lam ^ 4 / (4 * ν) - 2 * β * α := by nlinarith
    exact_mod_cast this
  · obtain ⟨c, hc0, hc1, hpos⟩ := exists_c (caseA α hα0 (not_le.1 hαβ) hαs) hB
    refine lt_of_lt_of_le ?_ (quadratic_le_tailRate hν hγ hc1 (hf c hc0 hc1) α)
    have : 0 < (c - 1) * β ^ 2 * ν + lam ^ 4 / (4 * ν) - α ^ 2 / ν := by nlinarith
    exact_mod_cast this

/-- `λ̲ ≤ λ̄` for every `f`: an `α` with positive tail rate lies below every `α'` with negative
tail rate, by antitonicity of the tail rate. -/
theorem lowerGrowthIndex_le_upperGrowthIndex (f : ℝ → ℝ → ℝ≥0∞) :
    lowerGrowthIndex f ≤ upperGrowthIndex f := by
  refine sSup_le ?_
  rintro _ ⟨α, ⟨-, hα⟩, rfl⟩
  refine le_sInf ?_
  rintro _ ⟨α', ⟨-, hα'⟩, rfl⟩
  refine EReal.coe_le_coe_iff.2 (le_of_not_gt fun hlt => ?_)
  have := tailRate_antitone f hlt.le
  exact absurd (hα.trans_le this) (not_lt.2 hα'.le)

/-- Proposition `P2:Ex-Exp` (display `E2:Ex-Exp`): given the lower minorant of the proof (for
every `c ∈ [0,1)`) and the upper envelopes `f ≤ A e^{(νβ'² + λ⁴/(4ν))t − 2β'|x|}` of
Theorem `T2:Growth` for every `β' ∈ (0, β)` (available since `μ ∈ 𝓜^{β'}_{G,+}` for `β' < β`),
`λ̲ = λ̄ = βν/2 + λ⁴/(8νβ)` if `β ≤ λ²/(2ν)` and `λ²/2` otherwise. -/
theorem exExp_growth_eq {f : ℝ → ℝ → ℝ≥0∞} {ν lam β : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0)
    (hβ : 0 < β)
    (hlow : ∀ c : ℝ, 0 ≤ c → c < 1 → ∃ T₀, ∀ t ≥ T₀, ∀ x,
      ENNReal.ofReal (Eac (ν * t / 2) (-2 * β) x * Real.exp (β ^ 2 * ν * t) *
          Phi (-β * Real.sqrt (ν * (1 - c) * t)) ^ 2 *
          (Real.exp (lam ^ 4 / (4 * ν) * t) - Real.exp (c * (lam ^ 4 / (4 * ν)) * t))) ≤ f t x)
    (hup : ∀ β', 0 < β' → β' < β → ∃ A T₀, ∀ t ≥ T₀, ∀ x,
      f t x ≤ ENNReal.ofReal (A * Real.exp ((ν * β' ^ 2 + lam ^ 4 / (4 * ν)) * t - 2 * β' * |x|))) :
    lowerGrowthIndex f =
        ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
          EReal) ∧
      upperGrowthIndex f =
        ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
          EReal) := by
  set s : ℝ := if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2
    with hs
  have hΛ : 0 < |lam| := abs_pos.2 hlam
  have hΛ2 : |lam| ^ 2 = lam ^ 2 := sq_abs lam
  have hΛ4 : |lam| ^ 4 = lam ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, hΛ2]
  -- the upper bound for each `β' < β`
  have hupper : ∀ β', 0 < β' → β' < β → upperGrowthIndex f ≤
      ((if β' < lam ^ 2 / (2 * ν) then β' * ν / 2 + lam ^ 4 / (8 * ν * β') else lam ^ 2 / 2 : ℝ) :
        EReal) := by
    intro β' hβ'0 hβ'β
    have := upperGrowthIndex_le_piecewise (f := f) (Λ := |lam|) hν hΛ hβ'0
      (fun b hb0 hbβ' => by
        obtain ⟨A, T₀, h⟩ := hup b hb0 (hbβ'.trans_lt hβ'β)
        exact ⟨A, T₀, by rw [hΛ4]; exact h⟩)
    rwa [hΛ2, hΛ4] at this
  have hU : upperGrowthIndex f ≤ (s : EReal) := by
    rw [hs]
    split_ifs with hb
    · -- `β ≤ λ²/(2ν)`: let `β' ↑ β` in `β'ν/2 + λ⁴/(8νβ')`
      set g : ℝ → ℝ := fun x => x * ν / 2 + lam ^ 4 / (8 * ν * x) with hg
      have hcont : ContinuousAt g β :=
        ((continuousAt_id.mul continuousAt_const).div_const _).add
          (continuousAt_const.div (continuousAt_const.mul continuousAt_id) (by positivity))
      refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
      induction a using EReal.rec with
      | bot => exact absurd ha (not_lt.2 bot_le)
      | top => exact le_top
      | coe a =>
        have ha' : g β < a := by exact_mod_cast ha
        have hev : ∀ᶠ x in 𝓝[<] β, g x < a ∧ 0 < x ∧ x < β :=
          ((hcont.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds ha')).and
            (((eventually_gt_nhds hβ).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)
        obtain ⟨x, hxa, hx0, hxβ⟩ := hev.exists
        have h1 := hupper x hx0 hxβ
        simp only [show x < lam ^ 2 / (2 * ν) from hxβ.trans_le hb, ↓reduceIte] at h1
        exact h1.trans (by exact_mod_cast hxa.le)
    · -- `β > λ²/(2ν)`: any `β' ∈ (λ²/(2ν), β)` gives `λ̄ ≤ λ²/2`
      have hb' : lam ^ 2 / (2 * ν) < β := not_le.1 hb
      have hpos : 0 < lam ^ 2 / (2 * ν) := by positivity
      have h1 := hupper ((lam ^ 2 / (2 * ν) + β) / 2) (by linarith) (by linarith)
      have hn : ¬ (lam ^ 2 / (2 * ν) + β) / 2 < lam ^ 2 / (2 * ν) := by linarith
      simpa only [hn, ↓reduceIte] using h1
  have hL : (s : EReal) ≤ lowerGrowthIndex f := exExp_lowerIndex_of_envelope hν hlam hβ hlow
  have hLU := lowerGrowthIndex_le_upperGrowthIndex f
  exact ⟨le_antisymm (hLU.trans hU) hL, le_antisymm hU (hL.trans hLU)⟩


end ChenDalang15

end
