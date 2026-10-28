module

public import ChenDalang15.PhiE
public import ChenDalang15.ErfFacts
public import ChenDalang15.Kernel
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Paper `L2:IntGG` and `L:IntIntGG`: time integrals of heat kernels

Chen–Dalang (2015), Appendix, Lemmas `L2:IntGG` and `L:IntIntGG`, with
`G_ν(t,x) = (2πνt)^{-1/2} e^{-x²/(2νt)}` (`G`), `Erfc = erfc`, `Φ = Phi`.

* `integral_G_mul_G_time` (`L2:IntGG`): `∫₀ᵗ G_ν(r,x) G_σ(t-r,y) dr
  = Erfc((|x|/√ν + |y|/√σ)/√(2t)) / (2√(νσ))`;
  `integral_G_div_sqrt`, `integral_G_div_sqrt_le`: its case `x = 0` and the bound
  `Erfc z ≤ e^{-z²}`.
* `integral_G_time`, `integral_integral_G_mul_G`, `integral_integral_G_mul_G_diag`
  (`L:IntIntGG`), the last one being the case `τ = t` with the paper's convention
  `Φ(|x-y|/0) = 1`.

All statements are for positive times: at time `0` the right sides contain `|x|/√0`, a limit in
the paper but Lean's junk value `0` here.

The paper proves `L2:IntGG` by Laplace transforms (not available in Mathlib). Here the
substitution `r = t/(1 + e^{-2s})` turns the time integral into
`(2π√(νσ))⁻¹ ∫_ℝ sech s · e^{-λ M(s)} ds` with `λ = 1/(2t)`,
`M(s) = (A e^{-s} - B e^{s})² + (A+B)²`, `A = |x|/√ν`, `B = |y|/√σ`; the identity
`∫ sech s e^{-λM} ds = π Erfc(√λ (A+B))` (a two-parameter Craig formula) is proved by
differentiating in `λ`, where `∫ sech s · M e^{-λM} ds` has an explicit antiderivative in `s`
(`antiH`), and letting `λ → ∞`. The case `B = 0`, `λ = 1` gives `Erfc z ≤ e^{-z²}`,
the paper's DLMF 7.7.1 argument.
-/

set_option autoImplicit false

public section

namespace ChenDalang15

/-! Helpers live in `ChenDalang15.IntGG` (to avoid clashes with sibling modules that develop
the same `erf` facts); the six paper statements are in `ChenDalang15`. -/
namespace IntGG

open Real MeasureTheory Set Filter Topology

/-! ### The weight `1/cosh` -/

/-- `2/(eˢ + e⁻ˢ) = 1/cosh s`. -/
noncomputable def sech' (s : ℝ) : ℝ := 2 / (exp s + exp (-s))

theorem sech'_pos (s : ℝ) : 0 < sech' s := by unfold sech'; positivity

theorem continuous_sech' : Continuous sech' := by
  unfold sech'
  exact continuous_const.div (by fun_prop) fun s => by positivity

theorem sech'_le (s : ℝ) : sech' s ≤ 4 * (1 + s ^ 2)⁻¹ := by
  unfold sech'
  have h1 : 1 + s ^ 2 / 2 ≤ exp s + exp (-s) := by
    rcases le_total 0 s with hs | hs
    · have := quadratic_le_exp_of_nonneg hs
      have := exp_pos (-s)
      nlinarith
    · have := quadratic_le_exp_of_nonneg (neg_nonneg.2 hs)
      have := exp_pos s
      nlinarith
  rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [exp_pos s, exp_pos (-s)]

theorem integrable_sech' : Integrable sech' := by
  refine (integrable_inv_one_add_sq.const_mul 4).mono' continuous_sech'.aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (sech'_pos s)]
  exact sech'_le s

theorem integral_sech' : ∫ s, sech' s = π := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s => 2 * arctan (exp s)) (sech' s) s := by
    intro s
    have h : HasDerivAt (fun s => 2 * arctan (exp s)) _ s :=
      ((Real.hasDerivAt_arctan (exp s)).comp s (Real.hasDerivAt_exp s)).const_mul 2
    refine h.congr_deriv ?_
    unfold sech'
    rw [exp_neg]
    have := exp_pos s
    field_simp
    ring
  have hbot : Tendsto (fun s => 2 * arctan (exp s)) atBot (𝓝 (2 * arctan 0)) :=
    ((continuous_arctan.tendsto 0).comp tendsto_exp_atBot).const_mul 2
  have htop : Tendsto (fun s => 2 * arctan (exp s)) atTop (𝓝 (2 * (π / 2))) :=
    ((tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp tendsto_exp_atTop).const_mul 2
  rw [integral_of_hasDerivAt_of_tendsto hd integrable_sech' hbot htop]
  simp only [arctan_zero, mul_zero, sub_zero]
  ring

/-! ### The core identity `∫ sech s · e^{-λ M(s)} ds = π erfc(√λ (A+B))`

With `r = t/(1 + e^{-2s})` the time integral of `L2:IntGG` becomes an integral over `s ∈ ℝ`
with weight `1/cosh s` and exponent `λ M(s)`, `M(s) = (A e^{-s} - B e^{s})² + (A+B)²`. -/

/-- The exponent `M(s) = (A e^{-s} - B e^{s})² + (A+B)²`. -/
noncomputable def expoM (A B s : ℝ) : ℝ := (A * exp (-s) - B * exp s) ^ 2 + (A + B) ^ 2

theorem exp_neg_mul_exp (s : ℝ) : exp (-s) * exp s = 1 := by
  rw [← exp_add]; simp

theorem expoM_eq' (A B s : ℝ) :
    expoM A B s = (A * exp (-s) + B * exp s) ^ 2 + (A - B) ^ 2 := by
  unfold expoM
  linear_combination (-4 * A * B) * exp_neg_mul_exp s

theorem expoM_nonneg (A B s : ℝ) : 0 ≤ expoM A B s := by unfold expoM; positivity

theorem sq_le_expoM (A B s : ℝ) : (A + B) ^ 2 ≤ expoM A B s := by
  unfold expoM; nlinarith [sq_nonneg (A * exp (-s) - B * exp s)]

theorem continuous_expoM (A B : ℝ) : Continuous (expoM A B) := by
  unfold expoM; fun_prop

theorem sech'_mul_expoM (A B s : ℝ) :
    sech' s * expoM A B s = 2 * (A ^ 2 * exp (-s) + B ^ 2 * exp s) := by
  unfold sech' expoM
  have h1 := exp_neg_mul_exp s
  have hp : 0 < exp s + exp (-s) := by positivity
  rw [div_mul_eq_mul_div, div_eq_iff hp.ne']
  linear_combination (-(4 * A * B + 2 * A ^ 2 + 2 * B ^ 2)) * h1

/-- `y e^{-μ y} ≤ 1/μ` for `μ > 0`. -/
theorem mul_exp_neg_mul_le (y : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    y * exp (-(μ * y)) ≤ 1 / μ := by
  have h := add_one_le_exp (μ * y)
  have he : exp (-(μ * y)) * exp (μ * y) = 1 := by rw [← exp_add]; simp
  rw [le_div_iff₀ hμ]
  have : 0 ≤ exp (-(μ * y)) := (exp_pos _).le
  nlinarith

/-- An antiderivative of `2 (A² e^{-s} + B² e^{s}) e^{-λ M(s)}`. -/
noncomputable def antiH (A B l s : ℝ) : ℝ :=
  √π / (2 * √l) * (-(A + B) * exp (-l * (A + B) ^ 2) * erf (√l * (A * exp (-s) - B * exp s))
    - (A - B) * exp (-l * (A - B) ^ 2) * erf (√l * (A * exp (-s) + B * exp s)))

theorem hasDerivAt_antiH (A B : ℝ) {l : ℝ} (hl : 0 < l) (s : ℝ) :
    HasDerivAt (antiH A B l)
      (2 * (A ^ 2 * exp (-s) + B ^ 2 * exp s) * exp (-l * expoM A B s)) s := by
  have hm : HasDerivAt (fun s : ℝ => exp (-s)) (exp (-s) * -1) s := (hasDerivAt_neg s).exp
  have hv : HasDerivAt (fun s => √l * (A * exp (-s) - B * exp s))
      (√l * (A * (exp (-s) * -1) - B * exp s)) s :=
    ((hm.const_mul A).sub ((hasDerivAt_exp s).const_mul B)).const_mul (√l)
  have hw : HasDerivAt (fun s => √l * (A * exp (-s) + B * exp s))
      (√l * (A * (exp (-s) * -1) + B * exp s)) s :=
    ((hm.const_mul A).add ((hasDerivAt_exp s).const_mul B)).const_mul (√l)
  have h := ((((hasDerivAt_erf _).comp s hv).const_mul (-(A + B) * exp (-l * (A + B) ^ 2))).sub
    (((hasDerivAt_erf _).comp s hw).const_mul ((A - B) * exp (-l * (A - B) ^ 2)))).const_mul
    (√π / (2 * √l))
  refine h.congr_deriv ?_
  have hX : exp (-l * (A + B) ^ 2) * exp (-(√l * (A * exp (-s) - B * exp s)) ^ 2) =
      exp (-l * expoM A B s) := by
    rw [← exp_add]; congr 1; unfold expoM; rw [mul_pow, sq_sqrt hl.le]; ring
  have hY : exp (-l * (A - B) ^ 2) * exp (-(√l * (A * exp (-s) + B * exp s)) ^ 2) =
      exp (-l * expoM A B s) := by
    rw [← exp_add, expoM_eq']; congr 1; rw [mul_pow, sq_sqrt hl.le]; ring
  have hpi : 0 < √π := sqrt_pos.2 pi_pos
  have hsl : 0 < √l := sqrt_pos.2 hl
  have hc : √π / (2 * √l) * (2 / √π) * √l = 1 := by field_simp
  linear_combination
    (√π / (2 * √l) * (2 / √π) * √l) * ((A + B) * (A * exp (-s) + B * exp s)) * hX
    + (√π / (2 * √l) * (2 / √π) * √l) * ((A - B) * (A * exp (-s) - B * exp s)) * hY
    + (2 * (A ^ 2 * exp (-s) + B ^ 2 * exp s) * exp (-l * expoM A B s)) * hc

/-- `erf(√λ (a f + c g)) → [a ≠ 0]` when `f → ∞`, `g → 0`, `a ≥ 0`. -/
theorem tendsto_erf_lin {α : Type*} {l' : Filter α} {f g : α → ℝ} (hf : Tendsto f l' atTop)
    (hg : Tendsto g l' (𝓝 0)) {a : ℝ} (ha : 0 ≤ a) (c : ℝ) {l : ℝ} (hl : 0 < l) :
    Tendsto (fun s => erf (√l * (a * f s + c * g s))) l' (𝓝 (if a = 0 then 0 else 1)) := by
  rcases ha.eq_or_lt with rfl | ha
  · have h := (continuous_erf.tendsto (√l * (0 + c * 0))).comp
      (((hg.const_mul c).const_add 0).const_mul (√l))
    simp only [mul_zero, add_zero, erf_zero] at h
    simp only [↓reduceIte]
    refine h.congr fun s => ?_
    simp
  · simp only [ha.ne', ite_false]
    have h1 : Tendsto (fun s => a * f s + c * g s) l' atTop :=
      (hf.const_mul_atTop ha).atTop_add (hg.const_mul c)
    exact tendsto_erf_atTop.comp (h1.const_mul_atTop (sqrt_pos.2 hl))

theorem integrable_sech'_mul_expoM_exp (A B : ℝ) {l : ℝ} (hl : 0 < l) :
    Integrable (fun s => 2 * (A ^ 2 * exp (-s) + B ^ 2 * exp s) * exp (-l * expoM A B s)) := by
  refine (integrable_sech'.mul_const (1 / l)).mono'
    (Continuous.aestronglyMeasurable
      (by have := continuous_expoM A B; have := continuous_sech'; fun_prop))
    (Eventually.of_forall fun s => ?_)
  rw [← sech'_mul_expoM, Real.norm_eq_abs, abs_of_nonneg (by
    have := sech'_pos s; have := expoM_nonneg A B s; positivity)]
  have h := mul_exp_neg_mul_le (expoM A B s) hl
  have h2 : sech' s * expoM A B s * exp (-l * expoM A B s) =
      sech' s * (expoM A B s * exp (-(l * expoM A B s))) := by ring_nf
  rw [h2]
  exact mul_le_mul_of_nonneg_left h (sech'_pos s).le

theorem integral_sech'_mul_expoM_exp {A B l : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hl : 0 < l) :
    ∫ s, 2 * (A ^ 2 * exp (-s) + B ^ 2 * exp s) * exp (-l * expoM A B s) =
      (A + B) * (√π / √l) * exp (-l * (A + B) ^ 2) := by
  have hm0 : Tendsto (fun s : ℝ => exp (-s)) atTop (𝓝 0) := tendsto_exp_neg_atTop_nhds_zero
  have hm1 : Tendsto (fun s : ℝ => exp (-s)) atBot atTop :=
    tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  -- limits at `+∞`
  have hv1 := tendsto_erf_lin tendsto_exp_atTop hm0 hB (-A) hl
  have hw1 := tendsto_erf_lin tendsto_exp_atTop hm0 hB A hl
  -- limits at `-∞`
  have hv2 := tendsto_erf_lin hm1 tendsto_exp_atBot hA (-B) hl
  have hw2 := tendsto_erf_lin hm1 tendsto_exp_atBot hA B hl
  set χA : ℝ := if A = 0 then 0 else 1
  set χB : ℝ := if B = 0 then 0 else 1
  have htop : Tendsto (antiH A B l) atTop (𝓝 (√π / (2 * √l) *
      (-(A + B) * exp (-l * (A + B) ^ 2) * (-χB) - (A - B) * exp (-l * (A - B) ^ 2) * χB))) := by
    have hv1' : Tendsto (fun s => erf (√l * (A * exp (-s) - B * exp s))) atTop (𝓝 (-χB)) := by
      refine hv1.neg.congr fun s => ?_
      rw [← erf_neg]; congr 1; ring
    have hw1' : Tendsto (fun s => erf (√l * (A * exp (-s) + B * exp s))) atTop (𝓝 χB) := by
      refine hw1.congr fun s => ?_
      congr 1; ring
    exact (((hv1'.const_mul _).sub (hw1'.const_mul _)).const_mul _)
  have hbot : Tendsto (antiH A B l) atBot (𝓝 (√π / (2 * √l) *
      (-(A + B) * exp (-l * (A + B) ^ 2) * χA - (A - B) * exp (-l * (A - B) ^ 2) * χA))) := by
    have hv2' : Tendsto (fun s => erf (√l * (A * exp (-s) - B * exp s))) atBot (𝓝 χA) := by
      refine hv2.congr fun s => ?_
      congr 1; ring
    have hw2' : Tendsto (fun s => erf (√l * (A * exp (-s) + B * exp s))) atBot (𝓝 χA) := by
      refine hw2.congr fun s => ?_
      ring_nf
    exact (((hv2'.const_mul _).sub (hw2'.const_mul _)).const_mul _)
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_antiH A B hl)
    (integrable_sech'_mul_expoM_exp A B hl) hbot htop]
  have hsl : 0 < √l := sqrt_pos.2 hl
  have hpi : 0 < √π := sqrt_pos.2 pi_pos
  by_cases hA0 : A = 0 <;> by_cases hB0 : B = 0 <;> simp only [χA, χB, hA0, hB0, ite_true,
    ite_false] <;> field_simp <;> ring_nf

theorem integrable_sech'_mul_exp (A B : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    Integrable (fun s => sech' s * exp (-l * expoM A B s)) := by
  refine integrable_sech'.mono'
    (Continuous.aestronglyMeasurable
      (by have := continuous_expoM A B; have := continuous_sech'; fun_prop))
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by have := sech'_pos s; positivity)]
  have h : exp (-l * expoM A B s) ≤ 1 := by
    rw [exp_le_one_iff]; have := expoM_nonneg A B s; nlinarith
  have := sech'_pos s
  nlinarith

theorem integral_sech'_mul_exp_le {A B l : ℝ} (hl : 0 ≤ l) :
    ∫ s, sech' s * exp (-l * expoM A B s) ≤ π * exp (-l * (A + B) ^ 2) := by
  rw [← integral_sech', ← integral_mul_const]
  refine integral_mono (integrable_sech'_mul_exp A B hl)
    (integrable_sech'.mul_const _) fun s => ?_
  refine mul_le_mul_of_nonneg_left ?_ (sech'_pos s).le
  rw [exp_le_exp]
  have := sq_le_expoM A B s
  nlinarith

theorem integral_sech'_mul_exp_nonneg {A B l : ℝ} :
    0 ≤ ∫ s, sech' s * exp (-l * expoM A B s) :=
  integral_nonneg fun s => by have := sech'_pos s; positivity

/-- Differentiation in `λ` under the integral sign. -/
theorem hasDerivAt_integral_sech'_mul_exp (A B : ℝ) {l : ℝ} (hl : 0 < l) :
    HasDerivAt (fun l => ∫ s, sech' s * exp (-l * expoM A B s))
      (-∫ s, 2 * (A ^ 2 * exp (-s) + B ^ 2 * exp s) * exp (-l * expoM A B s)) l := by
  have hl2 : 0 < l / 2 := by positivity
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun l s => sech' s * exp (-l * expoM A B s))
    (F' := fun l s => -(2 * (A ^ 2 * exp (-s) + B ^ 2 * exp s) * exp (-l * expoM A B s)))
    (bound := fun s => sech' s * (1 / (l / 2))) (x₀ := l) (Ioi_mem_nhds (half_lt_self hl))
    (Eventually.of_forall fun l' => Continuous.aestronglyMeasurable
      (by have := continuous_expoM A B; have := continuous_sech'; fun_prop))
    (integrable_sech'_mul_exp A B hl.le)
    (Continuous.aestronglyMeasurable
      (by have := continuous_expoM A B; have := continuous_sech'; fun_prop))
    (Eventually.of_forall fun s l' hl' => ?_) (integrable_sech'.mul_const _)
    (Eventually.of_forall fun s l' _ => ?_)
  · rw [integral_neg] at key
    exact key.2
  · have hl'0 : l / 2 < l' := hl'
    rw [norm_neg, ← sech'_mul_expoM, Real.norm_eq_abs, abs_of_nonneg (by
      have := sech'_pos s; have := expoM_nonneg A B s; positivity)]
    have h := mul_exp_neg_mul_le (expoM A B s) hl2
    have hM := expoM_nonneg A B s
    have h3 : exp (-l' * expoM A B s) ≤ exp (-(l / 2 * expoM A B s)) := by
      rw [exp_le_exp]; nlinarith
    have h4 : expoM A B s * exp (-l' * expoM A B s) ≤ 1 / (l / 2) :=
      le_trans (mul_le_mul_of_nonneg_left h3 hM) h
    have h2 : sech' s * expoM A B s * exp (-l' * expoM A B s) =
        sech' s * (expoM A B s * exp (-l' * expoM A B s)) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h4 (sech'_pos s).le
  · have h := (((hasDerivAt_id l').neg.mul_const (expoM A B s)).exp).const_mul (sech' s)
    refine h.congr_deriv ?_
    rw [← sech'_mul_expoM]
    simp only [Pi.neg_apply, id_eq]
    ring

/-- The core identity: `∫ sech s · e^{-λ M(s)} ds = π erfc(√λ (A+B))`
for `A, B ≥ 0`, `λ > 0`
(a two-parameter form of Craig's formula). -/
theorem integral_sech'_mul_exp {A B l : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hl : 0 < l) :
    ∫ s, sech' s * exp (-l * expoM A B s) = π * erfc (√l * (A + B)) := by
  rcases (add_nonneg hA hB).eq_or_lt with hc | hc
  · have hA0 : A = 0 := by linarith
    have hB0 : B = 0 := by linarith
    subst hA0 hB0
    simp [expoM, integral_sech', erfc_zero]
  set c := A + B with hc_def
  set D : ℝ → ℝ := fun l => (∫ s, sech' s * exp (-l * expoM A B s)) - π * erfc (√l * c)
  have hD : ∀ l : ℝ, 0 < l → HasDerivAt D 0 l := by
    intro l hl
    have h1 := hasDerivAt_integral_sech'_mul_exp A B hl
    rw [integral_sech'_mul_expoM_exp hA hB hl, ← hc_def] at h1
    have herfc : ∀ x, HasDerivAt erfc (-(2 / √π * exp (-x ^ 2))) x := fun x =>
      (hasDerivAt_erf x).const_sub 1
    have h2 := ((herfc _).comp l ((hasDerivAt_sqrt hl.ne').mul_const c)).const_mul π
    refine (h1.sub h2).congr_deriv ?_
    have hsl : 0 < √l := sqrt_pos.2 hl
    have hpi : 0 < √π := sqrt_pos.2 pi_pos
    have he : exp (-(√l * c) ^ 2) = exp (-l * c ^ 2) := by
      congr 1; rw [mul_pow, sq_sqrt hl.le]; ring
    rw [he]
    have hpi2 : √π ^ 2 = π := sq_sqrt pi_pos.le
    field_simp
    ring_nf
    rw [hpi2]
    ring
  have hconst : ∀ μ : ℝ, 0 < μ → D μ = D l := by
    intro μ hμ
    refine (isOpen_Ioi (a := (0 : ℝ))).is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun x hx => (hD x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hD x hx).deriv) hμ hl
  have hlim : Tendsto D atTop (𝓝 0) := by
    have hI : Tendsto (fun l => ∫ s, sech' s * exp (-l * expoM A B s)) atTop (𝓝 0) := by
      have hup : Tendsto (fun l : ℝ => π * exp (-l * c ^ 2)) atTop (𝓝 0) := by
        have : Tendsto (fun l : ℝ => -l * c ^ 2) atTop atBot :=
          Tendsto.atBot_mul_const (pow_pos hc 2) tendsto_neg_atTop_atBot
        simpa using (tendsto_exp_atBot.comp this).const_mul π
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
        (Eventually.of_forall fun l => integral_sech'_mul_exp_nonneg) ?_
      filter_upwards [eventually_ge_atTop 0] with l hl
      exact integral_sech'_mul_exp_le hl
    have hE : Tendsto (fun l => π * erfc (√l * c)) atTop (𝓝 0) := by
      have := (tendsto_erfc_atTop.comp
        (tendsto_sqrt_atTop.atTop_mul_const hc)).const_mul π
      simpa using this
    have := hI.sub hE
    rw [sub_zero] at this
    exact this
  have hev : D =ᶠ[atTop] fun _ => D l := by
    filter_upwards [eventually_gt_atTop 0] with μ hμ
    exact hconst μ hμ
  have h0 : D l = 0 := tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hlim
  have : D l = (∫ s, sech' s * exp (-l * expoM A B s)) - π * erfc (√l * c) := rfl
  linarith

/-! ### The change of variables `r = t/(1 + e^{-2s})` -/

/-- The substitution `r = t/(1 + e^{-2s})`, a bijection `ℝ → (0, t)`. -/
noncomputable def rho (t s : ℝ) : ℝ := t / (1 + exp (-s) ^ 2)

theorem hasDerivAt_rho (t s : ℝ) :
    HasDerivAt (rho t) (2 * t * exp (-s) ^ 2 / (1 + exp (-s) ^ 2) ^ 2) s := by
  have hm : HasDerivAt (fun s : ℝ => exp (-s)) (exp (-s) * -1) s := (hasDerivAt_neg s).exp
  have hu : HasDerivAt (fun s => 1 + exp (-s) ^ 2) (2 * exp (-s) * (exp (-s) * -1)) s := by
    have := (hm.pow 2).const_add 1
    simpa using this
  have h := (hasDerivAt_const s t).div hu (by positivity)
  refine h.congr_deriv ?_
  ring

theorem injective_rho {t : ℝ} (ht : t ≠ 0) : Function.Injective (rho t) := by
  intro s₁ s₂ h
  unfold rho at h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have h2 : exp (-s₁) ^ 2 = exp (-s₂) ^ 2 := by
    have := mul_left_cancel₀ ht h
    linarith
  have h3 : exp (-s₁) = exp (-s₂) := by
    have := (sq_eq_sq₀ (exp_pos _).le (exp_pos _).le).1 h2
    exact this
  have := exp_injective h3
  linarith

theorem range_rho {t : ℝ} (ht : 0 < t) : rho t '' univ = Ioo 0 t := by
  ext r
  simp only [image_univ, mem_range, mem_Ioo]
  constructor
  · rintro ⟨s, rfl⟩
    unfold rho
    have hp : 0 < exp (-s) ^ 2 := by positivity
    refine ⟨by positivity, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  · rintro ⟨hr0, hrt⟩
    have hq : 0 < t / r - 1 := by
      rw [sub_pos, lt_div_iff₀ hr0]; linarith
    refine ⟨-(Real.log (t / r - 1) / 2), ?_⟩
    unfold rho
    have he : exp (-(-(Real.log (t / r - 1) / 2))) ^ 2 = t / r - 1 := by
      rw [← exp_nat_mul, neg_neg]
      push_cast
      rw [show (2 : ℝ) * (Real.log (t / r - 1) / 2) = Real.log (t / r - 1) by ring,
        exp_log hq]
    rw [he]
    field_simp
    ring

/-- The integrand of `L2:IntGG` after the substitution `r = ρ(s)`. -/
theorem abs_deriv_rho_mul_G {ν σ t : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (ht : 0 < t)
    (x y s : ℝ) :
    |2 * t * exp (-s) ^ 2 / (1 + exp (-s) ^ 2) ^ 2| *
        (G ν (rho t s) x * G σ (t - rho t s) y) =
      1 / (2 * π * √(ν * σ)) *
        (sech' s * exp (-(1 / (2 * t)) * expoM (|x| / √ν) (|y| / √σ) s)) := by
  set p := exp (-s) with hp_def
  have hp : 0 < p := exp_pos _
  have hes : exp s = p⁻¹ := by rw [hp_def, exp_neg, inv_inv]
  set A := |x| / √ν with hA_def
  set B := |y| / √σ with hB_def
  have hsν : 0 < √ν := sqrt_pos.2 hν
  have hsσ : 0 < √σ := sqrt_pos.2 hσ
  have hx2 : x ^ 2 = A ^ 2 * ν := by
    rw [hA_def, div_pow, sq_abs, sq_sqrt hν.le]; field_simp
  have hy2 : y ^ 2 = B ^ 2 * σ := by
    rw [hB_def, div_pow, sq_abs, sq_sqrt hσ.le]; field_simp
  have hr : rho t s = t / (1 + p ^ 2) := rfl
  have htr : t - rho t s = t * p ^ 2 / (1 + p ^ 2) := by
    rw [hr]; field_simp; ring
  unfold G sech' expoM
  rw [hes, ← hp_def, htr, hr, abs_of_nonneg (by positivity)]
  -- the square roots
  have hsq : √(2 * π * ν * (t / (1 + p ^ 2))) * √(2 * π * σ * (t * p ^ 2 / (1 + p ^ 2))) =
      2 * π * (√ν * √σ) * (t * p / (1 + p ^ 2)) := by
    rw [← sqrt_mul (by positivity)]
    rw [show 2 * π * ν * (t / (1 + p ^ 2)) * (2 * π * σ * (t * p ^ 2 / (1 + p ^ 2))) =
        (2 * π * (√ν * √σ) * (t * p / (1 + p ^ 2))) ^ 2 by
      simp only [mul_pow, div_pow, sq_sqrt hν.le, sq_sqrt hσ.le]; field_simp]
    exact sqrt_sq (by positivity)
  have hE : -x ^ 2 / (2 * ν * (t / (1 + p ^ 2))) +
      -y ^ 2 / (2 * σ * (t * p ^ 2 / (1 + p ^ 2))) =
      -(1 / (2 * t)) * ((A * p - B * p⁻¹) ^ 2 + (A + B) ^ 2) := by
    rw [hx2, hy2]
    field_simp
    ring
  rw [sqrt_mul hν.le]
  calc 2 * t * p ^ 2 / (1 + p ^ 2) ^ 2 *
        (1 / √(2 * π * ν * (t / (1 + p ^ 2))) * exp (-x ^ 2 / (2 * ν * (t / (1 + p ^ 2)))) *
          (1 / √(2 * π * σ * (t * p ^ 2 / (1 + p ^ 2))) *
            exp (-y ^ 2 / (2 * σ * (t * p ^ 2 / (1 + p ^ 2))))))
      = 2 * t * p ^ 2 / (1 + p ^ 2) ^ 2 /
          (√(2 * π * ν * (t / (1 + p ^ 2))) * √(2 * π * σ * (t * p ^ 2 / (1 + p ^ 2)))) *
          exp (-x ^ 2 / (2 * ν * (t / (1 + p ^ 2))) +
            -y ^ 2 / (2 * σ * (t * p ^ 2 / (1 + p ^ 2)))) := by
        rw [exp_add]; field_simp
    _ = _ := by
        rw [hsq, hE]
        field_simp

/-- **Paper L2:IntGG.** -/
theorem _root_.ChenDalang15.integral_G_mul_G_time
    {ν σ t : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (ht : 0 < t) (x y : ℝ) :
    ∫ r in (0 : ℝ)..t, G ν r x * G σ (t - r) y =
      1 / (2 * Real.sqrt (ν * σ)) *
        erfc ((|x| / Real.sqrt ν + |y| / Real.sqrt σ) / Real.sqrt (2 * t)) := by
  have hsub := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun s _ => (hasDerivAt_rho t s).hasDerivWithinAt) (injective_rho ht.ne').injOn
    (fun r => G ν r x * G σ (t - r) y)
  rw [range_rho ht] at hsub
  rw [intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo, hsub,
    Measure.restrict_univ]
  simp_rw [smul_eq_mul, abs_deriv_rho_mul_G hν hσ ht x y]
  have hl : 0 < 1 / (2 * t) := by positivity
  rw [integral_const_mul, integral_sech'_mul_exp (by positivity) (by positivity) hl]
  have h1 : √(1 / (2 * t)) * (|x| / √ν + |y| / √σ) = (|x| / √ν + |y| / √σ) / √(2 * t) := by
    rw [one_div, sqrt_inv]; ring
  rw [h1]
  have hs : 0 < √(ν * σ) := sqrt_pos.2 (by positivity)
  field_simp

/-- Paper L2:IntGG, special case `x = 0`, and its bound. -/
theorem _root_.ChenDalang15.integral_G_div_sqrt
    {ν σ t : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (ht : 0 < t) (y : ℝ) :
    ∫ r in (0 : ℝ)..t, G σ (t - r) y / Real.sqrt (2 * Real.pi * ν * r) =
      1 / (2 * Real.sqrt (ν * σ)) * erfc (|y| / Real.sqrt (2 * σ * t)) := by
  have hfun : (fun r => G σ (t - r) y / √(2 * π * ν * r)) = fun r => G ν r 0 * G σ (t - r) y := by
    funext r
    unfold G
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
      exp_zero, mul_one]
    ring
  rw [hfun, integral_G_mul_G_time hν hσ ht 0 y]
  congr 2
  rw [abs_zero, zero_div, zero_add, div_div, ← sqrt_mul hσ.le]
  congr 2
  ring

/-- `Erfc z ≤ e^{-z²}` for `z ≥ 0` (paper, proof of `L2:IntGG`, via Craig's formula). -/
theorem erfc_le_exp_neg_sq {z : ℝ} (hz : 0 ≤ z) : erfc z ≤ exp (-z ^ 2) := by
  have h1 := integral_sech'_mul_exp (A := z) (B := 0) (l := 1) hz le_rfl one_pos
  have h2 := integral_sech'_mul_exp_le (A := z) (B := 0) (l := 1) zero_le_one
  rw [h1] at h2
  simp only [sqrt_one, one_mul, add_zero, neg_mul] at h2
  exact le_of_mul_le_mul_left h2 pi_pos

theorem _root_.ChenDalang15.integral_G_div_sqrt_le
    {ν σ t : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (ht : 0 < t) (y : ℝ) :
    1 / (2 * Real.sqrt (ν * σ)) * erfc (|y| / Real.sqrt (2 * σ * t)) ≤
      Real.sqrt (Real.pi * t) / Real.sqrt (2 * ν) * G σ t y := by
  have hs : 0 < √(ν * σ) := sqrt_pos.2 (by positivity)
  have h := erfc_le_exp_neg_sq (z := |y| / √(2 * σ * t)) (by positivity)
  have hz : (|y| / √(2 * σ * t)) ^ 2 = y ^ 2 / (2 * σ * t) := by
    rw [div_pow, sq_abs, sq_sqrt (by positivity)]
  rw [hz] at h
  calc 1 / (2 * √(ν * σ)) * erfc (|y| / √(2 * σ * t))
      ≤ 1 / (2 * √(ν * σ)) * exp (-(y ^ 2 / (2 * σ * t))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = √(π * t) / √(2 * ν) * G σ t y := by
        unfold G
        have e1 : √(2 * π * σ * t) = √2 * √π * √σ * √t := by
          rw [sqrt_mul (by positivity), sqrt_mul (by positivity), sqrt_mul (by positivity)]
        have e2 : √(π * t) = √π * √t := sqrt_mul pi_pos.le _
        have e3 : √(2 * ν) = √2 * √ν := sqrt_mul (by norm_num) _
        have e4 : √(ν * σ) = √ν * √σ := sqrt_mul hν.le _
        have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
        have : 0 < √2 := by positivity
        have : 0 < √π := sqrt_pos.2 pi_pos
        have : 0 < √σ := sqrt_pos.2 hσ
        have : 0 < √ν := sqrt_pos.2 hν
        have : 0 < √t := sqrt_pos.2 ht
        rw [e1, e2, e3, e4, neg_div]
        field_simp
        exact h2

/-! ### Paper `L:IntIntGG` -/

/-- The antiderivative `F(r) = (2|x|/ν) Φ(|x|/√(νr)) + 2 r G_ν(r,x)` of `r ↦ G_ν(r,x)`. -/
noncomputable def antiG (ν x r : ℝ) : ℝ :=
  2 * |x| / ν * Phi (|x| / √(ν * r)) + 2 * r * G ν r x

theorem hasDerivAt_antiG {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) (x : ℝ) :
    HasDerivAt (antiG ν x) (G ν r x) r := by
  have hνr : 0 < ν * r := mul_pos hν hr
  have h2νr : 0 < 2 * ν * r := by positivity
  have h2πνr : 0 < 2 * π * ν * r := by positivity
  have hq : HasDerivAt (fun r => √(ν * r)) (1 / (2 * √(ν * r)) * (ν * 1)) r :=
    (hasDerivAt_sqrt hνr.ne').comp r ((hasDerivAt_id r).const_mul ν)
  have hq0 : √(ν * r) ≠ 0 := (sqrt_pos.2 hνr).ne'
  have hu : HasDerivAt (fun r => |x| / √(ν * r))
      ((0 * √(ν * r) - |x| * (1 / (2 * √(ν * r)) * (ν * 1))) / √(ν * r) ^ 2) r :=
    (hasDerivAt_const r |x|).div hq hq0
  have hP : HasDerivAt (fun r => 2 * |x| / ν * Phi (|x| / √(ν * r)))
      (2 * |x| / ν * (phiDensity (|x| / √(ν * r)) *
        ((0 * √(ν * r) - |x| * (1 / (2 * √(ν * r)) * (ν * 1))) / √(ν * r) ^ 2))) r :=
    ((hasDerivAt_Phi _).comp r hu).const_mul (2 * |x| / ν)
  have hS : HasDerivAt (fun r => √(2 * π * ν * r))
      (1 / (2 * √(2 * π * ν * r)) * (2 * π * ν * 1)) r :=
    (hasDerivAt_sqrt h2πνr.ne').comp r ((hasDerivAt_id r).const_mul (2 * π * ν))
  have hS0 : √(2 * π * ν * r) ≠ 0 := (sqrt_pos.2 h2πνr).ne'
  have hE : HasDerivAt (fun r => exp (-x ^ 2 / (2 * ν * r)))
      (exp (-x ^ 2 / (2 * ν * r)) *
        ((0 * (2 * ν * r) - -x ^ 2 * (2 * ν * 1)) / (2 * ν * r) ^ 2)) r :=
    ((hasDerivAt_const r (-x ^ 2)).div ((hasDerivAt_id r).const_mul (2 * ν)) h2νr.ne').exp
  have hI : HasDerivAt (fun r => 1 / √(2 * π * ν * r))
      ((0 * √(2 * π * ν * r) - 1 * (1 / (2 * √(2 * π * ν * r)) * (2 * π * ν * 1))) /
        √(2 * π * ν * r) ^ 2) r :=
    (hasDerivAt_const r (1 : ℝ)).div hS hS0
  have hG : HasDerivAt (fun r => 2 * r * G ν r x)
      (2 * 1 * G ν r x + 2 * r *
        (((0 * √(2 * π * ν * r) - 1 * (1 / (2 * √(2 * π * ν * r)) * (2 * π * ν * 1))) /
          √(2 * π * ν * r) ^ 2) * exp (-x ^ 2 / (2 * ν * r)) +
        1 / √(2 * π * ν * r) * (exp (-x ^ 2 / (2 * ν * r)) *
          ((0 * (2 * ν * r) - -x ^ 2 * (2 * ν * 1)) / (2 * ν * r) ^ 2)))) r :=
    ((hasDerivAt_id r).const_mul 2).mul (hI.mul hE)
  have h := hP.add hG
  refine h.congr_deriv ?_
  -- algebra: express everything through `q = √(ν r)` and `S = √(2π)`
  have hS2 : √(2 * π * ν * r) = √(2 * π) * √(ν * r) := by
    rw [← sqrt_mul (by positivity)]; ring_nf
  have hph : phiDensity (|x| / √(ν * r)) = (√(2 * π))⁻¹ * exp (-x ^ 2 / (2 * ν * r)) := by
    unfold phiDensity
    congr 2
    rw [div_pow, sq_abs, sq_sqrt hνr.le]
    field_simp
  rw [hph]
  unfold G
  rw [hS2]
  obtain ⟨q, hq_def⟩ : ∃ q, q = √(ν * r) := ⟨_, rfl⟩
  have hq2 : q ^ 2 = ν * r := by rw [hq_def, sq_sqrt hνr.le]
  have hqp : 0 < q := by rw [hq_def]; exact sqrt_pos.2 hνr
  rw [← hq_def]
  have hr' : r = q ^ 2 / ν := by field_simp; linarith
  have hSp : 0 < √(2 * π) := sqrt_pos.2 (by positivity)
  set E := exp (-x ^ 2 / (2 * ν * r))
  clear_value E
  subst hr'
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rw [hx2]
  field_simp
  ring_nf
  rw [sq_sqrt (by positivity)]
  ring

theorem continuous_G_time {ν x : ℝ} (hν : 0 < ν) : ContinuousOn (fun r => G ν r x) (Ioi 0) := by
  intro r hr
  have hr : (0 : ℝ) < r := hr
  unfold G
  have h1 : (0 : ℝ) < 2 * π * ν * r := by positivity
  have h2 : (0 : ℝ) < 2 * ν * r := by positivity
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.mul ?_ ?_
  · refine continuousAt_const.div ?_ (sqrt_pos.2 h1).ne'
    exact (continuous_sqrt.comp (by fun_prop)).continuousAt
  · exact (continuousAt_const.div (by fun_prop) h2.ne').rexp

theorem G_nonneg (ν r x : ℝ) : 0 ≤ G ν r x := by unfold G; positivity

/-- **Paper L:IntIntGG**, first identity (`τ ≥ t > 0`). -/
theorem _root_.ChenDalang15.integral_G_time
    {ν t τ : ℝ} (hν : 0 < ν) (ht : 0 < t) (htτ : t ≤ τ) (x : ℝ) :
    ∫ r in t..τ, G ν r x =
      2 * |x| / ν * (Phi (|x| / Real.sqrt (ν * τ)) - Phi (|x| / Real.sqrt (ν * t)))
        + 2 * τ * G ν τ x - 2 * t * G ν t x := by
  have hpos : ∀ r ∈ Icc t τ, 0 < r := fun r hr => lt_of_lt_of_le ht hr.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htτ
    (fun r hr => (hasDerivAt_antiG hν (hpos r hr) x).continuousAt.continuousWithinAt)
    (fun r hr => hasDerivAt_antiG hν (hpos r (Ioo_subset_Icc_self hr)) x)
    (((continuous_G_time hν).mono fun r hr => hpos r hr).intervalIntegrable_of_Icc htτ)]
  unfold antiG
  ring

/-- The space integral by the semigroup property: for `a, b > 0`,
`∫ G_ν(a, x - z) G_ν(b, y - z) dz = G_ν(a + b, x - y)`. -/
theorem integral_G_mul_G_space {ν a b : ℝ} (hν : 0 < ν) (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    ∫ z, G ν a (x - z) * G ν b (y - z) = G ν (a + b) (x - y) := by
  simp only [G_eq_heatKernel]
  have h := RoughHeatKernel.integral_heatKernel_mul_heatKernel (mul_pos hν hb) (mul_pos hν ha)
    (y - x)
  have h2 := integral_sub_left_eq_self
    (fun u => RoughHeatKernel.heatKernel (ν * a) (y - x - u) *
      RoughHeatKernel.heatKernel (ν * b) u) volume y
  rw [← h2] at h
  rw [mul_add, ← RoughHeatKernel.heatKernel_neg, neg_sub, ← h]
  congr 1
  funext z
  rw [← RoughHeatKernel.heatKernel_neg (ν * a) (x - z)]
  congr 2
  ring

/-- The `r`-integrand of the second identity, after the space integration. -/
theorem integral_integral_G_mul_G_eq {ν t τ : ℝ} (hν : 0 < ν) (ht : 0 < t) (htτ : t ≤ τ)
    (x y : ℝ) :
    ∫ r in (0 : ℝ)..t, ∫ z, G ν (t - r) (x - z) * G ν (τ - r) (y - z) =
      2⁻¹ * ∫ s in (τ - t)..(τ + t), G ν s (x - y) := by
  have h1 : ∫ r in (0 : ℝ)..t, ∫ z, G ν (t - r) (x - z) * G ν (τ - r) (y - z) =
      ∫ r in (0 : ℝ)..t, G ν (t + τ - 2 * r) (x - y) := by
    rw [intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_of_le ht.le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
    rw [integral_G_mul_G_space hν (by linarith [hr.2]) (by linarith [hr.2])]
    congr 1
    ring
  rw [h1, intervalIntegral.integral_comp_sub_mul (fun s => G ν s (x - y)) two_ne_zero,
    smul_eq_mul]
  congr 2 <;> ring

/-- **Paper L:IntIntGG**, second identity (`τ > t > 0`). -/
theorem _root_.ChenDalang15.integral_integral_G_mul_G
    {ν t τ : ℝ} (hν : 0 < ν) (ht : 0 < t) (htτ : t < τ) (x y : ℝ) :
    ∫ r in (0 : ℝ)..t, ∫ z, G ν (t - r) (x - z) * G ν (τ - r) (y - z) =
      |x - y| / ν *
          (Phi (|x - y| / Real.sqrt (ν * (τ + t))) - Phi (|x - y| / Real.sqrt (ν * (τ - t))))
        + (τ + t) * G ν (τ + t) (x - y) - (τ - t) * G ν (τ - t) (x - y) := by
  rw [integral_integral_G_mul_G_eq hν ht htτ.le,
    integral_G_time hν (by linarith) (by linarith) (x - y)]
  ring

theorem tendsto_Phi_atTop : Tendsto Phi atTop (𝓝 1) := by
  have h := ((tendsto_erf_atTop.comp (tendsto_id.atTop_div_const (sqrt_pos.2 two_pos))).const_add
    1).div_const 2
  norm_num at h
  refine h.congr fun x => ?_
  rw [Phi_eq_erf]

/-- `F(r) → 2|x|/ν` as `r → 0⁺`: the paper's convention `Φ(|x|/0) = 1`. -/
theorem tendsto_antiG_zero {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    Tendsto (antiG ν x) (𝓝[>] 0) (𝓝 (2 * |x| / ν)) := by
  have hP : Tendsto (fun r => 2 * |x| / ν * Phi (|x| / √(ν * r))) (𝓝[>] 0)
      (𝓝 (2 * |x| / ν)) := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hs : Tendsto (fun r => √(ν * r)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun r => √(ν * r)) (𝓝 0) (𝓝 (√(ν * 0))) :=
          (continuous_sqrt.comp (continuous_const.mul continuous_id)).tendsto 0
        simp only [mul_zero, sqrt_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact sqrt_pos.2 (mul_pos hν hr)
    have h1 : Tendsto (fun r => |x| / √(ν * r)) (𝓝[>] 0) atTop := by
      have := (tendsto_inv_nhdsGT_zero.comp hs).const_mul_atTop (abs_pos.2 hx)
      refine this.congr fun r => ?_
      simp [div_eq_mul_inv]
    have := (tendsto_Phi_atTop.comp h1).const_mul (2 * |x| / ν)
    simpa using this
  have hG : Tendsto (fun r => 2 * r * G ν r x) (𝓝[>] 0) (𝓝 0) := by
    have hup : Tendsto (fun r => 2 * √r / √(2 * π * ν)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun r => 2 * √r / √(2 * π * ν)) (𝓝 0) (𝓝 (2 * √0 / √(2 * π * ν))) :=
        ((continuous_const.mul continuous_sqrt).div_const _).tendsto 0
      simp only [sqrt_zero, mul_zero, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr : (0 : ℝ) < r := hr
      have := G_nonneg ν r x
      positivity
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr : (0 : ℝ) < r := hr
      unfold G
      have he : exp (-x ^ 2 / (2 * ν * r)) ≤ 1 := by
        rw [exp_le_one_iff, neg_div]
        have : 0 ≤ x ^ 2 / (2 * ν * r) := by positivity
        linarith
      have h1 : √(2 * π * ν * r) = √(2 * π * ν) * √r := sqrt_mul (by positivity) _
      have hsr : 0 < √r := sqrt_pos.2 hr
      have hc : 0 < √(2 * π * ν) := sqrt_pos.2 (by positivity)
      have hr2 : r = √r * √r := (mul_self_sqrt hr.le).symm
      rw [h1]
      calc 2 * r * (1 / (√(2 * π * ν) * √r) * exp (-x ^ 2 / (2 * ν * r)))
          ≤ 2 * r * (1 / (√(2 * π * ν) * √r) * 1) := by gcongr
        _ = 2 * √r / √(2 * π * ν) := by
          rw [show 2 * r * (1 / (√(2 * π * ν) * √r) * 1) =
              2 * (√r * √r) / (√(2 * π * ν) * √r) by rw [← hr2]; ring]
          field_simp
  have := hP.add hG
  rw [add_zero] at this
  exact this

/-- `∫₀ᵀ G_ν(r,x) dr = (2|x|/ν)(Φ(|x|/√(νT)) − 1) + 2T G_ν(T,x)` (the first identity of
`L:IntIntGG` at `t = 0`, with the paper's convention `Φ(|x|/0) = 1`). -/
theorem integral_G_time_zero {ν T : ℝ} (hν : 0 < ν) (hT : 0 < T) (x : ℝ) :
    ∫ r in (0 : ℝ)..T, G ν r x =
      2 * |x| / ν * (Phi (|x| / Real.sqrt (ν * T)) - 1) + 2 * T * G ν T x := by
  classical
  set F := Function.update (antiG ν x) 0 (2 * |x| / ν) with hF
  have hev : ∀ r : ℝ, 0 < r → F =ᶠ[𝓝 r] antiG ν x := by
    intro r hr
    filter_upwards [lt_mem_nhds hr] with z hz
    exact Function.update_of_ne hz.ne' _ _
  have hcont : ContinuousOn F (Icc 0 T) := by
    intro r hr
    rcases hr.1.eq_or_lt with rfl | hr0
    · rw [hF]
      refine continuousWithinAt_update_same.2 ((tendsto_antiG_zero hν x).mono_left ?_)
      refine nhdsWithin_mono _ fun z hz => ?_
      exact lt_of_le_of_ne hz.1.1 (Ne.symm hz.2)
    · exact ((hasDerivAt_antiG hν hr0 x).continuousAt.congr (hev r hr0).symm).continuousWithinAt
  have hderiv : ∀ r ∈ Ioo 0 T, HasDerivAt F (G ν r x) r := fun r hr =>
    (hasDerivAt_antiG hν hr.1 x).congr_of_eventuallyEq (hev r hr.1)
  have hint : IntervalIntegrable (fun r => G ν r x) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).2
      (intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv fun r _ => G_nonneg _ _ _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hcont hderiv hint, hF,
    Function.update_of_ne hT.ne', Function.update_self]
  unfold antiG
  ring

/-- **Paper L:IntIntGG**, second identity at `τ = t`, with the paper's convention
`Φ(|x-y|/0) = 1`. -/
theorem _root_.ChenDalang15.integral_integral_G_mul_G_diag
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x y : ℝ) :
    ∫ r in (0 : ℝ)..t, ∫ z, G ν (t - r) (x - z) * G ν (t - r) (y - z) =
      |x - y| / ν * (Phi (|x - y| / Real.sqrt (ν * (2 * t))) - 1)
        + 2 * t * G ν (2 * t) (x - y) := by
  rw [integral_integral_G_mul_G_eq hν ht le_rfl, sub_self, ← two_mul,
    integral_G_time_zero hν (by positivity) (x - y)]
  ring

end IntGG

end ChenDalang15

end
