module

public import ChenDalang15.ItoIdentity
public import ChenDalang15.MomentTheorems
public import ChenDalang15.MomentBridge
public import ChenDalang15.ExExpEnvelope
public import ChenDalang15.GrowthTheorem

/-!
# Second moments and uniqueness for every random field solution (Wave S2, glue)

Chen–Dalang (2015), Theorem `T2:ExUni` parts (1), (3), (4), (5) at `p = 2`, for **every** random
field solution `u` of `E2:WalshSI` in the sense of `Stoch.IsRandomFieldSolution`, with hypotheses
only on the data: the noise (`IsAugmentedWhiteNoise`), the Walsh integral (`IsWalshIntegral`),
`ν > 0`, the initial measure `μ ≥ 0` (s-finite and Gaussian tempered) and `ρ`.

This file connects the stochastic identity `Stoch.momentFn_two_eq_renewal`
(`E u² = J₀² + E ρ(u)² ⋆ G_ν²`, from `ChenDalang15.ItoIdentity`) to the deterministic adapters of
`ChenDalang15.MomentTheorems` (`secondMoment_upper_of_renewal`, `secondMoment_lower_of_renewal`,
`secondMoment_eq_of_renewal`, `eq_zero_of_renewal`), by supplying their remaining hypotheses:

* **measurability** (`measurable_cut_momentFn_two`): the moment function of a field that is jointly
  measurable on `(0,∞) × ℝ × Ω` is measurable at positive times (`LConv.cut`); this covers
  `E u²`, `E ρ(u)²` (`ρ` measurable), `E(u − v)²` and `E(ρ(u) − ρ(v))²`;
* **pointwise moment bounds** from the growth conditions on `ρ`
  (`momentFn_rho_le`, `le_momentFn_rho`, `momentFn_rho_eq`);
* **uniqueness inputs**: the Itô identity for the difference of two solutions
  (`momentFn_sub_eq_lstConv`: `E(u−v)² = E(ρ(u)−ρ(v))² ⋆ G_ν²`, an equality), the Lipschitz bound
  `momentFn_rho_sub_le`, and `momentFn_sub_le_two_mul` (`E(u−v)² ≤ 2(E u² + E v²)`).

## Headline theorems (namespace `ChenDalang15.Stoch`)

* `secondMoment_upper_of_solution` (`E2:SecMom-Up`, `p = 2`);
* `secondMoment_lower_of_solution` (`E2:SecMom-Lower`, `p = 2`; needs neither measurability of
  `ρ` nor any finiteness);
* `secondMoment_eq_of_solution` (`E2:SecMom`, `ρ(u) = λu`);
* `secondMoment_eq_quasilinear_of_solution` (`E2:SecMom`, general quasi-linear offset);
* `solution_unique` (`T2:ExUni(1)`, uniqueness part): two solutions with the same data agree a.s.
  at every `(t,x)` with `t > 0`, for Lipschitz `ρ`;
* end-to-end corollaries: `upperGrowthIndex_le_of_solution` (`T2:Growth(2)`, `p = 2`, `V = 0`),
  `lowerGrowthIndex_ge_of_solution` (`T2:Growth(1)`, `ϑ = 0`, `p = 2`),
  `P2_Ex_Exp_of_solution` (`P2:Ex-Exp`) and `T2_Growth_three_of_solution` (`T2:Growth(3)`, `p = 2`).

These are "for every solution" statements; existence of a solution is Wave S3/S4. All statements
are at `t > 0` (the solution predicate reads nothing at `t ≤ 0`), and all moments are lower
Lebesgue integrals (`momentFn`), so no integrability side condition enters.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.SolutionMoments

open MeasureTheory ProbabilityTheory Set ChenDalang15.Stoch ChenDalang15.LConv
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ### Measurability of moment functions at positive times -/

/-- If a field `X` is jointly measurable on `(0,∞) × ℝ × Ω` (clause `D2:Solution(2)`), then its
second-moment function is measurable at positive times, in the form `MomentTheorems` asks for. -/
theorem measurable_cut_momentFn_two [SFinite P] {X : ℝ → ℝ → Ω → ℝ}
    (hX : Measurable (fun q : Ioi (0 : ℝ) × ℝ × Ω => X q.1 q.2.1 q.2.2)) :
    Measurable (cut (momentFn P X 2)) := by
  have hΦ : Measurable (fun r : (Ioi (0 : ℝ) × ℝ) × Ω => ‖X r.1.1 r.1.2 r.2‖ₑ ^ (2 : ℝ)) := by
    have : Measurable (fun r : (Ioi (0 : ℝ) × ℝ) × Ω => X r.1.1 r.1.2 r.2) :=
      hX.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    exact this.enorm.pow_const _
  have hF : Measurable (fun p : Ioi (0 : ℝ) × ℝ => momentFn P X 2 p.1 p.2) :=
    hΦ.lintegral_prod_right'
  set s : Set (ℝ × ℝ) := {p | 0 < p.1} with hs
  have hfs : Measurable (fun q : s => momentFn P X 2 q.1.1 q.1.2) := by
    have hm : Measurable (fun q : s => ((⟨q.1.1, q.2⟩ : Ioi (0 : ℝ)), q.1.2)) :=
      (measurable_subtype_coe.fst.subtype_mk).prodMk measurable_subtype_coe.snd
    exact hF.comp hm
  have heq : cut (momentFn P X 2) = fun p => if hp : p ∈ s then
      (fun q : s => momentFn P X 2 q.1.1 q.1.2) ⟨p, hp⟩ else (fun _ : (sᶜ : Set (ℝ × ℝ)) => (0 : ℝ≥0∞)) ⟨p, hp⟩ := by
    funext p
    by_cases hp : 0 < p.1
    · simp [cut, hs, hp]
    · simp [cut, hs, hp]
  rw [heq]
  exact Measurable.dite hfs measurable_const (measurableSet_lt measurable_const measurable_fst)

/-! ### Pointwise moment bounds from the growth conditions on `ρ` -/

theorem enorm_rpow_two (a : ℝ) : ‖a‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (a ^ 2) := by
  rw [ENNReal.rpow_two]
  simpa using ItoIdentity.enorm_mul_sq a 1

/-- Upper growth: `|ρ(z)|² ≤ Lip² (V² + z²)` gives `E ρ(u)² ≤ Lip² (V² + E u²)`. -/
theorem momentFn_rho_le [IsProbabilityMeasure P] {ρ : ℝ → ℝ} {Lip V : ℝ}
    (hρ : ∀ z, ρ z ^ 2 ≤ Lip ^ 2 * (V ^ 2 + z ^ 2)) (u : ℝ → ℝ → Ω → ℝ) (s y : ℝ) :
    momentFn P (fun s y ω => ρ (u s y ω)) 2 s y ≤
      ENNReal.ofReal (Lip ^ 2) * (ENNReal.ofReal (V ^ 2) + momentFn P u 2 s y) := by
  simp only [momentFn, enorm_rpow_two]
  calc ∫⁻ ω, ENNReal.ofReal (ρ (u s y ω) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (Lip ^ 2) *
          (ENNReal.ofReal (V ^ 2) + ENNReal.ofReal (u s y ω ^ 2)) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hρ _)
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one]

/-- Lower growth: `lip² (ϑ² + z²) ≤ |ρ(z)|²` gives `lip² (ϑ² + E u²) ≤ E ρ(u)²`. -/
theorem le_momentFn_rho [IsProbabilityMeasure P] {ρ : ℝ → ℝ} {lip ϑ : ℝ}
    (hρ : ∀ z, lip ^ 2 * (ϑ ^ 2 + z ^ 2) ≤ ρ z ^ 2) (u : ℝ → ℝ → Ω → ℝ) (s y : ℝ) :
    ENNReal.ofReal (lip ^ 2) * (ENNReal.ofReal (ϑ ^ 2) + momentFn P u 2 s y) ≤
      momentFn P (fun s y ω => ρ (u s y ω)) 2 s y := by
  simp only [momentFn, enorm_rpow_two]
  calc ENNReal.ofReal (lip ^ 2) *
        (ENNReal.ofReal (ϑ ^ 2) + ∫⁻ ω, ENNReal.ofReal (u s y ω ^ 2) ∂P)
      = ∫⁻ ω, ENNReal.ofReal (lip ^ 2) *
          (ENNReal.ofReal (ϑ ^ 2) + ENNReal.ofReal (u s y ω ^ 2)) ∂P := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hρ _)

/-- Linear `ρ(z) = λ z`: `E ρ(u)² = λ² E u²`. -/
theorem momentFn_rho_eq {ρ : ℝ → ℝ} {lam : ℝ} (hρ : ∀ z, ρ z = lam * z)
    (u : ℝ → ℝ → Ω → ℝ) (s y : ℝ) :
    momentFn P (fun s y ω => ρ (u s y ω)) 2 s y = ENNReal.ofReal (lam ^ 2) * momentFn P u 2 s y := by
  simp only [momentFn, enorm_rpow_two, hρ, mul_pow, ENNReal.ofReal_mul (sq_nonneg lam)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ### Uniqueness inputs -/

/-- A Lipschitz map satisfies the pointwise bound used below. -/
theorem abs_sub_le_of_lipschitzWith {ρ : ℝ → ℝ} {K : ℝ≥0} (hρ : LipschitzWith K ρ) (a b : ℝ) :
    |ρ a - ρ b| ≤ (K : ℝ) * |a - b| := by
  simpa [Real.dist_eq] using hρ.dist_le_mul a b

/-- Lipschitz bound: `|ρ(a) − ρ(b)| ≤ LIP |a − b|` gives `E(ρ(u)−ρ(v))² ≤ LIP² E(u−v)²`. -/
theorem momentFn_rho_sub_le {ρ : ℝ → ℝ} {LIP : ℝ} (hρ : ∀ a b, |ρ a - ρ b| ≤ LIP * |a - b|)
    (u v : ℝ → ℝ → Ω → ℝ) (s y : ℝ) :
    momentFn P (fun s y ω => ρ (u s y ω) - ρ (v s y ω)) 2 s y ≤
      ENNReal.ofReal (LIP ^ 2) * momentFn P (fun s y ω => u s y ω - v s y ω) 2 s y := by
  simp only [momentFn, enorm_rpow_two]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := hρ (u s y ω) (v s y ω)
  have h0 := abs_nonneg (ρ (u s y ω) - ρ (v s y ω))
  calc (ρ (u s y ω) - ρ (v s y ω)) ^ 2 = |ρ (u s y ω) - ρ (v s y ω)| ^ 2 := (sq_abs _).symm
    _ ≤ (LIP * |u s y ω - v s y ω|) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = _ := by rw [mul_pow, sq_abs]

/-- `E(u−v)² ≤ 2(E u² + E v²)`, when `u(s,y)` is measurable (true at `s > 0` for a solution, by
adaptedness). The measurability is needed for additivity of the lower integral. -/
theorem momentFn_sub_le_two_mul [IsProbabilityMeasure P] {u v : ℝ → ℝ → Ω → ℝ} {s y : ℝ}
    (hu : Measurable (u s y)) :
    momentFn P (fun s y ω => u s y ω - v s y ω) 2 s y ≤
      2 * (momentFn P u 2 s y + momentFn P v 2 s y) := by
  simp only [momentFn, enorm_rpow_two]
  rw [← lintegral_add_left ((hu.pow_const 2).ennreal_ofReal),
    ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
  refine lintegral_mono fun ω => ?_
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (u s y ω + v s y ω)])

/-- The difference of two integral fields (same `J`, `ν`, `ρ`) is an integral field of the
difference `ρ(u) − ρ(v)` (with the identity as nonlinearity): linearity of `J`. -/
theorem isIntegralField_sub [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} {ν : ℝ} {ρ : ℝ → ℝ} {u v : ℝ → ℝ → Ω → ℝ}
    {Iu Iv : ℝ → ℝ → Lp ℝ 2 P} (hu : IsIntegralField J ν ρ u Iu)
    (hv : IsIntegralField J ν ρ v Iv) :
    IsIntegralField J ν (fun z => z) (fun s y ω => ρ (u s y ω) - ρ (v s y ω))
      (fun t x => Iu t x - Iv t x) := by
  intro t ht x
  obtain ⟨gu, hgu, hIu⟩ := hu t ht x
  obtain ⟨gv, hgv, hIv⟩ := hv t ht x
  refine ⟨gu - gv, ?_, by show Iu t x - Iv t x = _; rw [hIu, hIv, map_sub]⟩
  have hc : ((gu - gv : PredL2 F P) : Lp ℝ 2 (spaceTimeSample P)) =
      (gu : Lp ℝ 2 (spaceTimeSample P)) - gv := rfl
  rw [hc]
  filter_upwards [Lp.coeFn_sub (gu : Lp ℝ 2 (spaceTimeSample P)) gv, hgu, hgv] with q h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  ring

/-- **Itô identity for the difference of two solutions**:
`E(u−v)²(t,x) = (E(ρ(u)−ρ(v))² ⋆ G_ν²)(t,x)` for `t > 0` (an equality; uniqueness uses `≤`). -/
theorem momentFn_sub_eq_lstConv [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {ρ : ℝ → ℝ} {μ : Measure ℝ} {u v : ℝ → ℝ → Ω → ℝ}
    (hu : IsRandomFieldSolution J ν ρ μ u) (hv : IsRandomFieldSolution J ν ρ μ v)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    momentFn P (fun s y ω => u s y ω - v s y ω) 2 t x =
      lstConv (momentFn P (fun s y ω => ρ (u s y ω) - ρ (v s y ω)) 2)
        (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x := by
  obtain ⟨Iu, hIu, -, hequ⟩ := hu.integral
  obtain ⟨Iv, hIv, -, heqv⟩ := hv.integral
  have h : ∫⁻ ω, ‖(Iu t x - Iv t x) ω‖ₑ ^ 2 ∂P =
      lstConv (momentFn P (fun s y ω => ρ (u s y ω) - ρ (v s y ω)) 2)
        (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x :=
    lintegral_sq_integralField_eq_lstConv hW hJ hν (isIntegralField_sub hIu hIv) ht x
  rw [← h, momentFn]
  simp_rw [ENNReal.rpow_two]
  refine lintegral_congr_ae ?_
  filter_upwards [hequ t ht x, heqv t ht x, Lp.coeFn_sub (Iu t x) (Iv t x)] with ω h1 h2 h3
  rw [h1, h2, h3, Pi.sub_apply]
  ring_nf

end ChenDalang15.SolutionMoments

namespace ChenDalang15.Stoch

open MeasureTheory ProbabilityTheory Set ChenDalang15.SolutionMoments
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ### Measurability for solutions -/

theorem measurable_cut_momentFn_solution [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} {ν : ℝ} {ρ : ℝ → ℝ} {μ : Measure ℝ}
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u) :
    Measurable (LConv.cut (momentFn P u 2)) :=
  measurable_cut_momentFn_two hu.jointlyMeasurable

theorem measurable_cut_momentFn_rho_solution [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} {ν : ℝ} {ρ : ℝ → ℝ} (hρm : Measurable ρ) {μ : Measure ℝ}
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u) :
    Measurable (LConv.cut (momentFn P (fun s y ω => ρ (u s y ω)) 2)) :=
  measurable_cut_momentFn_two (hρm.comp hu.jointlyMeasurable)

/-! ### Headline theorems -/

/-- **`E2:SecMom-Up` (`p = 2`) for every solution.** For a white noise with its augmented
filtration, the Walsh integral `J`, `ν > 0`, an s-finite Gaussian-tempered `μ ≥ 0`, and a
measurable `ρ` with `|ρ(z)|² ≤ Lip² (V² + z²)`: every random field solution satisfies
`E|u(t,x)|² ≤ J₀² + J₀² ⋆ 𝓚_Lip + V² 𝓗_Lip(t)` for `t > 0`. -/
theorem secondMoment_upper_of_solution [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {Lip V : ℝ}
    (hρ : ∀ z, ρ z ^ 2 ≤ Lip ^ 2 * (V ^ 2 + z ^ 2))
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u) :
    ∀ t > 0, ∀ x, momentFn P u 2 t x ≤
      ENNReal.ofReal (secondMomentExpr (J0 ν μ) ν V Lip t x) :=
  MomentTheorems.secondMoment_upper_of_renewal hT hν Lip V
    (measurable_cut_momentFn_solution hu) (measurable_cut_momentFn_rho_solution hρm hu)
    (fun _ ht x => momentFn_two_eq_renewal hW hJ hν hu ht x)
    (fun s _ y => momentFn_rho_le hρ u s y) hu.finite

/-- **`E2:SecMom-Lower` (`p = 2`) for every solution.** With `lip² (ϑ² + z²) ≤ |ρ(z)|²`:
`J₀² + J₀² ⋆ 𝓚_lip + ϑ² 𝓗_lip(t) ≤ E|u(t,x)|²` for `t > 0`. No measurability of `ρ` is needed. -/
theorem secondMoment_lower_of_solution [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} {lip ϑ : ℝ} (hρ : ∀ z, lip ^ 2 * (ϑ ^ 2 + z ^ 2) ≤ ρ z ^ 2)
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u) :
    ∀ t > 0, ∀ x, ENNReal.ofReal (secondMomentExpr (J0 ν μ) ν ϑ lip t x) ≤
      momentFn P u 2 t x :=
  MomentTheorems.secondMoment_lower_of_renewal hT hν lip ϑ
    (measurable_cut_momentFn_solution hu)
    (fun _ ht x => momentFn_two_eq_renewal hW hJ hν hu ht x)
    (fun s _ y => le_momentFn_rho hρ u s y)

/-- **`E2:SecMom` for `ρ(u) = λu`, for every solution**: `E|u(t,x)|² = J₀² + J₀² ⋆ 𝓚_λ` for
`t > 0`. -/
theorem secondMoment_eq_of_solution [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} {lam : ℝ} (hρ : ∀ z, ρ z = lam * z)
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u) :
    ∀ t > 0, ∀ x, momentFn P u 2 t x = ENNReal.ofReal (secondMomentExpr (J0 ν μ) ν 0 lam t x) := by
  have hρm : Measurable ρ := by
    have : ρ = fun z => lam * z := funext hρ
    rw [this]; exact measurable_const.mul measurable_id
  exact MomentTheorems.secondMoment_eq_of_renewal hT hν lam
    (measurable_cut_momentFn_solution hu) (measurable_cut_momentFn_rho_solution hρm hu)
    (fun _ ht x => momentFn_two_eq_renewal hW hJ hν hu ht x)
    (fun s _ y => momentFn_rho_eq hρ u s y) hu.finite

/-- **`E2:SecMom` under the quasi-linear condition `E1:qlinear`, for every solution.**
The offset need not vanish: `ρ(z)² = λ² (ϑ² + z²)` gives
`E|u(t,x)|² = J₀² + J₀² ⋆ 𝓚_λ + ϑ² 𝓗_λ(t)` for `t > 0`.
This proves the second-moment part of `T2:ExUni(5)` for an existing solution;
it asserts neither existence nor the two-point formula. -/
theorem secondMoment_eq_quasilinear_of_solution [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {lam ϑ : ℝ}
    (hρ : ∀ z, ρ z ^ 2 = lam ^ 2 * (ϑ ^ 2 + z ^ 2))
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u) :
    ∀ t > 0, ∀ x, momentFn P u 2 t x =
      ENNReal.ofReal (secondMomentExpr (J0 ν μ) ν ϑ lam t x) :=
  fun t ht x => le_antisymm
    (secondMoment_upper_of_solution hW hJ hν hT hρm (fun z => (hρ z).le) hu t ht x)
    (secondMoment_lower_of_solution hW hJ hν hT (fun z => (hρ z).ge) hu t ht x)

/-- **Uniqueness (`T2:ExUni(1)`) for Lipschitz `ρ`.** Two random field solutions with the same
noise, `J`, `ν`, `ρ` and `μ` agree a.s. at every `(t,x)` with `t > 0`. `ρ` is measurable and
`|ρ(a) − ρ(b)| ≤ LIP |a − b|` (see `abs_sub_le_of_lipschitzWith` for `LipschitzWith`); `μ` is
s-finite and Gaussian tempered. -/
theorem solution_unique [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} [SFinite μ] (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {LIP : ℝ} (hρ : ∀ a b, |ρ a - ρ b| ≤ LIP * |a - b|)
    {u v : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u)
    (hv : IsRandomFieldSolution J ν ρ μ v) :
    ∀ t > 0, ∀ x, u t x =ᵐ[P] v t x := by
  have hw0 := MomentTheorems.eq_zero_of_renewal hT hν LIP
    (w := momentFn P (fun s y ω => u s y ω - v s y ω) 2)
    (g := momentFn P (fun s y ω => ρ (u s y ω) - ρ (v s y ω)) 2)
    (measurable_cut_momentFn_two (hu.jointlyMeasurable.sub hv.jointlyMeasurable))
    (measurable_cut_momentFn_solution hu)
    (measurable_cut_momentFn_rho_solution hρm hu) (measurable_cut_momentFn_rho_solution hρm hv)
    (fun t ht x => (momentFn_sub_eq_lstConv hW hJ hν hu hv ht x).le)
    (fun s _ y => momentFn_rho_sub_le hρ u v s y)
    (fun s hs y => momentFn_sub_le_two_mul ((hu.adapted s hs y).mono (F.le _) le_rfl))
    (fun t ht x => momentFn_two_eq_renewal hW hJ hν hu ht x)
    (fun t ht x => momentFn_two_eq_renewal hW hJ hν hv ht x)
    hu.finite hv.finite
  intro t ht x
  have h0 := hw0 t ht x
  have hmu : Measurable (u t x) := (hu.adapted t ht x).mono (F.le _) le_rfl
  have hmv : Measurable (v t x) := (hv.adapted t ht x).mono (F.le _) le_rfl
  have hmeas : Measurable fun ω => ‖u t x ω - v t x ω‖ₑ ^ (2 : ℝ) :=
    (hmu.sub hmv).enorm.pow_const _
  rw [momentFn, lintegral_eq_zero_iff hmeas] at h0
  filter_upwards [h0] with ω hω
  have hω' : ‖u t x ω - v t x ω‖ₑ ^ (2 : ℝ) = 0 := hω
  rw [enorm_rpow_two, ENNReal.ofReal_eq_zero] at hω'
  have : (u t x ω - v t x ω) ^ 2 = 0 := le_antisymm hω' (sq_nonneg _)
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)

/-! ### End-to-end corollaries: growth indices of every solution -/

/-- **`T2:Growth(2)` (`p = 2`, `V = 0`) for every solution.** For `μ ≥ 0` with
`∫ e^{β|y|} μ(dy) < ∞` (`β > 0`), measurable `ρ` with `|ρ(z)|² ≤ Lip² z²`, `Lip ≠ 0`:
`λ̄(2) ≤ βν/2 + Lip⁴/(8νβ)` if `β < Lip²/(2ν)`, and `≤ Lip²/2` otherwise. -/
theorem upperGrowthIndex_le_of_solution [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} {β : ℝ} (hβ : 0 < β) (hI : Integrable (fun y => Real.exp (β * |y|)) μ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) {Lip : ℝ} (hLip : Lip ≠ 0)
    (hρ : ∀ z, ρ z ^ 2 ≤ Lip ^ 2 * z ^ 2)
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u) :
    upperGrowthIndex (momentFn P u 2) ≤
      ((if β < Lip ^ 2 / (2 * ν) then β * ν / 2 + Lip ^ 4 / (8 * ν * β) else Lip ^ 2 / 2 : ℝ) :
        EReal) := by
  have := GrowthUpper.isFiniteMeasure_of_integrable_exp hβ.le hI
  have hT := RoughHeatKernel.isGaussianTempered_of_isFiniteMeasure μ
  refine T2_Growth_upper hν hβ hLip hI fun t ht x => ?_
  have h := secondMoment_upper_of_solution hW hJ hν hT hρm (V := 0)
    (fun z => by simpa using hρ z) hu t ht x
  simpa [secondMomentExpr] using h

/-- **`T2:Growth(1)` (`ϑ = 0`, `p = 2`) for every solution.** For a nonzero Gaussian-tempered
`μ ≥ 0` and `ρ` with `lip² z² ≤ |ρ(z)|²`, `lip ≠ 0`: `λ̲(2) ≥ lip²/2`. -/
theorem lowerGrowthIndex_ge_of_solution [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} [SFinite μ] (hμ0 : μ ≠ 0) (hT : RoughHeatKernel.IsGaussianTempered μ)
    {ρ : ℝ → ℝ} {lip : ℝ} (hlip : lip ≠ 0) (hρ : ∀ z, lip ^ 2 * z ^ 2 ≤ ρ z ^ 2)
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν ρ μ u) :
    ((lip ^ 2 / 2 : ℝ) : EReal) ≤ lowerGrowthIndex (momentFn P u 2) := by
  have hlow := secondMoment_lower_of_solution hW hJ hν hT (ϑ := 0)
    (fun z => by simpa using hρ z) hu
  refine T2_Growth_lower hμ0 (S1Glue.integrable_exp_neg_sq_iff.2 hT) hν hlip fun t ht x => ?_
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hlow t ht x)
  have hJ0 := MomentBridge.stConv_J0_sq_K_nonneg hν μ lip ht x
  rw [secondMomentExpr]
  nlinarith [sq_nonneg (J0 ν μ t x)]

/-- **`P2:Ex-Exp` for every solution** of `E2:WalshSI` with `ρ(u) = λu`, `λ ≠ 0`, and
`μ(dx) = e^{−β|x|} dx` (`β > 0`): both growth indices of `E|u|²` equal
`βν/2 + λ⁴/(8νβ)` if `β ≤ λ²/(2ν)`, and `λ²/2` otherwise. -/
theorem P2_Ex_Exp_of_solution [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {lam β : ℝ} (hlam : lam ≠ 0) (hβ : 0 < β) {u : ℝ → ℝ → Ω → ℝ}
    (hu : IsRandomFieldSolution J ν (fun z => lam * z)
      (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-β * |x|))) u) :
    lowerGrowthIndex (momentFn P u 2) =
        ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
          EReal) ∧
      upperGrowthIndex (momentFn P u 2) =
        ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
          EReal) :=
  P2_Ex_Exp hν hlam hβ
    (secondMoment_eq_of_solution hW hJ hν (ExExpEnvelope.isGaussianTempered_expMeasure hβ)
      (fun _ => rfl) hu)

/-- **`T2:Growth(3)` (`p = 2`, `ϑ = 0`) for every solution** with `ρ(u) = λu`, `λ ≠ 0`, a nonzero
`μ ≥ 0` with `∫ e^{β|y|} dμ < ∞` and `β ≥ λ²/(2ν)`: `λ̲(2) = λ̄(2) = λ²/2`. -/
theorem T2_Growth_three_of_solution [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} (hμ0 : μ ≠ 0) {lam β : ℝ} (hlam : lam ≠ 0) (hβ : lam ^ 2 / (2 * ν) ≤ β)
    (hI : Integrable (fun y => Real.exp (β * |y|)) μ)
    {u : ℝ → ℝ → Ω → ℝ} (hu : IsRandomFieldSolution J ν (fun z => lam * z) μ u) :
    lowerGrowthIndex (momentFn P u 2) = ((lam ^ 2 / 2 : ℝ) : EReal) ∧
      upperGrowthIndex (momentFn P u 2) = ((lam ^ 2 / 2 : ℝ) : EReal) := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have := GrowthUpper.isFiniteMeasure_of_integrable_exp hβ0.le hI
  have hT := RoughHeatKernel.isGaussianTempered_of_isFiniteMeasure μ
  have heq := secondMoment_eq_of_solution hW hJ hν hT (fun _ => rfl) hu
  refine T2_Growth_three hμ0 hν hlam hβ hI (fun t ht x => ?_) (fun t ht x => ?_)
  · rw [heq t ht x]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [secondMomentExpr]
    nlinarith [sq_nonneg (J0 ν μ t x)]
  · rw [heq t ht x, ← MomentBridge.ofReal_J0_sq_add_stConv hT hν lam ht x, secondMomentExpr]
    simp

end ChenDalang15.Stoch

end

end
