module

public import ChenDalang15.TwoPoint
public import ChenDalang15.IntHG
public import ChenDalang15.IntGG
public import ChenDalang15.KConv

/-!
# Corollary `C2:TP-Delta` (Chen–Dalang 2015): Dirac delta initial data

For `μ = δ₀` the homogeneous solution is `J₀ = G_ν`, and the deterministic identities behind
Corollary `C2:TP-Delta` are, for `ν > 0`, `λ ≠ 0`, every `ϑ`, `t > 0` and `x, y ∈ ℝ`:

* `E2:SecMom-Delta`: `G_ν²(t,x) + (G_ν² ⋆ 𝓚)(t,x) + ϑ²𝓗(t) = 𝓚(t,x)/λ² + ϑ²𝓗(t)`;
* `E2:TP-Delta` (`τ = t`): `G_ν(t,x)G_ν(t,y) + 𝓘(t,x,t,y)` equals
  `G_ν(t,x)G_ν(t,y) − ϑ² Erfc(|x−y|/(2√(νt)))
   + (λ²/(4ν) G_{ν/2}(t,(x+y)/2) + ϑ²) e^{(λ⁴t − 2λ²|x−y|)/(4ν)} Erfc((|x−y| − λ²t)/(2√(νt)))`.

Route (paper, Section `Ss:EUM-OtherProof`).

* `E2:SecMom-Delta`: `λ²G_ν² = 𝓛₀`, so `(G_ν² ⋆ 𝓚) = λ⁻² (𝓚 ⋆ 𝓛₀) = λ⁻²(𝓚 − 𝓛₀)` by the
  commutativity of `⋆` (two changes of variables, no integrability needed) and `E:KS-Kn-K0`.
* `E2:TP-Delta`: by the first identity the bracket of `rd1` is `𝓚(r,z)/λ² + ϑ²𝓗(r)` for
  `r > 0`. `L2:GG` writes `G_ν(s,x−z)G_ν(s,y−z) = G_{2ν}(s,x−y) G_{ν/2}(s,(x+y)/2 − z)`, so
  with `E:K` and the semigroup property the space integral is
  `G_{2ν}(t−r,x−y)(k(r)G_{ν/2}(t,(x+y)/2)/λ² + ϑ²𝓗(r))`. Splitting `k` and `𝓗 = (𝓗+1) − 1`
  leaves three time integrals: `L2:IntGG` (`x = 0` case), `L2:IntHG`, and `∫₀ᵗ G_{2ν}(r,x−y)dr`;
  the last one cancels the two explicit `ϑ²` terms of `rd1` at `τ = t`.

Every split of an integral is justified by an explicit integrability proof.

The paper's proof writes the integrand as `(ϑ² + 𝓚/λ² + ϑ²𝓗) G G` "by `E2:TP` (see also the
equivalent formula `E2_:TP`)"; with `rd1` itself the extra `ϑ²` is carried by the two explicit
`ϑ²` terms, which equal `λ²ϑ² ∫₀ᵗ∫ G_ν(t−r,x−z)G_ν(t−r,y−z) dz dr` at `τ = t`
(`L:IntIntGG`). With the convention `Φ(|x−y|/0) = 1` (`PhiGap`) and `(τ−t)G_ν(τ−t,·) = 0`,
`rd1` at `τ = t` is exactly what the corollary needs.

`C2_SecMom_Delta` does not involve `twoPointI`.
-/

set_option autoImplicit false

public section

namespace ChenDalang15

open Real MeasureTheory intervalIntegral

namespace TPDelta

/-! ### Commutativity of the space-time convolution -/

/-- `(f ⋆ g)(t,x) = (g ⋆ f)(t,x)`: the change of variables `(s,y) ↦ (t − s, x − y)`. No
integrability is needed (both changes of variables are measure-preserving bijections). -/
theorem stConv_comm (f g : ℝ → ℝ → ℝ) (t x : ℝ) : stConv f g t x = stConv g f t x := by
  unfold stConv
  have h1 : ∀ s, ∫ y, f s y * g (t - s) (x - y) =
      ∫ y, g (t - s) y * f (t - (t - s)) (x - y) := by
    intro s
    rw [← integral_sub_left_eq_self (fun y => g (t - s) y * f (t - (t - s)) (x - y)) volume x]
    congr 1
    funext y
    simp only [sub_sub_cancel]
    ring
  simp_rw [h1]
  have h2 := intervalIntegral.integral_comp_sub_left
    (fun s => ∫ y, g s y * f (t - s) (x - y)) t (a := 0) (b := t)
  simp only [sub_zero, sub_self] at h2
  exact h2

/-- `λ²G_ν² + λ²(G_ν² ⋆ 𝓚) = 𝓚`, i.e. `G_ν²(t,x) + (G_ν² ⋆ 𝓚)(t,x) = 𝓚(t,x)/λ²`, for `t > 0`
(from `E:KS-Kn-K0` and `𝓛₀ = λ²G_ν²`). -/
theorem G_sq_add_stConv {ν lam : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    G ν t x ^ 2 + stConv (fun s w => G ν s w ^ 2) (K ν lam) t x = K ν lam t x / lam ^ 2 := by
  have h := K_conv_L_zero (lam := lam) hν ht x
  have hL : stConv (K ν lam) (L ν lam 0) t x =
      lam ^ 2 * stConv (K ν lam) (fun s w => G ν s w ^ 2) t x := by
    unfold stConv
    simp only [L]
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    ring
  rw [hL, stConv_comm] at h
  simp only [L] at h
  rw [eq_div_iff (pow_ne_zero 2 hlam)]
  linear_combination h

/-! ### Kernel facts -/

theorem G_pos {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : ℝ) : 0 < G ν t x := by
  rw [G_eq_heatKernel]
  exact RoughHeatKernel.heatKernel_pos (mul_pos hν ht) x

theorem G_nonneg' (ν t x : ℝ) : 0 ≤ G ν t x := by
  unfold G
  positivity

theorem G_neg (ν t x : ℝ) : G ν t (-x) = G ν t x := by
  unfold G
  rw [neg_sq]

/-- `G_ν(t,x) ≤ (2πν)^{-1/2} t^{-1/2}` for `t > 0`. -/
theorem G_le_rpow {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : ℝ) :
    G ν t x ≤ 1 / Real.sqrt (2 * π * ν) * t ^ (-(1 / 2 : ℝ)) := by
  have h := RoughHeatKernel.heatKernel_le_heatKernel_zero (mul_pos hν ht) x
  rw [RoughHeatKernel.heatKernel_zero, ← G_eq_heatKernel] at h
  refine h.trans (le_of_eq ?_)
  rw [show 2 * π * (ν * t) = 2 * π * ν * t by ring, Real.sqrt_mul (by positivity) t,
    Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  field_simp

/-- Paper `L2:GG`, second part: `G_ν(s,a)G_ν(s,b) = G_{2ν}(s,a − b) G_{ν/2}(s,(a + b)/2)`. -/
theorem G_mul_G_eq {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (a b : ℝ) :
    G ν s a * G ν s b = G (2 * ν) s (a - b) * G (ν / 2) s ((a + b) / 2) := by
  unfold G
  have hA : 0 < 2 * π * ν * s := by positivity
  have hq : 0 < Real.sqrt (2 * π * ν * s) := Real.sqrt_pos.2 hA
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have e1 : Real.sqrt (2 * π * (2 * ν) * s) = Real.sqrt 2 * Real.sqrt (2 * π * ν * s) := by
    rw [← Real.sqrt_mul zero_le_two]
    ring_nf
  have e2 : Real.sqrt (2 * π * (ν / 2) * s) = Real.sqrt (2 * π * ν * s) / Real.sqrt 2 := by
    rw [eq_div_iff h2.ne', ← Real.sqrt_mul (by positivity)]
    ring_nf
  rw [e1, e2, mul_mul_mul_comm, ← Real.exp_add, mul_mul_mul_comm (1 / (Real.sqrt 2 * _)),
    ← Real.exp_add]
  congr 1
  · field_simp
  · congr 1
    field_simp
    ring

/-- `∫ G_ν(r,z) G_ν(s,m − z) dz = G_ν(r + s, m)` for `r, s > 0`. -/
theorem integral_G_mul_G_sub {ν r s : ℝ} (hν : 0 < ν) (hr : 0 < r) (hs : 0 < s) (m : ℝ) :
    ∫ z, G ν r z * G ν s (m - z) = G ν (r + s) m := by
  have h := IntGG.integral_G_mul_G_space hν hr hs 0 m
  simp only [zero_sub, G_neg] at h
  exact h

/-- `∫ G_ν(s,m − z) dz = 1` for `s > 0`. -/
theorem integral_G_sub {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (m : ℝ) :
    ∫ z, G ν s (m - z) = 1 := by
  rw [integral_sub_left_eq_self (fun z => G ν s z) volume m]
  simp only [G_eq_heatKernel]
  exact RoughHeatKernel.integral_heatKernel (mul_pos hν hs)

theorem integrable_G_sub {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (m : ℝ) :
    Integrable (fun z => G ν s (m - z)) := by
  have h := (RoughHeatKernel.integrable_heatKernel (mul_pos hν hs)).comp_sub_left m
  simpa only [G_eq_heatKernel] using h

/-- The space integral in `rd1` for `J₀ = G_ν`, after the bracket is reduced to
`𝓚(r,z)/λ² + c`: for `0 < r < t`,
`∫ (𝓚(r,z)/λ² + c) G_ν(t−r,x−z) G_ν(t−r,y−z) dz`
`  = G_{2ν}(t−r,x−y)(k(r)G_{ν/2}(t,(x+y)/2)/λ² + c)`. -/
theorem integral_K_GG {ν lam : ℝ} (hν : 0 < ν) {t r : ℝ} (hr : 0 < r) (hrt : r < t)
    (x y c : ℝ) :
    ∫ z, (K ν lam r z / lam ^ 2 + c) * (G ν (t - r) (x - z) * G ν (t - r) (y - z)) =
      G (2 * ν) (t - r) (x - y) * ((lam ^ 2 / Real.sqrt (4 * π * ν * r) +
          lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) *
            Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))) * G (ν / 2) t ((x + y) / 2) / lam ^ 2 +
          c) := by
  have hs : 0 < t - r := sub_pos.2 hrt
  have hν2 : 0 < ν / 2 := half_pos hν
  set m := (x + y) / 2 with hm
  have hpt : ∀ z, (K ν lam r z / lam ^ 2 + c) * (G ν (t - r) (x - z) * G ν (t - r) (y - z)) =
      G (2 * ν) (t - r) (x - y) * ((lam ^ 2 / Real.sqrt (4 * π * ν * r) +
          lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) *
            Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))) / lam ^ 2 *
        (G (ν / 2) r z * G (ν / 2) (t - r) (m - z)) + c * G (ν / 2) (t - r) (m - z)) := by
    intro z
    rw [K_eq hν hr z, G_mul_G_eq hν hs, show x - z - (y - z) = x - y by ring,
      show (x - z + (y - z)) / 2 = m - z by rw [hm]; ring]
    ring
  have hI1 : ∫ z, G (ν / 2) r z * G (ν / 2) (t - r) (m - z) = G (ν / 2) t m := by
    rw [integral_G_mul_G_sub hν2 hr hs m, add_sub_cancel]
  have hint1 : Integrable (fun z => G (ν / 2) r z * G (ν / 2) (t - r) (m - z)) :=
    Integrable.of_integral_ne_zero (by rw [hI1]; exact (G_pos hν2 (hr.trans hrt) m).ne')
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul, integral_add (hint1.const_mul _)
      ((integrable_G_sub hν2 hs m).const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, hI1, integral_G_sub hν2 hs m]
  ring

/-- Integrability of the space integrand of `rd1` for `J₀ = G_ν`, for `0 < r < t`. -/
theorem integrable_bracket_GG {ν lam : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) {t r : ℝ} (hr : 0 < r)
    (hrt : r < t) (x y v : ℝ) :
    Integrable (fun z => (G ν r z ^ 2 + stConv (fun s w => G ν s w ^ 2) (K ν lam) r z +
      v ^ 2 * Hfun ν lam r) * (G ν (t - r) (x - z) * G ν (t - r) (y - z))) := by
  have hs : 0 < t - r := sub_pos.2 hrt
  have hν2 : 0 < ν / 2 := half_pos hν
  set m := (x + y) / 2 with hm
  have hpt : ∀ z, (G ν r z ^ 2 + stConv (fun s w => G ν s w ^ 2) (K ν lam) r z +
      v ^ 2 * Hfun ν lam r) * (G ν (t - r) (x - z) * G ν (t - r) (y - z)) =
      G (2 * ν) (t - r) (x - y) * ((lam ^ 2 / Real.sqrt (4 * π * ν * r) +
          lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) *
            Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))) / lam ^ 2 *
        (G (ν / 2) r z * G (ν / 2) (t - r) (m - z)) +
          v ^ 2 * Hfun ν lam r * G (ν / 2) (t - r) (m - z)) := by
    intro z
    rw [G_sq_add_stConv hν hlam hr z, K_eq hν hr z, G_mul_G_eq hν hs,
      show x - z - (y - z) = x - y by ring,
      show (x - z + (y - z)) / 2 = m - z by rw [hm]; ring]
    ring
  have hI1 : ∫ z, G (ν / 2) r z * G (ν / 2) (t - r) (m - z) = G (ν / 2) t m := by
    rw [integral_G_mul_G_sub hν2 hr hs m, add_sub_cancel]
  have hint1 : Integrable (fun z => G (ν / 2) r z * G (ν / 2) (t - r) (m - z)) :=
    Integrable.of_integral_ne_zero (by rw [hI1]; exact (G_pos hν2 (hr.trans hrt) m).ne')
  simp_rw [hpt]
  exact ((hint1.const_mul _).add ((integrable_G_sub hν2 hs m).const_mul _)).const_mul _

/-! ### Integrability of the three time integrands -/

/-- `1/√(c u) = (1/√c) u^{-1/2}` for `c ≥ 0`, `u > 0`. -/
theorem one_div_sqrt_mul_eq {c u : ℝ} (hc : 0 ≤ c) (hu : 0 < u) :
    1 / Real.sqrt (c * u) = 1 / Real.sqrt c * u ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_mul hc u, Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  field_simp

theorem measurable_G_sub (σ t d : ℝ) : Measurable (fun r => G σ (t - r) d) := by
  unfold G
  fun_prop

/-- `r ↦ G_σ(t − r, d)` is interval integrable on `[0, t]` (bound `C (t − r)^{-1/2}`). -/
theorem intervalIntegrable_G_sub {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (d : ℝ) :
    IntervalIntegrable (fun r => G σ (t - r) d) volume 0 t := by
  have hG : IntervalIntegrable (fun r => G σ r d) volume 0 t := by
    have hg := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
      (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (1 / Real.sqrt (2 * π * σ))
    refine hg.mono_fun' ?_ ?_
    · have hm : Measurable (fun r => G σ r d) := by unfold G; fun_prop
      exact hm.aestronglyMeasurable
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      refine Filter.Eventually.of_forall fun r hr => ?_
      rw [Set.uIoc_of_le ht.le] at hr
      rw [Real.norm_of_nonneg (G_nonneg' _ _ _)]
      exact G_le_rpow hσ hr.1 d
  have h := hG.comp_sub_left t
  simp only [sub_zero, sub_self] at h
  exact h.symm

/-- `r ↦ G_σ(t − r, d)/√(2πσr)` is interval integrable on `[0, t]` (Beta bound
`C r^{-1/2} (t − r)^{-1/2}`). -/
theorem intervalIntegrable_G_sub_div_sqrt {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (d : ℝ) :
    IntervalIntegrable (fun r => G σ (t - r) d / Real.sqrt (2 * π * σ * r)) volume 0 t := by
  have hg := (intervalIntegrable_rpow_mul_sub_rpow (a := 1 / 2) (b := 1 / 2) (by norm_num)
    (by norm_num) ht).const_mul ((1 / Real.sqrt (2 * π * σ)) ^ 2)
  refine hg.mono_fun' ?_ ?_
  · have hm : Measurable (fun r => G σ (t - r) d / Real.sqrt (2 * π * σ * r)) := by
      unfold G; fun_prop
    exact hm.aestronglyMeasurable
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall fun r hr => ?_
    rw [Set.uIoc_of_le ht.le] at hr
    rw [Real.norm_of_nonneg (div_nonneg (G_nonneg' _ _ _) (Real.sqrt_nonneg _))]
    rcases hr.2.lt_or_eq with hrt | hrt
    · have h1 := G_le_rpow hσ (sub_pos.2 hrt) d
      have h2 := one_div_sqrt_mul_eq (c := 2 * π * σ) (by positivity) hr.1
      rw [div_eq_mul_one_div, h2, show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
      calc G σ (t - r) d * (1 / Real.sqrt (2 * π * σ) * r ^ (-(1 / 2 : ℝ)))
          ≤ (1 / Real.sqrt (2 * π * σ) * (t - r) ^ (-(1 / 2 : ℝ))) *
              (1 / Real.sqrt (2 * π * σ) * r ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_right h1
              (mul_nonneg (by positivity) (Real.rpow_nonneg hr.1.le _))
        _ = (1 / Real.sqrt (2 * π * σ)) ^ 2 *
              (r ^ (-(1 / 2 : ℝ)) * (t - r) ^ (-(1 / 2 : ℝ))) := by ring
    · rw [hrt, sub_self, G_time_zero, zero_div]
      exact mul_nonneg (by positivity)
        (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg le_rfl _))

end TPDelta

/-- **Chen–Dalang (2015), Corollary `C2:TP-Delta`, display `E2:SecMom-Delta`.** For Dirac delta
initial data (`J₀ = G_ν`), `ν > 0` and `λ ≠ 0`, the second-moment expression `E2:SecMom` is
`𝓚(t,x)/λ² + ϑ²𝓗(t)` for every `t > 0` and `x`. -/
theorem C2_SecMom_Delta {ν lam : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) (v : ℝ) :
    ∀ t > 0, ∀ x, secondMomentExpr (G ν) ν v lam t x =
      K ν lam t x / lam ^ 2 + v ^ 2 * Hfun ν lam t := by
  intro t ht x
  unfold secondMomentExpr
  rw [TPDelta.G_sq_add_stConv hν hlam ht x]

namespace TPDelta

/-- Step 1 of `C2:TP-Delta`: the space integrals of `rd1` for `J₀ = G_ν` (the bracket is
`𝓚/λ² + ϑ²𝓗` for `r > 0`, then `L2:GG`, `E:K` and the semigroup property). -/
theorem integral_bracket_GG {ν lam : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) (v : ℝ) {t : ℝ}
    (ht : 0 < t) (x y : ℝ) :
    ∫ r in (0 : ℝ)..t, ∫ z,
        (G ν r z ^ 2 + stConv (fun s w => G ν s w ^ 2) (K ν lam) r z + v ^ 2 * Hfun ν lam r) *
          (G ν (t - r) (x - z) * G ν (t - r) (y - z)) =
      ∫ r in (0 : ℝ)..t, G (2 * ν) (t - r) (x - y) *
        ((lam ^ 2 / Real.sqrt (4 * π * ν * r) +
          lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) *
            Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))) * G (ν / 2) t ((x + y) / 2) / lam ^ 2 +
          v ^ 2 * Hfun ν lam r) := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real t] with r hrt hr
  rw [Set.uIoc_of_le ht.le] at hr
  simp_rw [G_sq_add_stConv hν hlam hr.1]
  exact integral_K_GG hν hr.1 (lt_of_le_of_ne hr.2 hrt) x y _

/-- `∫₀ᵗ G_{2ν}(t − r, d) dr = (|d|/ν)(Φ(|d|/√(2νt)) − 1) + 2t G_{2ν}(t, d)` (`L:IntIntGG` at
`τ = t`, after the space integration). -/
theorem integral_G_two_sub {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (d : ℝ) :
    ∫ r in (0 : ℝ)..t, G (2 * ν) (t - r) d =
      2 * |d| / (2 * ν) * (Phi (|d| / Real.sqrt (2 * ν * t)) - 1) + 2 * t * G (2 * ν) t d := by
  have h2ν : 0 < 2 * ν := by positivity
  have h := intervalIntegral.integral_comp_sub_left (fun r => G (2 * ν) r d) t (a := 0) (b := t)
  simp only [sub_zero, sub_self] at h
  rw [h, IntGG.integral_G_time_zero h2ν ht d]

theorem G_add_self_eq (ν t d : ℝ) : G ν (t + t) d = G (2 * ν) t d := by
  unfold G
  rw [show 2 * π * ν * (t + t) = 2 * π * (2 * ν) * t by ring,
    show 2 * ν * (t + t) = 2 * (2 * ν) * t by ring]

/-- The two explicit `ϑ²` terms of `rd1` at `τ = t` equal `λ²ϑ² ∫₀ᵗ G_{2ν}(t − r, x − y) dr`
(`= λ²ϑ² ∫₀ᵗ∫ G_ν(t−r,x−z)G_ν(t−r,y−z) dz dr`). -/
theorem explicit_terms_eq {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (lam v x y : ℝ) :
    lam ^ 2 * v ^ 2 / ν * |x - y| *
        (Phi (|x - y| / Real.sqrt (ν * (t + t))) - PhiGap ν t t (x - y)) +
      lam ^ 2 * v ^ 2 * ((t + t) * G ν (t + t) (x - y) - (t - t) * G ν (t - t) (x - y)) =
    lam ^ 2 * v ^ 2 * ∫ r in (0 : ℝ)..t, G (2 * ν) (t - r) (x - y) := by
  rw [integral_G_two_sub hν ht, G_add_self_eq, show ν * (t + t) = 2 * ν * t by ring]
  simp only [PhiGap, ite_true, sub_self, zero_mul, sub_zero]
  field_simp
  ring

theorem integral_G_two_sub_pos {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (d : ℝ) :
    0 < ∫ r in (0 : ℝ)..t, G (2 * ν) (t - r) d :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_G_sub (by positivity) ht d)
    (fun r hr => G_pos (by positivity) (sub_pos.2 hr.2) d) ht

/-- `𝓗(r) ≥ 0` for `r ≥ 0`, and the factor `Φ(λ²√(r/(2ν))) ≥ 1/2`. -/
theorem half_le_Phi_of_nonneg {b : ℝ} (hb : 0 ≤ b) : 1 / 2 ≤ Phi b := by
  rw [Phi_eq_erf]
  have := erf_nonneg (div_nonneg hb (Real.sqrt_nonneg 2))
  linarith

theorem Hfun_nonneg {ν lam r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) : 0 ≤ Hfun ν lam r := by
  unfold Hfun
  rw [one_conv_K hν hr 0]
  have h1 := half_le_Phi_of_nonneg (b := lam ^ 2 * Real.sqrt (r / (2 * ν))) (by positivity)
  have h2 : 1 ≤ Real.exp (lam ^ 4 * r / (4 * ν)) :=
    Real.one_le_exp (div_nonneg (mul_nonneg (by positivity) hr) (by positivity))
  nlinarith

/-- The time-space integral of `rd1` (for `J₀ = G_ν`, `τ = t`) is nonnegative. -/
theorem integral_bracket_GG_nonneg {ν lam : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) (v : ℝ) {t : ℝ}
    (ht : 0 < t) (x y : ℝ) :
    0 ≤ ∫ r in (0 : ℝ)..t, ∫ z,
        (G ν r z ^ 2 + stConv (fun s w => G ν s w ^ 2) (K ν lam) r z + v ^ 2 * Hfun ν lam r) *
          (G ν (t - r) (x - z) * G ν (t - r) (y - z)) := by
  rw [integral_bracket_GG hν hlam v ht x y]
  refine intervalIntegral.integral_nonneg ht.le fun r hr => ?_
  have hΦ := half_le_Phi_of_nonneg (b := lam ^ 2 * Real.sqrt (r / (2 * ν))) (by positivity)
  have hH := Hfun_nonneg (lam := lam) hν hr.1
  have hG1 := G_nonneg' (2 * ν) (t - r) (x - y)
  have hG2 := G_nonneg' (ν / 2) t ((x + y) / 2)
  have hk : 0 ≤ lam ^ 2 / Real.sqrt (4 * π * ν * r) +
      lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) *
        Phi (lam ^ 2 * Real.sqrt (r / (2 * ν))) := by
    have : 0 ≤ Phi (lam ^ 2 * Real.sqrt (r / (2 * ν))) := by linarith
    positivity
  positivity

/-- The core computation of `C2:TP-Delta`, stated for the expression of display `rd1` at `τ = t`
**with the paper's grouping**: `λ² (∫₀ᵗ ∫ [⋯] G G dz dr) + (explicit ϑ² terms)`. -/
theorem two_point_rd1 {ν lam : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) (v : ℝ) {t : ℝ} (ht : 0 < t)
    (x y : ℝ) :
    G ν t x * G ν t y +
        (lam ^ 2 * (∫ r in (0 : ℝ)..t, ∫ z,
            (G ν r z ^ 2 + stConv (fun s w => G ν s w ^ 2) (K ν lam) r z +
              v ^ 2 * Hfun ν lam r) * (G ν (t - r) (x - z) * G ν (t - r) (y - z))) +
          lam ^ 2 * v ^ 2 / ν * |x - y| *
            (Phi (|x - y| / Real.sqrt (ν * (t + t))) - PhiGap ν t t (x - y)) +
          lam ^ 2 * v ^ 2 * ((t + t) * G ν (t + t) (x - y) - (t - t) * G ν (t - t) (x - y))) =
      G ν t x * G ν t y - v ^ 2 * erfc (|x - y| / (2 * Real.sqrt (ν * t))) +
        (lam ^ 2 / (4 * ν) * G (ν / 2) t ((x + y) / 2) + v ^ 2) *
          Real.exp ((lam ^ 4 * t - 2 * lam ^ 2 * |x - y|) / (4 * ν)) *
          erfc ((|x - y| - lam ^ 2 * t) / (2 * Real.sqrt (ν * t))) := by
  have h2ν : 0 < 2 * ν := by positivity
  have hl2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
  -- Step 1: the space integrals (bracket of `rd1` = `𝓚/λ² + ϑ²𝓗` for `r > 0`).
  have hinner := integral_bracket_GG hν hlam v ht x y
  -- Step 2: split the time integrand into the three integrals of `L2:IntGG`, `L2:IntHG`
  -- and `∫₀ᵗ G_{2ν}(t − r, x − y) dr`.
  set Gm := G (ν / 2) t ((x + y) / 2) with hGm
  have hsplit : ∫ r in (0 : ℝ)..t, lam ^ 2 * (G (2 * ν) (t - r) (x - y) *
        ((lam ^ 2 / Real.sqrt (4 * π * ν * r) +
          lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) *
            Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))) * Gm / lam ^ 2 +
          v ^ 2 * Hfun ν lam r)) =
      ∫ r in (0 : ℝ)..t, (lam ^ 2 * Gm *
          (G (2 * ν) (t - r) (x - y) / Real.sqrt (2 * π * (2 * ν) * r)) +
        (lam ^ 4 / (4 * ν) * Gm + lam ^ 2 * v ^ 2) *
          ((2 * Real.exp (lam ^ 4 * r / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))) *
            G (2 * ν) (t - r) (x - y)) -
        lam ^ 2 * v ^ 2 * G (2 * ν) (t - r) (x - y)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun r hr => ?_)
    rw [Set.uIoc_of_le ht.le] at hr
    have hr0 := hr.1
    simp only [Hfun]
    rw [one_conv_K hν hr0.le 0, show 4 * π * ν * r = 2 * π * (2 * ν) * r by ring]
    have : 0 < Real.sqrt (2 * π * (2 * ν) * r) := Real.sqrt_pos.2 (by positivity)
    field_simp
    ring
  have hI1 := intervalIntegrable_G_sub_div_sqrt h2ν ht (x - y)
  have hI3 := intervalIntegrable_G_sub h2ν ht (x - y)
  have hI2 : IntervalIntegrable (fun r => (2 * Real.exp (lam ^ 4 * r / (4 * ν)) *
      Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))) * G (2 * ν) (t - r) (x - y)) volume 0 t := by
    refine hI3.continuousOn_mul ?_
    have hΦ : Continuous Phi := continuous_Phi
    exact Continuous.continuousOn (by fun_prop)
  -- Step 3: the three time integrals.
  have hA := integral_G_div_sqrt h2ν h2ν ht (x - y)
  have hB := integral_H_add_one_mul_G hν hlam ht (x - y)
  have hC := integral_G_two_sub hν ht (x - y)
  -- Step 4: assemble; at `τ = t`, `PhiGap = 1` and `(τ − t) G_ν(τ − t, ·) = 0`.
  simp only [PhiGap, ite_true, sub_self, zero_mul, sub_zero]
  rw [hinner, ← intervalIntegral.integral_const_mul, hsplit,
    intervalIntegral.integral_sub ((hI1.const_mul _).add (hI2.const_mul _)) (hI3.const_mul _),
    intervalIntegral.integral_add (hI1.const_mul _) (hI2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hA, hB, hC]
  have e1 : Real.sqrt (2 * ν * (2 * ν)) = 2 * ν := Real.sqrt_mul_self h2ν.le
  have e2 : Real.sqrt (2 * (2 * ν) * t) = 2 * Real.sqrt (ν * t) := by
    rw [show 2 * (2 * ν) * t = 2 ^ 2 * (ν * t) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq zero_le_two]
  have e3 : ν * (t + t) = 2 * ν * t := by ring
  have e4 : G ν (t + t) (x - y) = G (2 * ν) t (x - y) := G_add_self_eq ν t (x - y)
  rw [e1, e2, e3, e4]
  field_simp
  ring

end TPDelta

/-- **Chen–Dalang (2015), Corollary `C2:TP-Delta`, display `E2:TP-Delta`.** For Dirac delta
initial data (`J₀ = G_ν`), `ν > 0`, `λ ≠ 0`, every `ϑ`, `t > 0` and `x, y`, the two-point
expression `E2:TP` at `τ = t` (with `𝓘` from `rd1`, paper convention `Φ(|x−y|/0) = 1`) is
`G_ν(t,x)G_ν(t,y) − ϑ² Erfc(|x−y|/(2√(νt)))
  + (λ²/(4ν) G_{ν/2}(t,(x+y)/2) + ϑ²) e^{(λ⁴t − 2λ²|x−y|)/(4ν)} Erfc((|x−y| − λ²t)/(2√(νt)))`. -/
theorem C2_TP_Delta {ν lam : ℝ} (hν : 0 < ν) (hlam : lam ≠ 0) (v : ℝ) :
    ∀ t > 0, ∀ x y, G ν t x * G ν t y + twoPointI (G ν) ν v lam t x t y =
      G ν t x * G ν t y - v ^ 2 * erfc (|x - y| / (2 * Real.sqrt (ν * t))) +
        (lam ^ 2 / (4 * ν) * G (ν / 2) t ((x + y) / 2) + v ^ 2) *
          Real.exp ((lam ^ 4 * t - 2 * lam ^ 2 * |x - y|) / (4 * ν)) *
          erfc ((|x - y| - lam ^ 2 * t) / (2 * Real.sqrt (ν * t))) := by
  intro t ht x y
  unfold twoPointI
  exact TPDelta.two_point_rd1 hν hlam v ht x y

end ChenDalang15

end
