module

public import ChenDalang15.H
public import ChenDalang15.KConv
public import ChenDalang15.MomentBridge
public import Mathlib.Analysis.LConvolution

/-!
# The lower-integral space-time convolution `lstConv` (Wave S1, renewal algebra)

Moment functions such as `E|u(t,x)|²` naturally live in `ℝ≥0∞`, and the renewal inequalities
of Chen–Dalang (2015) (`E2:SecMom-Up`, `E2:SecMom-Lower`) are iterated space-time convolutions
of nonnegative functions. This file sets up that convolution as a lower Lebesgue integral,
for which Tonelli needs no integrability hypotheses:

`lstConv f g t x = ∫⁻_{s ∈ (0,t)} ∫⁻_ℝ f(s,y) g(t−s, x−y) dy ds`.

**Choice of the time domain.** We integrate over the open interval `Ioo 0 t`. For `t > 0` this
differs from `stConv`'s `∫ s in 0..t` (whose set is `Ioc 0 t`) by the null set `{t}`
(`lstConv_eq_Ioc`). The open interval makes associativity an *exact* identity: both nestings
integrate over `{0 < r < s < t}` with no boundary point to discard, and the convolution is
literally Mathlib's `lconvolution` on `ℝ × ℝ` of the functions cut off at positive times
(`lstConv_eq_lconvolution`). For `t ≤ 0` the value is `0` (`lstConv_of_nonpos`), which is the
paper's convention, and only the values of `f` and `g` at positive times matter.

Main results:

* algebra: `lstConv_mono_left/right`, `lstConv_zero_left/right`, `lstConv_add_left/right`,
  `lstConv_const_mul_left/right`, `lstConv_tsum_left`, `measurable_lstConv`, and
  associativity `lstConv_assoc` (jointly measurable arguments);
* Bochner bridge: `ofReal_stConv_le_lstConv` (no integrability), and equality
  `ofReal_stConv_eq_lstConv` (iterated integrability) / `ofReal_stConv_eq_lstConv_of_integrable`
  (integrability on `(0,t] × ℝ`, the form of `MomentBridge.integrable_J0_sq_K`);
* resolvent forms in `ℝ≥0∞`: `lstConv_ofReal_L_L_zero` (`𝓛ₙ ⋆ 𝓛₀ = 𝓛ₙ₊₁`, every `t`),
  `ofReal_K_eq_tsum` (`𝓚 = Σ 𝓛ₙ`, every `t`), `lstConv_ofReal_K_L_zero_add`
  (`𝓚 ⋆ 𝓛₀ + 𝓛₀ = 𝓚`, every `t`), `lstConv_one_ofReal_K` (`1 ⋆ 𝓚 = 𝓗`, `t ≥ 0`), and the
  Gaussian-tempered bridge `lstConv_ofReal_J0_sq_K`;
* `BCoeff_mono`, `L_le_BCoeff_mul_L_zero`, `lstConv_ofReal_L_zero_L_zero` (`𝓛₀ ⋆ 𝓛₀ = B₁(t) 𝓛₀`)
  and the remainder estimate `lstConv_ofReal_L_le_BCoeff_mul` (`f ⋆ 𝓛ₙ ≤ Bₙ(t) (f ⋆ 𝓛₀)`, every
  `f`, no measurability).
-/

set_option autoImplicit false

@[expose] public section

open scoped ENNReal
open MeasureTheory Set Filter Real

namespace ChenDalang15

/-- The space-time convolution of `ℝ≥0∞`-valued functions as a lower Lebesgue integral:
`(f ⋆ g)(t,x) = ∫⁻_{s ∈ (0,t)} ∫⁻_ℝ f(s,y) g(t−s, x−y) dy ds`. -/
noncomputable def lstConv (f g : ℝ → ℝ → ℝ≥0∞) (t x : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioo 0 t, ∫⁻ y, f s y * g (t - s) (x - y)

/-! ### Elementary facts -/

theorem lstConv_of_nonpos (f g : ℝ → ℝ → ℝ≥0∞) {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    lstConv f g t x = 0 := by
  simp [lstConv, Ioo_eq_empty (not_lt.mpr ht)]

/-- The `Ioc` form, matching the set of `stConv`'s `∫ s in 0..t`. -/
theorem lstConv_eq_Ioc (f g : ℝ → ℝ → ℝ≥0∞) (t x : ℝ) :
    lstConv f g t x = ∫⁻ s in Ioc 0 t, ∫⁻ y, f s y * g (t - s) (x - y) :=
  setLIntegral_congr Ioo_ae_eq_Ioc

@[simp] theorem lstConv_zero_left (g : ℝ → ℝ → ℝ≥0∞) : lstConv 0 g = 0 := by
  funext t x; simp [lstConv]

@[simp] theorem lstConv_zero_right (f : ℝ → ℝ → ℝ≥0∞) : lstConv f 0 = 0 := by
  funext t x; simp [lstConv]

/-- Monotonicity in the first argument (only values at times in `(0,t)` matter). -/
theorem lstConv_mono_left {f f' g : ℝ → ℝ → ℝ≥0∞} {t : ℝ}
    (h : ∀ s ∈ Ioo 0 t, ∀ y, f s y ≤ f' s y) (x : ℝ) :
    lstConv f g t x ≤ lstConv f' g t x := by
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => lintegral_mono fun y => ?_
  exact mul_le_mul_left (h s hs y) _

/-- Monotonicity in the second argument (only values at times in `(0,t)` matter). -/
theorem lstConv_mono_right {f g g' : ℝ → ℝ → ℝ≥0∞} {t : ℝ}
    (h : ∀ r ∈ Ioo 0 t, ∀ z, g r z ≤ g' r z) (x : ℝ) :
    lstConv f g t x ≤ lstConv f g' t x := by
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => lintegral_mono fun y => ?_
  exact mul_le_mul_right (h (t - s) ⟨sub_pos.mpr hs.2, by linarith [hs.1]⟩ (x - y)) _

theorem lstConv_mono {f f' g g' : ℝ → ℝ → ℝ≥0∞} (hf : f ≤ f') (hg : g ≤ g') :
    lstConv f g ≤ lstConv f' g' := fun _ x =>
  (lstConv_mono_left (fun s _ y => hf s y) x).trans (lstConv_mono_right (fun r _ z => hg r z) x)

theorem lstConv_const_mul_left (f g : ℝ → ℝ → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ⊤) (t x : ℝ) :
    lstConv (fun s y => c * f s y) g t x = c * lstConv f g t x := by
  simp only [lstConv, mul_assoc]
  rw [← lintegral_const_mul' _ _ hc]
  congr 1; funext s
  rw [lintegral_const_mul' _ _ hc]

theorem lstConv_const_mul_right (f g : ℝ → ℝ → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ⊤) (t x : ℝ) :
    lstConv f (fun s y => c * g s y) t x = c * lstConv f g t x := by
  simp only [lstConv, mul_left_comm _ c]
  rw [← lintegral_const_mul' _ _ hc]
  congr 1; funext s
  rw [lintegral_const_mul' _ _ hc]

namespace LConv

/-- The integrand `(s,y) ↦ f(s,y) g(t−s, x−y)` is jointly measurable. -/
theorem measurable_integrand {f g : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g)) (t x : ℝ) :
    Measurable fun p : ℝ × ℝ => f p.1 p.2 * g (t - p.1) (x - p.2) := by
  have h2 : Measurable fun p : ℝ × ℝ => (t - p.1, x - p.2) := by fun_prop
  exact hf.mul (hg.comp h2)

/-- `f` cut off at positive times, as a function on `ℝ × ℝ`. -/
noncomputable def cut (f : ℝ → ℝ → ℝ≥0∞) (p : ℝ × ℝ) : ℝ≥0∞ :=
  if 0 < p.1 then f p.1 p.2 else 0

theorem measurable_cut {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) :
    Measurable (cut f) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_fst) hf measurable_const

end LConv

open LConv

/-- **`lstConv` is Mathlib's `lconvolution` on `ℝ × ℝ`** of the functions cut off at positive
times. -/
theorem lstConv_eq_lconvolution {f g : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g)) (t x : ℝ) :
    lstConv f g t x = (cut f ⋆ₗ cut g) (t, x) := by
  rw [lconvolution_def, Measure.volume_eq_prod, lintegral_prod]
  · rw [lstConv, ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun s => ?_
    by_cases h0 : 0 < s
    · by_cases h1 : s < t
      · have h2 : 0 < -s + t := by linarith
        simp [indicator, h0, h1, cut, neg_add_eq_sub]
      · have h2 : ¬ 0 < -s + t := by linarith
        simp [indicator, h1, h2, cut]
    · simp [indicator, h0, cut]
  · have h2 : Measurable fun p : ℝ × ℝ => -p + (t, x) := by fun_prop
    exact ((measurable_cut hf).mul ((measurable_cut hg).comp h2)).aemeasurable

/-- `lstConv` of jointly measurable functions is jointly measurable. -/
theorem measurable_lstConv {f g : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g)) : Measurable (Function.uncurry (lstConv f g)) := by
  have : Function.uncurry (lstConv f g) = cut f ⋆ₗ cut g := by
    funext p
    exact lstConv_eq_lconvolution hf hg p.1 p.2
  rw [this]
  exact measurable_lconvolution _ (measurable_cut hf) (measurable_cut hg)

theorem cut_lstConv {f g : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g)) : cut (lstConv f g) = cut f ⋆ₗ cut g := by
  funext p
  by_cases h : 0 < p.1
  · simp only [cut, h, ite_true]
    exact lstConv_eq_lconvolution hf hg p.1 p.2
  · simp only [cut, h, ite_false]
    rw [← lstConv_eq_lconvolution hf hg p.1 p.2, lstConv_of_nonpos f g (not_lt.mp h)]

/-- **Associativity** of the lower-integral space-time convolution, for jointly measurable
arguments: `(f ⋆ g) ⋆ h = f ⋆ (g ⋆ h)` at every `(t,x)`. -/
theorem lstConv_assoc {f g h : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g)) (hh : Measurable (Function.uncurry h)) (t x : ℝ) :
    lstConv (lstConv f g) h t x = lstConv f (lstConv g h) t x := by
  rw [lstConv_eq_lconvolution (measurable_lstConv hf hg) hh,
    lstConv_eq_lconvolution hf (measurable_lstConv hg hh), cut_lstConv hf hg,
    cut_lstConv hg hh, lconvolution_assoc (measurable_cut hf) (measurable_cut hg)
      (measurable_cut hh)]

/-! ### Linearity -/

theorem lstConv_add_left {f₁ f₂ g : ℝ → ℝ → ℝ≥0∞} (hf₁ : Measurable (Function.uncurry f₁))
    (hg : Measurable (Function.uncurry g)) (t x : ℝ) :
    lstConv (f₁ + f₂) g t x = lstConv f₁ g t x + lstConv f₂ g t x := by
  have hm := measurable_integrand hf₁ hg t x
  simp only [lstConv, Pi.add_apply, add_mul]
  rw [← lintegral_add_left (hm.lintegral_prod_right')]
  refine lintegral_congr fun s => ?_
  exact lintegral_add_left (hm.comp measurable_prodMk_left) _

theorem lstConv_add_right {f g₁ g₂ : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    (hg₁ : Measurable (Function.uncurry g₁)) (t x : ℝ) :
    lstConv f (g₁ + g₂) t x = lstConv f g₁ t x + lstConv f g₂ t x := by
  have hm := measurable_integrand hf hg₁ t x
  simp only [lstConv, Pi.add_apply, mul_add]
  rw [← lintegral_add_left (hm.lintegral_prod_right')]
  refine lintegral_congr fun s => ?_
  exact lintegral_add_left (hm.comp measurable_prodMk_left) _

/-- Countable additivity in the first argument. -/
theorem lstConv_tsum_left {f : ℕ → ℝ → ℝ → ℝ≥0∞} {g : ℝ → ℝ → ℝ≥0∞}
    (hf : ∀ n, Measurable (Function.uncurry (f n))) (hg : Measurable (Function.uncurry g))
    (t x : ℝ) :
    lstConv (fun s y => ∑' n, f n s y) g t x = ∑' n, lstConv (f n) g t x := by
  have hm := fun n => measurable_integrand (hf n) hg t x
  simp only [lstConv, ← ENNReal.tsum_mul_right]
  rw [← lintegral_tsum fun n => (hm n).lintegral_prod_right'.aemeasurable]
  refine lintegral_congr fun s => ?_
  exact lintegral_tsum fun n => ((hm n).comp measurable_prodMk_left).aemeasurable

/-! ### The Bochner bridge -/

namespace LConv

/-- `stConv` at `t ≥ 0` as a set integral over `Ioo 0 t`. -/
theorem stConv_eq_setIntegral_Ioo (f g : ℝ → ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    stConv f g t x = ∫ s in Ioo 0 t, ∫ y, f s y * g (t - s) (x - y) := by
  rw [stConv, intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]

/-- `ofReal (∫ φ) ≤ ∫⁻ ofReal φ` for an a.e. nonnegative `φ` (no integrability). -/
theorem ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ : α → ℝ} (hφ : 0 ≤ᵐ[μ] φ) :
    ENNReal.ofReal (∫ a, φ a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (φ a) ∂μ := by
  by_cases hi : Integrable φ μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi hφ).le
  · simp [integral_undef hi]

end LConv

/-- **Bochner bridge, inequality.** For real `f, g` nonnegative at positive times and `t ≥ 0`,
`ofReal ((f ⋆ g)(t,x)) ≤ (ofReal f ⋆ ofReal g)(t,x)`, with no integrability hypothesis (when the
Bochner integral is junk it is `0`). -/
theorem ofReal_stConv_le_lstConv {f g : ℝ → ℝ → ℝ} (hf : ∀ s, 0 < s → ∀ y, 0 ≤ f s y)
    (hg : ∀ s, 0 < s → ∀ y, 0 ≤ g s y) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    ENNReal.ofReal (stConv f g t x) ≤
      lstConv (fun s y => ENNReal.ofReal (f s y)) (fun s y => ENNReal.ofReal (g s y)) t x := by
  have hnn : ∀ s ∈ Ioo 0 t, ∀ y, 0 ≤ f s y * g (t - s) (x - y) := fun s hs y =>
    mul_nonneg (hf s hs.1 y) (hg _ (sub_pos.mpr hs.2) _)
  rw [stConv_eq_setIntegral_Ioo f g ht x]
  refine (LConv.ofReal_integral_le_lintegral ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun s hs => ?_)
    exact integral_nonneg (hnn s hs)
  · refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
    refine (LConv.ofReal_integral_le_lintegral (Eventually.of_forall (hnn s hs))).trans ?_
    refine le_of_eq (lintegral_congr fun y => ?_)
    exact ENNReal.ofReal_mul (hf s hs.1 y)

/-- **Bochner bridge, equality (iterated integrability).** If for a.e. `s ∈ (0,t)` the space
integrand is integrable and the resulting time integrand is integrable on `(0,t)`, then
`ofReal ((f ⋆ g)(t,x)) = (ofReal f ⋆ ofReal g)(t,x)`. -/
theorem ofReal_stConv_eq_lstConv {f g : ℝ → ℝ → ℝ} (hf : ∀ s, 0 < s → ∀ y, 0 ≤ f s y)
    (hg : ∀ s, 0 < s → ∀ y, 0 ≤ g s y) {t : ℝ} (ht : 0 ≤ t) (x : ℝ)
    (hin : ∀ᵐ s ∂(volume.restrict (Ioo 0 t)), Integrable fun y => f s y * g (t - s) (x - y))
    (hout : IntegrableOn (fun s => ∫ y, f s y * g (t - s) (x - y)) (Ioo 0 t)) :
    ENNReal.ofReal (stConv f g t x) =
      lstConv (fun s y => ENNReal.ofReal (f s y)) (fun s y => ENNReal.ofReal (g s y)) t x := by
  have hnn : ∀ s ∈ Ioo 0 t, ∀ y, 0 ≤ f s y * g (t - s) (x - y) := fun s hs y =>
    mul_nonneg (hf s hs.1 y) (hg _ (sub_pos.mpr hs.2) _)
  rw [stConv_eq_setIntegral_Ioo f g ht x, ofReal_integral_eq_lintegral_ofReal hout]
  · refine lintegral_congr_ae ?_
    filter_upwards [hin, ae_restrict_mem measurableSet_Ioo] with s hs hmem
    rw [ofReal_integral_eq_lintegral_ofReal hs (Eventually.of_forall (hnn s hmem))]
    exact lintegral_congr fun y => ENNReal.ofReal_mul (hf s hmem.1 y)
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun s hs => ?_)
    exact integral_nonneg (hnn s hs)

/-- **Bochner bridge, equality (integrability on `(0,t] × ℝ`)**, in the form of
`MomentBridge.integrable_J0_sq_K`. -/
theorem ofReal_stConv_eq_lstConv_of_integrable {f g : ℝ → ℝ → ℝ}
    (hf : ∀ s, 0 < s → ∀ y, 0 ≤ f s y) (hg : ∀ s, 0 < s → ∀ y, 0 ≤ g s y) {t : ℝ}
    (ht : 0 ≤ t) (x : ℝ)
    (hint : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * g (t - p.1) (x - p.2))
      ((volume.restrict (Ioc 0 t)).prod volume)) :
    ENNReal.ofReal (stConv f g t x) =
      lstConv (fun s y => ENNReal.ofReal (f s y)) (fun s y => ENNReal.ofReal (g s y)) t x := by
  have hμ : volume.restrict (Ioc (0 : ℝ) t) = volume.restrict (Ioo 0 t) :=
    (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
  rw [hμ] at hint
  exact ofReal_stConv_eq_lstConv hf hg ht x hint.prod_right_ae hint.integral_prod_left

/-! ### The resolvent kernels in `ℝ≥0∞` -/

namespace LConv

/-- `G_ν(t,·) = 0` for `t ≤ 0`, `ν ≥ 0` (junk value of the square root). -/
theorem G_of_nonpos {ν t : ℝ} (hν : 0 ≤ ν) (ht : t ≤ 0) (x : ℝ) : G ν t x = 0 := by
  have h : Real.sqrt (2 * π * ν * t) = 0 :=
    Real.sqrt_eq_zero'.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) ht)
  simp [G, h]

/-- Every `𝓛ₙ` vanishes at times `t ≤ 0`. -/
theorem L_of_nonpos {ν : ℝ} (hν : 0 ≤ ν) (lam : ℝ) (n : ℕ) {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    L ν lam n t x = 0 := by
  cases n with
  | zero => simp [L, G_of_nonpos hν ht]
  | succ n =>
    rw [L.eq_2, stConv]
    have h : ∀ s ∈ uIcc 0 t, (∫ y, L ν lam n s y * L ν lam 0 (t - s) (x - y)) = 0 := by
      intro s hs
      rw [uIcc_of_ge ht] at hs
      have hts : t - s ≤ 0 := by linarith [hs.1]
      simp [L, G_of_nonpos hν hts]
    rw [intervalIntegral.integral_congr h]
    simp

theorem G_nonneg {ν t : ℝ} (hν : 0 < ν) (x : ℝ) : 0 ≤ G ν t x := by
  rcases le_or_gt t 0 with ht | ht
  · rw [G_of_nonpos hν.le ht]
  · rw [G_eq_heatKernel]
    exact (RoughHeatKernel.heatKernel_pos (mul_pos hν ht) x).le

/-- The closed form of `𝓛ₙ` at every time (zero for `t ≤ 0`). -/
theorem L_eq_ite {ν : ℝ} (hν : 0 < ν) (lam : ℝ) (n : ℕ) :
    L ν lam n = fun t x =>
      if 0 < t then G (ν / 2) t x * lCoeff ν lam n * t ^ (((n : ℝ) - 1) / 2) else 0 := by
  funext t x
  split_ifs with ht
  · exact L_eq hν n ht x
  · exact L_of_nonpos hν.le lam n (not_lt.mp ht) x

theorem L_nonneg {ν : ℝ} (hν : 0 < ν) (lam : ℝ) (n : ℕ) (t x : ℝ) : 0 ≤ L ν lam n t x := by
  rw [L_eq_ite hν lam n]
  dsimp only
  split_ifs with ht
  · have := G_nonneg (t := t) (half_pos hν) x
    have := lCoeff_nonneg ν lam n
    have := Real.rpow_nonneg ht.le (((n : ℝ) - 1) / 2)
    positivity
  · exact le_rfl

theorem measurable_L {ν : ℝ} (hν : 0 < ν) (lam : ℝ) (n : ℕ) :
    Measurable (Function.uncurry (L ν lam n)) := by
  rw [L_eq_ite hν lam n]
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  simp only [G]
  fun_prop

theorem measurable_ofReal_L {ν : ℝ} (hν : 0 < ν) (lam : ℝ) (n : ℕ) :
    Measurable (Function.uncurry fun t x => ENNReal.ofReal (L ν lam n t x)) :=
  (measurable_L hν lam n).ennreal_ofReal

theorem K_nonneg {ν : ℝ} (hν : 0 < ν) (lam t x : ℝ) : 0 ≤ K ν lam t x :=
  tsum_nonneg fun n => L_nonneg hν lam n t x

/-- For `0 < s < t`, the space integral of `𝓛ₙ(s,·) 𝓛₀(t−s, x−·)` (the Beta integrand). -/
theorem integral_L_mul_L_zero {ν lam : ℝ} (hν : 0 < ν) (n : ℕ) {s t : ℝ} (hs : 0 < s)
    (hst : s < t) (x : ℝ) :
    ∫ y, L ν lam n s y * L ν lam 0 (t - s) (x - y) =
      G (ν / 2) t x * (lCoeff ν lam n * bConst ν lam) *
        (s ^ (((n : ℝ) + 1) / 2 - 1) * (t - s) ^ ((1 / 2 : ℝ) - 1)) := by
  have hν2 : 0 < ν / 2 := half_pos hν
  have hts : 0 < t - s := sub_pos.mpr hst
  have hfun : (fun y => L ν lam n s y * L ν lam 0 (t - s) (x - y)) = fun y =>
      (lCoeff ν lam n * s ^ (((n : ℝ) - 1) / 2) * bConst ν lam * (t - s) ^ (-(1 / 2 : ℝ))) *
        (G (ν / 2) (t - s) (x - y) * G (ν / 2) s y) := by
    funext y
    rw [L_eq hν n hs y, L_zero_eq hν hts (x - y)]
    ring
  rw [hfun, MeasureTheory.integral_const_mul, integral_G_mul_G hν2 hs hst x]
  have e1 : ((n : ℝ) + 1) / 2 - 1 = ((n : ℝ) - 1) / 2 := by ring
  have e2 : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
  rw [e1, e2]
  ring

theorem integrable_L_mul_L_zero {ν lam : ℝ} (hν : 0 < ν) (n : ℕ) {s t : ℝ} (hs : 0 < s)
    (hst : s < t) (x : ℝ) :
    Integrable fun y => L ν lam n s y * L ν lam 0 (t - s) (x - y) := by
  have hν2 : 0 < ν / 2 := half_pos hν
  have hts : 0 < t - s := sub_pos.mpr hst
  have hfun : (fun y => L ν lam n s y * L ν lam 0 (t - s) (x - y)) = fun y =>
      (lCoeff ν lam n * s ^ (((n : ℝ) - 1) / 2) * bConst ν lam * (t - s) ^ (-(1 / 2 : ℝ))) *
        (RoughHeatKernel.heatKernel (ν / 2 * s) (y - 0) *
          RoughHeatKernel.heatKernel (ν / 2 * (t - s)) (x - y)) := by
    funext y
    rw [L_eq hν n hs y, L_zero_eq hν hts (x - y), sub_zero]
    simp only [G_eq_heatKernel]
    ring
  rw [hfun]
  exact (RoughHeatKernel.integrable_heatKernel_sub_mul_heatKernel_sub (mul_pos hν2 hs)
    (mul_pos hν2 hts) x 0).const_mul _

end LConv

open LConv

/-- **`𝓛ₙ ⋆ 𝓛₀ = 𝓛ₙ₊₁` in `ℝ≥0∞`**, at every `(t,x)` (both sides vanish for `t ≤ 0`). -/
theorem lstConv_ofReal_L_L_zero {ν : ℝ} (hν : 0 < ν) (lam : ℝ) (n : ℕ) (t x : ℝ) :
    lstConv (fun s y => ENNReal.ofReal (L ν lam n s y))
        (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x =
      ENNReal.ofReal (L ν lam (n + 1) t x) := by
  rcases le_or_gt t 0 with ht | ht
  · rw [lstConv_of_nonpos _ _ ht, L_of_nonpos hν.le lam _ ht, ENNReal.ofReal_zero]
  have hL : L ν lam (n + 1) t x = stConv (L ν lam n) (L ν lam 0) t x := by rw [L.eq_2]
  rw [hL, ofReal_stConv_eq_lstConv (fun s _ y => L_nonneg hν lam n s y)
    (fun s _ y => L_nonneg hν lam 0 s y) ht.le x]
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun s hs => ?_)
    exact integrable_L_mul_L_zero hν n hs.1 hs.2 x
  · have hI : IntervalIntegrable (fun s => G (ν / 2) t x * (lCoeff ν lam n * bConst ν lam) *
        (s ^ (((n : ℝ) + 1) / 2 - 1) * (t - s) ^ ((1 / 2 : ℝ) - 1))) volume 0 t :=
      (intervalIntegrable_rpow_mul_sub_rpow (by positivity : (0 : ℝ) < ((n : ℝ) + 1) / 2)
        (by norm_num : (0 : ℝ) < 1 / 2) ht).const_mul _
    refine ((hI.1).mono_set Ioo_subset_Ioc_self).congr_fun (fun s hs => ?_) measurableSet_Ioo
    exact (integral_L_mul_L_zero hν n hs.1 hs.2 x).symm

/-- **`𝓚 = Σₙ 𝓛ₙ` in `ℝ≥0∞`**, at every `(t,x)`. -/
theorem ofReal_K_eq_tsum {ν : ℝ} (hν : 0 < ν) (lam t x : ℝ) :
    ENNReal.ofReal (K ν lam t x) = ∑' n, ENNReal.ofReal (L ν lam n t x) := by
  have hsum : Summable fun n => L ν lam n t x := by
    rcases le_or_gt t 0 with ht | ht
    · simp only [L_of_nonpos hν.le lam _ ht x]
      exact summable_zero
    · exact summable_L hν ht x
  exact ENNReal.ofReal_tsum_of_nonneg (fun n => L_nonneg hν lam n t x) hsum

/-- **`𝓚 ⋆ 𝓛₀ + 𝓛₀ = 𝓚` in `ℝ≥0∞`** (the resolvent identity `E:KS-Kn-K0`), at every `(t,x)`. -/
theorem lstConv_ofReal_K_L_zero_add {ν : ℝ} (hν : 0 < ν) (lam t x : ℝ) :
    lstConv (fun s y => ENNReal.ofReal (K ν lam s y))
        (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x + ENNReal.ofReal (L ν lam 0 t x) =
      ENNReal.ofReal (K ν lam t x) := by
  have hK : (fun s y => ENNReal.ofReal (K ν lam s y)) =
      fun s y => ∑' n, ENNReal.ofReal (L ν lam n s y) := by
    funext s y; exact ofReal_K_eq_tsum hν lam s y
  have h1 := lstConv_tsum_left (f := fun n s y => ENNReal.ofReal (L ν lam n s y))
    (g := fun s y => ENNReal.ofReal (L ν lam 0 s y)) (fun n => measurable_ofReal_L hν lam n)
    (measurable_ofReal_L hν lam 0) t x
  have h2 : ∑' n, ENNReal.ofReal (L ν lam n t x) =
      ENNReal.ofReal (L ν lam 0 t x) + ∑' n, ENNReal.ofReal (L ν lam (n + 1) t x) :=
    tsum_eq_zero_add' ENNReal.summable
  rw [hK, h1, ofReal_K_eq_tsum hν lam t x, h2, add_comm]
  congr 1
  exact tsum_congr fun n => lstConv_ofReal_L_L_zero hν lam n t x

/-- The scalar factor `k(r)` of `𝓚(r,·) = G_{ν/2}(r,·) k(r)` (display `E:K`). -/
noncomputable def LConv.kFac (ν lam r : ℝ) : ℝ :=
  lam ^ 2 / Real.sqrt (4 * π * ν * r) +
    lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))

/-- The scalar factor `k` of `𝓚` is interval integrable on `[0,t]`. -/
theorem LConv.intervalIntegrable_kFac {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun r => LConv.kFac ν lam r) volume 0 t := by
  have hI1 : IntervalIntegrable (fun r => lam ^ 2 / Real.sqrt (4 * π * ν * r)) volume 0 t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
      (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (bConst ν lam)
    refine h.congr fun r hr => ?_
    rw [Set.uIoc_of_le ht] at hr
    show bConst ν lam * r ^ (-(1 / 2 : ℝ)) = lam ^ 2 / Real.sqrt (4 * π * ν * r)
    rw [bConst, Real.sqrt_mul (by positivity) r, Real.rpow_neg hr.1.le, ← Real.sqrt_eq_rpow]
    field_simp
  have hI2 : IntervalIntegrable (fun r => lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * r / (4 * ν)) *
      Phi (lam ^ 2 * Real.sqrt (r / (2 * ν)))) volume 0 t := by
    have hΦ : Continuous Phi := continuous_Phi
    apply Continuous.intervalIntegrable
    fun_prop
  exact hI1.add hI2

/-- **`1 ⋆ 𝓚 = 𝓗` in `ℝ≥0∞`** (display `E2:H`): for `t ≥ 0`,
`(1 ⋆ 𝓚)(t,x) = ofReal (2 e^{λ⁴t/(4ν)} Φ(λ² √(t/(2ν))) − 1)`. -/
theorem lstConv_one_ofReal_K {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    lstConv (fun _ _ => 1) (fun s y => ENNReal.ofReal (K ν lam s y)) t x =
      ENNReal.ofReal
        (2 * Real.exp (lam ^ 4 * t / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (t / (2 * ν))) - 1) := by
  have h1 : (fun _ _ => (1 : ℝ≥0∞) : ℝ → ℝ → ℝ≥0∞) = fun _ _ => ENNReal.ofReal 1 := by simp
  rw [← one_conv_K hν ht x, h1, ofReal_stConv_eq_lstConv (fun _ _ _ => zero_le_one)
    (fun s _ y => K_nonneg hν lam s y) ht x]
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun s hs => ?_)
    have hr : 0 < t - s := sub_pos.mpr hs.2
    have hfun : (fun y => (1 : ℝ) * K ν lam (t - s) (x - y)) =
        fun y => LConv.kFac ν lam (t - s) *
          RoughHeatKernel.heatKernel (ν / 2 * (t - s)) (x - y) := by
      funext y
      rw [K_eq hν hr (x - y), LConv.kFac, G_eq_heatKernel]
      ring
    rw [hfun]
    exact ((RoughHeatKernel.integrable_heatKernel (mul_pos (half_pos hν) hr)).comp_sub_left
      x).const_mul _
  · have hI := ((LConv.intervalIntegrable_kFac (lam := lam) hν ht).comp_sub_left t).symm
    simp only [sub_zero, sub_self] at hI
    refine ((hI.1).mono_set Ioo_subset_Ioc_self).congr_fun (fun s hs => ?_) measurableSet_Ioo
    have hr : 0 < t - s := sub_pos.mpr hs.2
    have hfun : (fun y => (1 : ℝ) * K ν lam (t - s) (x - y)) =
        fun y => LConv.kFac ν lam (t - s) * G (ν / 2) (t - s) (x - y) := by
      funext y
      rw [K_eq hν hr (x - y), LConv.kFac]
      ring
    show LConv.kFac ν lam (t - s) = ∫ y, (1 : ℝ) * K ν lam (t - s) (x - y)
    rw [hfun, MeasureTheory.integral_const_mul,
      integral_sub_left_eq_self (fun y => G (ν / 2) (t - s) y) (volume : Measure ℝ) x]
    simp only [G_eq_heatKernel]
    rw [RoughHeatKernel.integral_heatKernel (mul_pos (half_pos hν) hr), mul_one]

/-- **Gaussian-tempered bridge.** For a Gaussian-tempered `μ`, `ν > 0` and `t > 0`,
`(J₀² ⋆ 𝓚_λ)(t,x)` (Bochner) is the lower-integral convolution of `ofReal J₀²` and
`ofReal 𝓚_λ`. -/
theorem lstConv_ofReal_J0_sq_K {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    lstConv (fun s y => ENNReal.ofReal (J0 ν μ s y ^ 2)) (fun s y => ENNReal.ofReal (K ν lam s y))
      t x = ENNReal.ofReal (stConv (fun s y => J0 ν μ s y ^ 2) (K ν lam) t x) :=
  (ofReal_stConv_eq_lstConv_of_integrable (fun _ _ _ => sq_nonneg _)
    (fun s _ y => K_nonneg hν lam s y) ht.le x
    (MomentBridge.integrable_J0_sq_K hT hν lam ht x)).symm

/-! ### The coefficients `Bₙ(t)` and the remainder estimate -/

/-- `Bₙ(t)` is monotone in `t ≥ 0` (for `b ≥ 0`). -/
theorem BCoeff_mono {b : ℝ} (hb : 0 ≤ b) (n : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    BCoeff b s n ≤ BCoeff b t n := by
  unfold BCoeff
  have hΓ : 0 < Real.Gamma (((n : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h := Real.rpow_le_rpow hs hst (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
  have hp : 0 ≤ Real.pi ^ (((n : ℝ) + 1) / 2) * b ^ n := by positivity
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h hp) hΓ.le

/-- `𝓛ₙ(s,y) ≤ Bₙ(t) 𝓛₀(s,y)` for every `s ≤ t` (both sides vanish for `s ≤ 0`). -/
theorem L_le_BCoeff_mul_L_zero {ν : ℝ} (hν : 0 < ν) (lam : ℝ) (n : ℕ) {s t : ℝ} (hst : s ≤ t)
    (y : ℝ) : L ν lam n s y ≤ BCoeff (bConst ν lam) t n * L ν lam 0 s y := by
  rcases le_or_gt s 0 with hs | hs
  · simp [L_of_nonpos hν.le lam _ hs]
  rw [L_eq_L_zero_mul_BCoeff hν n hs y, mul_comm]
  exact mul_le_mul_of_nonneg_right (BCoeff_mono (bConst_nonneg ν lam) n hs.le hst)
    (L_nonneg hν lam 0 s y)

/-- `𝓛₀ ⋆ 𝓛₀ = 𝓛₁ = B₁(t) 𝓛₀` in `ℝ≥0∞`, at every `(t,x)`. -/
theorem lstConv_ofReal_L_zero_L_zero {ν : ℝ} (hν : 0 < ν) (lam t x : ℝ) :
    lstConv (fun s y => ENNReal.ofReal (L ν lam 0 s y))
        (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x =
      ENNReal.ofReal (BCoeff (bConst ν lam) t 1) * ENNReal.ofReal (L ν lam 0 t x) := by
  rw [lstConv_ofReal_L_L_zero hν lam 0 t x]
  rcases le_or_gt t 0 with ht | ht
  · simp [L_of_nonpos hν.le lam _ ht]
  rw [L_eq_L_zero_mul_BCoeff hν 1 ht x, mul_comm, ENNReal.ofReal_mul
    (BCoeff_nonneg (bConst_nonneg ν lam) ht.le 1)]

/-- **Remainder estimate** `f ⋆ 𝓛ₙ ≤ Bₙ(t) (f ⋆ 𝓛₀)` at `(t,x)`, for every `f : ℝ → ℝ → ℝ≥0∞`
(no measurability needed). -/
theorem lstConv_ofReal_L_le_BCoeff_mul {ν : ℝ} (hν : 0 < ν) (lam : ℝ) (n : ℕ)
    (f : ℝ → ℝ → ℝ≥0∞) (t x : ℝ) :
    lstConv f (fun s y => ENNReal.ofReal (L ν lam n s y)) t x ≤
      ENNReal.ofReal (BCoeff (bConst ν lam) t n) *
        lstConv f (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x := by
  rw [← lstConv_const_mul_right _ _ ENNReal.ofReal_ne_top]
  refine lstConv_mono_right (fun r hr z => ?_) x
  rw [← ENNReal.ofReal_mul' (L_nonneg hν lam 0 r z)]
  exact ENNReal.ofReal_le_ofReal (L_le_BCoeff_mul_L_zero hν lam n hr.2.le z)

end ChenDalang15

end
