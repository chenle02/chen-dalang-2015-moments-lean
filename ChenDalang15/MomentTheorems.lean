module

public import ChenDalang15.LConv
public import ChenDalang15.S1Glue
public import ChenDalang15.TwoPoint

/-!
# Deterministic half of the second-moment theorems (Wave S2, part d)

Chen–Dalang (2015), Theorem `T2:ExUni` parts (1), (3), (4), (5) at `p = 2`: once the Itô
isometry has turned the equation `E2:WalshSI` into a renewal inequality for
`f(t,x) = E[u(t,x)²]` (display `E2:fint` and its one-sided versions), everything else is pure
analysis on `ℝ≥0∞`-valued functions. This file proves that analysis, with hypotheses only on
`f`, `J₀`, `ν` and constants.

All convolutions are the lower-integral convolution `lstConv` of `ChenDalang15.LConv`
(`(f ⋆ g)(t,x) = ∫⁻_{(0,t)} ∫⁻ f(s,y) g(t−s,x−y)`), with the moment function on the left and
the kernel on the right; `𝓛₀(λ) = λ² G_ν²`, `𝓚(λ) = Σₙ 𝓛ₙ(λ)` (as `ofReal` of the companion's
real kernels). Only values of `f` at positive times are read; measurability is asked for `f`
cut off at positive times (`LConv.cut f`), which is what joint measurability of a random field on
`(0,∞) × ℝ × Ω` gives.

## Main results

* `renewal_lower` (**S-Low**, generic): `a + (e + f) ⋆ 𝓛₀ ≤ f` on `(0,T] × ℝ` implies
  `a + (e + a) ⋆ 𝓚 ≤ f` there. No finiteness. The paper's `E2:SecMom-Lower` is
  `secondMoment_lower` (`a = J₀²`, `e = ϑ²`).
* `renewal_upper` (**S-Up**, generic): `f ≤ a + (e + f) ⋆ 𝓛₀` on `(0,T] × ℝ` and
  `((e + f) ⋆ 𝓛₀)(t,x) < ∞` imply `f(t,x) ≤ a(t,x) + ((e + a) ⋆ 𝓚)(t,x)`. The paper's
  `E2:SecMom-Up` is `secondMoment_upper` (`a = J₀²`, `e = V²`).
* `secondMoment_eq` (**S-Eq**, `E2:fint` ⇒ `E2:SecMom` for `ρ(u) = λu`).
* `eq_zero_of_le_lstConv_L_zero` (**uniqueness core**, `T2:ExUni(1)` Step 5):
  `w ≤ w ⋆ 𝓛₀` on `(0,T] × ℝ` with `w ⋆ 𝓛₀ < ∞` there gives `w = 0` on `(0,T] × ℝ`.
* `secondMoment_*_secondMomentExpr`: for Gaussian-tempered `μ`, the right sides are
  `ofReal (secondMomentExpr (J0 ν μ) ν V λ t x)` (`J₀² + J₀² ⋆ 𝓚 + V² 𝓗`).
* Bridges to the solution predicate (`StochDefs.IsRandomFieldSolution`):
  `lstConv_G_sq_eq_setLIntegral` (the `finite` field is `(E ρ(u)² ⋆ G²)(t,x) < ∞`),
  `lstConv_G_sq_le_lstConv_L_zero` / `lstConv_L_zero_le_lstConv_G_sq` (Lipschitz / lower
  Lipschitz bounds on `ρ` turn `E ρ(u)² ⋆ G²` into `(V² + f) ⋆ 𝓛₀`), and
  `lstConv_L_zero_ne_top` (the finiteness that S-Up needs follows from the upper renewal
  inequality `f ≤ J₀² + E ρ(u)² ⋆ G²` and the `finite` field, for Gaussian-tempered `μ`).

## The argument (paper, proof of `T2:ExUni`, display after `E2:fint`)

Iterating `f ≤ a + (e + f) ⋆ 𝓛₀` with associativity and `𝓛ₙ ⋆ 𝓛₀ = 𝓛ₙ₊₁` gives
`f ≤ a + Σ_{k<n} (e + a) ⋆ 𝓛ₖ + (e + f) ⋆ 𝓛ₙ` (`iterate_le`), and the remainder obeys
`(e + f) ⋆ 𝓛ₙ ≤ Bₙ(t) ((e + f) ⋆ 𝓛₀)` with `Bₙ(t) → 0` (`summable_BCoeff_rpow`). For the
lower bound the remainder is simply dropped. For uniqueness we use the same iteration (with
`a = e = 0`), not the paper's Step 5 subtraction `w ⋆ 𝓚 ≤ w ⋆ 𝓚 − w ⋆ 𝓛₀`, which needs
`(w ⋆ 𝓚)(t,x) < ∞` (not stated there); the iteration needs only `(w ⋆ 𝓛₀)(t,x) < ∞`.
-/

set_option autoImplicit false

@[expose] public section

open scoped ENNReal
open MeasureTheory Set Filter Real Topology

namespace ChenDalang15

namespace MomentTheorems

open LConv

/-! ### Kernels and cut-offs -/

/-- `𝓛ₙ(ν,λ)` as an `ℝ≥0∞`-valued kernel. -/
noncomputable abbrev lL (ν lam : ℝ) (n : ℕ) : ℝ → ℝ → ℝ≥0∞ :=
  fun s y => ENNReal.ofReal (L ν lam n s y)

/-- `𝓚(ν,λ)` as an `ℝ≥0∞`-valued kernel. -/
noncomputable abbrev lK (ν lam : ℝ) : ℝ → ℝ → ℝ≥0∞ :=
  fun s y => ENNReal.ofReal (K ν lam s y)

/-- `f` cut off at positive times. -/
noncomputable def pos (f : ℝ → ℝ → ℝ≥0∞) : ℝ → ℝ → ℝ≥0∞ :=
  fun s y => if 0 < s then f s y else 0

theorem uncurry_pos (f : ℝ → ℝ → ℝ≥0∞) : Function.uncurry (pos f) = cut f := rfl

theorem pos_of_pos (f : ℝ → ℝ → ℝ≥0∞) {s : ℝ} (hs : 0 < s) (y : ℝ) : pos f s y = f s y :=
  by simp [pos, hs]

theorem measurable_pos {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f)) :
    Measurable (Function.uncurry (pos f)) := hf

/-- `lstConv` only reads its first argument at times in `(0,t)`. -/
theorem lstConv_congr_left {f f' g : ℝ → ℝ → ℝ≥0∞} {t : ℝ}
    (h : ∀ s ∈ Ioo 0 t, ∀ y, f s y = f' s y) (x : ℝ) :
    lstConv f g t x = lstConv f' g t x :=
  le_antisymm (lstConv_mono_left (fun s hs y => (h s hs y).le) x)
    (lstConv_mono_left (fun s hs y => (h s hs y).ge) x)

theorem lstConv_pos_left (f g : ℝ → ℝ → ℝ≥0∞) (t x : ℝ) :
    lstConv (pos f) g t x = lstConv f g t x :=
  lstConv_congr_left (fun _ hs y => pos_of_pos f hs.1 y) x

/-! ### Additivity -/

theorem lstConv_add_left' {f₁ f₂ g : ℝ → ℝ → ℝ≥0∞} (hf₁ : Measurable (Function.uncurry f₁))
    (hg : Measurable (Function.uncurry g)) (t x : ℝ) :
    lstConv (fun s y => f₁ s y + f₂ s y) g t x = lstConv f₁ g t x + lstConv f₂ g t x :=
  lstConv_add_left hf₁ hg t x

theorem measurable_sum_range {φ : ℕ → ℝ → ℝ → ℝ≥0∞}
    (hφ : ∀ k, Measurable (Function.uncurry (φ k))) (n : ℕ) :
    Measurable (Function.uncurry fun s y => ∑ k ∈ Finset.range n, φ k s y) := by
  have h := Finset.measurable_sum (Finset.range n) fun k _ => hφ k
  convert h using 1
  funext p
  simp [Function.uncurry]

/-- Finite additivity in the first argument. -/
theorem lstConv_sum_left {φ : ℕ → ℝ → ℝ → ℝ≥0∞} {g : ℝ → ℝ → ℝ≥0∞}
    (hφ : ∀ k, Measurable (Function.uncurry (φ k))) (hg : Measurable (Function.uncurry g))
    (n : ℕ) (t x : ℝ) :
    lstConv (fun s y => ∑ k ∈ Finset.range n, φ k s y) g t x =
      ∑ k ∈ Finset.range n, lstConv (φ k) g t x := by
  induction n with
  | zero => simp [lstConv]
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    rw [← ih]
    exact lstConv_add_left' (measurable_sum_range hφ n) hg t x

/-- Countable additivity in the second argument. -/
theorem lstConv_tsum_right {f : ℝ → ℝ → ℝ≥0∞} {g : ℕ → ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : ∀ n, Measurable (Function.uncurry (g n)))
    (t x : ℝ) :
    lstConv f (fun s y => ∑' n, g n s y) t x = ∑' n, lstConv f (g n) t x := by
  have hm := fun n => measurable_integrand hf (hg n) t x
  simp only [lstConv, ← ENNReal.tsum_mul_left]
  rw [← lintegral_tsum fun n => (hm n).lintegral_prod_right'.aemeasurable]
  refine lintegral_congr fun s => ?_
  exact lintegral_tsum fun n => ((hm n).comp measurable_prodMk_left).aemeasurable

/-! ### Kernel facts -/

theorem measurable_lL {ν : ℝ} (hν : 0 < ν) (lam : ℝ) (n : ℕ) :
    Measurable (Function.uncurry (lL ν lam n)) := measurable_ofReal_L hν lam n

theorem measurable_lK {ν : ℝ} (hν : 0 < ν) (lam : ℝ) :
    Measurable (Function.uncurry (lK ν lam)) := by
  have h : lK ν lam = fun s y => ∑' n, lL ν lam n s y := by
    funext s y; exact ofReal_K_eq_tsum hν lam s y
  rw [h]
  have : Measurable fun p : ℝ × ℝ => ∑' n, lL ν lam n p.1 p.2 := by
    simp_rw [ENNReal.tsum_eq_iSup_sum]
    exact .iSup fun s => s.measurable_fun_sum fun i _ => measurable_lL hν lam i
  exact this

/-- `(φ ⋆ 𝓛ₖ) ⋆ 𝓛₀ = φ ⋆ 𝓛ₖ₊₁`. -/
theorem lstConv_lstConv_lL {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {φ : ℝ → ℝ → ℝ≥0∞}
    (hφ : Measurable (Function.uncurry φ)) (k : ℕ) (t x : ℝ) :
    lstConv (lstConv φ (lL ν lam k)) (lL ν lam 0) t x = lstConv φ (lL ν lam (k + 1)) t x := by
  rw [lstConv_assoc hφ (measurable_lL hν lam k) (measurable_lL hν lam 0)]
  have h : lstConv (lL ν lam k) (lL ν lam 0) = lL ν lam (k + 1) := by
    funext r z; exact lstConv_ofReal_L_L_zero hν lam k r z
  rw [h]

/-- `φ ⋆ 𝓚 = Σₖ φ ⋆ 𝓛ₖ`. -/
theorem lstConv_lK_eq_tsum {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {φ : ℝ → ℝ → ℝ≥0∞}
    (hφ : Measurable (Function.uncurry φ)) (t x : ℝ) :
    lstConv φ (lK ν lam) t x = ∑' k, lstConv φ (lL ν lam k) t x := by
  have h : lK ν lam = fun s y => ∑' n, lL ν lam n s y := by
    funext s y; exact ofReal_K_eq_tsum hν lam s y
  rw [h, lstConv_tsum_right hφ (measurable_lL hν lam)]

/-- `Bₙ(t) → 0`. -/
theorem tendsto_BCoeff {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => BCoeff b t n) atTop (𝓝 0) := by
  have h := summable_BCoeff_rpow hb ht (m := 1) one_pos
  simp only [Nat.cast_one, div_one, Real.rpow_one] at h
  exact h.tendsto_atTop_zero

/-! ### The iteration -/

/-- **Upper iteration.** If `f ≤ a + (e + f) ⋆ 𝓛₀` on `(0,T] × ℝ`, then for every `n`,
`f ≤ a + Σ_{k<n} (e + a) ⋆ 𝓛ₖ + (e + f) ⋆ 𝓛ₙ` on `(0,T] × ℝ`. -/
theorem iterate_le {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {a e f : ℝ → ℝ → ℝ≥0∞}
    (ha : Measurable (Function.uncurry a)) (he : Measurable (Function.uncurry e))
    (hf : Measurable (Function.uncurry f)) {T : ℝ}
    (h : ∀ t ∈ Ioc 0 T, ∀ x, f t x ≤ a t x + lstConv (e + f) (lL ν lam 0) t x) (n : ℕ) :
    ∀ t ∈ Ioc 0 T, ∀ x, f t x ≤ a t x + ∑ k ∈ Finset.range n, lstConv (e + a) (lL ν lam k) t x +
      lstConv (e + f) (lL ν lam n) t x := by
  have hea : Measurable (Function.uncurry (e + a)) := he.add ha
  have hef : Measurable (Function.uncurry (e + f)) := he.add hf
  induction n with
  | zero => simpa using h
  | succ n ih =>
    intro t ht x
    refine (h t ht x).trans ?_
    rw [add_assoc]
    gcongr a t x + ?_
    have hφ : ∀ s ∈ Ioo 0 t, ∀ y, (e + f) s y ≤
        ((e + a) s y + ∑ k ∈ Finset.range n, lstConv (e + a) (lL ν lam k) s y) +
          lstConv (e + f) (lL ν lam n) s y := by
      intro s hs y
      have := ih s ⟨hs.1, hs.2.le.trans ht.2⟩ y
      simp only [Pi.add_apply]
      calc e s y + f s y ≤ e s y + (a s y + ∑ k ∈ Finset.range n,
            lstConv (e + a) (lL ν lam k) s y + lstConv (e + f) (lL ν lam n) s y) := by gcongr
        _ = _ := by ring
    refine (lstConv_mono_left hφ x).trans (le_of_eq ?_)
    have hS := measurable_sum_range (φ := fun k => lstConv (e + a) (lL ν lam k))
      (fun k => measurable_lstConv hea (measurable_lL hν lam k)) n
    have heaS : Measurable (Function.uncurry fun s y =>
        (e + a) s y + ∑ k ∈ Finset.range n, lstConv (e + a) (lL ν lam k) s y) := hea.add hS
    rw [lstConv_add_left' heaS (measurable_lL hν lam 0),
      lstConv_add_left' hea (measurable_lL hν lam 0),
      lstConv_sum_left (fun k => measurable_lstConv hea (measurable_lL hν lam k))
        (measurable_lL hν lam 0),
      lstConv_lstConv_lL hν lam hef, Finset.sum_range_succ']
    simp only [lstConv_lstConv_lL hν lam hea]
    ring

/-- **Lower iteration.** If `a + (e + f) ⋆ 𝓛₀ ≤ f` on `(0,T] × ℝ`, then for every `n`,
`a + Σ_{k<n} (e + a) ⋆ 𝓛ₖ + (e + f) ⋆ 𝓛ₙ ≤ f` on `(0,T] × ℝ`. -/
theorem iterate_ge {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {a e f : ℝ → ℝ → ℝ≥0∞}
    (ha : Measurable (Function.uncurry a)) (he : Measurable (Function.uncurry e))
    (hf : Measurable (Function.uncurry f)) {T : ℝ}
    (h : ∀ t ∈ Ioc 0 T, ∀ x, a t x + lstConv (e + f) (lL ν lam 0) t x ≤ f t x) (n : ℕ) :
    ∀ t ∈ Ioc 0 T, ∀ x, a t x + ∑ k ∈ Finset.range n, lstConv (e + a) (lL ν lam k) t x +
      lstConv (e + f) (lL ν lam n) t x ≤ f t x := by
  have hea : Measurable (Function.uncurry (e + a)) := he.add ha
  have hef : Measurable (Function.uncurry (e + f)) := he.add hf
  induction n with
  | zero => simpa using h
  | succ n ih =>
    intro t ht x
    refine le_trans ?_ (h t ht x)
    rw [add_assoc]
    gcongr a t x + ?_
    have hφ : ∀ s ∈ Ioo 0 t, ∀ y,
        ((e + a) s y + ∑ k ∈ Finset.range n, lstConv (e + a) (lL ν lam k) s y) +
          lstConv (e + f) (lL ν lam n) s y ≤ (e + f) s y := by
      intro s hs y
      have := ih s ⟨hs.1, hs.2.le.trans ht.2⟩ y
      simp only [Pi.add_apply]
      calc _ = e s y + (a s y + ∑ k ∈ Finset.range n,
            lstConv (e + a) (lL ν lam k) s y + lstConv (e + f) (lL ν lam n) s y) := by ring
        _ ≤ e s y + f s y := by gcongr
    refine le_trans (le_of_eq ?_) (lstConv_mono_left hφ x)
    have hS := measurable_sum_range (φ := fun k => lstConv (e + a) (lL ν lam k))
      (fun k => measurable_lstConv hea (measurable_lL hν lam k)) n
    have heaS : Measurable (Function.uncurry fun s y =>
        (e + a) s y + ∑ k ∈ Finset.range n, lstConv (e + a) (lL ν lam k) s y) := hea.add hS
    rw [lstConv_add_left' heaS (measurable_lL hν lam 0),
      lstConv_add_left' hea (measurable_lL hν lam 0),
      lstConv_sum_left (fun k => measurable_lstConv hea (measurable_lL hν lam k))
        (measurable_lL hν lam 0),
      lstConv_lstConv_lL hν lam hef, Finset.sum_range_succ']
    simp only [lstConv_lstConv_lL hν lam hea]
    ring

/-! ### Passing to the limit (jointly measurable arguments) -/

theorem renewal_lower_of_measurable {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {a e f : ℝ → ℝ → ℝ≥0∞}
    (ha : Measurable (Function.uncurry a)) (he : Measurable (Function.uncurry e))
    (hf : Measurable (Function.uncurry f)) {T : ℝ}
    (h : ∀ t ∈ Ioc 0 T, ∀ x, a t x + lstConv (e + f) (lL ν lam 0) t x ≤ f t x) :
    ∀ t ∈ Ioc 0 T, ∀ x, a t x + lstConv (e + a) (lK ν lam) t x ≤ f t x := by
  have hea : Measurable (Function.uncurry (e + a)) := he.add ha
  intro t ht x
  rw [lstConv_lK_eq_tsum hν lam hea, ENNReal.tsum_eq_iSup_nat, ENNReal.add_iSup]
  refine iSup_le fun n => ?_
  exact le_trans le_self_add (iterate_ge hν lam ha he hf h n t ht x)

theorem renewal_upper_of_measurable {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {a e f : ℝ → ℝ → ℝ≥0∞}
    (ha : Measurable (Function.uncurry a)) (he : Measurable (Function.uncurry e))
    (hf : Measurable (Function.uncurry f)) {T : ℝ}
    (h : ∀ t ∈ Ioc 0 T, ∀ x, f t x ≤ a t x + lstConv (e + f) (lL ν lam 0) t x)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : ℝ) (hfin : lstConv (e + f) (lL ν lam 0) t x ≠ ⊤) :
    f t x ≤ a t x + lstConv (e + a) (lK ν lam) t x := by
  have hea : Measurable (Function.uncurry (e + a)) := he.add ha
  set C := lstConv (e + f) (lL ν lam 0) t x
  set S := lstConv (e + a) (lK ν lam) t x
  have hbound : ∀ n : ℕ, f t x ≤
      a t x + S + ENNReal.ofReal (BCoeff (bConst ν lam) t n) * C := by
    intro n
    refine (iterate_le hν lam ha he hf h n t ht x).trans ?_
    gcongr
    · exact (ENNReal.sum_le_tsum _).trans (lstConv_lK_eq_tsum hν lam hea t x).ge
    · exact lstConv_ofReal_L_le_BCoeff_mul hν lam n (e + f) t x
  have hlim : Tendsto (fun n : ℕ => a t x + S + ENNReal.ofReal (BCoeff (bConst ν lam) t n) * C)
      atTop (𝓝 (a t x + S + 0 * C)) := by
    refine tendsto_const_nhds.add (ENNReal.Tendsto.mul_const ?_ (Or.inr hfin))
    have := (ENNReal.tendsto_ofReal (tendsto_BCoeff (bConst_nonneg ν lam) ht.1.le))
    simpa using this
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim hbound

/-! ### The renewal theorems (measurability at positive times only) -/

theorem pos_add (e f : ℝ → ℝ → ℝ≥0∞) : pos e + pos f = pos (e + f) := by
  funext s y
  simp only [pos, Pi.add_apply]
  split_ifs <;> simp

/-- **S-Low (generic).** If `a + (e + f) ⋆ 𝓛₀(λ) ≤ f` on `(0,T] × ℝ`, then
`a + (e + a) ⋆ 𝓚(λ) ≤ f` on `(0,T] × ℝ`. No finiteness hypothesis. -/
theorem renewal_lower {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {a e f : ℝ → ℝ → ℝ≥0∞}
    (ha : Measurable (cut a)) (he : Measurable (cut e)) (hf : Measurable (cut f)) {T : ℝ}
    (h : ∀ t ∈ Ioc 0 T, ∀ x, a t x + lstConv (e + f) (lL ν lam 0) t x ≤ f t x) :
    ∀ t ∈ Ioc 0 T, ∀ x, a t x + lstConv (e + a) (lK ν lam) t x ≤ f t x := by
  have h' : ∀ t ∈ Ioc 0 T, ∀ x,
      pos a t x + lstConv (pos e + pos f) (lL ν lam 0) t x ≤ pos f t x := by
    intro t ht x
    rw [pos_of_pos a ht.1, pos_of_pos f ht.1, pos_add, lstConv_pos_left]
    exact h t ht x
  intro t ht x
  have := renewal_lower_of_measurable hν lam (measurable_pos ha) (measurable_pos he)
    (measurable_pos hf) h' t ht x
  rwa [pos_of_pos a ht.1, pos_of_pos f ht.1, pos_add, lstConv_pos_left] at this

/-- **S-Up (generic).** If `f ≤ a + (e + f) ⋆ 𝓛₀(λ)` on `(0,T] × ℝ`, then at every
`(t,x) ∈ (0,T] × ℝ` with `((e + f) ⋆ 𝓛₀(λ))(t,x) < ∞`, `f ≤ a + (e + a) ⋆ 𝓚(λ)`. -/
theorem renewal_upper {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {a e f : ℝ → ℝ → ℝ≥0∞}
    (ha : Measurable (cut a)) (he : Measurable (cut e)) (hf : Measurable (cut f)) {T : ℝ}
    (h : ∀ t ∈ Ioc 0 T, ∀ x, f t x ≤ a t x + lstConv (e + f) (lL ν lam 0) t x)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : ℝ) (hfin : lstConv (e + f) (lL ν lam 0) t x ≠ ⊤) :
    f t x ≤ a t x + lstConv (e + a) (lK ν lam) t x := by
  have h' : ∀ t ∈ Ioc 0 T, ∀ x,
      pos f t x ≤ pos a t x + lstConv (pos e + pos f) (lL ν lam 0) t x := by
    intro t ht x
    rw [pos_of_pos a ht.1, pos_of_pos f ht.1, pos_add, lstConv_pos_left]
    exact h t ht x
  have hfin' : lstConv (pos e + pos f) (lL ν lam 0) t x ≠ ⊤ := by
    rwa [pos_add, lstConv_pos_left]
  have := renewal_upper_of_measurable hν lam (measurable_pos ha) (measurable_pos he)
    (measurable_pos hf) h' ht x hfin'
  rwa [pos_of_pos a ht.1, pos_of_pos f ht.1, pos_add, lstConv_pos_left] at this

/-- **Uniqueness core** (`T2:ExUni(1)`, Step 5). If `w ≤ w ⋆ 𝓛₀(λ)` on `(0,T] × ℝ` and
`w ⋆ 𝓛₀(λ) < ∞` on `(0,T] × ℝ`, then `w = 0` on `(0,T] × ℝ`. -/
theorem eq_zero_of_le_lstConv_L_zero {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {w : ℝ → ℝ → ℝ≥0∞}
    (hw : Measurable (cut w)) {T : ℝ}
    (h : ∀ t ∈ Ioc 0 T, ∀ x, w t x ≤ lstConv w (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x)
    (hfin : ∀ t ∈ Ioc 0 T, ∀ x, lstConv w (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x ≠ ⊤) :
    ∀ t ∈ Ioc 0 T, ∀ x, w t x = 0 := by
  have h0 : Measurable (cut (0 : ℝ → ℝ → ℝ≥0∞)) := by
    have : cut (0 : ℝ → ℝ → ℝ≥0∞) = fun _ => 0 := by funext p; simp [cut]
    rw [this]; exact measurable_const
  intro t ht x
  have := renewal_upper hν lam (a := 0) (e := 0) h0 h0 hw (T := T)
    (fun t ht x => by simpa using h t ht x) ht x (by simpa using hfin t ht x)
  simpa using this

/-! ### Measurability of `J₀` -/

theorem measurable_J0 (ν : ℝ) (μ : Measure ℝ) [SFinite μ] :
    Measurable (Function.uncurry (J0 ν μ)) := by
  have h : StronglyMeasurable (Function.uncurry fun (p : ℝ × ℝ) (z : ℝ) => G ν p.1 (p.2 - z)) := by
    apply Measurable.stronglyMeasurable
    simp only [G]
    fun_prop
  exact (h.integral_prod_right (ν := μ)).measurable

theorem measurable_cut_ofReal_J0_sq (ν : ℝ) (μ : Measure ℝ) [SFinite μ] :
    Measurable (cut fun s y => ENNReal.ofReal (J0 ν μ s y ^ 2)) :=
  measurable_cut ((measurable_J0 ν μ).pow_const 2).ennreal_ofReal

theorem measurable_cut_const (c : ℝ≥0∞) : Measurable (cut fun _ _ => c) :=
  measurable_cut measurable_const

/-! ### The paper's statements: `E2:SecMom-Lower`, `E2:SecMom-Up`, `E2:SecMom` -/

/-- **S-Low (`E2:SecMom-Lower`, `p = 2`).** If `f` satisfies the lower renewal inequality
`J₀² + (ϑ² + f) ⋆ 𝓛₀(lip) ≤ f` at positive times, then
`J₀² + (ϑ² + J₀²) ⋆ 𝓚(lip) ≤ f` at positive times. No finiteness hypothesis. -/
theorem secondMoment_lower {μ : Measure ℝ} [SFinite μ] {ν : ℝ} (hν : 0 < ν) (lip ϑ : ℝ)
    {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f))
    (h : ∀ t > 0, ∀ x, ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (fun s y => ENNReal.ofReal (ϑ ^ 2) + f s y)
        (fun s y => ENNReal.ofReal (L ν lip 0 s y)) t x ≤ f t x) :
    ∀ t > 0, ∀ x, ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (fun s y => ENNReal.ofReal (ϑ ^ 2) + ENNReal.ofReal (J0 ν μ s y ^ 2))
        (fun s y => ENNReal.ofReal (K ν lip s y)) t x ≤ f t x := by
  intro t ht x
  exact renewal_lower hν lip (a := fun s y => ENNReal.ofReal (J0 ν μ s y ^ 2))
    (e := fun _ _ => ENNReal.ofReal (ϑ ^ 2)) (measurable_cut_ofReal_J0_sq ν μ)
    (measurable_cut_const _) hf (T := t) (fun s hs y => h s hs.1 y) t ⟨ht, le_rfl⟩ x

/-- **S-Up (`E2:SecMom-Up`, `p = 2`).** If `f` satisfies the upper renewal inequality
`f ≤ J₀² + (V² + f) ⋆ 𝓛₀(Lip)` at positive times and `(V² + f) ⋆ 𝓛₀(Lip) < ∞` at positive
times, then `f ≤ J₀² + (V² + J₀²) ⋆ 𝓚(Lip)` at positive times. -/
theorem secondMoment_upper {μ : Measure ℝ} [SFinite μ] {ν : ℝ} (hν : 0 < ν) (Lip V : ℝ)
    {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f))
    (h : ∀ t > 0, ∀ x, f t x ≤ ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (fun s y => ENNReal.ofReal (V ^ 2) + f s y)
        (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) t x)
    (hfin : ∀ t > 0, ∀ x, lstConv (fun s y => ENNReal.ofReal (V ^ 2) + f s y)
        (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) t x ≠ ⊤) :
    ∀ t > 0, ∀ x, f t x ≤ ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (fun s y => ENNReal.ofReal (V ^ 2) + ENNReal.ofReal (J0 ν μ s y ^ 2))
        (fun s y => ENNReal.ofReal (K ν Lip s y)) t x := by
  intro t ht x
  exact renewal_upper hν Lip (a := fun s y => ENNReal.ofReal (J0 ν μ s y ^ 2))
    (e := fun _ _ => ENNReal.ofReal (V ^ 2)) (measurable_cut_ofReal_J0_sq ν μ)
    (measurable_cut_const _) hf (T := t) (fun s hs y => h s hs.1 y) ⟨ht, le_rfl⟩ x
    (hfin t ht x)

/-- **S-Eq (`E2:fint` ⇒ `E2:SecMom`, `ρ(u) = λu`).** If `f = J₀² + f ⋆ 𝓛₀(λ)` at positive
times and `f ⋆ 𝓛₀(λ) < ∞` at positive times, then `f = J₀² + J₀² ⋆ 𝓚(λ)` at positive
times. -/
theorem secondMoment_eq {μ : Measure ℝ} [SFinite μ] {ν : ℝ} (hν : 0 < ν) (lam : ℝ)
    {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f))
    (h : ∀ t > 0, ∀ x, f t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv f (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x)
    (hfin : ∀ t > 0, ∀ x, lstConv f (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x ≠ ⊤) :
    ∀ t > 0, ∀ x, f t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (fun s y => ENNReal.ofReal (J0 ν μ s y ^ 2))
        (fun s y => ENNReal.ofReal (K ν lam s y)) t x := by
  have h0 : Measurable (cut (0 : ℝ → ℝ → ℝ≥0∞)) := by
    have : cut (0 : ℝ → ℝ → ℝ≥0∞) = fun _ => 0 := by funext p; simp [cut]
    rw [this]; exact measurable_const
  intro t ht x
  refine le_antisymm ?_ ?_
  · have := renewal_upper hν lam (a := fun s y => ENNReal.ofReal (J0 ν μ s y ^ 2)) (e := 0)
      (measurable_cut_ofReal_J0_sq ν μ) h0 hf (T := t)
      (fun s hs y => by rw [zero_add]; exact (h s hs.1 y).le) ⟨ht, le_rfl⟩ x
      (by rw [zero_add]; exact hfin t ht x)
    simpa using this
  · have := renewal_lower hν lam (a := fun s y => ENNReal.ofReal (J0 ν μ s y ^ 2)) (e := 0)
      (measurable_cut_ofReal_J0_sq ν μ) h0 hf (T := t)
      (fun s hs y => by rw [zero_add]; exact (h s hs.1 y).ge) t ⟨ht, le_rfl⟩ x
    simpa using this

/-! ### Connection to `secondMomentExpr` (Gaussian-tempered `μ`) -/

theorem Hfun_nonneg {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Hfun ν lam t :=
  intervalIntegral.integral_nonneg ht fun _ _ =>
    integral_nonneg fun _ => mul_nonneg zero_le_one (K_nonneg hν lam _ _)

/-- `ofReal 𝓗(t) = (1 ⋆ 𝓚)(t,x)` in `ℝ≥0∞`, for every `x`. -/
theorem ofReal_Hfun {ν : ℝ} (hν : 0 < ν) (lam : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    ENNReal.ofReal (Hfun ν lam t) = lstConv (fun _ _ => 1) (lK ν lam) t x := by
  rw [lstConv_one_ofReal_K hν lam ht x, Hfun, one_conv_K hν ht 0]

/-- For Gaussian-tempered `μ` and `t > 0`:
`J₀² + (V² + J₀²) ⋆ 𝓚(λ) = ofReal (secondMomentExpr (J0 ν μ) ν V λ t x)` in `ℝ≥0∞`. -/
theorem J0_sq_add_lstConv_eq_secondMomentExpr {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (V lam : ℝ) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (fun s y => ENNReal.ofReal (V ^ 2) + ENNReal.ofReal (J0 ν μ s y ^ 2))
        (fun s y => ENNReal.ofReal (K ν lam s y)) t x =
      ENNReal.ofReal (secondMomentExpr (J0 ν μ) ν V lam t x) := by
  have hc : lstConv (fun _ _ => ENNReal.ofReal (V ^ 2)) (lK ν lam) t x =
      ENNReal.ofReal (V ^ 2) * ENNReal.ofReal (Hfun ν lam t) := by
    rw [ofReal_Hfun hν lam ht.le x, ← lstConv_const_mul_left _ _ ENNReal.ofReal_ne_top]
    simp
  rw [lstConv_add_left' measurable_const (measurable_lK hν lam), hc,
    lstConv_ofReal_J0_sq_K hT hν lam ht x, secondMomentExpr,
    ENNReal.ofReal_add (add_nonneg (sq_nonneg _)
      (MomentBridge.stConv_J0_sq_K_nonneg hν μ lam ht x))
      (mul_nonneg (sq_nonneg V) (Hfun_nonneg hν lam ht.le)),
    ENNReal.ofReal_add (sq_nonneg _) (MomentBridge.stConv_J0_sq_K_nonneg hν μ lam ht x),
    ENNReal.ofReal_mul (sq_nonneg V)]
  ring

/-- `(J₀² ⋆ 𝓚)(t,x)` in `lstConv` form is the lower integral of `MomentBridge`. -/
theorem lstConv_J0_sq_K_eq_lintegral (μ : Measure ℝ) (ν lam t x : ℝ) :
    lstConv (fun s y => ENNReal.ofReal (J0 ν μ s y ^ 2))
        (fun s y => ENNReal.ofReal (K ν lam s y)) t x =
      ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * K ν lam (t - s) (x - y)) := by
  rw [lstConv_eq_Ioc]
  refine lintegral_congr fun s => lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_mul (sq_nonneg _)]

/-- **S-Low in `secondMomentExpr` form**, Gaussian-tempered `μ`. -/
theorem secondMoment_lower_secondMomentExpr {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (lip ϑ : ℝ)
    {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f))
    (h : ∀ t > 0, ∀ x, ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (fun s y => ENNReal.ofReal (ϑ ^ 2) + f s y)
        (fun s y => ENNReal.ofReal (L ν lip 0 s y)) t x ≤ f t x) :
    ∀ t > 0, ∀ x, ENNReal.ofReal (secondMomentExpr (J0 ν μ) ν ϑ lip t x) ≤ f t x := by
  intro t ht x
  rw [← J0_sq_add_lstConv_eq_secondMomentExpr hT hν ϑ lip ht x]
  exact secondMoment_lower hν lip ϑ hf h t ht x

/-- **S-Up in `secondMomentExpr` form**, Gaussian-tempered `μ`. -/
theorem secondMoment_upper_secondMomentExpr {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (Lip V : ℝ)
    {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f))
    (h : ∀ t > 0, ∀ x, f t x ≤ ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (fun s y => ENNReal.ofReal (V ^ 2) + f s y)
        (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) t x)
    (hfin : ∀ t > 0, ∀ x, lstConv (fun s y => ENNReal.ofReal (V ^ 2) + f s y)
        (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) t x ≠ ⊤) :
    ∀ t > 0, ∀ x, f t x ≤ ENNReal.ofReal (secondMomentExpr (J0 ν μ) ν V Lip t x) := by
  intro t ht x
  rw [← J0_sq_add_lstConv_eq_secondMomentExpr hT hν V Lip ht x]
  exact secondMoment_upper hν Lip V hf h hfin t ht x

/-- **S-Eq in `secondMomentExpr` form** (`E2:SecMom` with `ϑ = 0`), Gaussian-tempered `μ`. -/
theorem secondMoment_eq_secondMomentExpr {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (lam : ℝ)
    {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f))
    (h : ∀ t > 0, ∀ x, f t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv f (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x)
    (hfin : ∀ t > 0, ∀ x, lstConv f (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x ≠ ⊤) :
    ∀ t > 0, ∀ x, f t x = ENNReal.ofReal (secondMomentExpr (J0 ν μ) ν 0 lam t x) := by
  intro t ht x
  rw [← J0_sq_add_lstConv_eq_secondMomentExpr hT hν 0 lam ht x, secondMoment_eq hν lam hf h hfin
    t ht x]
  simp

/-- **S-Eq in the form of `P2_Ex_Exp_lintegral`'s hypothesis.** -/
theorem secondMoment_eq_lintegral {μ : Measure ℝ} [SFinite μ] {ν : ℝ} (hν : 0 < ν) (lam : ℝ)
    {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f))
    (h : ∀ t > 0, ∀ x, f t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv f (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x)
    (hfin : ∀ t > 0, ∀ x, lstConv f (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x ≠ ⊤) :
    ∀ t > 0, ∀ x, f t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * K ν lam (t - s) (x - y)) := by
  intro t ht x
  rw [secondMoment_eq hν lam hf h hfin t ht x, lstConv_J0_sq_K_eq_lintegral]

/-- **S-Up in the form of `T2_Growth_upper_lintegral`'s hypothesis** (`V = 0`). -/
theorem secondMoment_upper_lintegral {μ : Measure ℝ} [SFinite μ] {ν : ℝ} (hν : 0 < ν)
    (Lip : ℝ) {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f))
    (h : ∀ t > 0, ∀ x, f t x ≤ ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv f (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) t x)
    (hfin : ∀ t > 0, ∀ x, lstConv f (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) t x ≠ ⊤) :
    ∀ t > 0, ∀ x, f t x ≤ ENNReal.ofReal (J0 ν μ t x ^ 2) +
      ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * K ν Lip (t - s) (x - y)) := by
  intro t ht x
  have := secondMoment_upper hν Lip 0 hf (fun t ht x => by simpa using h t ht x)
    (fun t ht x => by simpa using hfin t ht x) t ht x
  simpa [lstConv_J0_sq_K_eq_lintegral] using this

/-- **S-Low in the forms of `T2_Growth_lower` and `T2_Growth_lower_top`'s hypotheses**,
Gaussian-tempered `μ`. -/
theorem secondMoment_lower_growth_inputs {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (lip ϑ : ℝ)
    {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f))
    (h : ∀ t > 0, ∀ x, ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (fun s y => ENNReal.ofReal (ϑ ^ 2) + f s y)
        (fun s y => ENNReal.ofReal (L ν lip 0 s y)) t x ≤ f t x) :
    (∀ t > 0, ∀ x, ENNReal.ofReal (stConv (fun s y => J0 ν μ s y ^ 2) (K ν lip) t x) ≤ f t x) ∧
      (∀ t > 0, ∀ x,
        ENNReal.ofReal (ϑ ^ 2 * stConv (fun _ _ => (1 : ℝ)) (K ν lip) t x) ≤ f t x) := by
  have key := secondMoment_lower_secondMomentExpr hT hν lip ϑ hf h
  have hJ := fun t (ht : 0 < t) x => MomentBridge.stConv_J0_sq_K_nonneg hν μ lip ht x
  have hH := fun t (ht : 0 < t) => Hfun_nonneg hν lip ht.le
  have hH' : ∀ t, 0 < t → ∀ x, stConv (fun _ _ => (1 : ℝ)) (K ν lip) t x = Hfun ν lip t :=
    fun t ht x => by rw [Hfun, one_conv_K hν ht.le x, one_conv_K hν ht.le 0]
  refine ⟨fun t ht x => le_trans (ENNReal.ofReal_le_ofReal ?_) (key t ht x),
    fun t ht x => le_trans (ENNReal.ofReal_le_ofReal ?_) (key t ht x)⟩
  · have := hH t ht
    have := sq_nonneg ϑ
    have := sq_nonneg (J0 ν μ t x)
    rw [secondMomentExpr]
    nlinarith
  · rw [hH' t ht x, secondMomentExpr]
    have := hJ t ht x
    have := sq_nonneg (J0 ν μ t x)
    linarith

/-! ### Bridges to the solution predicate -/

/-- **The `finite` field as a convolution.** For `g` measurable at positive times,
`(g ⋆ G_ν²)(t,x) = ∫⁻_{(0,t) × ℝ} G_ν(t−s,x−y)² g(s,y)`, the lower integral in
`StochDefs.IsRandomFieldSolution.finite` (with `g = E ρ(u)²`). -/
theorem lstConv_G_sq_eq_setLIntegral {ν : ℝ} {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (cut g))
    (t x : ℝ) :
    lstConv g (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x =
      ∫⁻ z in Ioo 0 t ×ˢ univ, ENNReal.ofReal (G ν (t - z.1) (x - z.2) ^ 2) * g z.1 z.2 := by
  have hcongr : ∫⁻ z in Ioo 0 t ×ˢ univ, ENNReal.ofReal (G ν (t - z.1) (x - z.2) ^ 2) * g z.1 z.2 =
      ∫⁻ z in Ioo 0 t ×ˢ univ, pos g z.1 z.2 * ENNReal.ofReal (G ν (t - z.1) (x - z.2) ^ 2) := by
    refine setLIntegral_congr_fun (measurableSet_Ioo.prod MeasurableSet.univ) fun z hz => ?_
    rw [pos_of_pos g hz.1.1, mul_comm]
  have hm : Measurable fun z : ℝ × ℝ => pos g z.1 z.2 * ENNReal.ofReal (G ν (t - z.1) (x - z.2) ^ 2) := by
    refine (measurable_pos hg).mul ?_
    refine Measurable.ennreal_ofReal ?_
    simp only [G]
    fun_prop
  rw [hcongr, Measure.volume_eq_prod, setLIntegral_prod _ hm.aemeasurable, ← lstConv_pos_left]
  simp [lstConv]

/-- `𝓛₀(λ) = λ² · G²` in `ℝ≥0∞`. -/
theorem lL_zero_eq (ν lam s y : ℝ) :
    lL ν lam 0 s y = ENNReal.ofReal (lam ^ 2) * ENNReal.ofReal (G ν s y ^ 2) := by
  simp only [lL, S1Glue.L0_eq, ENNReal.ofReal_mul (sq_nonneg lam)]

/-- **Upper Lipschitz bridge.** If `g ≤ Lip² (h)` at times in `(0,t)` (e.g. `g = E ρ(u)²`,
`h = V² + E u²` under `|ρ(u)|² ≤ Lip²(V² + u²)`), then `(g ⋆ G²)(t,x) ≤ (h ⋆ 𝓛₀(Lip))(t,x)`. -/
theorem lstConv_G_sq_le_lstConv_L_zero {ν : ℝ} (Lip : ℝ) {g h : ℝ → ℝ → ℝ≥0∞} {t : ℝ}
    (hgh : ∀ s ∈ Ioo 0 t, ∀ y, g s y ≤ ENNReal.ofReal (Lip ^ 2) * h s y) (x : ℝ) :
    lstConv g (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x ≤
      lstConv h (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) t x := by
  have e : (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) =
      fun s y => ENNReal.ofReal (Lip ^ 2) * ENNReal.ofReal (G ν s y ^ 2) := by
    funext s y; exact lL_zero_eq ν Lip s y
  rw [e, lstConv_const_mul_right _ _ ENNReal.ofReal_ne_top,
    ← lstConv_const_mul_left _ _ ENNReal.ofReal_ne_top]
  exact lstConv_mono_left hgh x

/-- **Lower Lipschitz bridge.** If `lip² (h) ≤ g` at times in `(0,t)` (e.g. under
`|ρ(u)|² ≥ lip²(ϑ² + u²)`), then `(h ⋆ 𝓛₀(lip))(t,x) ≤ (g ⋆ G²)(t,x)`. -/
theorem lstConv_L_zero_le_lstConv_G_sq {ν : ℝ} (lip : ℝ) {g h : ℝ → ℝ → ℝ≥0∞} {t : ℝ}
    (hgh : ∀ s ∈ Ioo 0 t, ∀ y, ENNReal.ofReal (lip ^ 2) * h s y ≤ g s y) (x : ℝ) :
    lstConv h (fun s y => ENNReal.ofReal (L ν lip 0 s y)) t x ≤
      lstConv g (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x := by
  have e : (fun s y => ENNReal.ofReal (L ν lip 0 s y)) =
      fun s y => ENNReal.ofReal (lip ^ 2) * ENNReal.ofReal (G ν s y ^ 2) := by
    funext s y; exact lL_zero_eq ν lip s y
  rw [e, lstConv_const_mul_right _ _ ENNReal.ofReal_ne_top,
    ← lstConv_const_mul_left _ _ ENNReal.ofReal_ne_top]
  exact lstConv_mono_left hgh x

theorem lL_zero_le_lK {ν : ℝ} (hν : 0 < ν) (lam s y : ℝ) : lL ν lam 0 s y ≤ lK ν lam s y := by
  simp only [lL, lK]
  rw [ofReal_K_eq_tsum hν lam s y]
  exact ENNReal.le_tsum (f := fun n => ENNReal.ofReal (L ν lam n s y)) 0

/-- **Finiteness for S-Up from the solution.** Let `μ` be Gaussian tempered, `t > 0`. If
`f ≤ J₀² + g ⋆ G²` at times in `(0,t)` (the upper half of the Itô identity `E2:fint`, with
`g = E ρ(u)²` measurable at positive times) and `(g ⋆ G²)(t,x) < ∞` (the solution's `finite`
field, via `lstConv_G_sq_eq_setLIntegral`), then `((V² + f) ⋆ 𝓛₀(Lip))(t,x) < ∞`. -/
theorem lstConv_L_zero_ne_top {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (Lip V : ℝ)
    {f g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (cut g)) {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hle : ∀ s ∈ Ioo 0 t, ∀ y, f s y ≤ ENNReal.ofReal (J0 ν μ s y ^ 2) +
      lstConv g (fun r z => ENNReal.ofReal (G ν r z ^ 2)) s y)
    (hfin : lstConv g (fun r z => ENNReal.ofReal (G ν r z ^ 2)) t x ≠ ⊤) :
    lstConv (fun s y => ENNReal.ofReal (V ^ 2) + f s y)
      (fun s y => ENNReal.ofReal (L ν Lip 0 s y)) t x ≠ ⊤ := by
  set G2 : ℝ → ℝ → ℝ≥0∞ := fun r z => ENNReal.ofReal (G ν r z ^ 2) with hG2
  have hG2L : G2 = lL ν 1 0 := by
    funext r z; simp [hG2, lL, S1Glue.L0_eq]
  have hmG2 : Measurable (Function.uncurry G2) := by rw [hG2L]; exact measurable_lL hν 1 0
  have hmc : Measurable (Function.uncurry fun (_ : ℝ) (_ : ℝ) => ENNReal.ofReal (V ^ 2)) :=
    measurable_const
  have hmJ : Measurable (Function.uncurry fun s y => ENNReal.ofReal (J0 ν μ s y ^ 2)) :=
    ((measurable_J0 ν μ).pow_const 2).ennreal_ofReal
  -- split
  have hsplit : lstConv (fun s y => ENNReal.ofReal (V ^ 2) + f s y) (lL ν Lip 0) t x ≤
      lstConv (fun _ _ => ENNReal.ofReal (V ^ 2)) (lL ν Lip 0) t x +
        lstConv (fun s y => ENNReal.ofReal (J0 ν μ s y ^ 2)) (lL ν Lip 0) t x +
        lstConv (lstConv (pos g) G2) (lL ν Lip 0) t x := by
    calc _ ≤ lstConv (fun s y => (ENNReal.ofReal (V ^ 2) + ENNReal.ofReal (J0 ν μ s y ^ 2)) +
          lstConv (pos g) G2 s y) (lL ν Lip 0) t x := by
          refine lstConv_mono_left (fun s hs y => ?_) x
          rw [lstConv_pos_left, add_assoc]
          gcongr
          exact hle s hs y
      _ = _ := by
          have hmcJ : Measurable (Function.uncurry fun s y =>
              ENNReal.ofReal (V ^ 2) + ENNReal.ofReal (J0 ν μ s y ^ 2)) := hmc.add hmJ
          rw [lstConv_add_left' hmcJ (measurable_lL hν Lip 0),
            lstConv_add_left' hmc (measurable_lL hν Lip 0)]
  refine ne_top_of_le_ne_top ?_ hsplit
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩
  · -- the constant term: `V² (1 ⋆ 𝓛₀) ≤ V² (1 ⋆ 𝓚) < ∞`
    have e1 : lstConv (fun _ _ => ENNReal.ofReal (V ^ 2)) (lL ν Lip 0) t x =
        ENNReal.ofReal (V ^ 2) * lstConv (fun _ _ => 1) (lL ν Lip 0) t x := by
      rw [← lstConv_const_mul_left _ _ ENNReal.ofReal_ne_top]; simp
    rw [e1]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ?_
      (lstConv_mono_right (fun r _ z => lL_zero_le_lK hν Lip r z) x))
    rw [lstConv_one_ofReal_K hν Lip ht.le x]
    exact ENNReal.ofReal_ne_top
  · -- `J₀² ⋆ 𝓛₀ < ∞` (`L2:InDt`)
    have e2 : lstConv (fun s y => ENNReal.ofReal (J0 ν μ s y ^ 2)) (lL ν Lip 0) t x =
        ∫⁻ s in Ioc 0 t, ∫⁻ y, ENNReal.ofReal (J0 ν μ s y ^ 2 * L ν Lip 0 (t - s) (x - y)) := by
      rw [lstConv_eq_Ioc]
      refine lintegral_congr fun s => lintegral_congr fun y => ?_
      rw [ENNReal.ofReal_mul (sq_nonneg _)]
    rw [e2]
    exact (L2_InDt_L0_lt_top hT hν ht Lip x).ne
  · -- `(g ⋆ G²) ⋆ 𝓛₀ = g ⋆ (G² ⋆ 𝓛₀) ≤ Lip² B₁(t) (g ⋆ G²) < ∞`
    rw [lstConv_assoc (measurable_pos hg) hmG2 (measurable_lL hν Lip 0)]
    have hk : ∀ r ∈ Ioo 0 t, ∀ z, lstConv G2 (lL ν Lip 0) r z ≤
        ENNReal.ofReal (Lip ^ 2) * ENNReal.ofReal (BCoeff (bConst ν 1) t 1) * G2 r z := by
      intro r hr z
      have e3 : lL ν Lip 0 = fun s y => ENNReal.ofReal (Lip ^ 2) * lL ν 1 0 s y := by
        funext s y; rw [lL_zero_eq, ← hG2L]
      rw [e3, lstConv_const_mul_right _ _ ENNReal.ofReal_ne_top, hG2L,
        lstConv_ofReal_L_zero_L_zero hν 1 r z, mul_assoc]
      gcongr
      exact BCoeff_mono (bConst_nonneg ν 1) 1 hr.1.le hr.2.le
    refine ne_top_of_le_ne_top ?_ (lstConv_mono_right hk x)
    rw [lstConv_const_mul_right _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top), lstConv_pos_left]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hfin

/-- Finiteness for the uniqueness core: if `w ≤ 2 (f₁ + f₂)` at times in `(0,t)` (e.g.
`E(u−v)² ≤ 2(Eu² + Ev²)`) and `f₁ ⋆ k`, `f₂ ⋆ k` are finite at `(t,x)`, so is `w ⋆ k`. -/
theorem lstConv_ne_top_of_le_two_mul_add {f₁ f₂ w k : ℝ → ℝ → ℝ≥0∞} (hf₁ : Measurable (cut f₁))
    (hk : Measurable (Function.uncurry k)) {t : ℝ} (x : ℝ)
    (h : ∀ s ∈ Ioo 0 t, ∀ y, w s y ≤ 2 * (f₁ s y + f₂ s y))
    (h₁ : lstConv f₁ k t x ≠ ⊤) (h₂ : lstConv f₂ k t x ≠ ⊤) : lstConv w k t x ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (lstConv_mono_left (g := k)
    (f' := fun s y => 2 * (pos f₁ s y + f₂ s y)) (fun s hs y => ?_) x)
  · rw [lstConv_const_mul_left _ _ ENNReal.ofNat_ne_top,
      lstConv_add_left' (measurable_pos hf₁) hk, lstConv_pos_left]
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.mpr ⟨h₁, h₂⟩)
  · rw [pos_of_pos f₁ hs.1]; exact h s hs y

/-! ### Adapters from the Itô renewal identity

The stochastic side (`Stoch.momentFn_two_eq_renewal`) supplies, for `t > 0`,
`f t x = ofReal (J₀(t,x)²) + (g ⋆ G_ν²)(t,x)` with `f = E u²`, `g = E ρ(u)²`, and the solution's
`finite` field `∫⁻_{(0,t) × ℝ} G_ν(t−s,x−y)² g(s,y) < ∞`. The theorems below take exactly these
hypotheses (with `g` and `f` measurable at positive times) plus the growth bound on `ρ`. -/

/-- The `finite` field gives `(g ⋆ G²)(t,x) ≠ ∞`. -/
theorem lstConv_G_sq_ne_top_of_finite {ν : ℝ} {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (cut g))
    {t : ℝ} (x : ℝ)
    (hfin : ∫⁻ z in Ioo 0 t ×ˢ univ, ENNReal.ofReal (G ν (t - z.1) (x - z.2) ^ 2) *
      g z.1 z.2 < ∞) :
    lstConv g (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x ≠ ⊤ := by
  rw [lstConv_G_sq_eq_setLIntegral hg]; exact hfin.ne

/-- **S-Up from the Itô identity** (`E2:SecMom-Up`, `p = 2`): if `f = J₀² + g ⋆ G²` at positive
times, `g ≤ Lip² (V² + f)` at positive times (from `|ρ(u)|² ≤ Lip²(V² + u²)`), and the `finite`
field holds, then for Gaussian-tempered `μ`, `f ≤ ofReal (secondMomentExpr (J0 ν μ) ν V Lip)`
at positive times. -/
theorem secondMoment_upper_of_renewal {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (Lip V : ℝ)
    {f g : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f)) (hg : Measurable (cut g))
    (hid : ∀ t > 0, ∀ x, f t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv g (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x)
    (hgrowth : ∀ s > 0, ∀ y, g s y ≤ ENNReal.ofReal (Lip ^ 2) * (ENNReal.ofReal (V ^ 2) + f s y))
    (hfin : ∀ t > 0, ∀ x, ∫⁻ z in Ioo 0 t ×ˢ univ, ENNReal.ofReal (G ν (t - z.1) (x - z.2) ^ 2) *
      g z.1 z.2 < ∞) :
    ∀ t > 0, ∀ x, f t x ≤ ENNReal.ofReal (secondMomentExpr (J0 ν μ) ν V Lip t x) := by
  refine secondMoment_upper_secondMomentExpr hT hν Lip V hf (fun t ht x => ?_) (fun t ht x => ?_)
  · rw [hid t ht x]
    exact add_le_add_right (lstConv_G_sq_le_lstConv_L_zero (ν := ν) (t := t) Lip
      (fun s hs y => hgrowth s hs.1 y) x) _
  · exact lstConv_L_zero_ne_top hT hν Lip V hg ht x (fun s hs y => (hid s hs.1 y).le)
      (lstConv_G_sq_ne_top_of_finite hg x (hfin t ht x))

/-- **S-Low from the Itô identity** (`E2:SecMom-Lower`, `p = 2`): if `f = J₀² + g ⋆ G²` (only
`≥` is used) and `lip² (ϑ² + f) ≤ g` at positive times (from `|ρ(u)|² ≥ lip²(ϑ² + u²)`), then for
Gaussian-tempered `μ`, `ofReal (secondMomentExpr (J0 ν μ) ν ϑ lip) ≤ f` at positive times. No
finiteness is needed. -/
theorem secondMoment_lower_of_renewal {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (lip ϑ : ℝ)
    {f g : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f))
    (hid : ∀ t > 0, ∀ x, f t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv g (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x)
    (hgrowth : ∀ s > 0, ∀ y, ENNReal.ofReal (lip ^ 2) * (ENNReal.ofReal (ϑ ^ 2) + f s y) ≤ g s y) :
    ∀ t > 0, ∀ x, ENNReal.ofReal (secondMomentExpr (J0 ν μ) ν ϑ lip t x) ≤ f t x := by
  refine secondMoment_lower_secondMomentExpr hT hν lip ϑ hf (fun t ht x => ?_)
  rw [hid t ht x]
  exact add_le_add_right (lstConv_L_zero_le_lstConv_G_sq (ν := ν) (t := t) lip
    (fun s hs y => hgrowth s hs.1 y) x) _

/-- **S-Eq from the Itô identity** (`E2:SecMom`, `ρ(u) = λu`): if `f = J₀² + g ⋆ G²` with
`g = λ² f` at positive times and the `finite` field holds, then for Gaussian-tempered `μ`,
`f = ofReal (secondMomentExpr (J0 ν μ) ν 0 λ)` at positive times. -/
theorem secondMoment_eq_of_renewal {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (lam : ℝ)
    {f g : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (cut f)) (hg : Measurable (cut g))
    (hid : ∀ t > 0, ∀ x, f t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv g (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x)
    (hlin : ∀ s > 0, ∀ y, g s y = ENNReal.ofReal (lam ^ 2) * f s y)
    (hfin : ∀ t > 0, ∀ x, ∫⁻ z in Ioo 0 t ×ˢ univ, ENNReal.ofReal (G ν (t - z.1) (x - z.2) ^ 2) *
      g z.1 z.2 < ∞) :
    ∀ t > 0, ∀ x, f t x = ENNReal.ofReal (secondMomentExpr (J0 ν μ) ν 0 lam t x) := by
  have hconv : ∀ t > 0, ∀ x, lstConv g (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x =
      lstConv f (fun s y => ENNReal.ofReal (L ν lam 0 s y)) t x := fun t _ x =>
    le_antisymm (lstConv_G_sq_le_lstConv_L_zero lam (fun s hs y => (hlin s hs.1 y).le) x)
      (lstConv_L_zero_le_lstConv_G_sq lam (fun s hs y => (hlin s hs.1 y).ge) x)
  refine secondMoment_eq_secondMomentExpr hT hν lam hf (fun t ht x => ?_) (fun t ht x => ?_)
  · rw [← hconv t ht x]; exact hid t ht x
  · have := lstConv_L_zero_ne_top hT hν lam 0 hg ht x (fun s hs y => (hid s hs.1 y).le)
      (lstConv_G_sq_ne_top_of_finite hg x (hfin t ht x))
    simpa using this

/-- **Uniqueness from the Itô identity** (`T2:ExUni(1)`, Step 5, deterministic core). Let
`w = E(u−v)²`, `f₁ = E u²`, `f₂ = E v²` (measurable at positive times), with
`w ≤ g ⋆ G²` and `g ≤ LIP² w` at positive times (`g = E(ρ(u)−ρ(v))²`, from the Itô isometry and
the Lipschitz bound), `w ≤ 2(f₁ + f₂)`, and `f₁`, `f₂` each satisfying the Itô identity with the
`finite` field (`g₁ = E ρ(u)²`, `g₂ = E ρ(v)²`). Then for Gaussian-tempered `μ`, `w = 0` at
positive times. -/
theorem eq_zero_of_renewal {μ : Measure ℝ} [SFinite μ]
    (hT : RoughHeatKernel.IsGaussianTempered μ) {ν : ℝ} (hν : 0 < ν) (LIP : ℝ)
    {w g f₁ f₂ g₁ g₂ : ℝ → ℝ → ℝ≥0∞} (hw : Measurable (cut w)) (hf₁ : Measurable (cut f₁))
    (hg₁ : Measurable (cut g₁)) (hg₂ : Measurable (cut g₂))
    (hle : ∀ t > 0, ∀ x, w t x ≤ lstConv g (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x)
    (hlip : ∀ s > 0, ∀ y, g s y ≤ ENNReal.ofReal (LIP ^ 2) * w s y)
    (hw2 : ∀ s > 0, ∀ y, w s y ≤ 2 * (f₁ s y + f₂ s y))
    (hid₁ : ∀ t > 0, ∀ x, f₁ t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv g₁ (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x)
    (hid₂ : ∀ t > 0, ∀ x, f₂ t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv g₂ (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x)
    (hfin₁ : ∀ t > 0, ∀ x, ∫⁻ z in Ioo 0 t ×ˢ univ,
      ENNReal.ofReal (G ν (t - z.1) (x - z.2) ^ 2) * g₁ z.1 z.2 < ∞)
    (hfin₂ : ∀ t > 0, ∀ x, ∫⁻ z in Ioo 0 t ×ˢ univ,
      ENNReal.ofReal (G ν (t - z.1) (x - z.2) ^ 2) * g₂ z.1 z.2 < ∞) :
    ∀ t > 0, ∀ x, w t x = 0 := by
  have hfi : ∀ {fi gi : ℝ → ℝ → ℝ≥0∞}, Measurable (cut gi) →
      (∀ t > 0, ∀ x, fi t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
        lstConv gi (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x) →
      (∀ t > 0, ∀ x, ∫⁻ z in Ioo 0 t ×ˢ univ,
        ENNReal.ofReal (G ν (t - z.1) (x - z.2) ^ 2) * gi z.1 z.2 < ∞) →
      ∀ t > 0, ∀ x, lstConv fi (fun s y => ENNReal.ofReal (L ν LIP 0 s y)) t x ≠ ⊤ := by
    intro fi gi hgi hidi hfini t ht x
    have := lstConv_L_zero_ne_top hT hν LIP 0 hgi ht x (fun s hs y => (hidi s hs.1 y).le)
      (lstConv_G_sq_ne_top_of_finite hgi x (hfini t ht x))
    simpa using this
  intro t ht x
  refine eq_zero_of_le_lstConv_L_zero hν LIP hw (T := t) (fun s hs y => ?_) (fun s hs y => ?_)
    t ⟨ht, le_rfl⟩ x
  · exact (hle s hs.1 y).trans
      (lstConv_G_sq_le_lstConv_L_zero LIP (fun r hr z => hlip r hr.1 z) y)
  · exact lstConv_ne_top_of_le_two_mul_add hf₁ (measurable_lL hν LIP 0) y
      (fun r hr z => hw2 r hr.1 z) (hfi hg₁ hid₁ hfin₁ s hs.1 y) (hfi hg₂ hid₂ hfin₂ s hs.1 y)

end MomentTheorems

end ChenDalang15

end
