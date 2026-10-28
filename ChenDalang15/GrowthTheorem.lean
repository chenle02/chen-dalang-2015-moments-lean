module

public import ChenDalang15.GrowthIndex
public import ChenDalang15.GrowthUpper
public import ChenDalang15.GrowthLower

/-!
# Theorem `T2:Growth` for `p = 2`, conditional on the moment inequalities

Chen–Dalang (2015), Theorem `T2:Growth` (printed Theorem 2.12), parts (1) and (2) for the
second moment. The moment inputs of Theorem `T2:ExUni` are named hypotheses on a function
`g(t,x)` standing for `E|u(t,x)|²`:

* lower bounds (`E2:SecMom-Lower`): `(J₀² ⋆ 𝓚_l)(t,x) ≤ g(t,x)` (case `ϑ = 0`), and
  `ϑ²𝓗(t) ≤ g(t,x)` (case `ϑ ≠ 0`), with `𝓚_l = 𝓚(·,·;ν,l)`, `l = lip_ρ`;
* upper bound (`E2:SecMom-Up` with `Vip = 0`): `g(t,x) ≤ J₀²(t,x) + (J₀² ⋆ 𝓚_Λ)(t,x)`,
  `Λ = Lip_ρ`.

These hypotheses are proved for the actual solution only once `T2:ExUni` is (Waves 5–6); the
deductions below are the deterministic part of the paper's proof.
-/

set_option autoImplicit false

public section

open scoped ENNReal Topology
open Filter MeasureTheory

namespace ChenDalang15

/-- **`T2:Growth(1)`, `ϑ = 0`, `p = 2`.** For a nonzero measure `μ ∈ 𝓜_{H,+}(ℝ)` and `l ≠ 0`,
if `(J₀² ⋆ 𝓚_l)(t,x) ≤ g(t,x)` for all `t > 0`, then `λ̲(g) ≥ l²/2`. -/
theorem T2_Growth_lower {μ : Measure ℝ} (hμ0 : μ ≠ 0)
    (hμ : ∀ a > 0, Integrable (fun y => Real.exp (-a * y ^ 2)) μ)
    {ν l : ℝ} (hν : 0 < ν) (hl : l ≠ 0) {g : ℝ → ℝ → ℝ≥0∞}
    (hg : ∀ t > 0, ∀ x,
      ENNReal.ofReal (stConv (fun s y => J0 ν μ s y ^ 2) (K ν l) t x) ≤ g t x) :
    ((l ^ 2 / 2 : ℝ) : EReal) ≤ lowerGrowthIndex g := by
  set γ := l ^ 4 / (4 * ν) with hγdef
  have hγ : 0 < γ := by positivity
  -- for every `ξ ∈ (0, ν)`: `√(γξ) ≤ λ̲`
  have hξ : ∀ ξ, 0 < ξ → ξ < ν → ((Real.sqrt (γ * ξ) : ℝ) : EReal) ≤ lowerGrowthIndex g := by
    intro ξ hξ0 hξν
    obtain ⟨c, hc, T₀, hT₀, h⟩ := lower_envelope_gaussian hμ0 hμ hν hl
      (f := fun t x => stConv (fun s y => J0 ν μ s y ^ 2) (K ν l) t x) (fun t _ x => le_rfl)
      hξ0 hξν
    have key := le_lowerGrowthIndex_of_gaussian_envelope (f := g) (γ := γ) (ξ := ξ / 2) hγ
      (by positivity) hc ⟨T₀, hT₀, fun t ht x => by
        have ht0 : 0 < t := lt_of_lt_of_le hT₀ ht
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hg t ht0 x)
        have := h t ht x
        rwa [hγdef, show l ^ 4 / (4 * ν) * t = l ^ 4 * t / (4 * ν) by ring]⟩
    rwa [show 2 * γ * (ξ / 2) = γ * ξ by ring] at key
  -- let `ξ ↑ ν`
  have hlim : Tendsto (fun ξ : ℝ => ((Real.sqrt (γ * ξ) : ℝ) : EReal)) (𝓝[<] ν)
      (𝓝 ((Real.sqrt (γ * ν) : ℝ) : EReal)) := by
    have hc : Continuous fun ξ : ℝ => Real.sqrt (γ * ξ) := by fun_prop
    exact (continuous_coe_real_ereal.comp hc).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ ξ in 𝓝[<] ν, ((Real.sqrt (γ * ξ) : ℝ) : EReal) ≤ lowerGrowthIndex g := by
    filter_upwards [Ioo_mem_nhdsLT hν] with ξ hξm using hξ ξ hξm.1 hξm.2
  have hle := le_of_tendsto hlim hev
  have hval : Real.sqrt (γ * ν) = l ^ 2 / 2 := by
    rw [hγdef, show l ^ 4 / (4 * ν) * ν = (l ^ 2 / 2) ^ 2 by field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  rwa [hval] at hle

/-- **`T2:Growth(1)`, `ϑ ≠ 0`, `p = 2`.** If `ϑ²𝓗(t) ≤ g(t,x)` for all `t > 0`, with
`l ≠ 0` and `ϑ ≠ 0`, then `λ̲(g) = λ̄(g) = +∞`. -/
theorem T2_Growth_lower_top {ν l v : ℝ} (hν : 0 < ν) (hl : l ≠ 0) (hv : v ≠ 0)
    {g : ℝ → ℝ → ℝ≥0∞}
    (hg : ∀ t > 0, ∀ x,
      ENNReal.ofReal (v ^ 2 * stConv (fun _ _ => (1 : ℝ)) (K ν l) t x) ≤ g t x) :
    lowerGrowthIndex g = ⊤ ∧ upperGrowthIndex g = ⊤ := by
  obtain ⟨c, hc, T₀, h⟩ := lower_envelope_uniform hν hl hv
    (f := fun t x => v ^ 2 * stConv (fun _ _ => (1 : ℝ)) (K ν l) t x) (fun t _ x => le_rfl)
  refine growthIndices_eq_top_of_uniform_growth (c := c) (γ := l ^ 4 / (4 * ν)) hc
    (by positivity) ⟨max T₀ 1, fun t ht x => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hg t ht0 x)
  have := h t (le_trans (le_max_left _ _) ht) x
  rwa [show l ^ 4 / (4 * ν) * t = l ^ 4 * t / (4 * ν) by ring]

/-- **`T2:Growth(2)`, `p = 2`.** For a measure `μ` with `∫ e^{β|y|} μ(dy) < ∞` (`β > 0`),
`Λ ≠ 0`, and `g(t,x) ≤ J₀²(t,x) + (J₀² ⋆ 𝓚_Λ)(t,x)` for all `t > 0`:
`λ̄(g) ≤ βν/2 + Λ⁴/(8νβ)` if `β < Λ²/(2ν)`, and `λ̄(g) ≤ Λ²/2` otherwise. -/
theorem T2_Growth_upper {μ : Measure ℝ} {ν β lam : ℝ} (hν : 0 < ν) (hβ : 0 < β)
    (hlam : lam ≠ 0) (hI : Integrable (fun y => Real.exp (β * |y|)) μ)
    {g : ℝ → ℝ → ℝ≥0∞}
    (hg : ∀ t > 0, ∀ x, g t x ≤ ENNReal.ofReal
      (J0 ν μ t x ^ 2 + stConv (fun s y => J0 ν μ s y ^ 2) (K ν lam) t x)) :
    upperGrowthIndex g ≤
      ((if β < lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β) else lam ^ 2 / 2 : ℝ) :
        EReal) := by
  have hΛ : 0 < |lam| := abs_pos.2 hlam
  have h2 : |lam| ^ 2 = lam ^ 2 := sq_abs lam
  have h4 : |lam| ^ 4 = lam ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, ← pow_mul]
  have key := upperGrowthIndex_le_piecewise (f := g) (Λ := |lam|) hν hΛ hβ ?_
  · rwa [h2, h4] at key
  intro β' hβ' hβ'β
  have hI' : Integrable (fun y => Real.exp (β' * |y|)) μ := by
    refine hI.mono' (by fun_prop) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hβ'β (abs_nonneg y))
  obtain ⟨A, T₀, h⟩ := upper_envelope_exp hν hβ' zero_le_one hlam hI' rfl
    (f := fun t x => J0 ν μ t x ^ 2 + stConv (fun s y => J0 ν μ s y ^ 2) (K ν lam) t x)
    (fun t _ x => by simp)
  refine ⟨A, max T₀ 1, fun t ht x => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  refine le_trans (hg t ht0 x) (ENNReal.ofReal_le_ofReal ?_)
  rw [h4]
  exact h t (le_trans (le_max_left _ _) ht) x

end ChenDalang15

end
