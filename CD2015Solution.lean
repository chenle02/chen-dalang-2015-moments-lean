module

public import ChenDalang15.S5Headlines
public import ChenDalang15.S5MomentHeadline

public import ChenDalang15.Summability
public import ChenDalang15.KClosed
public import ChenDalang15.KConv
public import ChenDalang15.H
public import ChenDalang15.PhiE

/-!
# Solution: proofs of the statements in `CD2015Challenge.lean`

Each theorem is proved by the corresponding result of the development (`ChenDalang15.*`).
The definitions `G`, `stConv`, `L`, `K`, `Phi` come from `ChenDalang15.Defs`, whose marked block
is byte-identical to the one in `CD2015Challenge.lean`; Comparator checks the constants agree.
-/

set_option autoImplicit false

public section

namespace ChenDalang2015

open ChenDalang15

/-- **`P2:K`, display `E:KS-LB`.** For `ν > 0` and `t > 0`,
`𝓛ₙ(t,x) = G_{ν/2}(t,x) · (b√π)^{n+1} / Γ((n+1)/2) · t^{(n-1)/2}` with `b = λ²/√(4πν)`. -/
theorem P2K_L_closed_form {ν lam : ℝ} (hν : 0 < ν) (n : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    L ν lam n t x =
      G (ν / 2) t x *
        ((lam ^ 2 / Real.sqrt (4 * Real.pi * ν) * Real.sqrt Real.pi) ^ (n + 1) /
          Real.Gamma (((n : ℝ) + 1) / 2)) *
        t ^ (((n : ℝ) - 1) / 2) := by
  exact L_eq hν n ht x

/-- **`P2:K`, display `E:K`, with convergence.** For `ν > 0` and `t > 0` the series
`Σₙ 𝓛ₙ(t,x)` converges, with sum
`G_{ν/2}(t,x) (λ²/√(4πνt) + λ⁴/(2ν) · e^{λ⁴t/(4ν)} · Φ(λ² √(t/(2ν))))`. -/
theorem P2K_hasSum {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (fun n => L ν lam n t x)
      (G (ν / 2) t x * (lam ^ 2 / Real.sqrt (4 * Real.pi * ν * t) +
        lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * t / (4 * ν)) *
          Phi (lam ^ 2 * Real.sqrt (t / (2 * ν))))) := by
  exact hasSum_L hν ht x

/-- **`P2:K`, display `E:K`.** For `ν > 0` and `t > 0`,
`𝓚(t,x) = G_{ν/2}(t,x) (λ²/√(4πνt) + λ⁴/(2ν) · e^{λ⁴t/(4ν)} · Φ(λ² √(t/(2ν))))`. -/
theorem P2K_K_closed_form {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    K ν lam t x =
      G (ν / 2) t x * (lam ^ 2 / Real.sqrt (4 * Real.pi * ν * t) +
        lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * t / (4 * ν)) *
          Phi (lam ^ 2 * Real.sqrt (t / (2 * ν)))) := by
  exact K_eq hν ht x

/-- **`P2:K`, display `E:KS-Kn-K0`.** For `ν > 0` and `t > 0`,
`(𝓚 ⋆ 𝓛₀)(t,x) = 𝓚(t,x) − 𝓛₀(t,x)`. -/
theorem P2K_resolvent {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    stConv (K ν lam) (L ν lam 0) t x = K ν lam t x - L ν lam 0 t x := by
  exact K_conv_L_zero hν ht x

/-- **`P2:K`, summability claim.** With `Bₙ(t) = π^{(n+1)/2} bⁿ t^{n/2} / Γ((n+1)/2)` and
`b = λ²/√(4πν)`, for `ν > 0`, `t ≥ 0` and every integer `m ≥ 1`, `Σₙ Bₙ(t)^{1/m} < ∞`. -/
theorem P2K_summable {ν lam t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) {m : ℕ} (hm : 0 < m) :
    Summable (fun n : ℕ =>
      (Real.pi ^ (((n : ℝ) + 1) / 2) * (lam ^ 2 / Real.sqrt (4 * Real.pi * ν)) ^ n *
          t ^ ((n : ℝ) / 2) / Real.Gamma (((n : ℝ) + 1) / 2)) ^ ((1 : ℝ) / m)) := by
  exact summable_BCoeff_rpow (b := bConst ν lam) (by unfold bConst; positivity) ht hm

/-- **Display `E2:H`.** For `ν > 0`, `t ≥ 0` and every `x`,
`𝓗(t) := (1 ⋆ 𝓚)(t,x) = 2 e^{λ⁴t/(4ν)} Φ(λ² √(t/(2ν))) − 1`. -/
theorem E2H_closed_form {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    stConv (fun _ _ => (1 : ℝ)) (K ν lam) t x =
      2 * Real.exp (lam ^ 4 * t / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (t / (2 * ν))) - 1 := by
  exact one_conv_K hν ht x

/-- **Lemma `LA:Phi-E`, for `b > 0`.** The paper states it for `b ≠ 0`; see the next theorem. -/
theorem LA_Phi_E {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    Real.pi * ∫ u in (0 : ℝ)..t,
        Real.exp (Real.pi * b ^ 2 * u) * Phi (Real.sqrt (2 * Real.pi * b ^ 2 * u)) =
      Real.exp (Real.pi * b ^ 2 * t) * Phi (Real.sqrt (2 * Real.pi * b ^ 2 * t)) / b ^ 2
        - 1 / (2 * b ^ 2) - Real.sqrt t / b := by
  exact integral_exp_mul_Phi hb ht

/-- **`LA:Phi-E` is false for `b < 0`:** the paper's identity fails at `b = −1`, `t = 1`
(its last term should be `−√t/|b|`). This does not affect the paper, which uses `b > 0`. -/
theorem LA_Phi_E_false_at_neg_one :
    ¬ (Real.pi * ∫ u in (0 : ℝ)..1,
          Real.exp (Real.pi * (-1 : ℝ) ^ 2 * u) * Phi (Real.sqrt (2 * Real.pi * (-1 : ℝ) ^ 2 * u)) =
        Real.exp (Real.pi * (-1 : ℝ) ^ 2 * 1) * Phi (Real.sqrt (2 * Real.pi * (-1 : ℝ) ^ 2 * 1)) /
            (-1 : ℝ) ^ 2
          - 1 / (2 * (-1 : ℝ) ^ 2) - Real.sqrt 1 / (-1 : ℝ)) := by
  exact integral_exp_mul_Phi_false_of_neg


open MeasureTheory ProbabilityTheory Set ChenDalang15.Stoch
open scoped ENNReal NNReal Topology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem T2_ExUni_p2_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ}
    (hμ : ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) μ)
    {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        ∀ v : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ v →
          ∀ t : ℝ, 0 < t → ∀ x : ℝ, u t x =ᵐ[P] v t x := by
  exact ChenDalang15.S5Headlines.T2_ExUni_p2_headline hW hν hμ hLip

theorem T2_Growth_one_zero_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ}
    (hμ : ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) μ) (hμ0 : μ ≠ 0)
    {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) {lip : ℝ} (hlip : lip ≠ 0)
    (hρ : ∀ z : ℝ, lip ^ 2 * z ^ 2 ≤ ρ z ^ 2) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        ∀ p : ℝ, 2 ≤ p → ((lip ^ 2 / 2 : ℝ) : EReal) ≤ lowerGrowthIndex (momentFn P u p) := by
  exact ChenDalang15.S5Headlines.T2_Growth_one_zero_headline hW hν hμ hμ0 hLip hlip hρ

theorem T2_Growth_one_top_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ}
    (hμ : ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) μ)
    {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) {lip θ : ℝ} (hlip : lip ≠ 0) (hθ : θ ≠ 0)
    (hρ : ∀ z : ℝ, lip ^ 2 * (θ ^ 2 + z ^ 2) ≤ ρ z ^ 2) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        ∀ p : ℝ, 2 ≤ p →
        lowerGrowthIndex (momentFn P u p) = ⊤ ∧ upperGrowthIndex (momentFn P u p) = ⊤ := by
  exact ChenDalang15.S5Headlines.T2_Growth_one_top_headline hW hν hμ hLip hlip hθ hρ

theorem T2_Growth_two_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) {β Lip : ℝ} (hβ : 0 < β)
    (hI : Integrable (fun y : ℝ => Real.exp (β * |y|)) μ)
    (hLip0 : Lip ≠ 0) (hρ : ∀ z : ℝ, ρ z ^ 2 ≤ Lip ^ 2 * z ^ 2) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        upperGrowthIndex (momentFn P u 2) ≤
          ((if β < Lip ^ 2 / (2 * ν) then β * ν / 2 + Lip ^ 4 / (8 * ν * β)
            else Lip ^ 2 / 2 : ℝ) : EReal) := by
  exact ChenDalang15.S5Headlines.T2_Growth_two_headline hW hν hLip hβ hI hLip0 hρ

theorem T2_Growth_three_zero_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) {lam β : ℝ} (hlam : lam ≠ 0) (hμ0 : μ ≠ 0)
    (hβ : lam ^ 2 / (2 * ν) ≤ β)
    (hI : Integrable (fun y : ℝ => Real.exp (β * |y|)) μ)
    (hρ : ∀ z : ℝ, ρ z ^ 2 = lam ^ 2 * z ^ 2) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        lowerGrowthIndex (momentFn P u 2) = ((lam ^ 2 / 2 : ℝ) : EReal) ∧
          upperGrowthIndex (momentFn P u 2) = ((lam ^ 2 / 2 : ℝ) : EReal) := by
  exact ChenDalang15.S5Headlines.T2_Growth_three_zero_headline hW hν hLip hlam hμ0 hβ hI hρ

theorem T2_Growth_three_top_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ}
    (hμ : ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) μ)
    {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) {lam θ : ℝ} (hlam : lam ≠ 0) (hθ : θ ≠ 0)
    (hρ : ∀ z : ℝ, ρ z ^ 2 = lam ^ 2 * (θ ^ 2 + z ^ 2)) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        ∀ p : ℝ, 2 ≤ p →
        lowerGrowthIndex (momentFn P u p) = ⊤ ∧ upperGrowthIndex (momentFn P u p) = ⊤ := by
  exact ChenDalang15.S5Headlines.T2_Growth_three_top_headline hW hν hμ hLip hlam hθ hρ

theorem P2_Ex_Exp_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {lam β : ℝ} (hlam : lam ≠ 0) (hβ : 0 < β) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν (fun z : ℝ => lam * z)
          (volume.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (-β * |y|)))) u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν (fun z : ℝ => lam * z)
          (volume.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (-β * |y|)))) u →
        lowerGrowthIndex (momentFn P u 2) =
          ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β)
            else lam ^ 2 / 2 : ℝ) : EReal) ∧
        upperGrowthIndex (momentFn P u 2) =
          ((if β ≤ lam ^ 2 / (2 * ν) then β * ν / 2 + lam ^ 4 / (8 * ν * β)
            else lam ^ 2 / 2 : ℝ) : EReal) := by
  exact ChenDalang15.S5Headlines.P2_Ex_Exp_headline hW hν hlam hβ

theorem T2_ExUni_secondMoment_headline [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsAugmentedWhiteNoise P F W) {ν : ℝ} (hν : 0 < ν)
    {μ : Measure ℝ}
    (hμ : ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) μ)
    {ρ : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L ρ) {lam θ : ℝ}
    (hρ : ∀ z : ℝ, ρ z ^ 2 = lam ^ 2 * (θ ^ 2 + z ^ 2)) :
    (∃ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J) ∧
    ∀ J : PredL2 F P →L[ℝ] Lp ℝ 2 P, IsWalshIntegral W J →
      (∃ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u) ∧
      ∀ u : ℝ → ℝ → Ω → ℝ, IsRandomFieldSolution J ν ρ μ u →
        ∀ t : ℝ, 0 < t → ∀ x : ℝ,
          momentFn P u 2 t x = ENNReal.ofReal
            (J0 ν μ t x ^ 2 +
              stConv (fun s y => J0 ν μ s y ^ 2) (K ν lam) t x +
              θ ^ 2 * stConv (fun _ _ => (1 : ℝ)) (K ν lam) t x) := by
  exact ChenDalang15.S5MomentHeadline.T2_ExUni_secondMoment_headline hW hν hμ hLip hρ

end ChenDalang2015

end
