module

public import Mathlib

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Chen–Dalang (2015): explicit resolvent kernels for the stochastic heat equation

L. Chen and R. C. Dalang, *Moments and growth indices for the nonlinear stochastic heat
equation with rough initial conditions*, Ann. Probab. 43 (2015) 3006–3051,
doi:10.1214/14-AOP954.

For the parabolic Anderson model `∂ₜu = (ν/2)∂²ₓu + λ u Ẇ`, the second moment of the solution
is `E[u(t,x)²] = J₀²(t,x) + (J₀² ⋆ 𝓚)(t,x)`, where `𝓚 = Σₙ 𝓛ₙ` sums the iterated space-time
convolutions of `𝓛₀ = λ² G_ν²` (paper, Section 2). The statements below are the paper's
explicit evaluation of these kernels: Proposition `P2:K` (displays `E:KS-LB`, `E:K`,
`E:KS-Kn-K0` and the summability claim) and display `E2:H`, together with Lemma `LA:Phi-E`,
whose hypothesis `b ≠ 0` in the paper must be `b > 0` (it fails for `b < 0`).

Only Mathlib is imported. The definitions are documented below; `λ` is written `lam`.
Throughout, `b = λ²/√(4πν)` is the constant of `P2:K`.
-/

set_option autoImplicit false

@[expose] public section

namespace ChenDalang15

-- BEGIN SHARED DEFINITIONS (keep byte-identical with CD2015Challenge.lean)

/-- A named numeral instance keeps the shared statement layer independent of
module-local auxiliary-proof sharing when elaborating L² dictionaries. -/
instance (priority := 2000) instAtLeastTwoTwo : Nat.AtLeastTwo (1 + 1) :=
  ⟨by decide⟩

/-- The heat kernel `G_ν(t,x) = (2πνt)^{-1/2} exp(-x²/(2νt))`, the fundamental solution of
`∂_t − (ν/2)∂²_x` (paper, Section 2). For `νt ≤ 0` Lean's conventions give the value `0`,
matching the paper's convention `G_ν(t,·) ≡ 0` for `t ≤ 0` when `ν > 0`.
The heat-kernel interpretation requires `ν > 0`: if both `ν < 0` and `t < 0`,
the literal formula has `νt > 0` and need not vanish. -/
noncomputable def G (ν t x : ℝ) : ℝ :=
  1 / Real.sqrt (2 * Real.pi * ν * t) * Real.exp (-x ^ 2 / (2 * ν * t))

/-- The space-time convolution `(f ⋆ g)(t,x) = ∫₀ᵗ ∫_ℝ f(s,y) g(t-s, x-y) dy ds`. -/
noncomputable def stConv (f g : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, ∫ y, f s y * g (t - s) (x - y)

/-- The kernels `𝓛ₙ(t,x;ν,λ)` of the paper's display `E:Def-Ln`: `𝓛₀ = λ² G_ν²` and
`𝓛ₙ₊₁ = 𝓛ₙ ⋆ 𝓛₀` (the `(n+1)`-fold space-time convolution of `𝓛₀`, nested to the left). -/
noncomputable def L (ν lam : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0 => fun t x => lam ^ 2 * G ν t x ^ 2
  | n + 1 => stConv (L ν lam n) (L ν lam 0)

/-- The kernel `𝓚 = Σₙ 𝓛ₙ` of the paper's display `E:Def-K` (an unconditional `tsum`; its
convergence is part of the advertised theorem `P2K_hasSum`). -/
noncomputable def K (ν lam : ℝ) (t x : ℝ) : ℝ := ∑' n, L ν lam n t x

/-- The standard normal distribution function `Φ(x) = ∫_{-∞}^x (2π)^{-1/2} e^{-y²/2} dy`. -/
noncomputable def Phi (x : ℝ) : ℝ :=
  ∫ y in Set.Iic x, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2)

-- END SHARED DEFINITIONS

end ChenDalang15

-- BEGIN SHARED DEFINITIONS: GrowthDefs
open scoped ENNReal

namespace ChenDalang15

/-- `sup_{|x| ≥ αt} f(t,x)`. -/
noncomputable def tailSup (f : ℝ → ℝ → ℝ≥0∞) (α t : ℝ) : ℝ≥0∞ :=
  letI : SupSet ℝ≥0∞ :=
    @CompleteLattice.toSupSet ℝ≥0∞
      (@CompleteLinearOrder.toCompleteLattice ℝ≥0∞ ENNReal.instCompleteLinearOrder)
  ⨆ (x : ℝ) (_ : α * t ≤ |x|), f t x

/-- `limsup_{t→∞} t⁻¹ log sup_{|x| ≥ αt} f(t,x)`, valued in `EReal`. -/
noncomputable def tailRate (f : ℝ → ℝ → ℝ≥0∞) (α : ℝ) : EReal :=
  Filter.limsup (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * ENNReal.log (tailSup f α t)) Filter.atTop

/-- The lower exponential growth index `λ̲` of `f` (display `E1:GrowInd-0`). -/
noncomputable def lowerGrowthIndex (f : ℝ → ℝ → ℝ≥0∞) : EReal :=
  sSup ((fun α : ℝ => (α : EReal)) '' {α | 0 < α ∧ 0 < tailRate f α})

/-- The upper exponential growth index `λ̄` of `f` (display `E1:GrowInd-1`). -/
noncomputable def upperGrowthIndex (f : ℝ → ℝ → ℝ≥0∞) : EReal :=
  sInf ((fun α : ℝ => (α : EReal)) '' {α | 0 < α ∧ tailRate f α < 0})

/-- The `p`-th moment function `E|X(t,x)|^p` of a random field `X` under `P`. -/
noncomputable def momentFn {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (X : ℝ → ℝ → Ω → ℝ) (p : ℝ) : ℝ → ℝ → ℝ≥0∞ :=
  fun t x => ∫⁻ ω, ‖X t x ω‖ₑ ^ p ∂P

/-- The solution of the homogeneous heat equation with initial data `μ`:
`J₀(t,x) = (G_ν(t,·) * μ)(x) = ∫ G_ν(t, x − y) μ(dy)` (paper, Section 2). -/
noncomputable def J0 (ν : ℝ) (μ : MeasureTheory.Measure ℝ) (t x : ℝ) : ℝ :=
  ∫ y, G ν t (x - y) ∂μ

end ChenDalang15
-- END SHARED DEFINITIONS: GrowthDefs

-- BEGIN SHARED DEFINITIONS: StochDefs (keep byte-identical with CD2015Challenge.lean)

noncomputable section

namespace ChenDalang15.Stoch

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-- Lebesgue measure on time-space with time restricted to `(0, ∞)` (copy of
`WalshIntegral.WhiteNoise.timeSpaceVolume`). -/
def timeSpaceVolume : Measure (ℝ × ℝ) := (volume.restrict (Ioi (0 : ℝ))).prod volume

/-- The Hilbert space `L²((0,∞) × ℝ)` of deterministic integrands. -/
abbrev H := Lp ℝ 2 timeSpaceVolume

/-- Essential support in `(0,t] × ℝ`. -/
def SupportedBefore (t : ℝ≥0) (h : H) : Prop :=
  ∀ᵐ z ∂timeSpaceVolume, (t : ℝ) < z.1 → h z = 0

/-- Essential support in `(s,∞) × ℝ`. -/
def SupportedAfter (s : ℝ≥0) (h : H) : Prop :=
  ∀ᵐ z ∂timeSpaceVolume, z.1 ≤ (s : ℝ) → h z = 0

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The σ-field generated by the noise after time `s`. -/
@[instance_reducible]
def futureSigma (W : H →L[ℝ] Lp ℝ 2 P) (s : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ h : {h : H // SupportedAfter s h},
    MeasurableSpace.comap (fun ω => W h.val ω) inferInstance

/-- The raw natural σ-field of the noise up to time `t`: generated by `W h` for `h` essentially
supported in `(0,t] × ℝ` (paper: `σ(W_s(A), 0 ≤ s ≤ t, A ∈ 𝓑_b(ℝ))`). -/
@[instance_reducible]
def pastSigma (W : H →L[ℝ] Lp ℝ 2 P) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ h : {h : H // SupportedBefore t h},
    MeasurableSpace.comap (fun ω => W h.val ω) inferInstance

/-- `F` is the natural filtration of `W` augmented by the null sets: an ambient measurable event
lies in `F t` iff it agrees a.s. with an event of `pastSigma W t` (copy of
`WalshIntegral.WhiteNoise.IsCompletedNatural`). On a complete probability space this is
`σ(W_s(A), s ≤ t) ∨ 𝓝`, the paper's `𝓕ₜ`. -/
def IsCompletedNatural (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (W : H →L[ℝ] Lp ℝ 2 P) : Prop :=
  ∀ t S, MeasurableSet[F t] S ↔
    MeasurableSet S ∧ ∃ B, MeasurableSet[pastSigma W t] B ∧ S =ᵐ[P] B

/-- Space-time white noise relative to the filtration `F` (copy of
`WalshIntegral.WhiteNoise.IsWhiteNoise`): an isometric, centred Gaussian, `F`-adapted family
`W h`, `h ∈ L²((0,∞) × ℝ)`, whose future is independent of `F s`. -/
structure IsWhiteNoise (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 mΩ) (W : H →L[ℝ] Lp ℝ 2 P) : Prop where
  isometry : Isometry W
  gaussian : ∀ h : H, P.map (fun ω => W h ω) = gaussianReal 0 (‖h‖₊ ^ 2)
  adapted : ∀ (t : ℝ≥0) (h : H), SupportedBefore t h →
    ∃ X : Ω → ℝ, StronglyMeasurable[F t] X ∧ X =ᵐ[P] (fun ω => W h ω)
  future_independent : ∀ s : ℝ≥0, Indep (futureSigma W s) (F s) P

/-- The paper's probability setting (Section 2.2): a white noise `W` on a complete probability
space, with `F` its natural filtration augmented by the null sets (augmented natural filtration). -/
structure IsAugmentedWhiteNoise (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 mΩ) (W : H →L[ℝ] Lp ℝ 2 P) : Prop where
  complete : P.IsComplete
  whiteNoise : IsWhiteNoise P F W
  completedNatural : IsCompletedNatural P F W

/-- The predictable σ-field on `ℝ × ℝ × Ω` (copy of `WalshIntegral.Predictable.predictableSigma`),
generated by `(s,t] × A × B` with `B ∈ F s` and by `C × A × B` with `C ⊆ (−∞,0]`, `B ∈ F 0`. -/
@[instance_reducible]
def predictableSigma (F : Filtration ℝ≥0 mΩ) : MeasurableSpace (ℝ × ℝ × Ω) :=
  MeasurableSpace.generateFrom {S |
    (∃ (s t : ℝ≥0) (A : Set ℝ) (B : Set Ω),
      s < t ∧ MeasurableSet A ∧ MeasurableSet[F s] B ∧
        S = Ioc (s : ℝ) (t : ℝ) ×ˢ (A ×ˢ B)) ∨
    (∃ (C A : Set ℝ) (B : Set Ω),
      MeasurableSet C ∧ C ⊆ Iic 0 ∧ MeasurableSet A ∧ MeasurableSet[F 0] B ∧
        S = C ×ˢ (A ×ˢ B))}

/-- `ds dy dP` with `s > 0`. -/
def spaceTimeSample (P : Measure Ω) : Measure (ℝ × ℝ × Ω) :=
  (volume.restrict (Ioi (0 : ℝ))).prod (volume.prod P)

/-- Predictable classes in `L²(ds dy dP)`. -/
abbrev predL2Submodule (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    Submodule ℝ (Lp ℝ 2 (spaceTimeSample P)) :=
  lpMeas ℝ ℝ (predictableSigma F) 2 (spaceTimeSample P)

/-- The paper's `𝒫₂` (Section 3.1): predictable square-integrable integrands. -/
abbrev PredL2 (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) := ↥(predL2Submodule F P)

/-- `J` is the Walsh integral against `W`: a continuous linear map on `𝒫₂` that sends every
elementary integrand `c(ω) 1_{(s,t]}(r) 1_A(y)` (`c` bounded and `F s`-measurable, `A` of finite
measure) to `c · W(1_{(s,t] × A})`. -/
def IsWalshIntegral [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (W : H →L[ℝ] Lp ℝ 2 P) (J : PredL2 F P →L[ℝ] Lp ℝ 2 P) : Prop :=
  ∀ (s t : ℝ≥0) (A : Set ℝ) (c : Ω → ℝ), s < t → MeasurableSet A → volume A ≠ ∞ →
    Measurable[F s] c → (∃ C : ℝ, ∀ ω, |c ω| ≤ C) →
    ∀ (g : PredL2 F P) (r : H),
      (fun q => (g : Lp ℝ 2 (spaceTimeSample P)) q) =ᵐ[spaceTimeSample P]
        (fun q => c q.2.2 * (Ioc (s : ℝ) t ×ˢ A).indicator (fun _ => (1 : ℝ)) (q.1, q.2.1)) →
      (fun z => r z) =ᵐ[timeSpaceVolume] (Ioc (s : ℝ) t ×ˢ A).indicator (fun _ => (1 : ℝ)) →
      (fun ω => J g ω) =ᵐ[P] fun ω => c ω * W r ω

/-- `I` is the stochastic integral field of `u` (paper, display after `E2:WalshSI`): for every
`t > 0` and `x`, the integrand `(s,y,ω) ↦ G_ν(t−s, x−y) ρ(u(s,y,ω))` has a class `g` in `𝒫₂`
and `I(t,x) = J g`. -/
def IsIntegralField [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (J : PredL2 F P →L[ℝ] Lp ℝ 2 P) (ν : ℝ) (ρ : ℝ → ℝ) (u : ℝ → ℝ → Ω → ℝ)
    (I : ℝ → ℝ → Lp ℝ 2 P) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x : ℝ, ∃ g : PredL2 F P,
    (fun q => (g : Lp ℝ 2 (spaceTimeSample P)) q) =ᵐ[spaceTimeSample P]
      (fun q => G ν (t - q.1) (x - q.2.1) * ρ (u q.1 q.2.1 q.2.2)) ∧ I t x = J g

/-- Random field solution of `u = J₀ + ∬ G_ν(t−s,x−y) ρ(u(s,y)) W(ds,dy)` (paper, Definition
`D2:Solution`); see the module docstring for the clause-by-clause comparison. -/
structure IsRandomFieldSolution [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (J : PredL2 F P →L[ℝ] Lp ℝ 2 P) (ν : ℝ) (ρ : ℝ → ℝ) (μ : Measure ℝ)
    (u : ℝ → ℝ → Ω → ℝ) : Prop where
  /-- `D2:Solution(1)`. -/
  adapted : ∀ t : ℝ, 0 < t → ∀ x : ℝ, Measurable[F t.toNNReal] (u t x)
  /-- `D2:Solution(2)`. -/
  jointlyMeasurable : Measurable (fun q : Ioi (0 : ℝ) × ℝ × Ω => u q.1 q.2.1 q.2.2)
  /-- `D2:Solution(3)`, first half. -/
  finite : ∀ t : ℝ, 0 < t → ∀ x : ℝ,
    ∫⁻ z in Ioo 0 t ×ˢ univ, ENNReal.ofReal (G ν (t - z.1) (x - z.2) ^ 2) *
      momentFn P (fun s y ω => ρ (u s y ω)) 2 z.1 z.2 < ∞
  /-- `D2:Solution(3)`, second half, and `D2:Solution(4)`. -/
  integral : ∃ I : ℝ → ℝ → Lp ℝ 2 P, IsIntegralField J ν ρ u I ∧
    ContinuousOn (fun z : ℝ × ℝ => I z.1 z.2) (Ioi 0 ×ˢ univ) ∧
    ∀ t : ℝ, 0 < t → ∀ x : ℝ, u t x =ᵐ[P] fun ω => J0 ν μ t x + I t x ω

end ChenDalang15.Stoch

end

-- END SHARED DEFINITIONS: StochDefs

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
  sorry

/-- **`P2:K`, display `E:K`, with convergence.** For `ν > 0` and `t > 0` the series
`Σₙ 𝓛ₙ(t,x)` converges, with sum
`G_{ν/2}(t,x) (λ²/√(4πνt) + λ⁴/(2ν) · e^{λ⁴t/(4ν)} · Φ(λ² √(t/(2ν))))`. -/
theorem P2K_hasSum {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (fun n => L ν lam n t x)
      (G (ν / 2) t x * (lam ^ 2 / Real.sqrt (4 * Real.pi * ν * t) +
        lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * t / (4 * ν)) *
          Phi (lam ^ 2 * Real.sqrt (t / (2 * ν))))) := by
  sorry

/-- **`P2:K`, display `E:K`.** For `ν > 0` and `t > 0`,
`𝓚(t,x) = G_{ν/2}(t,x) (λ²/√(4πνt) + λ⁴/(2ν) · e^{λ⁴t/(4ν)} · Φ(λ² √(t/(2ν))))`. -/
theorem P2K_K_closed_form {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    K ν lam t x =
      G (ν / 2) t x * (lam ^ 2 / Real.sqrt (4 * Real.pi * ν * t) +
        lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * t / (4 * ν)) *
          Phi (lam ^ 2 * Real.sqrt (t / (2 * ν)))) := by
  sorry

/-- **`P2:K`, display `E:KS-Kn-K0`.** For `ν > 0` and `t > 0`,
`(𝓚 ⋆ 𝓛₀)(t,x) = 𝓚(t,x) − 𝓛₀(t,x)`. -/
theorem P2K_resolvent {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    stConv (K ν lam) (L ν lam 0) t x = K ν lam t x - L ν lam 0 t x := by
  sorry

/-- **`P2:K`, summability claim.** With `Bₙ(t) = π^{(n+1)/2} bⁿ t^{n/2} / Γ((n+1)/2)` and
`b = λ²/√(4πν)`, for `ν > 0`, `t ≥ 0` and every integer `m ≥ 1`, `Σₙ Bₙ(t)^{1/m} < ∞`. -/
theorem P2K_summable {ν lam t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) {m : ℕ} (hm : 0 < m) :
    Summable (fun n : ℕ =>
      (Real.pi ^ (((n : ℝ) + 1) / 2) * (lam ^ 2 / Real.sqrt (4 * Real.pi * ν)) ^ n *
          t ^ ((n : ℝ) / 2) / Real.Gamma (((n : ℝ) + 1) / 2)) ^ ((1 : ℝ) / m)) := by
  sorry

/-- **Display `E2:H`.** For `ν > 0`, `t ≥ 0` and every `x`,
`𝓗(t) := (1 ⋆ 𝓚)(t,x) = 2 e^{λ⁴t/(4ν)} Φ(λ² √(t/(2ν))) − 1`. -/
theorem E2H_closed_form {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    stConv (fun _ _ => (1 : ℝ)) (K ν lam) t x =
      2 * Real.exp (lam ^ 4 * t / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (t / (2 * ν))) - 1 := by
  sorry

/-- **Lemma `LA:Phi-E`, for `b > 0`.** The paper states it for `b ≠ 0`; see the next theorem. -/
theorem LA_Phi_E {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    Real.pi * ∫ u in (0 : ℝ)..t,
        Real.exp (Real.pi * b ^ 2 * u) * Phi (Real.sqrt (2 * Real.pi * b ^ 2 * u)) =
      Real.exp (Real.pi * b ^ 2 * t) * Phi (Real.sqrt (2 * Real.pi * b ^ 2 * t)) / b ^ 2
        - 1 / (2 * b ^ 2) - Real.sqrt t / b := by
  sorry

/-- **`LA:Phi-E` is false for `b < 0`:** the paper's identity fails at `b = −1`, `t = 1`
(its last term should be `−√t/|b|`). This does not affect the paper, which uses `b > 0`. -/
theorem LA_Phi_E_false_at_neg_one :
    ¬ (Real.pi * ∫ u in (0 : ℝ)..1,
          Real.exp (Real.pi * (-1 : ℝ) ^ 2 * u) * Phi (Real.sqrt (2 * Real.pi * (-1 : ℝ) ^ 2 * u)) =
        Real.exp (Real.pi * (-1 : ℝ) ^ 2 * 1) * Phi (Real.sqrt (2 * Real.pi * (-1 : ℝ) ^ 2 * 1)) /
            (-1 : ℝ) ^ 2
          - 1 / (2 * (-1 : ℝ) ^ 2) - Real.sqrt 1 / (-1 : ℝ)) := by
  sorry


-- Data-only stochastic and growth headlines.
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end ChenDalang2015

end
