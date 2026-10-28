# What is proved

This is a selected-result formalization of Chen and Dalang (2015), not the entire
paper. The selected Comparator entry contains exactly 16 statements. All proof
code remains in this repository; its 200 other declared support claims are not
advertised as separately compared statements. Source-bound receipts identify
the exact verified revision and audit scope.

## Notation and interpretation

The heat operator is ∂t − (ν/2)∂xx with ν > 0. The initial measure is nonnegative
and integrable against every decaying Gaussian; it may have infinite total mass.
The stochastic statements use the explicit augmented white-noise and abstract
Walsh-integral characterization copied into the Mathlib-only Challenge. They
construct the integral and full solutions rather than assume the moment or
continuity conclusions. The full solution definition includes the actual stochastic integral being
L2-continuous in the output variables. Almost-sure uniqueness is separately at
each positive-time space point, not a common exceptional-set assertion.

The exact Lean headers below state every parameter, hypothesis and conjunct.
Their symbols are defined in [CD2015Challenge.lean](../CD2015Challenge.lean); proofs are in
[CD2015Solution.lean](../CD2015Solution.lean) and the imported development.

## Proposition 2.2: iterated kernels

The iterated space-time convolution kernels have the explicit heat-kernel/Gamma closed form, at general positive diffusivity and positive time.

`ChenDalang2015.P2K_L_closed_form`

<details><summary>Exact Lean statement</summary>

```lean
theorem P2K_L_closed_form {ν lam : ℝ} (hν : 0 < ν) (n : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    L ν lam n t x =
      G (ν / 2) t x *
        ((lam ^ 2 / Real.sqrt (4 * Real.pi * ν) * Real.sqrt Real.pi) ^ (n + 1) /
          Real.Gamma (((n : ℝ) + 1) / 2)) *
        t ^ (((n : ℝ) - 1) / 2)
```

</details>

## Proposition 2.2: resolvent series

The iterated kernels sum to the stated resolvent; this is actual series convergence and identification, not a definition of the desired answer.

`ChenDalang2015.P2K_hasSum`

<details><summary>Exact Lean statement</summary>

```lean
theorem P2K_hasSum {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (fun n => L ν lam n t x)
      (G (ν / 2) t x * (lam ^ 2 / Real.sqrt (4 * Real.pi * ν * t) +
        lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * t / (4 * ν)) *
          Phi (lam ^ 2 * Real.sqrt (t / (2 * ν)))))
```

</details>

## Proposition 2.2: closed resolvent

The resolvent has the displayed closed formula in Gaussian and normal-distribution terms.

`ChenDalang2015.P2K_K_closed_form`

<details><summary>Exact Lean statement</summary>

```lean
theorem P2K_K_closed_form {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    K ν lam t x =
      G (ν / 2) t x * (lam ^ 2 / Real.sqrt (4 * Real.pi * ν * t) +
        lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * t / (4 * ν)) *
          Phi (lam ^ 2 * Real.sqrt (t / (2 * ν))))
```

</details>

## Proposition 2.2: resolvent identity

The resolvent satisfies its convolution identity with the base squared heat kernel.

`ChenDalang2015.P2K_resolvent`

<details><summary>Exact Lean statement</summary>

```lean
theorem P2K_resolvent {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    stConv (K ν lam) (L ν lam 0) t x = K ν lam t x - L ν lam 0 t x
```

</details>

## Proposition 2.2: summability

The stated powers of the scalar Picard coefficients are summable, including the separately proved zero-time scalar endpoint.

`ChenDalang2015.P2K_summable`

<details><summary>Exact Lean statement</summary>

```lean
theorem P2K_summable {ν lam t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) {m : ℕ} (hm : 0 < m) :
    Summable (fun n : ℕ =>
      (Real.pi ^ (((n : ℝ) + 1) / 2) * (lam ^ 2 / Real.sqrt (4 * Real.pi * ν)) ^ n *
          t ^ ((n : ℝ) / 2) / Real.Gamma (((n : ℝ) + 1) / 2)) ^ ((1 : ℝ) / m))
```

</details>

## Display 2.18: integrated resolvent

The convolution of the constant function with the resolvent has the stated time-dependent closed form.

`ChenDalang2015.E2H_closed_form`

<details><summary>Exact Lean statement</summary>

```lean
theorem E2H_closed_form {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    stConv (fun _ _ => (1 : ℝ)) (K ν lam) t x =
      2 * Real.exp (lam ^ 4 * t / (4 * ν)) * Phi (lam ^ 2 * Real.sqrt (t / (2 * ν))) - 1
```

</details>

## Appendix A.1: positive parameter

The integral/normal-distribution identity is proved for positive b, the regime needed by the resolvent argument.

`ChenDalang2015.LA_Phi_E`

<details><summary>Exact Lean statement</summary>

```lean
theorem LA_Phi_E {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    Real.pi * ∫ u in (0 : ℝ)..t,
        Real.exp (Real.pi * b ^ 2 * u) * Phi (Real.sqrt (2 * Real.pi * b ^ 2 * u)) =
      Real.exp (Real.pi * b ^ 2 * t) * Phi (Real.sqrt (2 * Real.pi * b ^ 2 * t)) / b ^ 2
        - 1 / (2 * b ^ 2) - Real.sqrt t / b
```

</details>

## Appendix A.1: printed negative extension

A separate finite positive-time statement refutes the printed negative-parameter extension at b = -1 and t = 1; it is not a proof of the false printed extension.

`ChenDalang2015.LA_Phi_E_false_at_neg_one`

<details><summary>Exact Lean statement</summary>

```lean
theorem LA_Phi_E_false_at_neg_one :
    ¬ (Real.pi * ∫ u in (0 : ℝ)..1,
          Real.exp (Real.pi * (-1 : ℝ) ^ 2 * u) * Phi (Real.sqrt (2 * Real.pi * (-1 : ℝ) ^ 2 * u)) =
        Real.exp (Real.pi * (-1 : ℝ) ^ 2 * 1) * Phi (Real.sqrt (2 * Real.pi * (-1 : ℝ) ^ 2 * 1)) /
            (-1 : ℝ) ^ 2
          - 1 / (2 * (-1 : ℝ) ^ 2) - Real.sqrt 1 / (-1 : ℝ))
```

</details>

## Theorem 2.4: full existence and uniqueness

For the stated nonnegative Gaussian-tempered initial measure, positive diffusivity and globally Lipschitz coefficient on the augmented white-noise setting, an actual integral exists; every such integral admits a full solution; any two full solutions agree a.s. at each fixed positive-time space point.

`ChenDalang2015.T2_ExUni_p2_headline`

<details><summary>Exact Lean statement</summary>

```lean
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
          ∀ t : ℝ, 0 < t → ∀ x : ℝ, u t x =ᵐ[P] v t x
```

</details>

## Theorem 2.12(1): zero offset

Full solution existence is supplied and the lower-growth bound holds for every full solution and every real p at least 2 under the stated lower coefficient and nonzero-data hypotheses.

`ChenDalang2015.T2_Growth_one_zero_headline`

<details><summary>Exact Lean statement</summary>

```lean
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
        ∀ p : ℝ, 2 ≤ p → ((lip ^ 2 / 2 : ℝ) : EReal) ≤ lowerGrowthIndex (momentFn P u p)
```

</details>

## Theorem 2.12(1): nonzero offset

Under the stated nonzero-offset lower bound, full solutions exist and both indices are infinite in the asserted real-p range; zero initial measure is allowed where the statement says so.

`ChenDalang2015.T2_Growth_one_top_headline`

<details><summary>Exact Lean statement</summary>

```lean
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
        lowerGrowthIndex (momentFn P u p) = ⊤ ∧ upperGrowthIndex (momentFn P u p) = ⊤
```

</details>

## Theorem 2.12(2): finite upper bound

At p = 2, nonnegative data satisfying the literal exponential-moment hypothesis give the stated piecewise upper-growth bound, with its strict threshold branch and coefficient assumptions.

`ChenDalang2015.T2_Growth_two_headline`

<details><summary>Exact Lean statement</summary>

```lean
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
            else Lip ^ 2 / 2 : ℝ) : EReal)
```

</details>

## Theorem 2.12(3): exact zero-offset case

At p = 2 the stated general coefficient-square identity and exponential data condition yield both exact indices; the coefficient need not be literally linear.

`ChenDalang2015.T2_Growth_three_zero_headline`

<details><summary>Exact Lean statement</summary>

```lean
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
          upperGrowthIndex (momentFn P u 2) = ((lam ^ 2 / 2 : ℝ) : EReal)
```

</details>

## Theorem 2.12(3): nonzero offset

The applicable nonzero-offset square-identity regime gives the stated infinite-index conclusion for every full solution.

`ChenDalang2015.T2_Growth_three_top_headline`

<details><summary>Exact Lean statement</summary>

```lean
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
        lowerGrowthIndex (momentFn P u p) = ⊤ ∧ upperGrowthIndex (momentFn P u p) = ⊤
```

</details>

## Proposition 2.14: exact transition

For literal exponential initial density, nonzero coefficient and positive decay parameter, full solutions exist and both p = 2 indices equal the stated transition formula, including its boundary.

`ChenDalang2015.P2_Ex_Exp_headline`

<details><summary>Exact Lean statement</summary>

```lean
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
            else lam ^ 2 / 2 : ℝ) : EReal)
```

</details>

## Theorem 2.4(5): exact second moment

For a globally Lipschitz coefficient satisfying the general square identity, an integral and full solutions exist, and every full solution satisfies the explicit quasilinear second-moment convolution formula at positive time. Coefficient and offset zero cases are retained.

`ChenDalang2015.T2_ExUni_secondMoment_headline`

<details><summary>Exact Lean statement</summary>

```lean
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
              θ ^ 2 * stConv (fun _ _ => (1 : ℝ)) (K ν lam) t x)
```

</details>

## Not covered

Signed-data existence, higher-p upper bounds, two-point stochastic formulas,
sample-path continuity and full-paper coverage are not claimed. The Dirac-PAM
noise/integral/solution fixture is a proved nonvacuity check, not a seventeenth
selected Comparator statement. The source corrections and precise version
relationship are disclosed in [PAPER_SOURCE.md](PAPER_SOURCE.md).

## Trust and review

The proof development permits only propext, Classical.choice and Quot.sound.
Deliberate sorrys appear only in the Challenge statement file; the Solution must
have none. Read the committed native and Comparator receipts for the exact
checked source, names, toolchain, dependencies and independent-kernel results.
Agent fidelity review is distinct from human review; no independent human Lean
review is claimed.

## Reference

Le Chen and Robert C. Dalang, Ann. Probab. 43(6) (2015), 3006–3051,
[doi:10.1214/14-AOP954](https://doi.org/10.1214/14-AOP954),
[arXiv:1307.0600v3](https://arxiv.org/abs/1307.0600v3).
