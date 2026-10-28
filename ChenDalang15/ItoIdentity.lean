module

public import ChenDalang15.StochBridge
public import ChenDalang15.LConv

/-!
# The completed Itô identity and the renewal identity (Wave S2, part c)

For a white noise `W` with its augmented filtration, the Walsh integral `J` (any `J` with
`IsWalshIntegral W J`, which is `walshL2` by `isWalshIntegral_eq_walshL2`), `ν > 0`, and a
stochastic integral field `I` of `u` (`IsIntegralField J ν ρ u I`):

* `lintegral_sq_integralField`: `E|I(t,x)|² = ∫₀ᵗ ∫_ℝ G_ν(t−s,x−y)² E|ρ(u(s,y))|² dy ds` as
  lower integrals, for `t > 0`; `lintegral_sq_integralField_eq_lstConv` is the same identity as
  `lstConv (E|ρ(u)|²) (G_ν²)`.
  Route: `I(t,x) = J g` with `g =ᵐ G_ν(t−·,x−∘) ρ(u)` in `𝒫₂`; the Itô isometry
  `‖J g‖₂ = ‖g‖₂` (`WalshIntegral.Integral.walshL2` is a linear isometry); Tonelli on
  `spaceTimeSample P = ds|_{s>0} ⊗ (dy ⊗ dP)` for the a.e.-measurable integrand (no measurability
  of `ρ` or `u` is assumed); finally `G_ν(t−s,·) = 0` for `s ≥ t` cuts `s > 0` down to `0 < s < t`.
* `integral_mul_integralField`: the polarized identity `E[I(t,x) I(τ,y)]` (Bochner integrals),
  from preservation of inner products.
* `momentFn_two_eq_renewal`: `E|u(t,x)|² = J₀(t,x)² + (E|ρ(u)|² ⋆ G_ν²)(t,x)` for every random
  field solution, unconditionally. The cross term vanishes by mean zero of the Walsh integral
  (WalshIntegral v0.8.0, `integral_walshL2`), through `walshMeanZero_of_isWalshIntegral`; the
  general form `momentFn_two_eq_renewal_of_meanZero` assumes `WalshMeanZero J` for any `J`.
* `lintegral_sq_integralField_rho_zero`: sanity check, `ρ = 0` gives `E|I|² = 0`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.ItoIdentity

open MeasureTheory ProbabilityTheory Set ChenDalang15.Stoch
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- `‖f‖₂² = ∫⁻ ‖f‖ₑ²` for an element of `L²`. -/
theorem lintegral_enorm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℝ 2 μ) :
    ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ = ‖f‖ₑ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (Lp.aestronglyMeasurable f) (μ := μ)
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [Lp.enorm_def, h]

/-- `‖a b‖ₑ² = a² ‖b‖ₑ²` with the real factor squared inside `ofReal`. -/
theorem enorm_mul_sq (a b : ℝ) :
    ‖a * b‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) * ‖b‖ₑ ^ 2 := by
  rw [enorm_mul, mul_pow, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- Tonelli on `spaceTimeSample P` for an a.e.-measurable integrand: the iterated form
`∫⁻_{s>0} ∫⁻_y ∫⁻_ω`. -/
theorem lintegral_spaceTimeSample {Φ : ℝ × ℝ × Ω → ℝ≥0∞}
    (hΦ : AEMeasurable Φ (spaceTimeSample P)) [SFinite P] :
    ∫⁻ q, Φ q ∂spaceTimeSample P =
      ∫⁻ s in Ioi 0, ∫⁻ y, ∫⁻ ω, Φ (s, y, ω) ∂P := by
  have hm := hΦ.measurable_mk
  have hae : Φ =ᵐ[(volume.restrict (Ioi (0 : ℝ))).prod (volume.prod P)] hΦ.mk Φ :=
    hΦ.ae_eq_mk
  change ∫⁻ q, Φ q ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.prod P)) = _
  rw [lintegral_congr_ae hae, lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod hae] with s hs
  rw [lintegral_prod (fun z => hΦ.mk Φ (s, z)) (hm.comp measurable_prodMk_left).aemeasurable]
  refine (lintegral_congr_ae ?_)
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with y hy
  exact lintegral_congr_ae (hy.mono fun ω h => h.symm)

/-- `E|a + X|² = a² + E|X|²` for a centred `X ∈ L²(P)`. -/
theorem lintegral_sq_const_add [IsProbabilityMeasure P] (a : ℝ) (X : Lp ℝ 2 P)
    (h0 : ∫ ω, X ω ∂P = 0) :
    ∫⁻ ω, ‖a + X ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (a ^ 2) + ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂P := by
  have hX2 : Integrable (fun ω => X ω ^ 2) P := (Lp.memLp X).integrable_sq
  have hX : Integrable (fun ω => X ω) P := (Lp.memLp X).integrable (by norm_num)
  have hsq : ∀ b : ℝ, ‖b‖ₑ ^ 2 = ENNReal.ofReal (b ^ 2) := fun b => by
    simpa using ItoIdentity.enorm_mul_sq b 1
  have hf2 : Integrable (fun ω => (a + X ω) ^ 2) P := by
    have : (fun ω => (a + X ω) ^ 2) = fun ω => (a ^ 2 + 2 * a * X ω) + X ω ^ 2 := by
      funext ω; ring
    rw [this]
    exact ((integrable_const _).add (hX.const_mul _)).add hX2
  simp_rw [hsq]
  rw [← ofReal_integral_eq_lintegral_ofReal hf2 (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hX2 (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ← ENNReal.ofReal_add (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)]
  congr 1
  have : (fun ω => (a + X ω) ^ 2) = fun ω => (a ^ 2 + 2 * a * X ω) + X ω ^ 2 := by
    funext ω; ring
  rw [this, integral_add (f := fun ω => a ^ 2 + 2 * a * X ω) (g := fun ω => X ω ^ 2)
      ((integrable_const _).add (hX.const_mul _)) hX2,
    integral_add (f := fun _ => a ^ 2) (g := fun ω => 2 * a * X ω) (integrable_const _)
      (hX.const_mul _), integral_const_mul, h0]
  simp

end ChenDalang15.ItoIdentity

namespace ChenDalang15.Stoch

open MeasureTheory ProbabilityTheory Set ChenDalang15.ItoIdentity
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The Itô isometry for any `J` with `IsWalshIntegral W J`, as lower integrals. -/
theorem lintegral_sq_isWalshIntegral [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W) {J : PredL2 F P →L[ℝ] Lp ℝ 2 P}
    (hJ : IsWalshIntegral W J) (g : PredL2 F P) :
    ∫⁻ ω, ‖J g ω‖ₑ ^ 2 ∂P =
      ∫⁻ q, ‖(g : Lp ℝ 2 (spaceTimeSample P)) q‖ₑ ^ 2 ∂spaceTimeSample P := by
  rw [lintegral_enorm_sq, lintegral_enorm_sq,
    isWalshIntegral_eq_walshL2 ((isWhiteNoise_iff F W).1 hW) J hJ]
  exact congrArg (· ^ 2) ((WalshIntegral.Integral.walshL2 _).enorm_map g)

/-- **The completed Itô identity** (paper: `E I(t,x)² = (G_ν² ⋆ E ρ(u)²)(t,x)`, the identity
behind `E2:SecMom`). For a white noise `W`, the Walsh integral `J` and any stochastic integral
field `I` of `u` (`IsIntegralField`, a clause of `IsRandomFieldSolution`), at `t > 0`:
`E|I(t,x)|² = ∫₀ᵗ ∫_ℝ G_ν(t−s, x−y)² E|ρ(u(s,y))|² dy ds` as lower integrals. -/
theorem lintegral_sq_integralField [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {ρ : ℝ → ℝ} {u : ℝ → ℝ → Ω → ℝ} {I : ℝ → ℝ → Lp ℝ 2 P} (hI : IsIntegralField J ν ρ u I)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫⁻ ω, ‖I t x ω‖ₑ ^ 2 ∂P =
      ∫⁻ s in Ioo 0 t, ∫⁻ y, ENNReal.ofReal (G ν (t - s) (x - y) ^ 2) *
        momentFn P (fun s y ω => ρ (u s y ω)) 2 s y := by
  obtain ⟨g, hg, hIg⟩ := hI t ht x
  rw [hIg, lintegral_sq_isWalshIntegral hW.whiteNoise hJ g]
  set Φ : ℝ × ℝ × Ω → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (G ν (t - q.1) (x - q.2.1) ^ 2) * ‖ρ (u q.1 q.2.1 q.2.2)‖ₑ ^ 2 with hΦdef
  have hgΦ : (fun q => ‖(g : Lp ℝ 2 (spaceTimeSample P)) q‖ₑ ^ 2) =ᵐ[spaceTimeSample P] Φ :=
    hg.mono fun q hq => by beta_reduce at hq ⊢; rw [hq, ItoIdentity.enorm_mul_sq]
  have hΦ : AEMeasurable Φ (spaceTimeSample P) :=
    (((Lp.aestronglyMeasurable (g : Lp ℝ 2 (spaceTimeSample P))).enorm).pow_const 2).congr hgΦ
  rw [lintegral_congr_ae hgΦ, ItoIdentity.lintegral_spaceTimeSample hΦ]
  have hinner : ∀ s y, ∫⁻ ω, Φ (s, y, ω) ∂P =
      ENNReal.ofReal (G ν (t - s) (x - y) ^ 2) * momentFn P (fun s y ω => ρ (u s y ω)) 2 s y := by
    intro s y
    simp only [hΦdef, momentFn, ENNReal.rpow_two]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  simp_rw [hinner]
  set Fs : ℝ → ℝ≥0∞ := fun s => ∫⁻ y, ENNReal.ofReal (G ν (t - s) (x - y) ^ 2) *
    momentFn P (fun s y ω => ρ (u s y ω)) 2 s y with hFs
  have hzero : ∀ s, t ≤ s → Fs s = 0 := by
    intro s hs
    simp [hFs, LConv.G_of_nonpos hν.le (sub_nonpos.mpr hs)]
  calc ∫⁻ s in Ioi 0, Fs s = ∫⁻ s in Ioi 0, (Iio t).indicator Fs s := by
        refine lintegral_congr fun s => ?_
        by_cases hs : s < t
        · simp [hs]
        · simp [hs, hzero s (not_lt.mp hs)]
    _ = ∫⁻ s in Ioo 0 t, Fs s := by
        rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          Iio_inter_Ioi]

/-- The completed Itô identity in `lstConv` form: `E|I(t,x)|² = (E|ρ(u)|² ⋆ G_ν²)(t,x)`. -/
theorem lintegral_sq_integralField_eq_lstConv [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {ρ : ℝ → ℝ} {u : ℝ → ℝ → Ω → ℝ} {I : ℝ → ℝ → Lp ℝ 2 P} (hI : IsIntegralField J ν ρ u I)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫⁻ ω, ‖I t x ω‖ₑ ^ 2 ∂P =
      lstConv (momentFn P (fun s y ω => ρ (u s y ω)) 2)
        (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x := by
  rw [lintegral_sq_integralField hW hJ hν hI ht x, lstConv]
  simp_rw [mul_comm (ENNReal.ofReal _)]

/-- Sanity check: for `ρ = 0` the Itô identity gives `E|I(t,x)|² = 0`, consistent with
`integralField_rho_zero` (`I = 0`) and `momentFn_of_rho_zero` (`E|u|² = J₀²`). -/
theorem lintegral_sq_integralField_rho_zero [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ} (hν : 0 < ν)
    {u : ℝ → ℝ → Ω → ℝ} {I : ℝ → ℝ → Lp ℝ 2 P} (hI : IsIntegralField J ν (fun _ => 0) u I)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫⁻ ω, ‖I t x ω‖ₑ ^ 2 ∂P = 0 := by
  rw [lintegral_sq_integralField hW hJ hν hI ht x]
  simp [momentFn]

/-! ### The polarized Itô identity -/

/-- **Polarized Itô identity**: `E[I(t,x) I(τ,y)] = ∫_{s>0} ∫_ℝ G_ν(t−s,x−z) G_ν(τ−s,y−z)
E[ρ(u(s,z))²] dz ds` (Bochner integrals; the integrand vanishes for `s ≥ min t τ`). -/
theorem integral_mul_integralField [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) {ν : ℝ}
    {ρ : ℝ → ℝ} {u : ℝ → ℝ → Ω → ℝ} {I : ℝ → ℝ → Lp ℝ 2 P} (hI : IsIntegralField J ν ρ u I)
    {t τ : ℝ} (ht : 0 < t) (hτ : 0 < τ) (x y : ℝ) :
    ∫ ω, I t x ω * I τ y ω ∂P =
      ∫ s in Ioi 0, ∫ z, G ν (t - s) (x - z) * G ν (τ - s) (y - z) *
        ∫ ω, ρ (u s z ω) ^ 2 ∂P := by
  obtain ⟨g₁, hg₁, hI₁⟩ := hI t ht x
  obtain ⟨g₂, hg₂, hI₂⟩ := hI τ hτ y
  have hW' := (isWhiteNoise_iff F W).1 hW.whiteNoise
  have hinner := (WalshIntegral.Integral.walshL2 hW').inner_map_map g₁ g₂
  have hJeq := isWalshIntegral_eq_walshL2 hW' J hJ
  have hJ₁ : J g₁ = WalshIntegral.Integral.walshL2 hW' g₁ := by rw [hJeq]; rfl
  have hJ₂ : J g₂ = WalshIntegral.Integral.walshL2 hW' g₂ := by rw [hJeq]; rfl
  simp only [L2.inner_def, RCLike.inner_apply, conj_trivial] at hinner
  rw [hI₁, hI₂, hJ₁, hJ₂]
  simp_rw [mul_comm (WalshIntegral.Integral.walshL2 hW' g₁ _)]
  have hinner' : ∫ a, WalshIntegral.Integral.walshL2 hW' g₂ a *
      WalshIntegral.Integral.walshL2 hW' g₁ a ∂P =
      inner ℝ (g₁ : Lp ℝ 2 (spaceTimeSample P)) (g₂ : Lp ℝ 2 (spaceTimeSample P)) := hinner
  rw [L2.inner_def] at hinner'
  simp only [RCLike.inner_apply, conj_trivial] at hinner'
  rw [hinner']
  set Ψ : ℝ × ℝ × Ω → ℝ := fun q =>
    G ν (t - q.1) (x - q.2.1) * G ν (τ - q.1) (y - q.2.1) * ρ (u q.1 q.2.1 q.2.2) ^ 2 with hΨ
  have hae : (fun q => (g₂ : Lp ℝ 2 (spaceTimeSample P)) q * (g₁ : Lp ℝ 2 (spaceTimeSample P)) q)
      =ᵐ[spaceTimeSample P] Ψ := by
    filter_upwards [hg₁, hg₂] with q h1 h2
    rw [h1, h2, hΨ]
    ring
  have hint : Integrable Ψ ((volume.restrict (Ioi (0 : ℝ))).prod (volume.prod P)) :=
    ((Lp.memLp (g₂ : Lp ℝ 2 (spaceTimeSample P))).integrable_mul
      (Lp.memLp (g₁ : Lp ℝ 2 (spaceTimeSample P)))).congr hae
  rw [integral_congr_ae hae]
  change ∫ q, Ψ q ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.prod P)) = _
  rw [integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [hint.prod_right_ae] with s hs
  rw [integral_prod (fun p => Ψ (s, p)) hs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hΨ]
  exact integral_const_mul _ _

/-! ### The renewal identity -/

/-- Mean zero of the stochastic integral: `E[J g] = 0` for every `g ∈ 𝒫₂`. For the Walsh integral
this is WalshIntegral's `integral_walshL2` (v0.8.0); it enters the renewal identity only through
the cross term `2 J₀ E[I]`. -/
def WalshMeanZero [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (J : PredL2 F P →L[ℝ] Lp ℝ 2 P) : Prop :=
  ∀ g : PredL2 F P, ∫ ω, J g ω ∂P = 0

/-- The discharge route for `WalshMeanZero`: it suffices to know mean zero of `walshL2`. -/
theorem walshMeanZero_of_walshL2 [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W) {J : PredL2 F P →L[ℝ] Lp ℝ 2 P}
    (hJ : IsWalshIntegral W J)
    (h0 : ∀ g, ∫ ω, WalshIntegral.Integral.walshL2 ((isWhiteNoise_iff F W).1 hW) g ω ∂P = 0) :
    WalshMeanZero J := by
  rw [isWalshIntegral_eq_walshL2 ((isWhiteNoise_iff F W).1 hW) J hJ]
  exact h0

/-- Every Walsh integral has mean zero (WalshIntegral v0.8.0, `integral_walshL2`). -/
theorem walshMeanZero_of_isWalshIntegral [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W) {J : PredL2 F P →L[ℝ] Lp ℝ 2 P}
    (hJ : IsWalshIntegral W J) : WalshMeanZero J :=
  walshMeanZero_of_walshL2 hW hJ fun g => WalshIntegral.Integral.integral_walshL2 _ g

/-- The renewal identity for an abstract integral with mean zero (`hmean`); see
`momentFn_two_eq_renewal` for the Walsh integral. No integrability hypothesis on `u` is needed:
`u(t,x) = J₀(t,x) + I(t,x)` a.s. with `I(t,x) ∈ L²(P)`. -/
theorem momentFn_two_eq_renewal_of_meanZero [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J) (hmean : WalshMeanZero J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {μ : Measure ℝ} {u : ℝ → ℝ → Ω → ℝ}
    (hu : IsRandomFieldSolution J ν ρ μ u) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    momentFn P u 2 t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (momentFn P (fun s y ω => ρ (u s y ω)) 2)
        (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x := by
  obtain ⟨I, hI, -, heq⟩ := hu.integral
  obtain ⟨g, -, hIg⟩ := hI t ht x
  have h0 : ∫ ω, I t x ω ∂P = 0 := by rw [hIg]; exact hmean g
  rw [← lintegral_sq_integralField_eq_lstConv hW hJ hν hI ht x,
    ← ItoIdentity.lintegral_sq_const_add _ _ h0, momentFn]
  simp_rw [ENNReal.rpow_two]
  exact lintegral_congr_ae ((heq t ht x).mono fun ω h => by beta_reduce at h ⊢; rw [h])

/-- **The renewal identity** `E|u(t,x)|² = J₀(t,x)² + (E|ρ(u)|² ⋆ G_ν²)(t,x)` (paper:
`E2:SecMom` at `p = 2`) for every random field solution of `E2:WalshSI`. -/
theorem momentFn_two_eq_renewal [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsAugmentedWhiteNoise P F W)
    {J : PredL2 F P →L[ℝ] Lp ℝ 2 P} (hJ : IsWalshIntegral W J)
    {ν : ℝ} (hν : 0 < ν) {ρ : ℝ → ℝ} {μ : Measure ℝ} {u : ℝ → ℝ → Ω → ℝ}
    (hu : IsRandomFieldSolution J ν ρ μ u) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    momentFn P u 2 t x = ENNReal.ofReal (J0 ν μ t x ^ 2) +
      lstConv (momentFn P (fun s y ω => ρ (u s y ω)) 2)
        (fun s y => ENNReal.ofReal (G ν s y ^ 2)) t x :=
  momentFn_two_eq_renewal_of_meanZero hW hJ
    (walshMeanZero_of_isWalshIntegral hW.whiteNoise hJ) hν hu ht x

end ChenDalang15.Stoch

end

end
