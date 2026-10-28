module

public import ChenDalang15.Resolvent

/-!
# The coefficients `Bₙ(t)` of Chen–Dalang (2015), Proposition `P2:K`

The paper writes `𝓛ₙ = 𝓛₀ · Bₙ` (`E:KS-LB`, second equality) with
`Bₙ(t) = π^{(n+1)/2} bⁿ t^{n/2} / Γ((n+1)/2)`, and claims `Σₙ Bₙ(t)^{1/m} < ∞` for every
`m ≥ 1` (last sentence of `P2:K`).

The paper proves the summability by the ratio test together with the asymptotic
`Γ(n/2)/Γ((n+1)/2) ≈ (2/n)^{1/2}` (DLMF 5.11.12), which Mathlib does not have. Here the
ratio test is applied to the *two-step* ratio instead: the recurrence `Γ(x+1) = x Γ(x)` gives
the exact identity `B_{n+2}(t) = (2π b² t / (n+1)) · Bₙ(t)`, so the two-step ratio of
`Bₙ^{1/m}` tends to `0`, and the even and odd subsequences are summable separately. No Gamma
asymptotics are needed.
-/

set_option autoImplicit false

@[expose] public section

namespace ChenDalang15

open Real Filter Topology

/-- `B_n(t) = π^{(n+1)/2} b^n t^{n/2} / Γ((n+1)/2)` (paper, P2:K). -/
noncomputable def BCoeff (b t : ℝ) (n : ℕ) : ℝ :=
  Real.pi ^ (((n : ℝ) + 1) / 2) * b ^ n * t ^ ((n : ℝ) / 2) / Real.Gamma (((n : ℝ) + 1) / 2)

/-- Paper E:KS-LB, second equality: `𝓛ₙ = 𝓛₀ · Bₙ`. -/
theorem L_eq_L_zero_mul_BCoeff {ν lam : ℝ} (hν : 0 < ν) (n : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    L ν lam n t x = L ν lam 0 t x * BCoeff (bConst ν lam) t n := by
  rw [L_eq hν n ht x, L_eq hν 0 ht x]
  simp only [lCoeff, BCoeff]
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hΓ : Real.Gamma (((n : ℝ) + 1) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have e0 : (((0 : ℕ) : ℝ) + 1) / 2 = 1 / 2 := by norm_num
  have e1 : (((0 : ℕ) : ℝ) - 1) / 2 = -(1 / 2) := by norm_num
  have epi : π ^ (((n : ℝ) + 1) / 2) = Real.sqrt π ^ (n + 1) := by
    rw [Real.rpow_div_two_eq_sqrt _ Real.pi_pos.le, show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_natCast]
  have et : t ^ (((n : ℝ) - 1) / 2) = t ^ (-(1 / 2 : ℝ)) * t ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_add ht]
    ring_nf
  rw [e0, e1, Real.Gamma_one_half_eq, epi, et, zero_add, pow_one]
  field_simp
  ring

/-- `Bₙ(t) ≥ 0` for `b, t ≥ 0`. -/
theorem BCoeff_nonneg {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (n : ℕ) : 0 ≤ BCoeff b t n := by
  unfold BCoeff
  have hΓ : 0 < Real.Gamma (((n : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-- Two-step recurrence: `B_{n+2}(t) = (2π b² t) · (1/(n+1)) · Bₙ(t)` for `t ≥ 0`
(from `Γ(x+1) = x Γ(x)` at `x = (n+1)/2`). -/
theorem BCoeff_add_two (b : ℝ) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    BCoeff b t (n + 2) = (2 * π * b ^ 2 * t) * (1 / ((n : ℝ) + 1)) * BCoeff b t n := by
  unfold BCoeff
  have hx : 0 < ((n : ℝ) + 1) / 2 := by positivity
  have hΓ : Real.Gamma (((n : ℝ) + 1) / 2) ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  have eΓ : Real.Gamma ((((n + 2 : ℕ) : ℝ) + 1) / 2) =
      ((n : ℝ) + 1) / 2 * Real.Gamma (((n : ℝ) + 1) / 2) := by
    rw [← Real.Gamma_add_one hx.ne']
    congr 1
    push_cast
    ring
  have epi : π ^ ((((n + 2 : ℕ) : ℝ) + 1) / 2) = π ^ (((n : ℝ) + 1) / 2) * π := by
    rw [← Real.rpow_add_one Real.pi_pos.ne']
    congr 1
    push_cast
    ring
  have et : t ^ (((n + 2 : ℕ) : ℝ) / 2) = t ^ ((n : ℝ) / 2) * t := by
    have hne : (n : ℝ) / 2 + 1 ≠ 0 := by positivity
    have h := Real.rpow_add' ht hne
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    push_cast
    ring
  rw [eΓ, epi, et, pow_add]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- If `‖f (n+2)‖ ≤ r ‖f n‖` eventually with `r < 1`, then `f` is summable (ratio test applied
separately to the even and odd subsequences). -/
theorem summable_of_norm_add_two_eventually_le {f : ℕ → ℝ} {r : ℝ} (hr : r < 1)
    (h : ∀ᶠ n in atTop, ‖f (n + 2)‖ ≤ r * ‖f n‖) : Summable f := by
  refine Summable.even_add_odd ?_ ?_
  · refine summable_of_ratio_norm_eventually_le hr ?_
    have hT : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
      tendsto_atTop_atTop.2 fun N => ⟨N, fun k hk => by omega⟩
    filter_upwards [hT.eventually h] with k hk
    simpa [mul_add, mul_one] using hk
  · refine summable_of_ratio_norm_eventually_le hr ?_
    have hT : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
      tendsto_atTop_atTop.2 fun N => ⟨N, fun k hk => by omega⟩
    filter_upwards [hT.eventually h] with k hk
    have e : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
    simpa [e] using hk

/-- Paper P2:K, last claim: `Σₙ Bₙ(t)^{1/m} < ∞` for every `m ≥ 1`. -/
theorem summable_BCoeff_rpow {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) {m : ℕ} (hm : 0 < m) :
    Summable (fun n : ℕ => BCoeff b t n ^ ((1 : ℝ) / m)) := by
  have hp : (0 : ℝ) < 1 / m := by positivity
  set C : ℝ := 2 * π * b ^ 2 * t with hC
  have hC0 : 0 ≤ C := by positivity
  -- The two-step ratio `(C/(n+1))^{1/m}` tends to `0`.
  have hlim : Tendsto (fun n : ℕ => (C * (1 / ((n : ℝ) + 1))) ^ ((1 : ℝ) / m)) atTop (𝓝 0) := by
    refine Tendsto.rpow_const_nhds_zero ?_ hp
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C
  refine summable_of_norm_add_two_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [(tendsto_order.1 hlim).2 (1 / 2) (by norm_num)] with n hn
  have hB : 0 ≤ BCoeff b t n := BCoeff_nonneg hb ht n
  have hq : 0 ≤ C * (1 / ((n : ℝ) + 1)) := by positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (BCoeff_nonneg hb ht _) _),
    Real.norm_of_nonneg (Real.rpow_nonneg hB _), BCoeff_add_two b ht n, ← hC,
    Real.mul_rpow hq hB]
  exact mul_le_mul_of_nonneg_right hn.le (Real.rpow_nonneg hB _)

end ChenDalang15

end
