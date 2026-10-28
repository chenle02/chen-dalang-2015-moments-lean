module

public import ChenDalang15.KernelK
public import ChenDalang15.ErfSeries

/-!
# The closed form of `𝓚` (Chen–Dalang 2015, Proposition `P2:K`, display `E:K`)

For `ν > 0` and `t > 0`,
`𝓚(t,x) = G_{ν/2}(t,x) (λ²/√(4πνt) + λ⁴/(2ν) · e^{λ⁴t/(4ν)} · Φ(λ² √(t/(2ν))))`.

Route (as in the paper): with `z = b√(πt)`, `b = λ²/√(4πν)`, each `𝓛ₙ(t,x)` equals
`G_{ν/2}(t,x) z^{n+1} / (Γ((n+1)/2) t)` (`L_eq`), and
`Σₙ z^{n+1}/Γ((n+1)/2) = z/√π + z² e^{z²}(1 + Erf z)` (`hasSum_pow_div_Gamma` shifted by one).
Finally `1 + Erf z = 2 Φ(√2 z)` (`Phi_eq_erf`).
-/

set_option autoImplicit false

public section

namespace ChenDalang15

open Real

/-- The series of `P2:K` shifted by one: `Σₙ z^{n+1}/Γ((n+1)/2) = z/√π + z² e^{z²}(1+Erf z)`. -/
theorem hasSum_pow_succ_div_Gamma {z : ℝ} (hz : 0 ≤ z) :
    HasSum (fun n : ℕ => z ^ (n + 1) / Real.Gamma (((n : ℝ) + 1) / 2))
      (z / Real.sqrt π + z ^ 2 * (Real.exp (z ^ 2) * (1 + erf z))) := by
  have h := (hasSum_pow_div_Gamma hz).mul_left (z ^ 2)
  have hfun : (fun k : ℕ => z ^ 2 * (z ^ k / Real.Gamma ((k : ℝ) / 2 + 1))) =
      fun k : ℕ => z ^ ((k + 1) + 1) / Real.Gamma ((((k + 1 : ℕ) : ℝ) + 1) / 2) := by
    funext k
    rw [show (((k + 1 : ℕ) : ℝ) + 1) / 2 = (k : ℝ) / 2 + 1 by push_cast; ring, pow_succ, pow_succ]
    ring
  rw [hfun] at h
  have h0 := HasSum.zero_add (f := fun n : ℕ => z ^ (n + 1) / Real.Gamma (((n : ℝ) + 1) / 2)) h
  have hf0 : z ^ (0 + 1) / Real.Gamma ((((0 : ℕ) : ℝ) + 1) / 2) = z / Real.sqrt π := by
    rw [show (((0 : ℕ) : ℝ) + 1) / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq, zero_add, pow_one]
  rw [hf0] at h0
  exact h0

/-- Each term of `kSeries` in the variable `z = b√(πt)`. -/
theorem lCoeff_mul_rpow_eq {ν lam t : ℝ} (ht : 0 < t) (n : ℕ) :
    lCoeff ν lam n * t ^ (((n : ℝ) - 1) / 2) =
      (bConst ν lam * Real.sqrt (π * t)) ^ (n + 1) / Real.Gamma (((n : ℝ) + 1) / 2) / t := by
  have hsq : Real.sqrt t ^ (n + 1) = t ^ (((n : ℝ) + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    push_cast
    ring_nf
  have hpow : t ^ (((n : ℝ) - 1) / 2) = t ^ (((n : ℝ) + 1) / 2) / t := by
    rw [← Real.rpow_sub_one ht.ne']
    ring_nf
  rw [lCoeff, hpow, Real.sqrt_mul Real.pi_pos.le, ← hsq]
  ring

/-- The scalar series `k(t)` has the sum `(z/√π + z² e^{z²}(1+Erf z))/t`, `z = b√(πt)`. -/
theorem hasSum_kSeries {ν lam t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    HasSum (fun n : ℕ => lCoeff ν lam n * t ^ (((n : ℝ) - 1) / 2))
      ((bConst ν lam * Real.sqrt (π * t) / Real.sqrt π +
          (bConst ν lam * Real.sqrt (π * t)) ^ 2 *
            (Real.exp ((bConst ν lam * Real.sqrt (π * t)) ^ 2) *
              (1 + erf (bConst ν lam * Real.sqrt (π * t))))) / t) := by
  have hb : 0 ≤ bConst ν lam := by unfold bConst; positivity
  have hz : 0 ≤ bConst ν lam * Real.sqrt (π * t) := by positivity
  have h := (hasSum_pow_succ_div_Gamma hz).div_const t
  convert h using 1
  funext n
  exact lCoeff_mul_rpow_eq ht n

/-- The scalar identity behind `E:K`, in the paper's variables. -/
theorem kSeries_closed_form {ν lam t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    (bConst ν lam * Real.sqrt (π * t) / Real.sqrt π +
        (bConst ν lam * Real.sqrt (π * t)) ^ 2 *
          (Real.exp ((bConst ν lam * Real.sqrt (π * t)) ^ 2) *
            (1 + erf (bConst ν lam * Real.sqrt (π * t))))) / t =
      lam ^ 2 / Real.sqrt (4 * π * ν * t) +
        lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * t / (4 * ν)) *
          Phi (lam ^ 2 * Real.sqrt (t / (2 * ν))) := by
  -- Express every square root through `√π`, `√ν`, `√t`, `√2`.
  have hπ : 0 < π := Real.pi_pos
  have sπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have sν : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have st : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have s2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have e4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq two_pos.le]
  have hA : Real.sqrt (4 * π * ν) = 2 * Real.sqrt π * Real.sqrt ν := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), e4]
  have hB : Real.sqrt (π * t) = Real.sqrt π * Real.sqrt t := Real.sqrt_mul hπ.le t
  have hC : Real.sqrt (4 * π * ν * t) = 2 * Real.sqrt π * Real.sqrt ν * Real.sqrt t := by
    rw [Real.sqrt_mul (by positivity), hA]
  have hD : Real.sqrt (t / (2 * ν)) = Real.sqrt t / (Real.sqrt 2 * Real.sqrt ν) := by
    rw [Real.sqrt_div ht.le, Real.sqrt_mul (by norm_num)]
  have sq_π : Real.sqrt π ^ 2 = π := Real.sq_sqrt hπ.le
  have sq_ν : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt hν.le
  have sq_t : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have sq_2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- The argument of Erf and of Φ.
  set w := lam ^ 2 * Real.sqrt t / (2 * Real.sqrt ν) with hw
  have hz : bConst ν lam * Real.sqrt (π * t) = w := by
    rw [bConst, hA, hB, hw]
    field_simp
  have hPhi : Phi (lam ^ 2 * Real.sqrt (t / (2 * ν))) = (1 + erf w) / 2 := by
    rw [Phi_eq_erf, hD]
    congr 3
    rw [hw]
    field_simp
    rw [sq_2]
  have hw2 : w ^ 2 = lam ^ 4 * t / (4 * ν) := by
    rw [hw, div_pow, mul_pow, mul_pow, sq_t, sq_ν]
    ring
  rw [hz, hPhi, hw2, hC]
  rw [hw]
  field_simp
  have hst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  linear_combination 8 * lam ^ 2 * ν * hst

/-- `𝓚` as a convergent series with its explicit sum. -/
theorem hasSum_L {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (fun n => L ν lam n t x)
      (G (ν / 2) t x * (lam ^ 2 / Real.sqrt (4 * π * ν * t) +
        lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * t / (4 * ν)) *
          Phi (lam ^ 2 * Real.sqrt (t / (2 * ν))))) := by
  rw [← kSeries_closed_form hν ht]
  have h := (hasSum_kSeries (lam := lam) hν ht).mul_left (G (ν / 2) t x)
  convert h using 1
  funext n
  rw [L_eq hν n ht x]
  ring

/-- **Chen–Dalang (2015), Proposition `P2:K`, display `E:K`.** For `ν > 0`, `t > 0`,
`𝓚(t,x) = G_{ν/2}(t,x) (λ²/√(4πνt) + λ⁴/(2ν) · e^{λ⁴t/(4ν)} · Φ(λ² √(t/(2ν))))`. -/
theorem K_eq {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    K ν lam t x =
      G (ν / 2) t x * (lam ^ 2 / Real.sqrt (4 * π * ν * t) +
        lam ^ 4 / (2 * ν) * Real.exp (lam ^ 4 * t / (4 * ν)) *
          Phi (lam ^ 2 * Real.sqrt (t / (2 * ν)))) :=
  (hasSum_L hν ht x).tsum_eq

end ChenDalang15

end
