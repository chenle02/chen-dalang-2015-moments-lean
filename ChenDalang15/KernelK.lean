module

public import ChenDalang15.Resolvent

/-!
# The kernel `𝓚 = Σₙ 𝓛ₙ` of Chen–Dalang (2015), `E:Def-K`

`𝓚(t,x) = Σ_{n ≥ 0} 𝓛ₙ(t,x)`. By `L_eq`, for `t > 0` every `𝓛ₙ(t,x)` is `G_{ν/2}(t,x)` times a
scalar depending only on `t`, so `𝓚(t,x) = G_{ν/2}(t,x) · k(t)` with the scalar series
`k(t) = Σₙ (b√π)^{n+1} / Γ((n+1)/2) · t^{(n-1)/2}`. This factorization is used both for the
closed form `E:K` and for the resolvent identity `E:KS-Kn-K0`.
-/

set_option autoImplicit false

@[expose] public section

namespace ChenDalang15

open Real

-- `K` is defined in `ChenDalang15.Defs` (shared with the Palomar Challenge).

/-- The scalar series `k(t) = Σₙ (b√π)^{n+1} / Γ((n+1)/2) · t^{(n-1)/2}`. -/
noncomputable def kSeries (ν lam : ℝ) (t : ℝ) : ℝ := ∑' n : ℕ, lCoeff ν lam n * t ^ (((n : ℝ) - 1) / 2)

/-- For `t > 0`, `𝓚(t,x) = G_{ν/2}(t,x) · k(t)`. -/
theorem K_eq_G_mul_kSeries {ν lam : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    K ν lam t x = G (ν / 2) t x * kSeries ν lam t := by
  have h : (fun n => L ν lam n t x) =
      fun n : ℕ => G (ν / 2) t x * (lCoeff ν lam n * t ^ (((n : ℝ) - 1) / 2)) := by
    funext n
    rw [L_eq hν n ht x]
    ring
  rw [K, h, tsum_mul_left, kSeries]

end ChenDalang15

end
