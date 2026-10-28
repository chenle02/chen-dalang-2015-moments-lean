module

public import WalshIntegral.LpConvergence

public import ChenDalang15.Summability
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Summable L² differences from the Picard coefficient bound

The second-moment estimate in Step 3 of the proof of `T2:ExUni` implies
summability of L² norms by `summable_BCoeff_rpow` with `m = 2`.
The profile constant may be zero; no division by it is used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ChenDalang15.Picard

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Taking the square root of a genuine moment bound controls the L² seminorm. -/
theorem eLpNorm_two_le_of_moment_bound {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) {a : ℝ} (ha : 0 ≤ a) {C : ℝ≥0∞}
    (hbound : ∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal a * C) :
    eLpNorm f 2 P ≤ ENNReal.ofReal (a ^ (1 / 2 : ℝ)) * C ^ (1 / 2 : ℝ) := by
  exact WalshIntegral.LpConvergence.eLpNorm_two_le_of_moment_bound hf ha hbound

/-- A summable square-root coefficient envelope yields a finite sum of L² norms.
This analytic helper is independent of the specific Picard coefficient formula. -/
theorem tsum_eLpNorm_two_lt_top_of_moment_bound (f : ℕ → Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hsum : Summable (fun n => a n ^ (1 / 2 : ℝ)))
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ n, ∫⁻ ω, ‖f n ω‖ₑ ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal (a n) * C) :
    (∑' n, eLpNorm (f n) 2 P) < ⊤ := by
  exact WalshIntegral.LpConvergence.tsum_eLpNorm_two_lt_top_of_moment_bound f hf ha hsum hC hbound

/-- The manuscript's `Bₙ(t)` difference estimate implies summable L² differences,
including `b = 0`, `t = 0` and a zero finite profile constant. -/
theorem tsum_eLpNorm_two_lt_top_of_BCoeff (f : ℕ → Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ n, ∫⁻ ω, ‖f n ω‖ₑ ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal (BCoeff b t n) * C) :
    (∑' n, eLpNorm (f n) 2 P) < ⊤ :=
  tsum_eLpNorm_two_lt_top_of_moment_bound f hf (BCoeff_nonneg hb ht)
    (by simpa using summable_BCoeff_rpow hb ht (m := 2) (by norm_num)) hC hbound

/-- Each difference belongs to L² under the same coefficient bound. -/
theorem memLp_two_of_BCoeff (f : ℕ → Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ n, ∫⁻ ω, ‖f n ω‖ₑ ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal (BCoeff b t n) * C) (n : ℕ) : MemLp (f n) 2 P := by
  exact (eLpNorm_two_le_of_moment_bound (hf n) (BCoeff_nonneg hb ht n) (hbound n)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.ne))

end ChenDalang15.Picard

end
