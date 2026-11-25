/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
/-!
# The Lie product formula

The exponential of a sum as a limit of products of exponentials.

## i. Overview

In a complete normed algebra over `ℝ` with `‖1‖ = 1`,
`(exp (X / n) exp (Y / n)) ^ n → exp (X + Y)` as `n → ∞`. This is the Lie product formula,
known in physics as the Trotter product formula. It is what makes the generators of the
one-parameter subgroups of a closed group of matrices closed under addition.

The proof compares `a = exp (X / n) exp (Y / n)` with `b = exp ((X + Y) / n)`, whose `n`-th
power is `exp (X + Y)`. Both have norm at most `M = exp ((‖X‖ + ‖Y‖) / n)`, so telescoping
gives `‖a ^ n − b ^ n‖ ≤ n M ^ n ‖a − b‖`, with `M ^ n = exp (‖X‖ + ‖Y‖)`. The two curves
`t ↦ exp (t X) exp (t Y)` and `t ↦ exp (t (X + Y))` agree at `t = 0` together with their
derivatives, so `‖a − b‖` is small compared with `1 / n`, and `n ‖a − b‖ → 0`.

## ii. Key results

- `NormedSpace.norm_exp_le_exp_norm` : `‖exp x‖ ≤ exp ‖x‖`.
- `NormedSpace.norm_pow_sub_pow_le` : `‖a ^ n − b ^ n‖ ≤ n M ^ n ‖a − b‖` when `‖a‖, ‖b‖ ≤ M`
  and `1 ≤ M`.
- `NormedSpace.tendsto_exp_mul_exp_pow` : the Lie product formula.

## iii. Table of contents

- A. Norm bounds
- B. The Lie product formula

## iv. References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer (2015).

-/

@[expose] public section

open Filter Topology

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!

## A. Norm bounds

-/

/-- The exponential is bounded by the real exponential of the norm, term by term in the
  exponential series. -/
lemma norm_exp_le_exp_norm (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have h1 := exp_series_hasSum_exp' (𝕂 := ℝ) x
  have h2 := exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  rw [← Real.exp_eq_exp_ℝ] at h2
  refine h1.norm_le_of_bounded h2 fun n => ?_
  rw [norm_smul, Real.norm_of_nonneg (by positivity), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- The difference of two `n`-th powers, by telescoping:
  `‖a ^ n − b ^ n‖ ≤ n M ^ n ‖a − b‖` when `‖a‖, ‖b‖ ≤ M` and `1 ≤ M`. -/
lemma norm_pow_sub_pow_le {a b : 𝔸} {M : ℝ} (hM : 1 ≤ M) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M)
    (n : ℕ) : ‖a ^ n - b ^ n‖ ≤ n * M ^ n * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hMn : M ^ n ≤ M ^ (n + 1) := pow_le_pow_right₀ hM (Nat.le_succ n)
    have hbn : ‖b ^ n‖ ≤ M ^ n :=
      (norm_pow_le b n).trans (pow_le_pow_left₀ (norm_nonneg _) hb n)
    calc ‖a ^ (n + 1) - b ^ (n + 1)‖ = ‖a * (a ^ n - b ^ n) + (a - b) * b ^ n‖ := by
          rw [pow_succ', pow_succ', mul_sub, sub_mul]
          abel_nf
      _ ≤ ‖a‖ * ‖a ^ n - b ^ n‖ + ‖a - b‖ * ‖b ^ n‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ M * (n * M ^ n * ‖a - b‖) + ‖a - b‖ * M ^ n := by
          gcongr
      _ = n * M ^ (n + 1) * ‖a - b‖ + M ^ n * ‖a - b‖ := by ring
      _ ≤ n * M ^ (n + 1) * ‖a - b‖ + M ^ (n + 1) * ‖a - b‖ := by gcongr
      _ = ((n + 1 : ℕ) : ℝ) * M ^ (n + 1) * ‖a - b‖ := by push_cast; ring

/-!

## B. The Lie product formula

-/

omit [NormOneClass 𝔸] in
/-- The curves `t ↦ exp (t X) exp (t Y)` and `t ↦ exp (t (X + Y))` agree to first order at
  `t = 0`: `n (exp (X / n) exp (Y / n) − exp ((X + Y) / n)) → 0`. -/
lemma tendsto_nat_smul_exp_mul_exp_sub_exp (X Y : 𝔸) :
    Tendsto (fun n : ℕ => (n : ℝ) • (exp ((n : ℝ)⁻¹ • X) * exp ((n : ℝ)⁻¹ • Y) -
      exp ((n : ℝ)⁻¹ • (X + Y)))) atTop (𝓝 0) := by
  set F : ℝ → 𝔸 := fun t => exp (t • X) * exp (t • Y) - exp (t • (X + Y))
  have hF : HasDerivAt F 0 0 := by
    have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0)).sub
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (X + Y) 0)
    simp only [zero_smul, exp_zero, one_mul, mul_one, sub_self] at h
    exact h
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_nhds_zero_nat,
      (eventually_ne_atTop 0).mono fun n hn => by simpa using hn⟩
  refine (hF.tendsto_slope_zero.comp hinv).congr fun n => ?_
  simp [F]

/-- **The Lie product formula**: `(exp (X / n) exp (Y / n)) ^ n → exp (X + Y)`. -/
lemma tendsto_exp_mul_exp_pow (X Y : 𝔸) :
    Tendsto (fun n : ℕ => (exp ((n : ℝ)⁻¹ • X) * exp ((n : ℝ)⁻¹ • Y)) ^ n) atTop
      (𝓝 (exp (X + Y))) := by
  set K := Real.exp (‖X‖ + ‖Y‖)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim := (tendsto_nat_smul_exp_mul_exp_sub_exp X Y).norm.const_mul K
  rw [norm_zero, mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [norm_norm]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  set M := Real.exp ((n : ℝ)⁻¹ * (‖X‖ + ‖Y‖))
  have hM : 1 ≤ M := Real.one_le_exp (by positivity)
  have hMn : M ^ n = K := by
    rw [← Real.exp_nat_mul, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]
  have hpow : ∀ (m : ℕ) (Z : 𝔸), exp (m • Z) = exp Z ^ m := fun m Z => by
    induction m with
    | zero => simp
    | succ m ih =>
      have hr : ∀ W : 𝔸, W ∈ Metric.eball (0 : 𝔸) (expSeries ℝ 𝔸).radius := fun W => by
        simp [expSeries_radius_eq_top]
      rw [succ_nsmul, exp_add_of_commute_of_mem_ball (𝕂 := ℝ) ((Commute.refl Z).smul_left m)
        (hr _) (hr _), ih, pow_succ]
  have hb : exp (X + Y) = exp ((n : ℝ)⁻¹ • (X + Y)) ^ n := by
    rw [← hpow, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn', one_smul]
  have ha : ‖exp ((n : ℝ)⁻¹ • X) * exp ((n : ℝ)⁻¹ • Y)‖ ≤ M := by
    refine (norm_mul_le _ _).trans ?_
    calc _ ≤ Real.exp ‖(n : ℝ)⁻¹ • X‖ * Real.exp ‖(n : ℝ)⁻¹ • Y‖ :=
          mul_le_mul (norm_exp_le_exp_norm _) (norm_exp_le_exp_norm _) (norm_nonneg _)
            (Real.exp_pos _).le
      _ = M := by
          rw [← Real.exp_add, norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
            ← mul_add]
  have hb' : ‖exp ((n : ℝ)⁻¹ • (X + Y))‖ ≤ M := by
    refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
  calc ‖(exp ((n : ℝ)⁻¹ • X) * exp ((n : ℝ)⁻¹ • Y)) ^ n - exp (X + Y)‖
      ≤ n * M ^ n * ‖exp ((n : ℝ)⁻¹ • X) * exp ((n : ℝ)⁻¹ • Y) -
          exp ((n : ℝ)⁻¹ • (X + Y))‖ := by
        rw [hb]
        exact norm_pow_sub_pow_le hM ha hb' n
    _ = K * ‖(n : ℝ) • (exp ((n : ℝ)⁻¹ • X) * exp ((n : ℝ)⁻¹ • Y) -
          exp ((n : ℝ)⁻¹ • (X + Y)))‖ := by
        rw [hMn, norm_smul, Real.norm_natCast]
        ring

end NormedSpace
