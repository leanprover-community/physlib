/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Sqrt
/-!

# Calculus of the real square root near zero

## i. Overview

Two facts about the real square root at zero, where Mathlib's calculus does not reach: the
cube `√y ^ 3` is differentiable everywhere, with derivative `(3/2) √x`, and `√` is not
Lipschitz on any interval `[0, ε]`. The first gives the derivative of the potential of the
Norton dome, the second the failure of the Picard–Lindelöf hypothesis for its force.

## ii. Key results

- `hasDerivAt_sqrt_pow_three` is the derivative of `√y ^ 3` at every real number.
- `not_lipschitzOnWith_sqrt` is the failure of the Lipschitz property of `√` on `[0, ε]`.

## iii. Table of contents

- A. The derivative of the cube of the square root
- B. The square root is not Lipschitz at zero

## iv. References

- Norton, J. D., *The dome: an unexpectedly simple failure of determinism*, Philosophy of
  Science 75 (2008), 786–798.

-/

@[expose] public section

open Filter Topology

/-!

## A. The derivative of the cube of the square root

To the left of zero the square root vanishes, to the right the chain rule applies, and at zero
the difference quotient of `√t ^ 3 = t √t` is `√t`, which tends to zero.

-/

/-- The cube of the real square root, `√y ^ 3`, has derivative `(3/2) √x` at every real `x`. It
  is differentiable at `0`, with derivative `0`, even though `√` is not. -/
lemma hasDerivAt_sqrt_pow_three (x : ℝ) :
    HasDerivAt (fun y : ℝ => √y ^ 3) (3 / 2 * √x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hev : (fun y : ℝ => √y ^ 3) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [Real.sqrt_eq_zero'.mpr (Set.mem_Iio.mp hy).le]
    rw [Real.sqrt_eq_zero'.mpr hx.le, mul_zero]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · rw [Real.sqrt_zero, mul_zero, hasDerivAt_iff_tendsto_slope_zero]
    have h : ∀ t : ℝ, t ≠ 0 → √t = t⁻¹ • (√(0 + t) ^ 3 - √0 ^ 3) := by
      intro t ht
      rw [zero_add, Real.sqrt_zero, zero_pow three_ne_zero, sub_zero, smul_eq_mul]
      rcases le_or_gt t 0 with h | h
      · simp [Real.sqrt_eq_zero'.mpr h]
      · rw [pow_succ, Real.sq_sqrt h.le, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
    have hc : Tendsto (fun t : ℝ => √t) (𝓝[≠] 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact hc.congr' (eventually_nhdsWithin_of_forall fun t ht => h t ht)
  · have hs : √x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
    refine ((Real.hasDerivAt_sqrt hx.ne').pow 3).congr_deriv ?_
    rw [show (3 : ℕ) - 1 = 2 from rfl, Nat.cast_ofNat]
    field_simp

/-!

## B. The square root is not Lipschitz at zero

A bound `√y ≤ K y` on `[0, ε]` gives `1 ≤ K √y` for every positive `y ≤ ε`, which fails at
`y = min ε (1 / (2K + 1)²)`.

-/

/-- The real square root is not Lipschitz on any interval `[0, ε]` with `ε > 0`, for any
  Lipschitz constant. -/
lemma not_lipschitzOnWith_sqrt (K : NNReal) {ε : ℝ} (hε : 0 < ε) :
    ¬ LipschitzOnWith K (fun y : ℝ => √y) (Set.Icc 0 ε) := by
  intro h
  have hK : (0 : ℝ) ≤ K := K.2
  obtain ⟨y, hy0, hyε, hy⟩ : ∃ y : ℝ, 0 < y ∧ y ≤ ε ∧ (K : ℝ) * √y < 1 := by
    refine ⟨min ε ((1 / (2 * (K : ℝ) + 1)) ^ 2), ?_, min_le_left _ _, ?_⟩
    · exact lt_min hε (by positivity : (0 : ℝ) < (1 / (2 * (K : ℝ) + 1)) ^ 2)
    have h1 : √(min ε ((1 / (2 * (K : ℝ) + 1)) ^ 2)) ≤ 1 / (2 * K + 1) := by
      rw [Real.sqrt_le_left (by positivity)]
      exact min_le_right _ _
    calc (K : ℝ) * √(min ε ((1 / (2 * (K : ℝ) + 1)) ^ 2)) ≤ K * (1 / (2 * K + 1)) := by gcongr
      _ < 1 := by
        rw [mul_one_div, div_lt_one (by positivity)]
        linarith
  have := h.dist_le_mul y ⟨hy0.le, hyε⟩ 0 ⟨le_rfl, hε.le⟩
  simp only [Real.sqrt_zero, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hy0] at this
  have hsq : √y * √y = y := Real.mul_self_sqrt hy0.le
  have hs : 0 < √y := Real.sqrt_pos.mpr hy0
  nlinarith

end
