/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Slope
/-!

# Powers of the positive part

## i. Overview

The function `y ↦ max (y - c) 0 ^ (n + 2)` vanishes to the left of `c` and is a polynomial to
its right. It is differentiable everywhere, including at `c`, and is `C^(n+1)`. Functions of
this shape are the standard witnesses for the failure of uniqueness of ODEs with a
non-Lipschitz right-hand side, of which the Norton dome is the physical instance.

## ii. Key results

- `hasDerivAt_max_sub_pow` is the derivative `(n + 2) max (y - c) 0 ^ (n + 1)`, at every point.
- `contDiff_max_sub_pow` is the `C^(n+1)` regularity.

## iii. Table of contents

- A. The derivative
- B. Regularity

## iv. References

- Norton, J. D., *The dome: an unexpectedly simple failure of determinism*, Philosophy of
  Science 75 (2008), 786–798.

-/

@[expose] public section

open Filter Topology

/-!

## A. The derivative

By cases: to the left of `c` the function vanishes near the point, to the right it agrees near
the point with `(y - c) ^ (n + 2)`, and at `c` the difference quotient is `max t 0 ^ (n + 1)`,
which tends to zero.

-/

/-- The power `max (y - c) 0 ^ (n + 2)` of the positive part of `y - c` has derivative
  `(n + 2) max (x - c) 0 ^ (n + 1)` at every `x`, including the junction `x = c`. -/
lemma hasDerivAt_max_sub_pow (c : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => max (y - c) 0 ^ (n + 2))
      (((n : ℝ) + 2) * max (x - c) 0 ^ (n + 1)) x := by
  rcases lt_trichotomy x c with hx | rfl | hx
  · have hev : (fun y : ℝ => max (y - c) 0 ^ (n + 2)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [max_eq_right (sub_nonpos.mpr (Set.mem_Iio.mp hy).le)]
    rw [max_eq_right (sub_nonpos.mpr hx.le), zero_pow (Nat.succ_ne_zero _), mul_zero]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · rw [sub_self, max_self, zero_pow (Nat.succ_ne_zero _), mul_zero,
      hasDerivAt_iff_tendsto_slope_zero]
    have h : ∀ t : ℝ, t ≠ 0 →
        max t 0 ^ (n + 1) = t⁻¹ • (max (x + t - x) 0 ^ (n + 2) - max (x - x) 0 ^ (n + 2)) := by
      intro t ht
      rw [add_sub_cancel_left, sub_self, max_self, zero_pow (Nat.succ_ne_zero _), sub_zero,
        smul_eq_mul]
      rcases le_or_gt t 0 with h | h
      · simp [max_eq_right h]
      · rw [max_eq_left h.le]
        field_simp
        ring
    have hcont : Continuous (fun t : ℝ => max t 0 ^ (n + 1)) := by fun_prop
    have hc : Tendsto (fun t : ℝ => max t 0 ^ (n + 1)) (𝓝[≠] 0) (𝓝 0) := by
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    exact hc.congr' (eventually_nhdsWithin_of_forall fun t ht => h t ht)
  · have hev : (fun y : ℝ => max (y - c) 0 ^ (n + 2)) =ᶠ[𝓝 x] fun y => (y - c) ^ (n + 2) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [max_eq_left (sub_nonneg.mpr (Set.mem_Ioi.mp hy).le)]
    rw [max_eq_left (sub_nonneg.mpr hx.le)]
    have h1 : HasDerivAt (fun y : ℝ => y - c) 1 x := (hasDerivAt_id x).sub_const c
    refine ((HasDerivAt.pow h1 (n + 2)).congr_of_eventuallyEq hev).congr_deriv ?_
    show ((n + 2 : ℕ) : ℝ) * (x - c) ^ (n + 1) * 1 = _
    push_cast
    ring

/-!

## B. Regularity

By induction on `n`: the derivative of the `(n + 3)`-rd power is a constant multiple of the
`(n + 2)`-nd, which is `C^(n+1)` by the induction hypothesis.

-/

/-- The power `max (y - c) 0 ^ (n + 2)` of the positive part of `y - c` is `C^(n+1)`. -/
lemma contDiff_max_sub_pow (c : ℝ) (n : ℕ) :
    ContDiff ℝ (n + 1) (fun y : ℝ => max (y - c) 0 ^ (n + 2)) := by
  induction n with
  | zero =>
    have h : ((0 : ℕ) : WithTop ℕ∞) + 1 = 1 := by simp
    rw [h, contDiff_one_iff_deriv]
    refine ⟨fun y => (hasDerivAt_max_sub_pow c 0 y).differentiableAt, ?_⟩
    have hd : deriv (fun y : ℝ => max (y - c) 0 ^ (0 + 2)) =
        fun y => (((0 : ℕ) : ℝ) + 2) * max (y - c) 0 ^ (0 + 1) :=
      funext fun y => (hasDerivAt_max_sub_pow c 0 y).deriv
    rw [hd]
    fun_prop
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun y => (hasDerivAt_max_sub_pow c (n + 1) y).differentiableAt, by simp, ?_⟩
    have hd : deriv (fun y : ℝ => max (y - c) 0 ^ (n + 1 + 2)) =
        fun y => (((n + 1 : ℕ) : ℝ) + 2) * max (y - c) 0 ^ (n + 2) :=
      funext fun y => (hasDerivAt_max_sub_pow c (n + 1) y).deriv
    rw [hd]
    exact ContDiff.mul contDiff_const ih

end
