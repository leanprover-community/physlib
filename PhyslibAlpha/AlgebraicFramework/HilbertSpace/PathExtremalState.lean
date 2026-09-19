/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib

/-!

# The extremal state of the path observables

The unit vector `ψ_d ∈ ℂ^d` with coordinates `(-i)^j √(2 / (d + 1)) sin ((j + 1) π / (d + 1))`.

-/

@[expose] public section

open Finset

namespace PathObservables

/-- The angle `π / (d + 1)`. -/
noncomputable def angle (d : ℕ) : ℝ := Real.pi / ((d : ℝ) + 1)

/-- The unnormalised extremal vector, with coordinates `(-i)^j sin ((j + 1) π / (d + 1))`. -/
noncomputable def sineMode (d : ℕ) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun j => (-Complex.I) ^ (j : ℕ) * (Real.sin (((j : ℕ) + 1) * angle d) : ℂ)

/-- The cosines `cos (2π k / n)` sum to zero over a full period. -/
lemma sum_cos_two_pi_div {n : ℕ} (hn : 1 < n) :
    ∑ k ∈ range n, Real.cos (2 * Real.pi * k / n) = 0 := by
  have hn0 : n ≠ 0 := by omega
  have h := (Complex.isPrimitiveRoot_exp n hn0).geom_sum_eq_zero hn
  have h' := congrArg Complex.re h
  rw [Complex.re_sum] at h'
  simp only [← Complex.exp_nat_mul, Complex.zero_re] at h'
  rw [← h']
  refine sum_congr rfl fun k _ => ?_
  rw [← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

/-- The squared sines of the multiples of `π / (d + 1)` sum to `(d + 1) / 2`. -/
lemma sum_sin_sq_angle (d : ℕ) (hd : 1 ≤ d) :
    ∑ j : Fin d, Real.sin (((j : ℕ) + 1) * angle d) ^ 2 = ((d : ℝ) + 1) / 2 := by
  have h := sum_cos_two_pi_div (n := d + 1) (by omega)
  push_cast at h
  have hsq : ∀ k : ℕ, Real.sin (k * angle d) ^ 2 =
      (1 - Real.cos (2 * Real.pi * k / ((d : ℝ) + 1))) / 2 := by
    intro k
    rw [Real.sin_sq_eq_half_sub, show 2 * (k * angle d) = 2 * Real.pi * k / ((d : ℝ) + 1) by
      unfold angle; ring]
    ring
  have hL : ∑ k ∈ range (d + 1), (1 - Real.cos (2 * Real.pi * k / ((d : ℝ) + 1))) / 2 =
      ((d : ℝ) + 1) / 2 := by
    rw [← sum_div, sum_sub_distrib, h]
    simp
  have hS : ∑ k ∈ range (d + 1), Real.sin ((k : ℝ) * angle d) ^ 2 = ((d : ℝ) + 1) / 2 := by
    rw [sum_congr rfl fun k _ => hsq k]
    exact hL
  have h0 := sum_range_succ' (fun k => Real.sin ((k : ℝ) * angle d) ^ 2) d
  rw [hS] at h0
  rw [Fin.sum_univ_eq_sum_range (fun j => Real.sin (((j : ℕ) + 1) * angle d) ^ 2) d]
  simpa using h0.symm

/-- The squared norm of the unnormalised extremal vector is `(d + 1) / 2`. -/
lemma norm_sq_sineMode (d : ℕ) (hd : 1 ≤ d) : ‖sineMode d‖ ^ 2 = ((d : ℝ) + 1) / 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← sum_sin_sq_angle d hd]
  refine sum_congr rfl fun j _ => ?_
  rw [sineMode, WithLp.ofLp_toLp, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The extremal state: the unit vector `√(2 / (d + 1)) • sineMode d`. -/
noncomputable def extremalState (d : ℕ) : EuclideanSpace ℂ (Fin d) :=
  ((Real.sqrt (2 / ((d : ℝ) + 1)) : ℝ) : ℂ) • sineMode d

/-- The extremal state is a unit vector. -/
lemma norm_extremalState (d : ℕ) (hd : 1 ≤ d) : ‖extremalState d‖ = 1 := by
  have hpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hs : ‖sineMode d‖ = Real.sqrt (((d : ℝ) + 1) / 2) := by
    rw [← norm_sq_sineMode d hd, Real.sqrt_sq (norm_nonneg _)]
  rw [extremalState, norm_smul, hs, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    ← Real.sqrt_mul (by positivity)]
  rw [show 2 / ((d : ℝ) + 1) * (((d : ℝ) + 1) / 2) = 1 by field_simp]
  simp

end PathObservables
