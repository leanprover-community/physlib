/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib

/-!

# Weighted geometric sums at a primitive root of unity

The sums `∑_{k<N} k zᵏ` and `∑_{k<N} k² zᵏ` at `z = exp (2π i / N)`.

-/

@[expose] public section

open Finset

namespace PathObservables

/-- `∑_{k<n} k xᵏ` against `(x - 1)²`. -/
lemma sum_mul_pow_mul_sq (x : ℂ) (n : ℕ) :
    (∑ k ∈ range n, (k : ℂ) * x ^ k) * (x - 1) ^ 2 =
      x + ((n : ℂ) - 1) * x ^ (n + 1) - n * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih]
    push_cast
    ring

/-- `∑_{k<n} k² xᵏ` against `(x - 1)³`. -/
lemma sum_sq_mul_pow_mul_cube (x : ℂ) (n : ℕ) :
    (∑ k ∈ range n, (k : ℂ) ^ 2 * x ^ k) * (x - 1) ^ 3 =
      ((n : ℂ) - 1) ^ 2 * x ^ (n + 2) + (1 + 2 * n - 2 * (n : ℂ) ^ 2) * x ^ (n + 1) +
        (n : ℂ) ^ 2 * x ^ n - x ^ 2 - x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih]
    push_cast
    ring

/-! ## Sums at the primitive root -/

/-- The primitive `N`-th root of unity `exp (2π i / N)`. -/
noncomputable def root (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

lemma root_pow (N k : ℕ) :
    root N ^ k = Complex.exp (((2 * Real.pi * k / N : ℝ) : ℂ) * Complex.I) := by
  rw [root, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma root_pow_re (N k : ℕ) : (root N ^ k).re = Real.cos (2 * Real.pi * k / N) := by
  rw [root_pow, Complex.exp_ofReal_mul_I_re]

lemma root_pow_im (N k : ℕ) : (root N ^ k).im = Real.sin (2 * Real.pi * k / N) := by
  rw [root_pow, Complex.exp_ofReal_mul_I_im]

lemma root_ne_one {N : ℕ} (hN : 2 ≤ N) : root N ≠ 1 :=
  (Complex.isPrimitiveRoot_exp N (by omega)).ne_one hN

lemma root_pow_self (N : ℕ) (hN : N ≠ 0) : root N ^ N = 1 :=
  (Complex.isPrimitiveRoot_exp N hN).pow_eq_one

lemma sum_mul_root {N : ℕ} (hN : 2 ≤ N) :
    (∑ k ∈ range N, (k : ℂ) * root N ^ k) * (root N - 1) = N := by
  have h := sum_mul_pow_mul_sq (root N) N
  have h1 := root_pow_self N (by omega)
  have hz := sub_ne_zero.mpr (root_ne_one hN)
  have h2 : root N ^ (N + 1) = root N := by rw [pow_succ, h1, one_mul]
  rw [h2, h1] at h
  refine mul_right_cancel₀ hz ?_
  linear_combination h

lemma sum_sq_mul_root {N : ℕ} (hN : 2 ≤ N) :
    (∑ k ∈ range N, ((k ^ 2 : ℕ) : ℂ) * root N ^ k) * (root N - 1) ^ 2 =
      N * (((N : ℂ) - 2) * root N - N) := by
  push_cast
  have h := sum_sq_mul_pow_mul_cube (root N) N
  have h1 := root_pow_self N (by omega)
  have hz := sub_ne_zero.mpr (root_ne_one hN)
  have h2 : root N ^ (N + 1) = root N := by rw [pow_succ, h1, one_mul]
  have h3 : root N ^ (N + 2) = root N ^ 2 := by rw [pow_add, h1, one_mul]
  rw [h3, h2, h1] at h
  refine mul_right_cancel₀ hz ?_
  linear_combination h

end PathObservables
