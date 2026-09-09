/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samyak Rai, Joseph Tooby-Smith
-/
module

public import Mathlib.Data.NNReal.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
/-!

# Planck's constant

In this module we define the reduced Planck's constant `ℏ` as a positive real number.
and also define the Planck's constant `h` also to be a positive real number with the
definition `h = 2 π ℏ`.

-/

@[expose] public section

open NNReal

namespace Constants

/-- The value of the reduced Planck's constant in units of J.s. -/
def ℏ : Subtype fun x : ℝ => 0 < x := ⟨1.054571817e-34, by norm_num⟩

/-- reduced Planck's constant is positive. -/
@[simp]
lemma ℏ_pos : 0 < (ℏ : ℝ) := ℏ.2

/-- reduced Planck's constant is non-negative. -/
@[simp]
lemma ℏ_nonneg : 0 ≤ (ℏ : ℝ) := le_of_lt ℏ.2

/-- reduced Planck's constant is not equal to zero. -/
@[simp]
lemma ℏ_ne_zero : (ℏ : ℝ) ≠ 0 := ne_of_gt ℏ.2

/-- The definition of Planck's constant in terms of Reduced Planck's constant,
 defined as `2 π ℏ` -/
noncomputable def h : Subtype fun x : ℝ => 0 < x := ⟨2 * Real.pi * (ℏ : ℝ),
mul_pos (mul_pos (by norm_num) Real.pi_pos) ℏ_pos⟩

/-- Planck's constant is positive. -/
@[simp]
lemma h_pos : 0 < (h : ℝ) := h.2

/-- Planck's constant is non-negative. -/
@[simp]
lemma h_nonneg : 0 ≤ (h : ℝ) := le_of_lt h.2

/-- Planck's constnat is not equal to zero. -/
@[simp]
lemma h_ne_zero : (h : ℝ) ≠ 0 := ne_of_gt h.2

end Constants
