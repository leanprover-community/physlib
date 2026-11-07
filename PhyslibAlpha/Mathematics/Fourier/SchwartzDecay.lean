/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import PhyslibAlpha.Mathematics.Distribution.SchwartzPointwise

/-!

# The integral of a Fourier transform is bounded by Schwartz seminorms

The `L¹` norm of the Fourier transform of a Schwartz function is bounded by finitely many
Schwartz seminorms of the function.

## i. Overview

The Fourier transform is continuous on Schwartz space. A weighted supremum of the transform is
therefore bounded by finitely many seminorms of the function. The weight `(1 + ‖ξ‖)^n` with
`n` above the dimension makes the transform integrable. The constants do not depend on the
function.

## ii. Key results

- `exists_integral_norm_fourier_le` : the bound of `∫ ‖𝓕 g‖` by seminorms of `g`.

## iii. Table of contents

- A. The bound

## iv. References

None.

## A. The bound

- `exists_integral_norm_fourier_le` : the bound of `∫ ‖𝓕 g‖` by seminorms of `g`.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap FourierTransform
open MeasureTheory Module

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The `L¹` norm of a Fourier transform.** The integral of `‖𝓕 g‖` is bounded by a constant
times a finite supremum of Schwartz seminorms of `g`. -/
lemma exists_integral_norm_fourier_le :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ g : 𝓢(E, F),
      ∫ ξ : E, ‖𝓕 g ξ‖ ≤ C * (S.sup (schwartzSeminormFamily ℂ E F)) g := by
  set n : ℕ := finrank ℝ E + 1 with hn
  let q : Seminorm ℂ 𝓢(E, F) :=
    ((SchwartzMap.seminorm ℂ 0 0) + (SchwartzMap.seminorm ℂ n 0)).comp
      (SchwartzMap.fourierTransformCLM ℂ).toLinearMap
  have hq : Continuous q := by
    have h1 : Continuous (SchwartzMap.seminorm ℂ 0 0 : Seminorm ℂ 𝓢(E, F)) :=
      (schwartz_withSeminorms ℂ E F).continuous_seminorm (0, 0)
    have h2 : Continuous (SchwartzMap.seminorm ℂ n 0 : Seminorm ℂ 𝓢(E, F)) :=
      (schwartz_withSeminorms ℂ E F).continuous_seminorm (n, 0)
    exact (h1.add h2).comp (SchwartzMap.fourierTransformCLM ℂ).continuous
  obtain ⟨S, c, -, hS⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E F) q hq
  have hnr : (finrank ℝ E : ℝ) < (n : ℝ) := by rw [hn]; push_cast; linarith
  have hint := integrable_one_add_norm (E := E) (μ := volume) hnr
  refine ⟨S, 2 ^ (n - 1) * c * ∫ ξ : E, (1 + ‖ξ‖) ^ (-(n : ℝ)),
    mul_nonneg (mul_nonneg (by positivity) c.2) (integral_nonneg fun ξ => by positivity),
    fun g => ?_⟩
  have hqg : q g ≤ c * (S.sup (schwartzSeminormFamily ℂ E F)) g := by
    simpa [NNReal.smul_def] using hS g
  have hpt : ∀ ξ : E, ‖𝓕 g ξ‖ ≤ 2 ^ (n - 1) * q g * (1 + ‖ξ‖) ^ (-(n : ℝ)) := fun ξ =>
    norm_le_rpow_neg_mul ℂ (𝓕 g) n ξ
  calc ∫ ξ : E, ‖𝓕 g ξ‖
      ≤ ∫ ξ : E, 2 ^ (n - 1) * q g * (1 + ‖ξ‖) ^ (-(n : ℝ)) :=
        integral_mono (𝓕 g).integrable.norm (hint.const_mul _) hpt
    _ = 2 ^ (n - 1) * q g * ∫ ξ : E, (1 + ‖ξ‖) ^ (-(n : ℝ)) := integral_const_mul _ _
    _ ≤ 2 ^ (n - 1) * (c * (S.sup (schwartzSeminormFamily ℂ E F)) g) *
          ∫ ξ : E, (1 + ‖ξ‖) ^ (-(n : ℝ)) := by
        gcongr
    _ = _ := by ring

end SchwartzMap
