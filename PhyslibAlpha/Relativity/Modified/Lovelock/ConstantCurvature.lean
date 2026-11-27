/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Modified.Lovelock.Basic
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
/-!

# Constant-curvature Lovelock models

The constant-curvature algebraic tensor and its Gauss–Bonnet and Lanczos values.

## i. Overview

On `R^{ab}_{cd} = κ (δ^a_c δ^b_d - δ^a_d δ^b_c)`, the Gauss–Bonnet density is topological in four
dimensions while the Lanczos variation is non-zero in five.

## ii. Key results

- `constantCurvature` : constant-curvature algebraic tensor.
- `gaussBonnetScalar_constantCurvature_four` : `𝒢 = 24 κ²` in 4D.
- `lanczosTensor_constantCurvature_five` : `H^i_i = -12 κ²` in 5D.

## iii. Table of contents

- A. Constant-curvature models in four and five dimensions

## iv. References

* David Lovelock, *The Four-Dimensionality of Space and the Einstein Tensor*, *Journal of
  Mathematical Physics* 13, pp. 874-876 (1972). [ref: Lovelock1972]
* T. Padmanabhan and D. Kothawala, *Lanczos-Lovelock Models of Gravity*, *Physics Reports* (2013),
  Sec. 2-3 (https://arxiv.org/pdf/1302.2151#page=4). [ref: PadmanabhanKothawala2013]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Lovelock

/-!

## A. Constant-curvature models in four and five dimensions

-/

/-- Constant-curvature model `R^{ab}_{cd} = κ (δ^a_c δ^b_d - δ^a_d δ^b_c)` in `n` dimensions. -/
def constantCurvature (n : ℕ) (κ : ℝ) : AlgebraicCurvature n where
  rUp a b c d :=
    κ * ((if a = c then 1 else 0) * (if b = d then 1 else 0)
      - (if a = d then 1 else 0) * (if b = c then 1 else 0))
  antisymm12 a b c d := by ring
  antisymm34 a b c d := by ring

/-- In `n = 4`, a space of constant sectional curvature `κ` has non-vanishing Gauss–Bonnet
topological density `𝒢 = 24 κ²`, even though its metric variation `H^i_j` vanishes identically. -/
lemma gaussBonnetScalar_constantCurvature_four (κ : ℝ) :
    (constantCurvature 4 κ).gaussBonnetScalar = 24 * κ ^ 2 := by
  simp only [AlgebraicCurvature.gaussBonnetScalar, AlgebraicCurvature.ricciScalar,
    AlgebraicCurvature.ricciSq, AlgebraicCurvature.riemannSq, AlgebraicCurvature.ricciMixed,
    constantCurvature,
    Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  ring

private lemma ricciMixed_constantCurvature_five (κ : ℝ) (i j : Fin 5) :
    (constantCurvature 5 κ).ricciMixed i j = if i = j then 4 * κ else 0 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> decide
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by fin_cases j <;> decide
  simp only [AlgebraicCurvature.ricciMixed, constantCurvature]
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;>
    ring

private lemma ricciScalar_constantCurvature_five (κ : ℝ) :
    (constantCurvature 5 κ).ricciScalar = 20 * κ := by
  rw [← AlgebraicCurvature.trace_ricciMixed]
  simp only [ricciMixed_constantCurvature_five, Fin.sum_univ_five, ↓reduceIte]
  ring

private lemma gaussBonnetScalar_constantCurvature_five (κ : ℝ) :
    (constantCurvature 5 κ).gaussBonnetScalar = 120 * κ ^ 2 := by
  simp only [AlgebraicCurvature.gaussBonnetScalar, AlgebraicCurvature.ricciSq,
    AlgebraicCurvature.riemannSq]
  rw [ricciScalar_constantCurvature_five]
  simp only [ricciMixed_constantCurvature_five]
  simp only [constantCurvature, Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  ring

/-- In `n = 5`, the Gauss–Bonnet variation tensor `H^i_j` is dynamically non-trivial: on a 5D
constant-curvature space it evaluates to `H^i_i = -12 κ²`. -/
lemma lanczosTensor_constantCurvature_five (κ : ℝ) (i : Fin 5) :
    (constantCurvature 5 κ).lanczosTensor i i = -12 * κ ^ 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> decide
  simp only [AlgebraicCurvature.lanczosTensor]
  rw [gaussBonnetScalar_constantCurvature_five, ricciScalar_constantCurvature_five]
  simp only [ricciMixed_constantCurvature_five]
  simp only [constantCurvature]
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;>
    ring

end Lovelock

end Modified

end GeneralRelativity
