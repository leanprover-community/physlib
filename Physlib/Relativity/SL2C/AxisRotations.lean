/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
/-!
# Coordinate-axis rotations in `SL(2,ℂ)`

This file defines chosen `SL(2,ℂ)` rotations carrying the `z`-axis to a selected coordinate axis.
The spatial-axis convention is `0 = x`, `1 = y`, and `2 = z`; consequently, the rotation associated
with axis `2` is the identity.

Conjugation by these rotations transports a matrix written in the diagonal `z`-axis basis to
the corresponding coordinate-axis basis. This provides the common change of basis used by
coordinate-axis boosts and later constructions based on diagonal representatives.

The main declarations are:

- `rotationZToAxis`, the indexed family of rotations;
- `rotationZToAxis_zero_apply` and its companions, their matrix entries;
- `rotationZToAxis_zero_mul_diagonal_mul_inv` and its companions, their action on a
  diagonal matrix.
-/

@[expose] public section

namespace Lorentz.SL2C

open Matrix MatrixGroups

/-- The `SL(2,ℂ)` rotation carrying the `z`-axis to axis `i`. -/
noncomputable def rotationZToAxis : Fin 3 → SL(2,ℂ)
  | 0 =>
      ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -1; 1, 1], by
        rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow]
        norm_num [← Complex.ofReal_pow, Real.sq_sqrt]⟩
  | 1 =>
      ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, Complex.I; Complex.I, 1], by
        rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow,
          Complex.I_mul_I]
        norm_num [← Complex.ofReal_pow, Real.sq_sqrt]⟩
  | 2 => 1

/-- The matrix entries of the rotation carrying the `z`-axis to the `x`-axis. -/
@[simp] lemma rotationZToAxis_zero_apply (j k : Fin 2) :
    (rotationZToAxis 0).1 j k =
      ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -1; 1, 1]) j k := rfl

/-- The matrix entries of the rotation carrying the `z`-axis to the `y`-axis. -/
@[simp] lemma rotationZToAxis_one_apply (j k : Fin 2) :
    (rotationZToAxis 1).1 j k =
      ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, Complex.I; Complex.I, 1]) j k := rfl

/-- The rotation carrying the `z`-axis to itself is the identity matrix. -/
@[simp] lemma rotationZToAxis_two_apply (j k : Fin 2) :
    (rotationZToAxis 2).1 j k = (1 : Matrix (Fin 2) (Fin 2) ℂ) j k := rfl

/-- The matrix entries of the inverse rotation from the `x`-axis to the `z`-axis. -/
@[simp] lemma rotationZToAxis_zero_inv_apply (j k : Fin 2) :
    ((rotationZToAxis 0)⁻¹).1 j k =
      ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, 1; -1, 1]) j k := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases j <;> fin_cases k <;> simp [rotationZToAxis]

/-- The matrix entries of the inverse rotation from the `y`-axis to the `z`-axis. -/
@[simp] lemma rotationZToAxis_one_inv_apply (j k : Fin 2) :
    ((rotationZToAxis 1)⁻¹).1 j k =
      ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -Complex.I; -Complex.I, 1]) j k := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases j <;> fin_cases k <;> simp [rotationZToAxis]

/-- The inverse rotation from the `z`-axis to itself is the identity matrix. -/
@[simp] lemma rotationZToAxis_two_inv_apply (j k : Fin 2) :
    ((rotationZToAxis 2)⁻¹).1 j k = (1 : Matrix (Fin 2) (Fin 2) ℂ) j k := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases j <;> fin_cases k <;> simp [rotationZToAxis]

/-- Conjugating `diag(a, b)` by the rotation to the `x`-axis expresses it in the `x`-axis
basis. -/
lemma rotationZToAxis_zero_mul_diagonal_mul_inv (a b : ℂ) :
    (rotationZToAxis 0).1 * !![a, 0; 0, b] * ((rotationZToAxis 0)⁻¹).1 =
      !![(a + b) / 2, (a - b) / 2; (a - b) / 2, (a + b) / 2] := by
  have hsqrt_ne : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by simp
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rotationZToAxis_zero_apply,
      rotationZToAxis_zero_inv_apply] <;>
    simp <;>
    field_simp <;>
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt] <;>
    ring

/-- Conjugating `diag(a, b)` by the rotation to the `y`-axis expresses it in the `y`-axis
basis. -/
lemma rotationZToAxis_one_mul_diagonal_mul_inv (a b : ℂ) :
    (rotationZToAxis 1).1 * !![a, 0; 0, b] * ((rotationZToAxis 1)⁻¹).1 =
      !![(a + b) / 2, -Complex.I * (a - b) / 2;
        Complex.I * (a - b) / 2, (a + b) / 2] := by
  have hsqrt_ne : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by simp
  ext j k
  fin_cases j <;> fin_cases k
  all_goals
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rotationZToAxis_one_apply,
      rotationZToAxis_one_inv_apply]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.smul_apply, of_apply, cons_val',
      cons_val_zero, cons_val_fin_one, smul_eq_mul, mul_one, cons_val_one, mul_zero,
      add_zero, zero_add, mul_neg, neg_mul, Fin.mk_one]
    field_simp
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
  all_goals ring

/-- Conjugating `diag(a, b)` by the identity rotation leaves it unchanged. -/
lemma rotationZToAxis_two_mul_diagonal_mul_inv (a b : ℂ) :
    (rotationZToAxis 2).1 * !![a, 0; 0, b] * ((rotationZToAxis 2)⁻¹).1 =
      !![a, 0; 0, b] := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rotationZToAxis_two_apply,
      rotationZToAxis_two_inv_apply] <;>
    simp [Matrix.one_apply]

end Lorentz.SL2C

end
