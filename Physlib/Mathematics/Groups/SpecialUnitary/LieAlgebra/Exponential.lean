/-
Copyright (c) 2026 Nikolai Kashcheev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev
-/
module

public import Physlib.Mathematics.ForMathlib.DataStructures.Matrix.SpecialUnitary
public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.Basic

/-!
# Hermitian generators and special unitary coordinates

The real-linear identification of Hermitian generators with exponential coordinates.

## i. Overview

The existing Hermitian presentation of `su(n)` and the skew-Hermitian model of
the special unitary group are related by multiplication by `i`. The inverse
identification multiplies by `-i`. For a Hermitian generator `H`, use
`Matrix.specialUnitaryGroup.exp (SULieAlgebra.equivModelSubmodule n H)` to obtain
the special unitary matrix `exp (i • H)`.

The Hermitian bracket is `B(H, K) = i (HK - KH)`, so the matrix commutator of
`iH` and `iK` is `i B(H, K)`. This fixes the convention when using the existing
generators as exponential coordinates.

## ii. Key results

* `SULieAlgebra.equivModelSubmodule`: the real-linear identification with the model space.
* `SULieAlgebra.coe_equivModelSubmodule`: the matrix formula for the identification.
* `SULieAlgebra.coe_equivModelSubmodule_symm`: the matrix formula for its inverse.

## iii. Table of contents

- A. The coordinate identification

## iv. References

* None.
-/

public section

noncomputable section

namespace SULieAlgebra

/-!
## A. The coordinate identification
-/

/-- Multiplication by `i` identifies traceless Hermitian generators with the real
skew-Hermitian model of the special unitary group; the inverse multiplies by `-i`. -/
def equivModelSubmodule (n : ℕ) :
    SULieAlgebra n ℂ ≃ₗ[ℝ] Matrix.specialUnitaryGroup.modelSubmodule (Fin n) where
  toFun A := ⟨Complex.I • A.val, by
    rw [Matrix.specialUnitaryGroup.mem_modelSubmodule_iff]
    exact ⟨skewAdjoint.mem_iff.mp
      (Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint.mpr A.star_val_eq),
      by rw [Matrix.trace_smul, A.trace_val_eq_zero, smul_zero]⟩⟩
  invFun A := ofMatrix ((-Complex.I) • A.val)
    (skewAdjoint.negISMul ⟨A.val, A.property.1⟩).property
    (by rw [Matrix.trace_smul,
      (Matrix.specialUnitaryGroup.mem_modelSubmodule_iff.mp A.property).2, smul_zero])
  left_inv A := Subtype.ext (by simp [smul_smul])
  right_inv A := Subtype.ext (by simp [smul_smul])
  map_add' A B := Subtype.ext (smul_add Complex.I A.val B.val)
  map_smul' r A := Subtype.ext (smul_comm Complex.I r A.val)

/-- The matrix of the exponential coordinate of a Hermitian generator is `i` times
that generator. -/
@[simp] lemma coe_equivModelSubmodule {n : ℕ} (A : SULieAlgebra n ℂ) :
    (equivModelSubmodule n A).val = Complex.I • A.val := by
  unfold equivModelSubmodule
  rfl

/-- The inverse identification multiplies a skew-Hermitian coordinate matrix by `-i`. -/
@[simp] lemma coe_equivModelSubmodule_symm {n : ℕ}
    (A : Matrix.specialUnitaryGroup.modelSubmodule (Fin n)) :
    ((equivModelSubmodule n).symm A).val = (-Complex.I) • A.val := by
  unfold equivModelSubmodule
  rfl

end SULieAlgebra
