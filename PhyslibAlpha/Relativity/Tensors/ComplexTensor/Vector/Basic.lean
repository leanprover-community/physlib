/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Basic
public import PhyslibAlpha.Mathematics.RepresentationDual
/-!
# The dual of the complex covector representation

How dual complex covectors transform, on the dual basis.

## i. Overview

A covector representation induces one on the dual space, and a classification of invariant
tensors has to know how the dual basis transforms. For the complex covectors
`Lorentz.ComplexCoVector` the answer is that dual covectors transform contravariantly: the dual
basis vector `e^μ` goes to the combination of dual basis vectors given by the column `μ` of the
complexified Lorentz matrix. This is the complex analogue of
`Lorentz.CoVector.sl2Rep_dual_dualBasis`, and is obtained from
`Representation.dual_apply_dualBasis` with the transposed inverse matrix read off from
`Lorentz.ComplexCoVector.basis_ρ_apply`.

## ii. Key results

- `Lorentz.ComplexCoVector.SL2CRep_dual_dualBasis` : dual complex covectors transform by the columns
  of the complexified Lorentz matrix.

## iii. Table of contents

- A. The dual representation on the dual basis

## iv. References

The complex covector representation is in
`Physlib.Relativity.Tensors.ComplexTensor.Vector.Basic`.

-/

@[expose] public section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

namespace Lorentz

/-!

## A. The dual representation on the dual basis

-/

/-- The dual of the complex covector representation on the dual basis: dual covectors
  transform contravariantly, by the columns of the (complexified) Lorentz matrix. The
  complex analogue of `Lorentz.CoVector.sl2Rep_dual_dualBasis`. -/
lemma ComplexCoVector.SL2CRep_dual_dualBasis (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) :
    Lorentz.ComplexCoVector.SL2CRep.dual Λ (Lorentz.ComplexCoVector.basis.dualBasis μ) =
      ∑ j, (((Lorentz.SL2C.toLorentzGroup Λ).1 j μ : ℝ) : ℂ) •
        Lorentz.ComplexCoVector.basis.dualBasis j := by
  refine Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => (((Lorentz.SL2C.toLorentzGroup Λ).1 j l : ℝ) : ℂ))
    (fun j => ?_)
  have hexp : Lorentz.ComplexCoVector.SL2CRep Λ⁻¹ (Lorentz.ComplexCoVector.basis j) =
      ∑ l, (LinearMap.toMatrix Lorentz.ComplexCoVector.basis Lorentz.ComplexCoVector.basis
        (Lorentz.ComplexCoVector.SL2CRep Λ⁻¹)) l j • Lorentz.ComplexCoVector.basis l := by
    conv_lhs => rw [← Lorentz.ComplexCoVector.basis.sum_repr
      (Lorentz.ComplexCoVector.SL2CRep Λ⁻¹ (Lorentz.ComplexCoVector.basis j))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.toMatrix_apply]
  rw [hexp]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [Lorentz.ComplexCoVector.basis_ρ_apply, map_inv, Matrix.transpose_apply,
    ← LorentzGroup.toComplex_inv, Matrix.inv_inv_of_invertible]
  rfl

end Lorentz
