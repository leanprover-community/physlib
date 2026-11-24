/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.Tensorial
/-!
# Complex four-vectors as tensors

Complex four-vectors are the complex Lorentz tensors with one contravariant index.

## i. Overview

A complex four-vector is a complex Lorentz tensor with a single index of colour `.up`, and
`fromSingleT` is the linear equivalence between the two. It makes `Lorentz.ComplexVector` a
tensorial type, so that tensor products of it with other tensorial types are tensorial through
`TensorSpecies.Tensorial.prod`. The equivalence carries the action of `SL(2, ℂ)` on four-vectors to
the action on tensors, and the basis vector `e_μ` to the basis tensor with the single component
`μ` (A).

## ii. Key results

- `Lorentz.ComplexVector.tensorial` : complex four-vectors are the tensors with one index `.up`.
- `Lorentz.ComplexVector.toTensor_SL2CRep` : the equivalence intertwines the two actions.
- `Lorentz.ComplexVector.toTensor_basis` : the basis vector `e_μ` is the basis tensor with
  component `μ`.

## iii. Table of contents

- A. The tensorial instance

## iv. References

The tensorial class is in `Physlib.Relativity.Tensors.Tensorial`. The instance for real
four-vectors is in `Physlib.Relativity.Tensors.RealTensor.Vector.Tensorial`.

-/

@[expose] public section

namespace Lorentz.ComplexVector

open MatrixGroups TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensorial complexLorentzTensor

/-!

## A. The tensorial instance

-/

/-- Complex four-vectors are the complex Lorentz tensors with one index `.up`, through
  `fromSingleT`. -/
noncomputable instance tensorial : Tensorial complexLorentzTensor ![.up] ComplexVector where
  toTensor := fromSingleT (S := complexLorentzTensor) (c := .up)

lemma toTensor_eq_fromSingleT (v : ComplexVector) :
    toTensor v = fromSingleT (S := complexLorentzTensor) (c := .up) v := rfl

/-- The equivalence with the one-index tensors carries the action of `SL(2, ℂ)` on four-vectors to
  the action on tensors. -/
lemma toTensor_SL2CRep (g : SL(2,ℂ)) (v : ComplexVector) :
    toTensor (SL2CRep g v) = g • toTensor v := by
  rw [toTensor_eq_fromSingleT, toTensor_eq_fromSingleT, actionT_fromSingleT]

/-- The basis vector `e_μ` is the basis tensor with the single component `μ`. -/
lemma toTensor_basis (μ : Fin 1 ⊕ Fin 3) :
    toTensor (basis μ) = Tensor.basis (S := complexLorentzTensor) ![.up]
      (ComponentIdx.single.symm μ) := by
  rw [toTensor_eq_fromSingleT, fromSingleT_eq_pureT, Tensor.basis_apply]
  congr 1
  funext i
  fin_cases i
  rfl

end Lorentz.ComplexVector
