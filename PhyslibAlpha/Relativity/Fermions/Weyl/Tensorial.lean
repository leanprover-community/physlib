/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.Tensorial
/-!
# Weyl fermions as tensors

Left- and right-handed Weyl fermions are the complex Lorentz tensors with one undotted or one
dotted index.

## i. Overview

A left-handed Weyl fermion is a complex Lorentz tensor with a single index of colour `.upL`, and a
right-handed one a tensor with a single index of colour `.upR`. In both cases `fromSingleT` is the
linear equivalence between the two. It makes `Fermion.LeftHandedWeyl` and
`Fermion.RightHandedWeyl` tensorial types, so that tensor products of them with other tensorial
types are tensorial through `TensorSpecies.Tensorial.prod`. The equivalence carries the action of
`SL(2, ℂ)` on spinors to the action on tensors, and the basis spinor `e_a` to the basis tensor with
the single component `a`, for left-handed (A) and right-handed (B) fermions alike.

## ii. Key results

- `Fermion.LeftHandedWeyl.tensorial` : left-handed Weyl fermions are the tensors with one index
  `.upL`.
- `Fermion.RightHandedWeyl.tensorial` : right-handed Weyl fermions are the tensors with one index
  `.upR`.
- `Fermion.LeftHandedWeyl.toTensor_basis`, `Fermion.RightHandedWeyl.toTensor_basis` : the basis
  spinor `e_a` is the basis tensor with component `a`.

## iii. Table of contents

- A. Left-handed Weyl fermions
- B. Right-handed Weyl fermions

## iv. References

The tensorial class is in `Physlib.Relativity.Tensors.Tensorial`. The tensorial instance of complex
four-vectors is in `PhyslibAlpha.Relativity.Tensors.ComplexTensor.Vector.Tensorial`.

-/

@[expose] public section

namespace Fermion

open MatrixGroups TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensorial complexLorentzTensor

/-!

## A. Left-handed Weyl fermions

-/

namespace LeftHandedWeyl

/-- Left-handed Weyl fermions are the complex Lorentz tensors with one index `.upL`, through
  `fromSingleT`. -/
noncomputable instance tensorial : Tensorial complexLorentzTensor ![.upL] LeftHandedWeyl where
  toTensor := fromSingleT (S := complexLorentzTensor) (c := .upL)

lemma toTensor_eq_fromSingleT (ψ : LeftHandedWeyl) :
    toTensor ψ = fromSingleT (S := complexLorentzTensor) (c := .upL) ψ := rfl

/-- The equivalence with the one-index tensors carries the action of `SL(2, ℂ)` on left-handed
  spinors to the action on tensors. -/
lemma toTensor_rep (g : SL(2,ℂ)) (ψ : LeftHandedWeyl) :
    toTensor (rep g ψ) = g • toTensor ψ := by
  rw [toTensor_eq_fromSingleT, toTensor_eq_fromSingleT, actionT_fromSingleT]

/-- The basis spinor `e_a` is the basis tensor with the single component `a`. -/
lemma toTensor_basis (a : Fin 2) :
    toTensor (basis a) = Tensor.basis (S := complexLorentzTensor) ![.upL]
      (ComponentIdx.single.symm a) := by
  rw [toTensor_eq_fromSingleT, fromSingleT_eq_pureT, Tensor.basis_apply]
  congr 1
  funext i
  fin_cases i
  rfl

end LeftHandedWeyl

/-!

## B. Right-handed Weyl fermions

-/

namespace RightHandedWeyl

/-- Right-handed Weyl fermions are the complex Lorentz tensors with one index `.upR`, through
  `fromSingleT`. -/
noncomputable instance tensorial : Tensorial complexLorentzTensor ![.upR] RightHandedWeyl where
  toTensor := fromSingleT (S := complexLorentzTensor) (c := .upR)

lemma toTensor_eq_fromSingleT (ψ : RightHandedWeyl) :
    toTensor ψ = fromSingleT (S := complexLorentzTensor) (c := .upR) ψ := rfl

/-- The equivalence with the one-index tensors carries the action of `SL(2, ℂ)` on right-handed
  spinors to the action on tensors. -/
lemma toTensor_rep (g : SL(2,ℂ)) (ψ : RightHandedWeyl) :
    toTensor (rep g ψ) = g • toTensor ψ := by
  rw [toTensor_eq_fromSingleT, toTensor_eq_fromSingleT, actionT_fromSingleT]

/-- The basis spinor `e_a` is the basis tensor with the single component `a`. -/
lemma toTensor_basis (a : Fin 2) :
    toTensor (basis a) = Tensor.basis (S := complexLorentzTensor) ![.upR]
      (ComponentIdx.single.symm a) := by
  rw [toTensor_eq_fromSingleT, fromSingleT_eq_pureT, Tensor.basis_apply]
  congr 1
  funext i
  fin_cases i
  rfl

end RightHandedWeyl

end Fermion
