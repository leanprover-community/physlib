/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SL2C.Basic
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
/-!

# Fermionic parity

## i. Overview

The homomorphism `SL(2, ℂ) → LorentzGroup 3` is two-to-one, and the nontrivial element of its
kernel is `-1`. Physically it is the rotation by `2π`: it acts as the identity on every tensor,
and as `-1` on every spinor, so it measures the parity of the number of fermionic indices
carried by a quantity. We call it the *fermionic parity*.

Because it lies in the Lorentz group's double cover and projects to the identity, any quantity
required to be invariant under `SL(2, ℂ)` is fixed by it. A quantity carrying an odd number of
spinor indices is negated by it, and therefore vanishes: this is the selection rule that forbids
terms with an odd number of fermions.

## ii. Key results

- `LorentzGroup.fermionicParity` : the nontrivial element of the kernel of the covering
  `SL(2, ℂ) → LorentzGroup 3`.
- `LorentzGroup.toSelfAdjointMap_fermionicParity` : it acts trivially on self-adjoint matrices.
- `LorentzGroup.toLorentzGroup_fermionicParity` : it projects to the identity Lorentz
  transformation.
- `LorentzGroup.fermionicParity_sq` : it squares to one.
- `LorentzGroup.fermionicParity_ne_one` : it is not itself the identity.

## iii. Table of contents

- A. Fermionic parity
- B. The action on vectors and on spinors

-/

@[expose] public section

open Matrix MatrixGroups

namespace LorentzGroup

/-!

## A. Fermionic parity

-/

/-- Fermionic parity: the nontrivial element `-1` of the kernel of the two-to-one homomorphism
  `SL(2, ℂ) → LorentzGroup 3`, that is the rotation by `2π`. It acts trivially on tensors and by
  `-1` on spinors. -/
def fermionicParity : SL(2, ℂ) := -1

/-- Fermionic parity acts trivially on self-adjoint matrices: conjugation by `-1` is the
  identity. -/
lemma toSelfAdjointMap_fermionicParity :
    Lorentz.SL2C.toSelfAdjointMap fermionicParity = LinearMap.id := by
  ext A
  rw [Lorentz.SL2C.toSelfAdjointMap_apply]
  simp [fermionicParity, Matrix.conjTranspose_neg]

/-- Fermionic parity projects to the identity Lorentz transformation: it is invisible on
  tensors. -/
lemma toLorentzGroup_fermionicParity :
    Lorentz.SL2C.toLorentzGroup fermionicParity = 1 := by
  ext i j
  show Lorentz.SL2C.toMatrix fermionicParity i j = _
  rw [Lorentz.SL2C.toMatrix, MonoidHom.coe_mk, OneHom.coe_mk,
    toSelfAdjointMap_fermionicParity, LinearMap.toMatrix_id]
  rfl

@[simp]
lemma fermionicParity_sq : fermionicParity ^ 2 = 1 := by
  rw [fermionicParity, neg_pow, one_pow]
  simp

/-- Fermionic parity is not the identity of `SL(2, ℂ)`: the covering is genuinely
  two-to-one. -/
lemma fermionicParity_ne_one : fermionicParity ≠ 1 := by
  intro h
  have h1 : ((fermionicParity : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = -1 := by
    simp [fermionicParity, SpecialLinearGroup.coe_neg]
  rw [h] at h1
  simp only [SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at h1
  norm_num at h1

/-!

## B. The action on vectors and on spinors

Fermionic parity is invisible on Lorentz vectors and acts by `-1` on Weyl spinors: this is what
makes it measure the parity of the number of spinor indices.

-/

/-- Fermionic parity acts trivially on complex covariant Lorentz vectors, since it projects to
  the identity Lorentz transformation. -/
lemma coℂModule_SL2CRep_fermionicParity :
    Lorentz.CoℂModule.SL2CRep fermionicParity = LinearMap.id := by
  ext v
  rw [Lorentz.CoℂModule.SL2CRep_val]
  show ((LorentzGroup.toComplex (Lorentz.SL2C.toLorentzGroup fermionicParity))⁻¹ᵀ *ᵥ v.val) _ = _
  rw [toLorentzGroup_fermionicParity]
  simp

/-- Fermionic parity acts by `-1` on right-handed Weyl spinors. -/
lemma rightHandedWeyl_rep_fermionicParity :
    Fermion.RightHandedWeyl.rep fermionicParity = -LinearMap.id := by
  refine Fermion.RightHandedWeyl.basis.ext fun i => ?_
  rw [Fermion.RightHandedWeyl.rep_apply_basis]
  simp only [LinearMap.neg_apply, LinearMap.id_coe, id_eq]
  rw [show ((fermionicParity : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) = -1 from rfl]
  fin_cases i <;>
    simp [Matrix.one_apply, Fin.sum_univ_two]

end LorentzGroup
