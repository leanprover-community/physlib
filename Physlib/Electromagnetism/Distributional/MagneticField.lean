/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Distributional.FieldStrength
public import Physlib.Electromagnetism.Distributional.VectorPotential
/-!

# The Magnetic Field

## i. Overview

In general dimensions we define the magnetic field matrix from the spatial components of the
field strength matrix. This is an antisymmetric matrix. We define it
in this module for distributions.

## ii. Key results

- `DistElectromagneticPotential.magneticFieldMatrix` : The magnetic field matrix from the
  electromagnetic potential in general spatial dimensions.

## iii. Table of contents

- A. Magnetic field matrix for distributions
  - A.1. Magnetic field matrix in terms of vector potentials
  - A.2. The magnetic field matrix in terms of the field strength
  - A.3. Magnetic field matrix in 1d

## iv. References

* None.
-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor

/-!

## A. Magnetic field matrix for distributions

-/

namespace DistElectromagneticPotential
open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix SchwartzMap Lorentz
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-- The magnetic field matrix of an electromagnetic potential which is a distribution. -/
noncomputable def magneticFieldMatrix {d} (c : SpeedOfLight) :
    DistElectromagneticPotential d →ₗ[ℝ]
    (Time × Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d) ⊗[ℝ] EuclideanSpace ℝ (Fin d)) where
  toFun A :=
    ⟨TensorProduct.map (Lorentz.Vector.spatialCLM d).toLinearMap
      (Lorentz.Vector.spatialCLM d).toLinearMap, by continuity⟩ ∘L
    distTimeSlice c A.fieldStrength
  map_add' A1 A2 := by
    ext ε
    simp
  map_smul' r A := by
    ext ε
    simp

/-!

### A.1. Magnetic field matrix in terms of vector potentials

-/

lemma magneticFieldMatrix_eq_vectorPotential {c : SpeedOfLight}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(Time × Space d, ℝ)) :
    A.magneticFieldMatrix c ε = ∑ i, ∑ j,
    (Space.distSpaceDeriv j (A.vectorPotential c) ε i -
      Space.distSpaceDeriv i (A.vectorPotential c) ε j) •
    EuclideanSpace.basisFun (Fin d) ℝ i ⊗ₜ[ℝ] EuclideanSpace.basisFun (Fin d) ℝ j := by
  simp only [magneticFieldMatrix, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_mk', Function.comp_apply, distTimeSlice_apply, fieldStrength_eq_basis,
    Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, inl_0_inl_0, one_mul, inr_i_inr_i, neg_mul, sub_neg_eq_add, sub_self,
    zero_smul, zero_add, map_add, map_sum, map_smul, map_tmul, ContinuousLinearMap.coe_coe,
    Lorentz.Vector.spatialCLM_basis_sum_inl, Lorentz.Vector.spatialCLM_basis_sum_inr,
    EuclideanSpace.basisFun_apply, zero_tmul, smul_zero, Finset.sum_const_zero, tmul_zero]
  simp [← distTimeSlice_apply, distTimeSlice_distDeriv_inr, vectorPotential,
  Space.distSpaceDeriv_apply_CLM, Lorentz.Vector.spatialCLM, neg_add_eq_sub]

lemma magneticFieldMatrix_basis_repr_eq_vector_potential {c : SpeedOfLight}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(Time × Space d, ℝ)) (i j : Fin d) :
    ((PiLp.basisFun 2 ℝ (Fin d)).tensorProduct (PiLp.basisFun 2 ℝ (Fin d))).repr
        (A.magneticFieldMatrix c ε) (i, j) =
      Space.distSpaceDeriv j (A.vectorPotential c) ε i -
      Space.distSpaceDeriv i (A.vectorPotential c) ε j := by
  simp [magneticFieldMatrix_eq_vectorPotential]

lemma magneticFieldMatrix_distSpaceDeriv_basis_repr_eq_vector_potential {c : SpeedOfLight}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(Time × Space d, ℝ)) (i j k : Fin d) :
    ((PiLp.basisFun 2 ℝ (Fin d)).tensorProduct (PiLp.basisFun 2 ℝ (Fin d))).repr
    (Space.distSpaceDeriv k (A.magneticFieldMatrix c) ε) (i, j) =
    Space.distSpaceDeriv k (Space.distSpaceDeriv j (A.vectorPotential c)) ε i -
    Space.distSpaceDeriv k (Space.distSpaceDeriv i (A.vectorPotential c)) ε j := by
  simp [Space.distSpaceDeriv_apply', magneticFieldMatrix_basis_repr_eq_vector_potential]
  ring

/-!

### A.2. The magnetic field matrix in terms of the field strength

-/

lemma magneticFieldMatrix_basis_repr_eq_fieldStrength {c : SpeedOfLight}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(Time × Space d, ℝ)) (i j : Fin d) :
    ((PiLp.basisFun 2 ℝ (Fin d)).tensorProduct (PiLp.basisFun 2 ℝ (Fin d))).repr
        (A.magneticFieldMatrix c ε) (i, j) =
      (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr
        (distTimeSlice c A.fieldStrength ε) (Sum.inr i, Sum.inr j) := by
  simp only [magneticFieldMatrix_eq_vectorPotential, EuclideanSpace.basisFun_apply, map_sum,
    map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
    Basis.tensorProduct_repr_tmul_apply, PiLp.basisFun_repr, PiLp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero, distTimeSlice_apply,
    fieldStrength_basis_repr_eq_single, inr_i_inr_i, neg_mul, one_mul, sub_neg_eq_add]
  simp only [vectorPotential, Vector.spatialCLM, LinearMap.coe_mk, AddHom.coe_mk,
    Space.distSpaceDeriv_apply_CLM, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_mk',
    Function.comp_apply, ← distTimeSlice_apply, distTimeSlice_distDeriv_inr]
  ring

/-!

### A.3. Magnetic field matrix in 1d

-/

@[simp]
lemma magneticFieldMatrix_one_dim_eq_zero {c : SpeedOfLight}
    (A : DistElectromagneticPotential 1) :
    A.magneticFieldMatrix c = 0 := by
  ext ε
  simp [magneticFieldMatrix_eq_vectorPotential]

end DistElectromagneticPotential
end Electromagnetism
