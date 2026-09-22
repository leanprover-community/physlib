/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Distributional.Basic
public import Physlib.Relativity.Tensors.RealTensor.Metrics.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
/-!

# The Field Strength Tensor

## i. Overview

In this module we define the field strength tensor in terms of the electromagnetic potential.

## ii. Key results

- `DistElectromagneticPotential.fieldStrength` : The field strength for
  electromagnetic potentials which are distributions.

## iii. Table of contents

- A. Field strength for distributions
  - A.1. Auxiliary definition of field strength for distributions, with no linearity
  - A.2. The definition of the field strength
  - A.3. Field strength written in terms of a basis
  - A.4. Equivariance of the field strength for distributions

## iv. References

* None.
-/

@[expose] public section
namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor

/-!

## A. Field strength for distributions

-/

namespace DistElectromagneticPotential
open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct Lorentz
open minkowskiMatrix SchwartzMap
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

### A.1. Auxiliary definition of field strength for distributions, with no linearity

-/

/-- An auxiliary definition for the field strength of an electromagnetic potential
  based on a distribution. On Schwartz maps this has the same value as the field strength
  tensor, but no linearity or continuous properties built in. -/
noncomputable def fieldStrengthAux {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) : Lorentz.Vector d ⊗[ℝ] Lorentz.Vector d :=
  Tensorial.toTensor.symm
      (permT id (IsReindexing.auto) {(η d | μ μ' ⊗ distTensorDeriv A ε | μ' ν) + -
      (η d | ν ν' ⊗ distTensorDeriv A ε | ν' μ)}ᵀ)

lemma fieldStrengthAux_eq_add {d} (A : DistElectromagneticPotential d) (ε : 𝓢(SpaceTime d, ℝ)) :
    fieldStrengthAux A ε =
    Tensorial.toTensor.symm
      (permT id (IsReindexing.auto) {(η d | μ μ' ⊗ distTensorDeriv A ε | μ' ν)}ᵀ)
    - Tensorial.toTensor.symm (permT ![1, 0] (IsReindexing.auto)
      {(η d | μ μ' ⊗ distTensorDeriv A ε | μ' ν)}ᵀ) := by
  rw [fieldStrengthAux]
  simp only [map_add, map_neg]
  rw [sub_eq_add_neg]
  apply congrArg₂
  · rfl
  · rw [permT_permT]
    rfl

lemma toTensor_fieldStrengthAux {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    Tensorial.toTensor (fieldStrengthAux A ε) =
    (permT id (IsReindexing.auto) {(η d | μ μ' ⊗ distTensorDeriv A ε | μ' ν)}ᵀ)
    - (permT ![1, 0] (IsReindexing.auto)
      {(η d | μ μ' ⊗ distTensorDeriv A ε | μ' ν)}ᵀ) := by
  rw [fieldStrengthAux_eq_add]
  simp

lemma toTensor_fieldStrengthAux_basis_repr {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ))
    (b : ComponentIdx (S := realLorentzTensor d) (Fin.append ![Color.up] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (fieldStrengthAux A ε)) b =
    ∑ κ, (η (b 0) κ * SpaceTime.distDeriv κ A ε (b 1) -
      η (b 1) κ * SpaceTime.distDeriv κ A ε (b 0)) := by
  rw [toTensor_fieldStrengthAux]
  simp only [map_sub, Finsupp.coe_sub, Pi.sub_apply]
  rw [Tensor.permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [1, 2, n]
    rw [Tensor.prodT_basis_repr_apply, contrMetric_repr_apply_eq_minkowskiMatrix]
    enter [1]
    change η (b 0) n
  conv_lhs =>
    enter [1, 2, n, 2]
    rw [toTensor_distTensorDeriv_basis_repr_apply]
    change distDeriv n A ε (b 1)
  rw [Tensor.permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [2, 2, n]
    rw [Tensor.prodT_basis_repr_apply, contrMetric_repr_apply_eq_minkowskiMatrix]
    enter [1]
    change η (b 1) n
  conv_lhs =>
    enter [2, 2, n, 2]
    rw [toTensor_distTensorDeriv_basis_repr_apply]
    change distDeriv n A ε (b 0)
  rw [← Finset.sum_sub_distrib]

lemma fieldStrengthAux_tensor_basis_eq_basis {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ))
    (b : ComponentIdx (S := realLorentzTensor d) (Fin.append ![Color.up] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (A.fieldStrengthAux ε)) b =
    (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (A.fieldStrengthAux ε)
      (b 0, b 1) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Fin.isValue]
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.Vector.basis (d := d)).reindex Lorentz.Vector.indexEquiv.symm).tensorProduct
          (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
          ((Lorentz.Vector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
          (Lorentz.Vector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
        ext b
        match b with
        | ⟨i, j⟩ =>
        simp
  rw [hb]
  rw [Finsupp.equivMapDomain_apply, Module.Basis.repr_reindex_apply]
  congr 1

lemma fieldStrengthAux_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : DistElectromagneticPotential d) (ε : 𝓢(SpaceTime d, ℝ)) :
    (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (A.fieldStrengthAux ε) μν =
    ∑ κ, ((η μν.1 κ * distDeriv κ A ε μν.2) - η μν.2 κ * distDeriv κ A ε μν.1) := by
  match μν with
  | (μ, ν) =>
  trans (Tensor.basis _).repr (Tensorial.toTensor (A.fieldStrengthAux ε))
    (fun | 0 => μ | 1 => ν); swap
  · rw [toTensor_fieldStrengthAux_basis_repr]
  rw [fieldStrengthAux_tensor_basis_eq_basis]

lemma fieldStrengthAux_basis_repr_apply_eq_single {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : DistElectromagneticPotential d) (ε : 𝓢(SpaceTime d, ℝ)) :
    (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (A.fieldStrengthAux ε) μν =
    ((η μν.1 μν.1 * distDeriv μν.1 A ε μν.2) - η μν.2 μν.2 * distDeriv μν.2 A ε μν.1) := by
  rw [fieldStrengthAux_basis_repr_apply]
  simp only [Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single μν.1, Finset.sum_eq_single μν.2]
  · intro b _ hb
    rw [minkowskiMatrix.off_diag_zero]
    simp only [zero_mul]
    exact id (Ne.symm hb)
  · simp
  · intro b _ hb
    rw [minkowskiMatrix.off_diag_zero]
    simp only [zero_mul]
    exact id (Ne.symm hb)
  · simp

lemma fieldStrengthAux_eq_basis {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    (A.fieldStrengthAux ε) = ∑ μ, ∑ ν,
      ((η μ μ * distDeriv μ A ε ν) - η ν ν * distDeriv ν A ε μ)
      • Lorentz.Vector.basis μ ⊗ₜ[ℝ] Lorentz.Vector.basis ν := by
  apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  ext b
  match b with
  | (μ, ν) =>
  simp [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, smul_eq_mul]
  simp [Finsupp.single_apply]
  rw [fieldStrengthAux_basis_repr_apply_eq_single]

/-!

### A.2. The definition of the field strength

-/

/-- The field strength of an electromagnetic potential which is a distribution. -/
noncomputable def fieldStrength {d} :
    DistElectromagneticPotential d →ₗ[ℝ]
    (SpaceTime d) →d[ℝ] Lorentz.Vector d ⊗[ℝ] Lorentz.Vector d where
  toFun A := {
    toFun ε := A.fieldStrengthAux ε
    map_add' ε1 ε2 := by
      apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
      ext μν
      simp [fieldStrengthAux_basis_repr_apply_eq_single]
      ring
    map_smul' c ε := by
      apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
      ext μν
      simp [fieldStrengthAux_basis_repr_apply_eq_single]
      ring
    cont := by
      simp [fieldStrengthAux_eq_basis]
      fun_prop}
  map_add' A1 A2 := by
    ext ε
    apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
    ext μν
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      fieldStrengthAux_basis_repr_apply_eq_single, map_add, add_apply,
      Lorentz.Vector.apply_add, Finsupp.coe_add, Pi.add_apply]
    ring
  map_smul' c A := by
    ext ε
    apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
    ext μν
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      fieldStrengthAux_basis_repr_apply_eq_single, map_smul, FunLike.coe_smul,
      Pi.smul_apply, Lorentz.Vector.apply_smul, Real.ringHom_apply, Finsupp.coe_smul, smul_eq_mul]
    ring

lemma fieldStrength_eq_fieldStrengthAux {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    A.fieldStrength ε = A.fieldStrengthAux ε := by rfl
/-!

### A.3. Field strength written in terms of a basis

-/

lemma fieldStrength_eq_basis {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    A.fieldStrength ε = ∑ μ, ∑ ν,
      ((η μ μ * distDeriv μ A ε ν) - η ν ν * distDeriv ν A ε μ)
      • Lorentz.Vector.basis μ ⊗ₜ[ℝ] Lorentz.Vector.basis ν := by
  rw [fieldStrength]
  exact fieldStrengthAux_eq_basis A ε

lemma fieldStrength_basis_repr_eq_single {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : DistElectromagneticPotential d) (ε : 𝓢(SpaceTime d, ℝ)) :
    (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (A.fieldStrength ε) μν =
    ((η μν.1 μν.1 * distDeriv μν.1 A ε μν.2) - η μν.2 μν.2 * distDeriv μν.2 A ε μν.1) := by
  rw [fieldStrength]
  exact fieldStrengthAux_basis_repr_apply_eq_single A ε

@[simp]
lemma fieldStrength_diag_zero {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) (μ : Fin 1 ⊕ Fin d) :
    (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr
    (A.fieldStrength ε) (μ, μ) = 0 := by
  rw [fieldStrength_basis_repr_eq_single]
  simp

@[simp]
lemma distDeriv_fieldStrength_diag_zero {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) (μ ν : Fin 1 ⊕ Fin d) :
    (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr
    (distDeriv ν A.fieldStrength ε) (μ, μ) = 0 := by
  rw [SpaceTime.distDeriv_apply']
  simp

lemma fieldStrength_antisymmetric_basis {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) (μ ν : Fin 1 ⊕ Fin d) :
    (Vector.basis.tensorProduct Vector.basis).repr
    (A.fieldStrength ε) (μ, ν) = - (Vector.basis.tensorProduct Vector.basis).repr
    (A.fieldStrength ε) (ν, μ) := by
  rw [fieldStrength_basis_repr_eq_single, fieldStrength_basis_repr_eq_single]
  ring

/-!

### A.4. Equivariance of the field strength for distributions

-/

set_option backward.isDefEq.respectTransparency false in
lemma fieldStrength_equivariant {d} (A : DistElectromagneticPotential d)
    (Λ : LorentzGroup d) :
    (Λ • A).fieldStrength = Λ • A.fieldStrength := by
  ext ε
  rw [fieldStrength_eq_fieldStrengthAux, lorentzGroup_smul_dist_apply]
  rw [fieldStrengthAux_eq_add, distTensorDeriv_equivariant, lorentzGroup_smul_dist_apply,
    ← actionT_contrMetric Λ]
  generalize ((schwartzAction Λ⁻¹) ε) = ε'
  rw [fieldStrength_eq_fieldStrengthAux, fieldStrengthAux_eq_add]
  simp only [Tensorial.toTensor_smul, prodT_equivariant, contrT_equivariant, permT_equivariant,
    ← Tensorial.smul_toTensor_symm, smul_sub]

end DistElectromagneticPotential

end Electromagnetism
