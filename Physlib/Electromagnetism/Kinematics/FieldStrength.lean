/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Kinematics.EMPotential
public import Physlib.Relativity.Tensors.RealTensor.Metrics.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
/-!

# The Field Strength Tensor

## i. Overview

In this module we define the field strength tensor in terms of the electromagnetic potential.

We define the tensor and prove various properties of it. Its components are accessed
through index evaluation, `toField {A.toFieldStrength x | [μ] [ν]}ᵀ`.

## ii. Key results

- `toFieldStrength` : The field strength tensor from an electromagnetic potential.
- `toFieldStrength_eval_apply_eq_single` : The components of the field strength tensor
  in terms of derivatives of the potential, `F^{μν} = η^{μμ} ∂_μ A^ν - η^{νν} ∂_ν A^μ`.

## iii. Table of contents

- A. The field strength tensor
  - A.1. Tensor equalities
  - A.2. Vector equalities
  - A.3. The group action acting on the field strength tensor
  - A.4. Differentiability and smoothness of the field strength tensor
  - A.5. Components of the field strength tensor
    - A.5.1. Index evaluation
    - A.5.2. Differentiability of the components
  - A.6. The antisymmetry of the field strength tensor
  - A.7. Equivariance of the components of the field strength tensor
  - A.8. Linearity of the field strength tensor

## iv. References

* None.
-/

@[expose] public section
namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix Tensorial
open Lorentz

attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. The field strength tensor

We define the field strength tensor `F^{μν}` in terms of the derivative of the
electromagnetic potential `A^μ`. We then prove that this tensor transforms correctly
under Lorentz transformations.

-/
/-- The field strength from an electromagnetic potential, as a tensor `F^{μν}`. -/
noncomputable def toFieldStrength {d} (A : ElectromagneticPotential d) :
    SpaceTime d → Lorentz.Vector d ⊗[ℝ] Lorentz.Vector d := fun x =>
  Tensorial.toTensor.symm
  (permT id (IsReindexing.auto)
    {(η d | μ μ' ⊗ A.deriv x | μ' ν) + - (η d | ν ν' ⊗ A.deriv x | ν' μ)}ᵀ)

/-!

### A.1. Tensor equalities

These equalities for the field strength tensor are in
terms of tensor expressions and index notation. In practice,
we don't expect them to be used explicitly. They are useful for proving some
of the API within this module.

-/

lemma toFieldStrength_eq_deriv {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    toFieldStrength A x =
    Tensorial.toTensor.symm (permT id IsReindexing.auto {(η d | μ μ' ⊗ A.deriv x | μ' ν)
    + - (η d | ν ν' ⊗ A.deriv x | ν' μ)}ᵀ) := by
  rw [toFieldStrength]

lemma toFieldStrength_eq_tensorDeriv {d} {A : ElectromagneticPotential d}
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    toFieldStrength A x =
    Tensorial.toTensor.symm (permT id IsReindexing.auto {(η d | μ μ' ⊗ tensorDeriv A x | μ' ν)
    + - (η d | ν ν' ⊗ tensorDeriv A x | ν' μ)}ᵀ) := by
  rw [toFieldStrength_eq_deriv, deriv_eq_tensorDeriv _ hA]

lemma toFieldStrength_eq_add {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    toFieldStrength A x =
    Tensorial.toTensor.symm (permT id (IsReindexing.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ)
    - Tensorial.toTensor.symm (permT ![1, 0] (IsReindexing.auto)
      {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ) := by
  simp only [toFieldStrength, map_add, map_neg, sub_eq_add_neg, permT_permT]
  rfl

lemma toFieldStrength_eq_sub_tensorDeriv {d} {A : ElectromagneticPotential d}
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    toFieldStrength A x =
    Tensorial.toTensor.symm (permT id IsReindexing.auto {η d | μ μ' ⊗ tensorDeriv A x | μ' ν}ᵀ)
    - Tensorial.toTensor.symm (permT ![1, 0] IsReindexing.auto
    {η d | μ μ' ⊗ tensorDeriv A x | μ' ν}ᵀ) := by
  simp only [toFieldStrength_eq_tensorDeriv hA, map_add, map_neg, sub_eq_add_neg, permT_permT]
  rfl

lemma toTensor_toFieldStrength {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    Tensorial.toTensor (toFieldStrength A x) =
    (permT id (IsReindexing.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ)
    - (permT ![1, 0] (IsReindexing.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ) := by
  simp [toFieldStrength_eq_add]

/-!

### A.2. Vector equalities

These equalities for the field strength tensor are in terms of vector basis.
They match some of the familiar forms one might expect to see the field strength
tensor in.

-/

/-- The statement that `F = F^{μν} eᵤ ⊗ eᵥ` written explicitly, with
  the components extracted via `toField`. -/
lemma toFieldStrength_eq_sum_basis_eval {d} {A : ElectromagneticPotential d} :
    A.toFieldStrength = fun x => ∑ μ, ∑ ν, toField {A.toFieldStrength x| [μ] [ν]}ᵀ •
      Vector.basis μ ⊗ₜ[ℝ] Vector.basis ν := by
  ext x
  exact prod_eq_sum_eval Vector.basis_eq_map_tensor_basis
      Vector.basis_eq_map_tensor_basis (A.toFieldStrength x)

/-- The statement that `F = F^{μν} eᵤ ⊗ eᵥ` written explicitly, with
  the components given by `∑ κ, (η μ κ * ∂_ κ A x ν - η ν κ * ∂_ κ A x μ)`. -/
lemma toFieldStrength_eq_sum_basis {d} {A : ElectromagneticPotential d}
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    A.toFieldStrength x = ∑ μ, ∑ ν, (∑ κ, (η μ κ * ∂_ κ A x ν - η ν κ * ∂_ κ A x μ)) •
      Lorentz.Vector.basis μ ⊗ₜ Lorentz.Vector.basis ν := by
  apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  ext ⟨μ, ν⟩
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero]
  simp only [prod_basis_of_map_reindex Vector.basis_eq_map_tensor_basis
        Vector.basis_eq_map_tensor_basis,
    toFieldStrength_eq_sub_tensorDeriv hA, ← deriv_eq_tensorDeriv _ hA, map_sub, Basis.repr_reindex,
    Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Finsupp.coe_sub, Pi.sub_apply, Finsupp.equivMapDomain_apply, permT_basis_repr_symm_apply,
    Function.comp_apply, contrT_basis_repr_apply_eq_fin, prodT_basis_repr_apply,
    contrMetric_repr_apply_eq_minkowskiMatrix,
    prod_tensor_basis_eq_map_reindex CoVector.basis_eq_map_tensor_basis
        Vector.basis_eq_map_tensor_basis,
    LinearEquiv.symm_apply_apply, Equiv.symm_symm, deriv_basis_repr_apply, Finset.sum_sub_distrib]
  rfl

/-- The statement that `F = F^{μν} eᵤ ⊗ eᵥ` written explicitly, with
  with the components given by `(η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ)`. -/
lemma toFieldStrength_eq_sum_basis_single {d} {A : ElectromagneticPotential d}
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    A.toFieldStrength x = ∑ μ, ∑ ν, (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ) •
      Lorentz.Vector.basis μ ⊗ₜ Lorentz.Vector.basis ν := by
  rw [toFieldStrength_eq_sum_basis hA x]
  apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  ext ⟨μ, ν⟩
  simp [Basis.tensorProduct_repr_tmul_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single μ
      (fun b _ hb => by simp [minkowskiMatrix.off_diag_zero hb.symm]) (by simp),
    Finset.sum_eq_single ν
      (fun b _ hb => by simp [minkowskiMatrix.off_diag_zero hb.symm]) (by simp)]

/-!

## A.3. The group action acting on the field strength tensor

We show that the field strength tensor is equivariant under the action of the Lorentz group.
That is transforming the potential and then taking the field strength is the same
as taking the field strength and then transforming the resulting tensor.

-/

lemma toFieldStrength_equivariant {d} (A : ElectromagneticPotential d) (Λ : LorentzGroup d)
    (hf : Differentiable ℝ A) (x : SpaceTime d) :
    (Λ • A).toFieldStrength x = Λ • A.toFieldStrength (Λ⁻¹ • x) := by
  rw [toFieldStrength, deriv_equivariant A Λ hf, ← actionT_contrMetric Λ, toFieldStrength]
  simp only [Tensorial.toTensor_smul, prodT_equivariant, contrT_equivariant, map_neg,
    permT_equivariant, map_add, ← Tensorial.smul_toTensor_symm, smul_add, smul_neg]

/-!

## A.4. Differentiability and smoothness of the field strength tensor

-/

@[fun_prop]
lemma differentiable_toFieldStrength {d} {A : ElectromagneticPotential d} (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ A.toFieldStrength := by
  change Differentiable ℝ (A.toFieldStrength ·)
  simp only [toFieldStrength_eq_sum_basis_single (hA.differentiable (by simp))]
  fun_prop

open ContDiff

@[fun_prop]
lemma differentiable_toFieldStrength_of_smooth {d}
    {A : ElectromagneticPotential d} (hA : ContDiff ℝ ∞ A) :
    Differentiable ℝ A.toFieldStrength :=
  differentiable_toFieldStrength (hA.of_le (ENat.LEInfty.out))

@[fun_prop]
lemma contDiff_toFieldStrength {d} {n : WithTop ℕ∞} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) : ContDiff ℝ n A.toFieldStrength := by
  change ContDiff ℝ n (A.toFieldStrength ·)
  simp only [toFieldStrength_eq_sum_basis_single (hA.differentiable (by simp))]
  fun_prop

/-!

### A.5. Components of the field strength tensor

The components `F^{μν}` of the field strength tensor are accessed through index evaluation,
`toField {A.toFieldStrength x | [μ] [ν]}ᵀ`. This is the canonical way to refer to the
components of the field strength tensor, and is what should be used downstream.

#### A.5.1. Index evaluation

-/

/-- Evaluating both tensor indices of the field strength gives the coefficient in the
tensor basis. -/
lemma toFieldStrength_eval_eq_tensor_basis_repr {d} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (μ ν : Fin 1 ⊕ Fin d) :
    toField {A.toFieldStrength x | [μ] [ν]}ᵀ =
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x)) (fun | 0 => μ | 1 => ν) := by
  rw [Vector.toField_eval_eval_eq_tensorProduct_repr, Vector.tensor_basis_repr_toTensor_prod_apply]

/-- The coefficient of the field strength tensor in the tensor basis is given by
index evaluation. -/
lemma toFieldStrength_tensor_basis_repr_eq_eval {d} (A : ElectromagneticPotential d)
    (x : SpaceTime d)
    (b : ComponentIdx (S := realLorentzTensor d) (Fin.append ![Color.up] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x)) b =
    toField {A.toFieldStrength x | [b 0] [b 1]}ᵀ := by
  rw [toFieldStrength_eval_eq_tensor_basis_repr]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The evaluated components of the field strength tensor in terms of derivatives of the
electromagnetic potential. -/
lemma toFieldStrength_eval_apply {d} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (μ ν : Fin 1 ⊕ Fin d) :
    toField {A.toFieldStrength x | [μ] [ν]}ᵀ =
    ∑ κ, (η μ κ * ∂_ κ A x ν - η ν κ * ∂_ κ A x μ) := by
  rw [toFieldStrength_eval_eq_tensor_basis_repr, toTensor_toFieldStrength]
  simp only [map_sub, Finsupp.coe_sub, Pi.sub_apply, Tensor.permT_basis_repr_symm_apply,
    contrT_basis_repr_apply_eq_fin, Tensor.prodT_basis_repr_apply,
    contrMetric_repr_apply_eq_minkowskiMatrix, toTensor_deriv_basis_repr_apply,
    ← Finset.sum_sub_distrib]
  rfl

/-- The evaluated components of the field strength tensor after using diagonal form of the
Minkowski metric. -/
lemma toFieldStrength_eval_apply_eq_single {d} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (μ ν : Fin 1 ⊕ Fin d) :
    toField {A.toFieldStrength x | [μ] [ν]}ᵀ =
    η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ := by
  rw [toFieldStrength_eval_apply, Finset.sum_sub_distrib,
    Finset.sum_eq_single μ
      (fun b _ hb => by simp [minkowskiMatrix.off_diag_zero hb.symm]) (by simp),
    Finset.sum_eq_single ν
      (fun b _ hb => by simp [minkowskiMatrix.off_diag_zero hb.symm]) (by simp)]

/-!

#### A.5.2. Differentiability of the components

-/
open ContDiff

lemma toFieldStrength_eval_differentiable {d} {A : ElectromagneticPotential d}
    {μ ν : Fin 1 ⊕ Fin d} (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ (fun x => toField {A.toFieldStrength x | [μ] [ν]}ᵀ) := by
  simp only [toFieldStrength_eval_apply_eq_single]
  fun_prop

lemma toFieldStrength_eval_differentiable_space {d} {A : ElectromagneticPotential d}
    {μ ν : Fin 1 ⊕ Fin d} (hA : ContDiff ℝ 2 A) (t : Time) {c : SpeedOfLight} :
    Differentiable ℝ (fun x =>
      toField {A.toFieldStrength ((toTimeAndSpace c).symm (t, x)) | [μ] [ν]}ᵀ) := by
  change Differentiable ℝ ((fun x => toField {A.toFieldStrength x | [μ] [ν]}ᵀ) ∘
    fun x => (toTimeAndSpace c).symm (t, x))
  exact (toFieldStrength_eval_differentiable hA).comp (by fun_prop)

lemma toFieldStrength_eval_differentiable_time {d} {A : ElectromagneticPotential d}
    {μ ν : Fin 1 ⊕ Fin d} (hA : ContDiff ℝ 2 A) (x : Space d) {c : SpeedOfLight} :
    Differentiable ℝ (fun t =>
      toField {A.toFieldStrength ((toTimeAndSpace c).symm (t, x)) | [μ] [ν]}ᵀ) := by
  change Differentiable ℝ ((fun x => toField {A.toFieldStrength x | [μ] [ν]}ᵀ) ∘
    fun t => (toTimeAndSpace c).symm (t, x))
  exact (toFieldStrength_eval_differentiable hA).comp (by fun_prop)

lemma toFieldStrength_eval_contDiff {d} {n : WithTop ℕ∞} {A : ElectromagneticPotential d}
    {μ ν : Fin 1 ⊕ Fin d} (hA : ContDiff ℝ (n + 1) A) :
    ContDiff ℝ n (fun x => toField {A.toFieldStrength x | [μ] [ν]}ᵀ) := by
  simp only [toFieldStrength_eval_apply_eq_single]
  fun_prop

lemma toFieldStrength_eval_smooth {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (μ ν : Fin 1 ⊕ Fin d) :
    ContDiff ℝ ∞ (fun x => toField {A.toFieldStrength x | [μ] [ν]}ᵀ) :=
  toFieldStrength_eval_contDiff (by simpa using hA)

/-!

### A.6. The antisymmetry of the field strength tensor

We show that the field strength tensor is antisymmetric.

-/

lemma toFieldStrength_eval_antisymm {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (μ ν : Fin 1 ⊕ Fin d) :
    toField {A.toFieldStrength x | [μ] [ν]}ᵀ = - toField {A.toFieldStrength x | [ν] [μ]}ᵀ := by
  rw [toFieldStrength_eval_apply, toFieldStrength_eval_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun κ _ => by simp

lemma toFieldStrength_eval_diag_eq_zero {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (μ : Fin 1 ⊕ Fin d) :
    toField {A.toFieldStrength x | [μ] [μ]}ᵀ = 0 := by
  rw [toFieldStrength_eval_apply_eq_single, sub_self]

lemma toFieldStrength_antisymmetric {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    {A.toFieldStrength x | μ ν = - (A.toFieldStrength x | ν μ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [permT_basis_repr_symm_apply, map_neg, Finsupp.coe_neg, Pi.neg_apply,
    toFieldStrength_tensor_basis_repr_eq_eval]
  rw [toFieldStrength_eval_antisymm]
  rfl

/-!

### A.7. Equivariance of the components of the field strength tensor

-/

lemma toFieldStrength_eval_equivariant {d} (A : ElectromagneticPotential d)
    (Λ : LorentzGroup d) (hf : Differentiable ℝ A) (x : SpaceTime d)
    (μ ν : Fin 1 ⊕ Fin d) :
    toField {(Λ • A).toFieldStrength x | [μ] [ν]}ᵀ =
    ∑ κ, ∑ ρ, (Λ.1 μ κ * Λ.1 ν ρ) * toField {A.toFieldStrength (Λ⁻¹ • x) | [κ] [ρ]}ᵀ := by
  simp only [Vector.toField_eval_eval_eq_tensorProduct_repr]
  rw [toFieldStrength_equivariant A Λ hf x]
  generalize A.toFieldStrength (Λ⁻¹ • x) = F
  induction F using TensorProduct.inductionOn with
  | tmul v w =>
    rw [Tensorial.smul_prod]
    simp only [Basis.tensorProduct_repr_tmul_apply, Lorentz.Vector.basis_repr_apply, smul_eq_mul]
    rw [Lorentz.Vector.smul_eq_sum, Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Lorentz.Vector.smul_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  | add F1 F2 h1 h2 =>
    simp only [smul_add, map_add, Finsupp.coe_add, Pi.add_apply, h1, h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun ρ _ => by ring

/-- This lemma expresses the component form of the transformed field strength
tensor: when a Lorentz transformation Λ acts on the potential A, the resulting field strength
tensor's components are given by the standard tensor transformation rule involving the Lorentz
matrix elements Λ^μ_κ and Λ^ν_ρ applied to the original field components. -/
lemma toFieldStrength_action_eq_sum {d} (A : ElectromagneticPotential d) (Λ : LorentzGroup d)
    (hf : Differentiable ℝ A) (x : SpaceTime d) :
    (Λ • A).toFieldStrength x = ∑ μ, ∑ ν,
      (∑ κ, ∑ ρ, Λ.1 μ κ * Λ.1 ν ρ * toField {A.toFieldStrength (Λ⁻¹ • x) | [κ] [ρ]}ᵀ) •
      Vector.basis μ ⊗ₜ[ℝ] Vector.basis ν := by
  rw [toFieldStrength_eq_sum_basis_eval]
  simp only [toFieldStrength_eval_equivariant A Λ hf x]

/-!

### A.8. Linearity of the field strength tensor

We show that the field strength tensor is linear in the potential.

-/

lemma toFieldStrength_eval_add {d} (A1 A2 : ElectromagneticPotential d)
    (x : SpaceTime d) (hA1 : Differentiable ℝ A1) (hA2 : Differentiable ℝ A2)
    (μ ν : Fin 1 ⊕ Fin d) :
    toField {(A1 + A2).toFieldStrength x | [μ] [ν]}ᵀ =
    toField {A1.toFieldStrength x | [μ] [ν]}ᵀ + toField {A2.toFieldStrength x | [μ] [ν]}ᵀ := by
  simp only [toFieldStrength_eval_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp only [SpaceTime.deriv_eq, add_val, fderiv_add hA1.differentiableAt hA2.differentiableAt,
    _root_.add_apply, Lorentz.Vector.apply_add]
  ring

lemma toFieldStrength_add {d} (A1 A2 : ElectromagneticPotential d)
    (x : SpaceTime d) (hA1 : Differentiable ℝ A1) (hA2 : Differentiable ℝ A2) :
    toFieldStrength (A1 + A2) x = toFieldStrength A1 x + toFieldStrength A2 x := by
  apply Tensorial.toTensor.injective
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [map_add, Finsupp.coe_add, Pi.add_apply, toFieldStrength_tensor_basis_repr_eq_eval]
  exact toFieldStrength_eval_add A1 A2 x hA1 hA2 _ _

lemma toFieldStrength_eval_smul {d} (c : ℝ) (A : ElectromagneticPotential d)
    (x : SpaceTime d) (hA : Differentiable ℝ A) (μ ν : Fin 1 ⊕ Fin d) :
    toField {(c • A).toFieldStrength x | [μ] [ν]}ᵀ =
    c * toField {A.toFieldStrength x | [μ] [ν]}ᵀ := by
  simp only [toFieldStrength_eval_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp only [SpaceTime.deriv_eq, smul_val, fderiv_const_smul hA.differentiableAt, FunLike.coe_smul,
    Pi.smul_apply, Lorentz.Vector.apply_smul]
  ring

lemma toFieldStrength_smul {d} (c : ℝ) (A : ElectromagneticPotential d)
    (x : SpaceTime d) (hA : Differentiable ℝ A) :
    toFieldStrength (c • A) x = c • toFieldStrength A x := by
  apply Tensorial.toTensor.injective
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
    toFieldStrength_tensor_basis_repr_eq_eval]
  exact toFieldStrength_eval_smul c A x hA _ _

end ElectromagneticPotential

end Electromagnetism
