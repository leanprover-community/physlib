/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Kinematics.EMPotential
/-!

# The Field Strength Tensor

## i. Overview

In this module we define the field strength tensor in terms of the electromagnetic potential.

We define a tensor version and a matrix version and prover various properties of these.

## ii. Key results

- `toFieldStrength` : The field strength tensor from an electromagnetic potential.
- `fieldStrengthMatrix` : The field strength matrix from an electromagnetic potential
  (matrix representation of the field strength tensor in the standard basis).
- `DistElectromagneticPotential.fieldStrength` : The field strength for
  electromagnetic potentials which are distributions.

## iii. Table of contents

- A. The field strength tensor
  - A.1. Basic equalities
  - A.2. Elements of the field strength tensor in terms of basis
  - A.3. The field strength matrix
    - A.3.1. Differentiability of the field strength matrix
  - A.4. The antisymmetry of the field strength tensor
  - A.5. Equivariance of the field strength tensor
  - A.6. Linearity of the field strength tensor
- B. Field strength for distributions
  - B.1. Auxiliary definition of field strength for distributions, with no linearity
  - B.2. The definition of the field strength
  - B.3. Field strength written in terms of a basis
  - B.4. Equivariance of the field strength for distributions

## iv. References

-/
namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. The field strength tensor

We define the field strength tensor `F_μ^ν` in terms of the derivative of the
electromagnetic potential `A^μ`. We then prove that this tensor transforms correctly
under Lorentz transformations.

-/
/-- The field strength from an electromagnetic potential, as a tensor `F_μ^ν`. -/
noncomputable def toFieldStrength {d} (A : ElectromagneticPotential d) :
    SpaceTime d → Lorentz.Vector d ⊗[ℝ] Lorentz.Vector d := fun x =>
  Tensorial.toTensor.symm
  (permT id (PermCond.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν) + - (η d | ν ν' ⊗ A.deriv x | ν' μ)}ᵀ)

/-!

### A.1. Basic equalities

-/

lemma toFieldStrength_eq_add {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    toFieldStrength A x =
    Tensorial.toTensor.symm (permT id (PermCond.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ)
    - Tensorial.toTensor.symm (permT ![1, 0] (PermCond.auto)
      {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ) := by
  rw [toFieldStrength]
  simp only [map_add, map_neg]
  rw [sub_eq_add_neg]
  apply congrArg₂
  · rfl
  · rw [permT_permT]
    rfl

lemma toTensor_toFieldStrength {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    Tensorial.toTensor (toFieldStrength A x) =
    (permT id (PermCond.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ)
    - (permT ![1, 0] (PermCond.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ) := by
  rw [toFieldStrength_eq_add]
  simp

/-!

### A.2. Elements of the field strength tensor in terms of basis

-/

lemma toTensor_toFieldStrength_basis_repr {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (b : ComponentIdx (S := realLorentzTensor d) (Fin.append ![Color.up] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x)) b =
    ∑ κ, (η (finSumFinEquiv.symm (b 0)) κ * ∂_ κ A x (finSumFinEquiv.symm (b 1)) -
      η (finSumFinEquiv.symm (b 1)) κ * ∂_ κ A x (finSumFinEquiv.symm (b 0))) := by
  rw [toTensor_toFieldStrength]
  simp only [Tensorial.self_toTensor_apply, map_sub,
    Finsupp.coe_sub, Pi.sub_apply]
  rw [Tensor.permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [1, 2, n]
    rw [Tensor.prodT_basis_repr_apply, contrMetric_repr_apply_eq_minkowskiMatrix]
    enter [1]
    change η (finSumFinEquiv.symm (b 0)) (finSumFinEquiv.symm n)
  conv_lhs =>
    enter [1, 2, n, 2]
    rw [toTensor_deriv_basis_repr_apply]
    change ∂_ (finSumFinEquiv.symm n) A x (finSumFinEquiv.symm (b 1))
  rw [Tensor.permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [2, 2, n]
    rw [Tensor.prodT_basis_repr_apply, contrMetric_repr_apply_eq_minkowskiMatrix]
    enter [1]
    change η (finSumFinEquiv.symm (b 1)) (finSumFinEquiv.symm n)
  conv_lhs =>
    enter [2, 2, n, 2]
    rw [toTensor_deriv_basis_repr_apply]
    change ∂_ (finSumFinEquiv.symm n) A x (finSumFinEquiv.symm (b 0))
  rw [← Finset.sum_sub_distrib]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Fin.isValue, Equiv.symm_apply_apply]

lemma toFieldStrength_tensor_basis_eq_basis {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (b : ComponentIdx (S := realLorentzTensor d) (Fin.append ![Color.up] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x)) b =
    (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (toFieldStrength A x)
      (finSumFinEquiv.symm (b 0), finSumFinEquiv.symm (b 1)) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Fin.isValue]
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
  rw [Module.Basis.repr_reindex_apply]
  congr 1

lemma toFieldStrength_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : ElectromagneticPotential d) (x : SpaceTime d) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x) μν =
    ∑ κ, ((η μν.1 κ * ∂_ κ A x μν.2) - η μν.2 κ * ∂_ κ A x μν.1) := by
  match μν with
  | (μ, ν) =>
  trans (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x))
    (fun | 0 => finSumFinEquiv μ | 1 => finSumFinEquiv ν); swap
  · rw [toTensor_toFieldStrength_basis_repr]
    simp
  rw [toFieldStrength_tensor_basis_eq_basis]
  congr 1
  change _ = (finSumFinEquiv.symm (finSumFinEquiv μ), finSumFinEquiv.symm (finSumFinEquiv ν))
  simp

lemma toFieldStrength_basis_repr_apply_eq_single {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : ElectromagneticPotential d) (x : SpaceTime d) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x) μν =
    ((η μν.1 μν.1 * ∂_ μν.1 A x μν.2) - η μν.2 μν.2 * ∂_ μν.2 A x μν.1) := by
  rw [toFieldStrength_basis_repr_apply]
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

/-!

### A.3. The field strength matrix

We define the field strength matrix to be the matrix representation of the field strength tensor
in the standard basis.

This is currently not used as much as it could be.
-/
open ContDiff

/-- The matrix corresponding to the field strength in the standard basis. -/
noncomputable abbrev fieldStrengthMatrix {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :=
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x)

lemma fieldStrengthMatrix_eq {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    A.fieldStrengthMatrix x =
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x) := by rfl

lemma fieldStrengthMatrix_eq_tensor_basis_repr {d} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (μ ν : (Fin 1 ⊕ Fin d)) :
    A.fieldStrengthMatrix x (μ, ν) =
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x))
    (fun | 0 => finSumFinEquiv μ | 1 => finSumFinEquiv ν) := by
  rw [toFieldStrength_tensor_basis_eq_basis]
  simp only [Equiv.symm_apply_apply]
  rfl

lemma toFieldStrength_eq_fieldStrengthMatrix {d} (A : ElectromagneticPotential d) :
    toFieldStrength A = fun x => ∑ μ, ∑ ν,
      A.fieldStrengthMatrix x (μ, ν) • (Lorentz.Vector.basis μ) ⊗ₜ (Lorentz.Vector.basis ν) := by
  ext x
  apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  simp only [map_sum, map_smul]
  ext κ
  match κ with
  | (μ', ν') =>
  simp [Finsupp.single_apply]
  rfl

/-!

#### A.3.1. Differentiability of the field strength matrix

-/

lemma fieldStrengthMatrix_differentiable {d} {A : ElectromagneticPotential d}
    {μν} (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ (A.fieldStrengthMatrix · μν) := by
  have diff_partial (μ) :
      ∀ ν, Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [SpaceTime.differentiable_vector]
    refine Differentiable.clm_apply ?_ ?_
    · exact ((contDiff_succ_iff_fderiv (n := 1)).mp hA).2.2.differentiable
        (by simp)
    · fun_prop
  conv => enter [2, x]; rw [toFieldStrength_basis_repr_apply_eq_single,
    SpaceTime.deriv_eq, SpaceTime.deriv_eq]
  apply Differentiable.sub
  apply Differentiable.const_mul
  · exact diff_partial _ _
  apply Differentiable.const_mul
  · exact diff_partial _ _

lemma toFieldStrength_differentiable {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ (toFieldStrength A) := by
  conv =>
    enter [2]
    rw [toFieldStrength_eq_fieldStrengthMatrix]
  apply Differentiable.fun_sum
  intro μ _
  apply Differentiable.fun_sum
  intro ν _
  apply Differentiable.smul_const
  exact fieldStrengthMatrix_differentiable hA

lemma fieldStrengthMatrix_differentiable_space {d} {A : ElectromagneticPotential d}
    {μν} (hA : ContDiff ℝ 2 A) (t : Time) {c : SpeedOfLight} :
    Differentiable ℝ (fun x => A.fieldStrengthMatrix ((toTimeAndSpace c).symm (t, x)) μν) := by
  change Differentiable ℝ ((A.fieldStrengthMatrix · μν) ∘ fun x => (toTimeAndSpace c).symm (t, x))
  refine Differentiable.comp ?_ ?_
  · exact fieldStrengthMatrix_differentiable hA
  · fun_prop

lemma fieldStrengthMatrix_differentiable_time {d} {A : ElectromagneticPotential d}
    {μν} (hA : ContDiff ℝ 2 A) (x : Space d) {c : SpeedOfLight} :
    Differentiable ℝ (fun t => A.fieldStrengthMatrix ((toTimeAndSpace c).symm (t, x)) μν) := by
  change Differentiable ℝ ((A.fieldStrengthMatrix · μν) ∘ fun t => (toTimeAndSpace c).symm (t, x))
  refine Differentiable.comp ?_ ?_
  · exact fieldStrengthMatrix_differentiable hA
  · fun_prop

lemma fieldStrengthMatrix_contDiff {d} {n : WithTop ℕ∞} {A : ElectromagneticPotential d}
    {μν} (hA : ContDiff ℝ (n + 1) A) :
    ContDiff ℝ n (A.fieldStrengthMatrix · μν) := by
  conv => enter [3, x]; rw [toFieldStrength_basis_repr_apply_eq_single,
    SpaceTime.deriv_eq, SpaceTime.deriv_eq]
  apply ContDiff.sub
  apply ContDiff.mul
  · fun_prop
  · match μν with
    | (μ, ν) =>
    simp only
    revert ν
    rw [SpaceTime.contDiff_vector]
    apply ContDiff.clm_apply
    · exact ContDiff.fderiv_right (m := n) hA (by rfl)
    · fun_prop
  apply ContDiff.mul
  · fun_prop
  · match μν with
    | (μ, ν) =>
    simp only
    revert μ
    rw [SpaceTime.contDiff_vector]
    apply ContDiff.clm_apply
    · exact ContDiff.fderiv_right (m := n) hA (by rfl)
    · fun_prop

lemma fieldStrengthMatrix_smooth {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (μν) :
    ContDiff ℝ ∞ (A.fieldStrengthMatrix · μν) := by
  apply fieldStrengthMatrix_contDiff
  simpa using hA

/-!

### A.4. The antisymmetry of the field strength tensor

We show that the field strength tensor is antisymmetric.

-/

lemma toFieldStrength_antisymmetric {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    {A.toFieldStrength x | μ ν = - (A.toFieldStrength x | ν μ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [toTensor_toFieldStrength_basis_repr]
  rw [permT_basis_repr_symm_apply, map_neg]
  simp only [Nat.reduceAdd, Fin.isValue, Nat.reduceSucc, Finsupp.coe_neg, Pi.neg_apply]
  rw [toTensor_toFieldStrength_basis_repr]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  simp only [Fin.isValue, Fin.cast_eq_self, neg_sub]
  rfl

lemma fieldStrengthMatrix_antisymm {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (μ ν : Fin 1 ⊕ Fin d) :
    A.fieldStrengthMatrix x (μ, ν) = - A.fieldStrengthMatrix x (ν, μ) := by
  rw [toFieldStrength_basis_repr_apply, toFieldStrength_basis_repr_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  simp

@[simp]
lemma fieldStrengthMatrix_diag_eq_zero {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (μ : Fin 1 ⊕ Fin d) :
    A.fieldStrengthMatrix x (μ, μ) = 0 := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp

/-!

### A.5. Equivariance of the field strength tensor

We show that the field strength tensor is equivariant under the action of the Lorentz group.
That is transforming the potential and then taking the field strength is the same
as taking the field strength and then transforming the resulting tensor.

-/

lemma toFieldStrength_equivariant {d} (A : ElectromagneticPotential d) (Λ : LorentzGroup d)
    (hf : Differentiable ℝ A) (x : SpaceTime d) :
    toFieldStrength (fun x => Λ • A (Λ⁻¹ • x)) x =
      Λ • toFieldStrength A (Λ⁻¹ • x) := by
  rw [toFieldStrength, deriv_equivariant A Λ hf, ← actionT_contrMetric Λ, toFieldStrength]
  simp only [Tensorial.toTensor_smul, prodT_equivariant, contrT_equivariant, map_neg,
    permT_equivariant, map_add, ← Tensorial.smul_toTensor_symm, smul_add, smul_neg]

lemma fieldStrengthMatrix_equivariant {d} (A : ElectromagneticPotential d)
    (Λ : LorentzGroup d) (hf : Differentiable ℝ A) (x : SpaceTime d)
    (μ : (Fin 1 ⊕ Fin d)) (ν : Fin 1 ⊕ Fin d) :
    fieldStrengthMatrix (fun x => Λ • A (Λ⁻¹ • x)) x (μ, ν) =
    ∑ κ, ∑ ρ, (Λ.1 μ κ * Λ.1 ν ρ) * A.fieldStrengthMatrix (Λ⁻¹ • x) (κ, ρ) := by
  rw [fieldStrengthMatrix, toFieldStrength_equivariant A Λ hf x]
  conv_rhs =>
    enter [2, κ, 2, ρ]
    rw [fieldStrengthMatrix]
  generalize A.toFieldStrength (Λ⁻¹ • x) = F
  let P (F : Lorentz.Vector d ⊗[ℝ] Lorentz.Vector d) : Prop :=
    ((Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (Λ • F)) (μ, ν) =
    ∑ κ, ∑ ρ, Λ.1 μ κ * Λ.1 ν ρ *
    ((Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr F) (κ, ρ)
  change P F
  apply TensorProduct.induction_on
  · simp [P]
  · intro x y
    dsimp [P]
    rw [Tensorial.smul_prod]
    simp only [Basis.tensorProduct_repr_tmul_apply, Lorentz.Vector.basis_repr_apply,
      Lorentz.CoVector.basis_repr_apply, smul_eq_mul]
    rw [Lorentz.Vector.smul_eq_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl (fun κ _ => ?_)
    rw [Lorentz.Vector.smul_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl (fun ρ _ => ?_)
    ring
  · intro F1 F2 h1 h2
    simp [P, h1, h2]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl (fun κ _ => ?_)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl (fun ρ _ => ?_)
    ring

/-!

### A.6. Linearity of the field strength tensor

We show that the field strength tensor is linear in the potential.

-/

lemma toFieldStrength_add {d} (A1 A2 : ElectromagneticPotential d)
    (x : SpaceTime d) (hA1 : Differentiable ℝ A1) (hA2 : Differentiable ℝ A2) :
    toFieldStrength (A1 + A2) x = toFieldStrength A1 x + toFieldStrength A2 x := by
  apply (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  ext μν
  simp only [map_add, Finsupp.coe_add, Pi.add_apply]
  repeat rw [toFieldStrength_basis_repr_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  repeat rw [SpaceTime.deriv_eq]
  rw [fderiv_add]
  simp only [ContinuousLinearMap.add_apply, Lorentz.Vector.apply_add]
  ring
  · exact hA1.differentiableAt
  · exact hA2.differentiableAt

lemma fieldStrengthMatrix_add {d} (A1 A2 : ElectromagneticPotential d)
    (x : SpaceTime d) (hA1 : Differentiable ℝ A1) (hA2 : Differentiable ℝ A2) :
    (A1 + A2).fieldStrengthMatrix x =
    A1.fieldStrengthMatrix x + A2.fieldStrengthMatrix x := by
  rw [fieldStrengthMatrix, toFieldStrength_add A1 A2 x hA1 hA2]
  conv_rhs => rw [fieldStrengthMatrix, fieldStrengthMatrix]
  simp

lemma toFieldStrength_smul {d} (c : ℝ) (A : ElectromagneticPotential d)
    (x : SpaceTime d) (hA : Differentiable ℝ A) :
    toFieldStrength (c • A) x = c • toFieldStrength A x := by
  apply (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  ext μν
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  repeat rw [toFieldStrength_basis_repr_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  repeat rw [SpaceTime.deriv_eq]
  rw [fderiv_const_smul]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, Lorentz.Vector.apply_smul]
  ring
  exact hA.differentiableAt

lemma fieldStrengthMatrix_smul {d} (c : ℝ) (A : ElectromagneticPotential d)
    (x : SpaceTime d) (hA : Differentiable ℝ A) :
    (c • A).fieldStrengthMatrix x = c • A.fieldStrengthMatrix x := by
  rw [fieldStrengthMatrix, toFieldStrength_smul c A x hA]
  conv_rhs => rw [fieldStrengthMatrix]
  simp

end ElectromagneticPotential

/-!

## B. Field strength for distributions

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

### B.1. Auxiliary definition of field strength for distributions, with no linearity

-/

/-- An auxiliary definition for the field strength of an electromagnetic potential
  based on a distribution. On Schwartz maps this has the same value as the field strength
  tensor, but no linearity or continuous properties built in. -/
noncomputable def fieldStrengthAux {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) : Lorentz.Vector d ⊗[ℝ] Lorentz.Vector d :=
  Tensorial.toTensor.symm
      (permT id (PermCond.auto) {(η d | μ μ' ⊗ A.deriv ε | μ' ν) + -
      (η d | ν ν' ⊗ A.deriv ε | ν' μ)}ᵀ)

lemma fieldStrengthAux_eq_add {d} (A : DistElectromagneticPotential d) (ε : 𝓢(SpaceTime d, ℝ)) :
    fieldStrengthAux A ε =
    Tensorial.toTensor.symm (permT id (PermCond.auto) {(η d | μ μ' ⊗ A.deriv ε | μ' ν)}ᵀ)
    - Tensorial.toTensor.symm (permT ![1, 0] (PermCond.auto)
      {(η d | μ μ' ⊗ A.deriv ε | μ' ν)}ᵀ) := by
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
    (permT id (PermCond.auto) {(η d | μ μ' ⊗ A.deriv ε | μ' ν)}ᵀ)
    - (permT ![1, 0] (PermCond.auto) {(η d | μ μ' ⊗ A.deriv ε | μ' ν)}ᵀ) := by
  rw [fieldStrengthAux_eq_add]
  simp

lemma toTensor_fieldStrengthAux_basis_repr {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ))
    (b : ComponentIdx (S := realLorentzTensor d) (Fin.append ![Color.up] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (fieldStrengthAux A ε)) b =
    ∑ κ, (η (finSumFinEquiv.symm (b 0)) κ * SpaceTime.distDeriv κ A ε (finSumFinEquiv.symm (b 1)) -
      η (finSumFinEquiv.symm (b 1)) κ * SpaceTime.distDeriv κ A ε (finSumFinEquiv.symm (b 0))) := by
  rw [toTensor_fieldStrengthAux]
  simp only [Tensorial.self_toTensor_apply, map_sub,
    Finsupp.coe_sub, Pi.sub_apply]
  rw [Tensor.permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [1, 2, n]
    rw [Tensor.prodT_basis_repr_apply, contrMetric_repr_apply_eq_minkowskiMatrix]
    enter [1]
    change η (finSumFinEquiv.symm (b 0)) (finSumFinEquiv.symm n)
  conv_lhs =>
    enter [1, 2, n, 2]
    rw [toTensor_deriv_basis_repr_apply]
    change distDeriv (finSumFinEquiv.symm n) A ε (finSumFinEquiv.symm (b 1))
  rw [Tensor.permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [2, 2, n]
    rw [Tensor.prodT_basis_repr_apply, contrMetric_repr_apply_eq_minkowskiMatrix]
    enter [1]
    change η (finSumFinEquiv.symm (b 1)) (finSumFinEquiv.symm n)
  conv_lhs =>
    enter [2, 2, n, 2]
    rw [toTensor_deriv_basis_repr_apply]
    change distDeriv (finSumFinEquiv.symm n) A ε (finSumFinEquiv.symm (b 0))
  rw [← Finset.sum_sub_distrib]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Fin.isValue, Equiv.symm_apply_apply]

lemma fieldStrengthAux_tensor_basis_eq_basis {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ))
    (b : ComponentIdx (S := realLorentzTensor d) (Fin.append ![Color.up] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (A.fieldStrengthAux ε)) b =
    (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (A.fieldStrengthAux ε)
      (finSumFinEquiv.symm (b 0), finSumFinEquiv.symm (b 1)) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Fin.isValue]
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
  rw [Module.Basis.repr_reindex_apply]
  congr 1

lemma fieldStrengthAux_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : DistElectromagneticPotential d) (ε : 𝓢(SpaceTime d, ℝ)) :
    (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (A.fieldStrengthAux ε) μν =
    ∑ κ, ((η μν.1 κ * distDeriv κ A ε μν.2) - η μν.2 κ * distDeriv κ A ε μν.1) := by
  match μν with
  | (μ, ν) =>
  trans (Tensor.basis _).repr (Tensorial.toTensor (A.fieldStrengthAux ε))
    (fun | 0 => finSumFinEquiv μ | 1 => finSumFinEquiv ν); swap
  · rw [toTensor_fieldStrengthAux_basis_repr]
    simp
  rw [fieldStrengthAux_tensor_basis_eq_basis]
  congr 1
  change _ = (finSumFinEquiv.symm (finSumFinEquiv μ), finSumFinEquiv.symm (finSumFinEquiv ν))
  simp

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
  simp [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, smul_eq_mul]
  simp [Finsupp.single_apply]
  rw [fieldStrengthAux_basis_repr_apply_eq_single]

/-!

### B.2. The definition of the field strength

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
      fieldStrengthAux_basis_repr_apply_eq_single, map_add, ContinuousLinearMap.add_apply,
      Lorentz.Vector.apply_add, Finsupp.coe_add, Pi.add_apply]
    ring
  map_smul' c A := by
    ext ε
    apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
    ext μν
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      fieldStrengthAux_basis_repr_apply_eq_single, map_smul, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, Lorentz.Vector.apply_smul, Real.ringHom_apply, Finsupp.coe_smul, smul_eq_mul]
    ring

lemma fieldStrength_eq_fieldStrengthAux {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    A.fieldStrength ε = A.fieldStrengthAux ε := by rfl
/-!

### B.3. Field strength written in terms of a basis

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

### B.4. Equivariance of the field strength for distributions

-/

lemma fieldStrength_equivariant {d} (A : DistElectromagneticPotential d)
    (Λ : LorentzGroup d) :
    (Λ • A).fieldStrength = Λ • A.fieldStrength := by
  ext ε
  rw [fieldStrength_eq_fieldStrengthAux, lorentzGroup_smul_dist_apply]
  rw [fieldStrengthAux_eq_add, deriv_equivariant, lorentzGroup_smul_dist_apply,
    ← actionT_contrMetric Λ]
  generalize ((schwartzAction Λ⁻¹) ε) = ε'
  rw [fieldStrength_eq_fieldStrengthAux, fieldStrengthAux_eq_add]
  simp only [Tensorial.toTensor_smul, prodT_equivariant, contrT_equivariant, permT_equivariant,
    ← Tensorial.smul_toTensor_symm, smul_sub]

end DistElectromagneticPotential

end Electromagnetism
