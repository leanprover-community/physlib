/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.Two
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Basic
/-!

## Pauli matrices as Lorentz tensors

The results in this file are primarily used to show that
the pauli matrices in invariant under the `SL(2,ℂ)` action.

-/

@[expose] public section

namespace Lorentz.ComplexVector

open Complex
open Lorentz
open Fermion
open TensorProduct

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct PauliMatrix

/-- The tensor `σ^μ^a^{dot a}` based on the Pauli-matrices as an element of
  `ComplexVector ⊗ LeftHandedWeyl ⊗ RightHandedWeyl`. -/
def pauliVal : ComplexVector ⊗[ℂ] (LeftHandedWeyl ⊗[ℂ] RightHandedWeyl) :=
  ∑ i, ComplexVector.basis i ⊗ₜ leftRightToMatrix.symm (pauliBasis i)

/-- The expansion of `ComplexVector.pauliVal` into `ComplexVector.basis` basis vectors. -/
lemma pauliVal_expand_basis : ComplexVector.pauliVal =
    ComplexVector.basis (Sum.inl 0) ⊗ₜ leftRightToMatrix.symm (pauliBasis (Sum.inl 0))
    + ComplexVector.basis (Sum.inr 0) ⊗ₜ leftRightToMatrix.symm (pauliBasis (Sum.inr 0))
    + ComplexVector.basis (Sum.inr 1) ⊗ₜ leftRightToMatrix.symm (pauliBasis (Sum.inr 1))
    + ComplexVector.basis (Sum.inr 2) ⊗ₜ leftRightToMatrix.symm (pauliBasis (Sum.inr 2)) := by
  rfl

/-- The components of `pauliVal` in the basis `e_μ ⊗ e_a ⊗ e_ḃ` are the entries of the
  Pauli matrices. -/
lemma pauliVal_repr (μ : Fin 1 ⊕ Fin 3) (a b : Fin 2) :
    (ComplexVector.basis.tensorProduct
      (LeftHandedWeyl.basis.tensorProduct RightHandedWeyl.basis)).repr pauliVal (μ, (a, b)) =
      pauliMatrix μ a b := by
  have hlr (M : Matrix (Fin 2) (Fin 2) ℂ) :
      (LeftHandedWeyl.basis.tensorProduct RightHandedWeyl.basis).repr
        (leftRightToMatrix.symm M) (a, b) = M a b := by
    change leftRightToMatrix (leftRightToMatrix.symm M) a b = M a b
    rw [LinearEquiv.apply_symm_apply]
  simp [- Fintype.sum_sum_type, pauliVal, Module.Basis.tensorProduct_repr_tmul_apply,
    Finsupp.single_apply, hlr, pauliBasis, pauliSelfAdjoint]

/-- The expansion of `ComplexVector.pauliVal` into the basis of tensor product vectors. -/
lemma pauliVal_expand_tmul : ComplexVector.pauliVal =
    ComplexVector.basis (Sum.inl 0) ⊗ₜ (LeftHandedWeyl.basis 0 ⊗ₜ RightHandedWeyl.basis 0)
    + ComplexVector.basis (Sum.inl 0) ⊗ₜ (LeftHandedWeyl.basis 1 ⊗ₜ RightHandedWeyl.basis 1)
    + ComplexVector.basis (Sum.inr 0) ⊗ₜ (LeftHandedWeyl.basis 0 ⊗ₜ RightHandedWeyl.basis 1)
    + ComplexVector.basis (Sum.inr 0) ⊗ₜ (LeftHandedWeyl.basis 1 ⊗ₜ RightHandedWeyl.basis 0)
    - I • ComplexVector.basis (Sum.inr 1) ⊗ₜ (LeftHandedWeyl.basis 0 ⊗ₜ RightHandedWeyl.basis 1)
    + I • ComplexVector.basis (Sum.inr 1) ⊗ₜ (LeftHandedWeyl.basis 1 ⊗ₜ RightHandedWeyl.basis 0)
    + ComplexVector.basis (Sum.inr 2) ⊗ₜ (LeftHandedWeyl.basis 0 ⊗ₜ RightHandedWeyl.basis 0)
    - ComplexVector.basis (Sum.inr 2) ⊗ₜ (LeftHandedWeyl.basis 1 ⊗ₜ RightHandedWeyl.basis 1) := by
  rw [ComplexVector.pauliVal_expand_basis]
  simp [leftRightToMatrix_symm_expand_tmul, pauliBasis, pauliSelfAdjoint, pauliMatrix,
    Fin.sum_univ_two, tmul_add, tmul_smul]
  module

/-- The Pauli tensor is invariant under the `SL(2, ℂ)` action. -/
lemma pauliVal_invariant (Λ : SL(2,ℂ)) :
    TensorProduct.map (SL2CRep Λ)
      (TensorProduct.map (LeftHandedWeyl.rep Λ) (RightHandedWeyl.rep Λ)) pauliVal = pauliVal := by
  have h (i j) : ∑ k, (SL2C.toLorentzGroup Λ).1 i k * (SL2C.toLorentzGroup Λ⁻¹).1 k j =
      (1 : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) i j := by
    rw [← mul_apply, ← lorentzGroupIsGroup_mul_coe, ← map_mul, mul_inv_cancel, map_one]
    rfl
  simp only [pauliVal, map_sum, map_tmul, SL2CRep_ρ_basis,
    leftRightToMatrix_ρ_symm_selfAdjoint _ (pauliBasis _).2, Subtype.coe_eta,
    SL2C.toSelfAdjointMap_pauliBasis, AddSubgroup.val_finsetSum, selfAdjoint.val_smul,
    ← Complex.coe_smul, map_smul, sum_tmul, tmul_sum, smul_tmul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← ofReal_mul, ← ofReal_sum, h, one_apply,
    apply_ite Complex.ofReal, ofReal_one, ofReal_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The tensor `σ^μ^a^{dot a}` based on the Pauli-matrices as a morphism,
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ ComplexVector ⊗ LeftHandedWeyl ⊗ RightHandedWeyl` manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def pauli :(Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (ComplexVector.SL2CRep.tprod (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep)) where
    toFun := fun a =>
      let a' : ℂ := a
      a' • ComplexVector.pauliVal
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl
    isIntertwining' M := by
      refine LinearMap.ext fun x : ℂ => ?_
      change x • pauliVal = TensorProduct.map _ (TensorProduct.map _ _) (x • pauliVal)
      rw [map_smul, pauliVal_invariant]

/-- The map `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ ComplexVector ⊗ LeftHandedWeyl ⊗ RightHandedWeyl`
  corresponding to Pauli matrices, when evaluated on `1` corresponds to the tensor
  `ComplexVector.pauliVal`. -/
lemma pauli_apply_one :
    ComplexVector.pauli (1 : ℂ) = ComplexVector.pauliVal := by
  change (1 : ℂ) • ComplexVector.pauliVal = ComplexVector.pauliVal
  simp only [one_smul]

end
end Lorentz.ComplexVector
