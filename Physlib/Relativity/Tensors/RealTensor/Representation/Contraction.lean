/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.Tensors.RealTensor.CoVector.Representation
public import Mathlib.RepresentationTheory.Intertwining
public import Physlib.Mathematics.ForMathlib.Contraction
/-!

# Contraction of Real Lorentz Vectors and Covectors

We define the intertwining maps which define the contraction of a contravariant Lorentz vector with
a covariant Lorentz vector, and vice versa.

Note: This file will eventually replace `./Pre/Contraction.lean` when we move
  `realLorentzTensor` over to `Vector` and `CoVector`.

-/

@[expose] public section

noncomputable section

open Matrix MatrixGroups Complex TensorProduct minkowskiMatrix

namespace Lorentz
attribute [-simp] Fintype.sum_sum_type
variable {d : ℕ}

/-!

## A. The definitions

-/

TODO "In a similar way to `Vector.contract` and `CoVector.contract`,
  we want to define metrics and units as intertwining maps of representations.
  This should copy (and eventually replace) the definitions e.g. `./Units/Pre.lean`."

/-- The intertwining map defining the contraction of a contravariant Lorentz vector with a
  covariant Lorentz vector. -/
def Vector.contract : (Vector.rep.tprod CoVector.rep).IntertwiningMap
    (Representation.trivial ℝ (LorentzGroup d) ℝ) where
  toLinearMap := by
    refine TensorProduct.lift (LinearMap.mk₂ ℝ (fun φ ψ => ∑ i, φ i * ψ i) ?_ ?_ ?_ ?_)
    · simp [add_mul, Finset.sum_add_distrib]
    · simp [Finset.mul_sum, mul_assoc]
    · simp [mul_add, Finset.sum_add_distrib]
    · intros
      simp_rw [CoVector.apply_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
  isIntertwining' Λ := by
    ext φ ψ
    trans (Λ.1 *ᵥ φ) ⬝ᵥ ((LorentzGroup.transpose Λ⁻¹).1 *ᵥ ψ)
    · simp [dotProduct, Vector.rep_apply_eq_mulVec, CoVector.rep_apply_eq_mulVec]
    · simp [dotProduct_mulVec, LorentzGroup.transpose_val,
        vecMul_transpose, mulVec_mulVec, LorentzGroup.coe_inv, inv_mul_of_invertible Λ.1]
      rfl

/-- The intertwining map defining the contraction of a covariant Lorentz vector with a
  contravariant Lorentz vector. -/
def CoVector.contract : (CoVector.rep.tprod Vector.rep).IntertwiningMap
    (Representation.trivial ℝ (LorentzGroup d) ℝ) where
  toLinearMap := by
    refine TensorProduct.lift (LinearMap.mk₂ ℝ (fun φ ψ => ∑ i, φ i * ψ i) ?_ ?_ ?_ ?_)
    · simp [add_mul, Finset.sum_add_distrib]
    · simp [Finset.mul_sum, mul_assoc]
    · simp [mul_add, Finset.sum_add_distrib]
    · intros
      simp_rw [Vector.apply_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
  isIntertwining' Λ := by
    ext φ ψ
    trans ((LorentzGroup.transpose Λ⁻¹).1 *ᵥ φ) ⬝ᵥ (Λ.1 *ᵥ ψ)
    · simp [dotProduct, Vector.rep_apply_eq_mulVec, CoVector.rep_apply_eq_mulVec]
    · simp [dotProduct_mulVec, LorentzGroup.transpose_val,
        mulVec_transpose, vecMul_vecMul, LorentzGroup.coe_inv, inv_mul_of_invertible Λ.1]
      rfl

/-!

## B. Properties of the contractions

-/

lemma Vector.contract_tmul (φ : Vector d) (ψ : CoVector d) :
    Vector.contract (φ ⊗ₜ ψ) = ∑ i, φ i * ψ i := rfl

lemma CoVector.contract_tmul (φ : CoVector d) (ψ : Vector d) :
    CoVector.contract (φ ⊗ₜ ψ) = ∑ i, φ i * ψ i := rfl

lemma Vector.contract_basis_left (μ : Fin 1 ⊕ Fin d) (ψ : CoVector d) :
    Vector.contract (basis μ ⊗ₜ ψ) = ψ μ := by simp [Vector.contract_tmul, basis_apply]

lemma CoVector.contract_basis_left (μ : Fin 1 ⊕ Fin d) (φ : Vector d) :
    CoVector.contract (basis μ ⊗ₜ φ) = φ μ := by simp [CoVector.contract_tmul, basis_apply]

lemma Vector.contract_basis_right (φ : Vector d) (μ : Fin 1 ⊕ Fin d) :
    Vector.contract (φ ⊗ₜ basis μ) = φ μ := by simp [Vector.contract_tmul, basis_apply]

lemma CoVector.contract_basis_right (ψ : CoVector d) (μ : Fin 1 ⊕ Fin d) :
    CoVector.contract (ψ ⊗ₜ basis μ) = ψ μ := by simp [CoVector.contract_tmul, basis_apply]

lemma Vector.contract_eq_coVector_contract (φ : Vector d) (ψ : CoVector d) :
    Vector.contract (φ ⊗ₜ ψ) = CoVector.contract (ψ ⊗ₜ φ) := by
  simp_rw [Vector.contract_tmul, CoVector.contract_tmul, mul_comm]

/-- The contraction `φ^μ ψ_μ` is the coordinate pairing of `Vector.basis` and `CoVector.basis`. -/
lemma Vector.coordPairing_basis_tmul (φ : Vector d) (ψ : CoVector d) :
    Vector.basis.coordPairing CoVector.basis (φ ⊗ₜ ψ) = Vector.contract (φ ⊗ₜ ψ) := by
  simp [Module.Basis.coordPairing_tmul, Vector.basis_repr_apply, CoVector.basis_repr_apply,
    Vector.contract_tmul]

lemma Vector.contract_rep (Λ : LorentzGroup d) (φ : Vector d) (ψ : CoVector d) :
    Vector.contract ((Vector.rep Λ φ) ⊗ₜ (CoVector.rep Λ ψ)) = Vector.contract (φ ⊗ₜ ψ) := by
  convert! Vector.contract.isIntertwining _ _ Λ (φ ⊗ₜ ψ)

lemma CoVector.contract_rep (Λ : LorentzGroup d) (φ : CoVector d) (ψ : Vector d) :
    CoVector.contract ((CoVector.rep Λ φ) ⊗ₜ (Vector.rep Λ ψ)) = CoVector.contract (φ ⊗ₜ ψ) := by
  convert! CoVector.contract.isIntertwining _ _ Λ (φ ⊗ₜ ψ)

end Lorentz
end
