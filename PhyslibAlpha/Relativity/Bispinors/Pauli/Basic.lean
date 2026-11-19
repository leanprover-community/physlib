/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Bispinors.Pauli.Basic
public import PhyslibAlpha.Relativity.SL2C.Basic
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Pre
/-!
# The Pauli tensor is the unique invariant

Up to scale, the Pauli tensor `σ^{μ α α̇}` is the only invariant with a vector, a left-handed and a
right-handed Weyl index.

## i. Overview

The covariant Pauli matrices `σ_μ = η_{μμ} σ^μ` move under `M ∈ SL(2, ℂ)` as a covariant vector,
`M σ_μ Mᴴ = Σ_ν Λ_{ν μ} σ_ν`, so `e_μ ↦ σ_μ` is an equivariant linear map `contrToLeftRight`
from the complex four-vectors to `LeftHandedWeyl ⊗ RightHandedWeyl` (A). By the Fierz completeness
relation the `σ_μ` span all `2 × 2` matrices, so this map is onto. Applied to the second index of
the metric `η^{μν}` it gives the Pauli tensor `pauliVal`, the two lowerings cancelling (B).

So an equivariant map `f` out of `ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)` composed with
`id ⊗ contrToLeftRight` is an equivariant map out of two four-vector indices with the same image,
sending the metric to `f σ`. The invariants in the image of `f` are then the line through `f σ`,
by the uniqueness of the metric of the complex four-vectors (C). For `f` the identity this says
that the invariants of `ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)` are the line through
`σ`, and so every intertwining map from the trivial representation is a multiple of `pauli`.

## ii. Key results

- `Lorentz.ComplexVector.contrToLeftRight` : the equivariant map `e_μ ↦ σ_μ`.
- `Lorentz.ComplexVector.lTensor_contrToLeftRight_metricVal` : it carries the metric to the Pauli
  tensor.
- `Lorentz.ComplexVector.invariants_inf_range_eq_span_map_pauliVal` : the invariants in the image
  of an equivariant map are the line through the image of the Pauli tensor.
- `Lorentz.ComplexVector.invariants_tprod_eq_span_pauliVal` : the invariants are the line through
  the Pauli tensor.
- `Lorentz.ComplexVector.intertwiningMap_eq_smul_pauli` : every intertwining map from the trivial
  representation is a multiple of the Pauli tensor.

## iii. Table of contents

- A. The Pauli matrices as an equivariant map
- B. The metric goes to the Pauli tensor
- C. The Pauli tensor is the unique invariant

## iv. References

The Pauli tensor `ComplexVector.pauliVal` and the intertwining map `ComplexVector.pauli` are in
`Physlib.Relativity.Bispinors.Pauli.Basic`, where these results are written to move. The
uniqueness of the metric of the complex four-vectors is in
`PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Pre`.

-/

@[expose] public section

namespace Lorentz.ComplexVector

open Matrix MatrixGroups TensorProduct Fermion PauliMatrix

noncomputable section

/-!

## A. The Pauli matrices as an equivariant map

-/

/-- The covariant Pauli matrices as a map `e_μ ↦ σ_μ` from complex four-vectors to a left- and a
  right-handed Weyl index. -/
def contrToLeftRightLinear : ComplexVector →ₗ[ℂ] LeftHandedWeyl ⊗[ℂ] RightHandedWeyl :=
  ComplexVector.basis.constr ℂ fun μ => leftRightToMatrix.symm (pauliLower μ)

/-- The basis vector `e_μ` is sent to the lowered Pauli matrix `σ_μ`. -/
lemma contrToLeftRightLinear_basis (μ : Fin 1 ⊕ Fin 3) :
    contrToLeftRightLinear (ComplexVector.basis μ) = leftRightToMatrix.symm (pauliLower μ) :=
  ComplexVector.basis.constr_basis ℂ _ μ

/-- The covariant Pauli matrices move as a covariant vector, so `e_μ ↦ σ_μ` is equivariant. -/
lemma contrToLeftRightLinear_rep (M : SL(2,ℂ)) (v : ComplexVector) :
    contrToLeftRightLinear (ComplexVector.SL2CRep M v) =
      TensorProduct.map (LeftHandedWeyl.rep M) (RightHandedWeyl.rep M)
        (contrToLeftRightLinear v) := by
  have h : contrToLeftRightLinear ∘ₗ ComplexVector.SL2CRep M =
      TensorProduct.map (LeftHandedWeyl.rep M) (RightHandedWeyl.rep M) ∘ₗ
        contrToLeftRightLinear := by
    refine ComplexVector.basis.ext fun μ => ?_
    simp only [LinearMap.comp_apply]
    rw [SL2CRep_ρ_basis, contrToLeftRightLinear_basis, ← pauliBasis'_coe,
      leftRightToMatrix_ρ_symm_selfAdjoint _ (pauliBasis' μ).2]
    change _ = leftRightToMatrix.symm (SL2C.toSelfAdjointMap M (pauliBasis' μ)).1
    have hs (r : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
        leftRightToMatrix.symm (r • X) = r • leftRightToMatrix.symm X :=
      leftRightToMatrix.symm.toLinearMap.map_smul_of_tower r X
    rw [SL2C.toSelfAdjointMap_basis]
    simp [map_sum, LinearMap.map_smul_of_tower, contrToLeftRightLinear_basis, pauliBasis'_coe,
      selfAdjoint.val_smul, hs]
  exact LinearMap.congr_fun h v

/-- The covariant Pauli matrices as an intertwining map `e_μ ↦ σ_μ` from complex four-vectors to
  a left- and a right-handed Weyl index. -/
def contrToLeftRight :
    ComplexVector.SL2CRep.IntertwiningMap (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep) :=
  contrToLeftRightLinear.intertwiningMap_of_isIntertwiningMap _ _ contrToLeftRightLinear_rep

/-- The basis vector `e_μ` is sent to the lowered Pauli matrix `σ_μ`. -/
lemma contrToLeftRight_basis (μ : Fin 1 ⊕ Fin 3) :
    contrToLeftRight (ComplexVector.basis μ) = leftRightToMatrix.symm (pauliLower μ) :=
  contrToLeftRightLinear_basis μ

/-- The covariant Pauli matrices span the `2 × 2` matrices, by the Fierz completeness relation,
  so `e_μ ↦ σ_μ` is onto. -/
lemma contrToLeftRight_surjective : Function.Surjective contrToLeftRight := by
  intro t
  obtain ⟨(X : Matrix (Fin 2) (Fin 2) ℂ), rfl⟩ := leftRightToMatrix.symm.surjective t
  refine ⟨∑ ρ, ((2 : ℂ)⁻¹ * ∑ β : Fin 2, ∑ β' : Fin 2, X β β' * pauliLower ρ β' β) •
    ComplexVector.basis ρ, ?_⟩
  apply leftRightToMatrix.symm.symm.injective
  simp only [map_sum, map_smul, contrToLeftRight_basis, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply]
  refine Matrix.ext fun α α' => ?_
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc ∑ ρ, (2⁻¹ * ∑ β : Fin 2, ∑ β' : Fin 2, X β β' * pauliLower ρ β' β) * pauliLower ρ α α'
      = 2⁻¹ * ∑ β : Fin 2, ∑ β' : Fin 2, X β β' *
          ∑ ρ, pauliLower ρ β' β * pauliLower ρ α α' := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun β' _ => Finset.sum_congr rfl fun ρ _ => by ring
    _ = X α α' := by
        simp only [sum_pauliLower_mul_pauliLower, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true]
        ring

/-!

## B. The metric goes to the Pauli tensor

-/

/-- Applying `e_μ ↦ σ_μ` to the second index of the metric `η^{μν}` gives the Pauli tensor. The
  lowering in `σ_μ` cancels the metric. -/
lemma lTensor_contrToLeftRight_metricVal :
    contrToLeftRight.lTensor ComplexVector.SL2CRep ComplexVector.metricVal =
      ComplexVector.pauliVal := by
  rw [ComplexVector.metricVal_expand_tmul, ComplexVector.pauliVal_expand_basis]
  simp only [map_sub, Representation.IntertwiningMap.lTensor_apply, contrToLeftRight_basis,
    pauliLower_eq_smul]
  simp [minkowskiMatrixZ, pauliBasis, pauliSelfAdjoint, sub_eq_add_neg, tmul_neg]

/-!

## C. The Pauli tensor is the unique invariant

-/

section Invariants

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ SL(2,ℂ) B}

/-- For an equivariant map `f` out of `ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)`, the
  `SL(2,ℂ)`-invariants in the image of `f` are the line through the image `f σ` of the Pauli
  tensor. Composing `f` with `id ⊗ contrToLeftRight` does not change its image and sends the
  metric to `f σ`. -/
lemma invariants_inf_range_eq_span_map_pauliVal
    (f : (ComplexVector.SL2CRep.tprod
      (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep)).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f ComplexVector.pauliVal := by
  rw [← Representation.invariants_inf_range_comp_of_surjective f
      (contrToLeftRight.lTensor ComplexVector.SL2CRep)
      (LinearMap.lTensor_surjective _ contrToLeftRight_surjective),
    ComplexVector.invariants_inf_range_eq_span_map_metricVal,
    Representation.IntertwiningMap.comp_apply, lTensor_contrToLeftRight_metricVal]

/-- The `SL(2,ℂ)`-invariants of `ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)` are the line
  through the Pauli tensor `σ^{μ α α̇}`. -/
lemma invariants_tprod_eq_span_pauliVal :
    (ComplexVector.SL2CRep.tprod (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep)).invariants =
      ℂ ∙ ComplexVector.pauliVal := by
  simpa using invariants_inf_range_eq_span_map_pauliVal (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into
  `ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)` is a multiple of the Pauli tensor. -/
lemma intertwiningMap_eq_smul_pauli
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (ComplexVector.SL2CRep.tprod (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep))) :
    ∃ z : ℂ, φ = z • ComplexVector.pauli :=
  Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span
    (by rw [ComplexVector.pauli_apply_one]; exact invariants_tprod_eq_span_pauliVal) φ

end Invariants

end

end Lorentz.ComplexVector
