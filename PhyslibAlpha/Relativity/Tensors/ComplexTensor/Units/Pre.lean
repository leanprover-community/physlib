/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Pre
/-!
# The units are the unique invariants

Up to scale, the unit `δ` is the only invariant of a complex Lorentz vector index and a covector
index.

## i. Overview

On `ComplexVector ⊗ ComplexCoVector` the group `SL(2, ℂ)` acts on the matrix of components by
`X ↦ Λ X Λ⁻¹`, and on `ComplexCoVector ⊗ ComplexVector` by `X ↦ Λ⁻¹ᵀ X Λᵀ`, with `Λ` the
complexified Lorentz matrix. Since `Λ⁻¹ = η Λᵀ η`, multiplying the matrix of components by the
complexified Minkowski matrix `η` on the right, respectively on the left, turns either action into
the action `Y ↦ Λ Y Λᵀ` on two contravariant indices (A). The classification of invariants for that
action in `PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Pre` then applies, and `η` goes to
`η η = 1`, the matrix of components of the unit. For each of the two orderings this gives three
statements: every invariant in the image of an equivariant map is a multiple of the image of the
unit, the invariants of the tensor product are the line through the unit, and every intertwining
map out of the trivial representation is a multiple of the unit (B, C).

## ii. Key results

- `Lorentz.ComplexCoVector.invariants_inf_range_eq_span_map_unitVal` : the invariants in the
  image of an equivariant map out of `ComplexVector ⊗ ComplexCoVector` are the line through the
  image of the unit.
- `Lorentz.ComplexCoVector.invariants_tprod_eq_span_unitVal` : the invariants of
  `ComplexVector ⊗ ComplexCoVector` are the line through the unit.
- `Lorentz.ComplexCoVector.intertwiningMap_eq_smul_unit` : every intertwining map from the trivial
  representation into `ComplexVector ⊗ ComplexCoVector` is a multiple of the unit.
- `Lorentz.ComplexVector.invariants_inf_range_eq_span_map_unitVal`,
  `Lorentz.ComplexVector.invariants_tprod_eq_span_unitVal`,
  `Lorentz.ComplexVector.intertwiningMap_eq_smul_unit` : the same for
  `ComplexCoVector ⊗ ComplexVector`.

## iii. Table of contents

- A. Reparametrising the mixed actions by the Minkowski matrix
- B. A contravariant then a covariant index
- C. A covariant then a contravariant index

## iv. References

The units are in `Physlib.Relativity.Tensors.ComplexTensor.Units.Pre`, where these results are
written to move. The analogous results for Weyl fermions are in
`PhyslibAlpha.Relativity.Fermions.Weyl.Unit`.

-/

@[expose] public section

noncomputable section

open Module Matrix MatrixGroups Complex TensorProduct

/-!

## A. Reparametrising the mixed actions by the Minkowski matrix

-/

namespace LorentzGroup

variable {d : ℕ}

/-- Multiplying on the right by `η` turns the action `X ↦ Λ X Λ⁻¹` on a contravariant and a
  covariant index into the action `Y ↦ Λ Y Λᵀ` on two contravariant indices. -/
lemma toComplex_mul_mul_minkowskiMatrix_map_mul_inv (Λ : LorentzGroup d)
    (Y : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℂ) :
    toComplex Λ * (Y * minkowskiMatrix.map ofRealHom) * (toComplex Λ)⁻¹ =
      toComplex Λ * Y * (toComplex Λ)ᵀ * minkowskiMatrix.map ofRealHom := by
  simp only [Matrix.mul_assoc, minkowskiMatrix_map_mul_inv_toComplex]

/-- Multiplying on the left by `η` turns the action `X ↦ Λ⁻¹ᵀ X Λᵀ` on a covariant and a
  contravariant index into the action `Y ↦ Λ Y Λᵀ` on two contravariant indices. -/
lemma inv_toComplex_transpose_mul_minkowskiMatrix_map_mul_mul (Λ : LorentzGroup d)
    (Y : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℂ) :
    (toComplex Λ)⁻¹ᵀ * (minkowskiMatrix.map ofRealHom * Y) * (toComplex Λ)ᵀ =
      minkowskiMatrix.map ofRealHom * (toComplex Λ * Y * (toComplex Λ)ᵀ) := by
  rw [← Matrix.mul_assoc, inv_toComplex_transpose_mul_minkowskiMatrix_map]
  simp only [Matrix.mul_assoc]

end LorentzGroup

namespace Lorentz

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ SL(2,ℂ) B}

/-!

## B. A contravariant then a covariant index

-/

/-- The invariants in the image of an equivariant map `f` out of
  `ComplexVector ⊗ ComplexCoVector` are the line through the image `f δⁱᵢ` of the unit. -/
lemma ComplexCoVector.invariants_inf_range_eq_span_map_unitVal
    (f : (ComplexVector.SL2CRep.tprod ComplexCoVector.SL2CRep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f ComplexCoVector.unitVal := by
  have h := invariants_inf_range_eq_span_map_minkowskiMatrix f
    (contrCoToMatrix.symm.toLinearMap ∘ₗ LinearMap.mulRight ℂ (minkowskiMatrix.map ofRealHom))
    (fun v => ⟨contrCoToMatrix v * minkowskiMatrix.map ofRealHom,
      by simp [Matrix.mul_assoc, LorentzGroup.minkowskiMatrix_map_mul_self]⟩)
    fun g Y => by
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearEquiv.coe_coe,
        Representation.tprod_apply, contrCoToMatrix_ρ_symm,
        LorentzGroup.toComplex_mul_mul_minkowskiMatrix_map_mul_inv]
  simpa [LorentzGroup.minkowskiMatrix_map_mul_self, ComplexCoVector.unitVal] using h

/-- Up to scale, the unit `δⁱᵢ` is the unique invariant of `ComplexVector ⊗ ComplexCoVector`. -/
lemma ComplexCoVector.invariants_tprod_eq_span_unitVal :
    (ComplexVector.SL2CRep.tprod ComplexCoVector.SL2CRep).invariants =
      ℂ ∙ ComplexCoVector.unitVal := by
  simpa using invariants_inf_range_eq_span_map_unitVal (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into
  `ComplexVector ⊗ ComplexCoVector` is a multiple of the unit `δⁱᵢ`. -/
lemma ComplexCoVector.intertwiningMap_eq_smul_unit
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (ComplexVector.SL2CRep.tprod ComplexCoVector.SL2CRep)) :
    ∃ z : ℂ, φ = z • ComplexCoVector.unit :=
  Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span
    (by rw [unit_apply_one]; exact invariants_tprod_eq_span_unitVal) φ

/-!

## C. A covariant then a contravariant index

-/

/-- The invariants in the image of an equivariant map `f` out of
  `ComplexCoVector ⊗ ComplexVector` are the line through the image `f δᵢⁱ` of the unit. -/
lemma ComplexVector.invariants_inf_range_eq_span_map_unitVal
    (f : (ComplexCoVector.SL2CRep.tprod ComplexVector.SL2CRep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f ComplexVector.unitVal := by
  have h := invariants_inf_range_eq_span_map_minkowskiMatrix f
    (coContrToMatrix.symm.toLinearMap ∘ₗ LinearMap.mulLeft ℂ (minkowskiMatrix.map ofRealHom))
    (fun v => ⟨minkowskiMatrix.map ofRealHom * coContrToMatrix v,
      by simp [LorentzGroup.minkowskiMatrix_map_mul_minkowskiMatrix_map_mul]⟩)
    fun g Y => by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe,
        Representation.tprod_apply, coContrToMatrix_ρ_symm,
        LorentzGroup.inv_toComplex_transpose_mul_minkowskiMatrix_map_mul_mul]
  simpa [LorentzGroup.minkowskiMatrix_map_mul_self, ComplexVector.unitVal] using h

/-- Up to scale, the unit `δᵢⁱ` is the unique invariant of `ComplexCoVector ⊗ ComplexVector`. -/
lemma ComplexVector.invariants_tprod_eq_span_unitVal :
    (ComplexCoVector.SL2CRep.tprod ComplexVector.SL2CRep).invariants =
      ℂ ∙ ComplexVector.unitVal := by
  simpa using invariants_inf_range_eq_span_map_unitVal (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into
  `ComplexCoVector ⊗ ComplexVector` is a multiple of the unit `δᵢⁱ`. -/
lemma ComplexVector.intertwiningMap_eq_smul_unit
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (ComplexCoVector.SL2CRep.tprod ComplexVector.SL2CRep)) :
    ∃ z : ℂ, φ = z • ComplexVector.unit :=
  Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span
    (by rw [unit_apply_one]; exact invariants_tprod_eq_span_unitVal) φ

end Lorentz
