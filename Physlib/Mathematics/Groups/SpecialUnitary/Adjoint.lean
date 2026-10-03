/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.Groups.SpecialUnitary.GellMann
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RepresentationTheory.Intertwining
/-!
# The adjoint representation of `SU(N)`

## i. Overview

The adjoint representation of `SU(N)` acts on the complexified Lie algebra
`SUAlgebraComplexified N = ℂ ⊗[ℝ] su(N)` as the complexification of the conjugation action
`X ↦ g X g⁻¹` on `su(N)` (A). The generalized Gell-Mann matrices, a real basis of `su(N)`, give the
basis `adjBasis N` of the complexified Lie algebra. Sending `z ⊗ X` to the matrix `z X` identifies
the complexified Lie algebra with the traceless complex matrices (`adjMat`), injectively
(`adjMat_injective`) and onto (`adjMat_ofTraceless`), and on matrices the adjoint action is
conjugation (`adjMat_adjRep`). The coordinates in the Gell-Mann basis are the trace pairings
`tr (λ_a A) / 2`.

In the Gell-Mann basis the adjoint action of `g` has the matrix `adjMatrix g`, with entries
`tr (λ_a g λ_b g⁻¹) / 2`: real, the Gell-Mann matrices being hermitian, and orthogonal, the matrix
of `g⁻¹` being the transpose (B).

The trace form `A ⊗ B ↦ tr (A B)` is symmetric and nondegenerate, the trace pairing with a Gell-Mann
matrix being twice the coordinate, and it is invariant under the adjoint action, so it is the
contraction `adjContr` of two adjoint indices (C).

## ii. Key results

- `suTensor.adjRep` : the adjoint representation on the complexified Lie algebra.
- `suTensor.adjMat` : the complexified Lie algebra as traceless complex matrices.
- `suTensor.adjMatrix` : the matrix of the adjoint action in the Gell-Mann basis.
- `suTensor.adjMatrix_inv` : the matrix of `g⁻¹` is the transpose of that of `g`.
- `suTensor.traceForm_nondegenerate` : the trace form is nondegenerate.
- `suTensor.adjContr` : the contraction of two adjoint indices.

## iii. Table of contents

- A. The adjoint representation on the complexified Lie algebra
- B. The matrix of the adjoint action
- C. The trace form and the contraction

-/

@[expose] public section

open Matrix Module TensorProduct

namespace suTensor

/-!

## A. The adjoint representation on the complexified Lie algebra

-/

variable (N : ℕ)

/-- The generalized Gell-Mann basis `1 ⊗ λ_a` of the complexified Lie algebra `ℂ ⊗[ℝ] su(N)`. -/
noncomputable def adjBasis : Basis (GellMann.Index N) ℂ (SUAlgebraComplexified N) :=
  GellMann.realBasis.baseChange ℂ

lemma adjBasis_apply (a : GellMann.Index N) :
    adjBasis N a = (1 : ℂ) ⊗ₜ[ℝ] GellMann.realBasis a :=
  Module.Basis.baseChange_apply _ _ a

variable {N}

lemma val_inv_mul_val (g : SU N) : (g⁻¹).1 * g.1 = 1 := by
  rw [← Submonoid.coe_mul, inv_mul_cancel]
  rfl

lemma val_inv (g : SU N) : (g⁻¹).1 = star g.1 := by
  have h : g.1 * star g.1 = 1 :=
    mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp g.2).1
  calc (g⁻¹).1 = (g⁻¹).1 * (g.1 * star g.1) := by rw [h, Matrix.mul_one]
    _ = star g.1 := by rw [← Matrix.mul_assoc, val_inv_mul_val, Matrix.one_mul]

/-- The adjoint action `X ↦ g X g†` of `SU(N)` on the real Lie algebra `su(N)`. -/
noncomputable def realAdjRep : Representation ℝ (SU N) (SUAlgebra N) :=
  (SUAlgebraOver.conj (R := ℂ)).comp
    (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)

@[simp]
lemma realAdjRep_val (g : SU N) (X : SUAlgebra N) :
    (realAdjRep g X).1 = g.1 * X.1 * star g.1 := rfl

variable (N)

/-- The adjoint representation on the complexified Lie algebra: the complexification of the
  adjoint action `X ↦ g X g⁻¹` on `su(N)`. -/
noncomputable def adjRep : Representation ℂ (SU N) (SUAlgebraComplexified N) where
  toFun g := (realAdjRep g).baseChange ℂ
  map_one' := by
    rw [map_one]
    exact LinearMap.baseChange_id
  map_mul' g h := by
    rw [map_mul]
    exact LinearMap.baseChange_comp _ _

/-- The matrix of an element of the complexified Lie algebra, `z ⊗ X ↦ z X`: a traceless complex
  matrix. -/
noncomputable def adjMat : SUAlgebraComplexified N →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  (SUAlgebraOver.submodule ℂ N).subtype.liftBaseChange ℂ

variable {N}

@[simp]
lemma adjMat_tmul (z : ℂ) (X : SUAlgebra N) : adjMat N (z ⊗ₜ X) = z • X.1 := rfl

@[simp]
lemma adjMat_adjBasis (a : GellMann.Index N) : adjMat N (adjBasis N a) = GellMann.matrix a := by
  rw [adjBasis_apply, adjMat_tmul, one_smul, GellMann.realBasis_apply_val]

/-- The matrix of an element of the complexified Lie algebra is traceless. -/
lemma trace_adjMat (A : SUAlgebraComplexified N) : (adjMat N A).trace = 0 := by
  induction A using TensorProduct.inductionOn with
  | tmul z X => rw [adjMat_tmul, trace_smul, X.trace_val, smul_zero]
  | add A B hA hB => rw [map_add, trace_add, hA, hB, add_zero]

/-- The adjoint representation moves the matrix by conjugation. -/
@[simp]
lemma adjMat_adjRep (g : SU N) (A : SUAlgebraComplexified N) :
    adjMat N (adjRep N g A) = g.1 * adjMat N A * (g⁻¹).1 := by
  induction A using TensorProduct.inductionOn with
  | tmul z X =>
    change adjMat N (z ⊗ₜ realAdjRep g X) = _
    rw [adjMat_tmul, adjMat_tmul, realAdjRep_val, val_inv, Matrix.mul_smul,
      Matrix.smul_mul]
  | add A B hA hB => rw [map_add, map_add, hA, hB, map_add, Matrix.mul_add, Matrix.add_mul]

/-- The coordinates in the Gell-Mann basis are read off by the trace form,
  `A = ∑ (tr (λ_a A) / 2) λ_a`. -/
lemma adjBasis_repr_apply (A : SUAlgebraComplexified N) (a : GellMann.Index N) :
    (adjBasis N).repr A a = (GellMann.matrix a * adjMat N A).trace / 2 := by
  conv_rhs => rw [← (adjBasis N).sum_repr A]
  simp only [map_sum, map_smul, adjMat_adjBasis, Matrix.mul_sum, Matrix.mul_smul, trace_sum,
    trace_smul, GellMann.trace_matrix_mul_matrix, smul_eq_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  ring

/-- An element of the complexified Lie algebra is determined by its matrix. -/
lemma adjMat_injective : Function.Injective (adjMat N) := fun A B h =>
  (adjBasis N).ext_elem fun a => by rw [adjBasis_repr_apply, adjBasis_repr_apply, h]

/-- The element of the complexified Lie algebra with a given traceless matrix. -/
noncomputable def ofTraceless (M : Matrix (Fin N) (Fin N) ℂ) : SUAlgebraComplexified N :=
  ∑ a, ((GellMann.matrix a * M).trace / 2) • adjBasis N a

/-- Every traceless matrix is the matrix of an element of the complexified Lie algebra. -/
@[simp]
lemma adjMat_ofTraceless {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.trace = 0) :
    adjMat N (ofTraceless M) = M := by
  have h := congrArg Subtype.val
    (GellMann.basis.sum_repr (⟨M, hM⟩ : ↥(LinearMap.ker (Matrix.traceLinearMap (Fin N) ℂ ℂ))))
  simp only [Submodule.coe_sum, Submodule.coe_smul, GellMann.basis_apply_val,
    GellMann.basis_repr_apply] at h
  simp only [ofTraceless, map_sum, map_smul, adjMat_adjBasis]
  exact h

/-!

## B. The matrix of the adjoint action

-/

/-- The matrix of the adjoint action of `g` in the Gell-Mann basis. -/
noncomputable abbrev adjMatrix (g : SU N) : Matrix (GellMann.Index N) (GellMann.Index N) ℂ :=
  LinearMap.toMatrix (adjBasis N) (adjBasis N) (adjRep N g)

/-- The entries of the matrix of the adjoint action, `tr (λ_a g λ_b g⁻¹) / 2`. -/
lemma adjMatrix_apply (g : SU N) (a b : GellMann.Index N) :
    adjMatrix g a b = (GellMann.matrix a * (g.1 * GellMann.matrix b * (g⁻¹).1)).trace / 2 := by
  rw [adjMatrix, LinearMap.toMatrix_apply, adjBasis_repr_apply, adjMat_adjRep, adjMat_adjBasis]

/-- The matrix of the adjoint action is real, the Gell-Mann matrices being hermitian. -/
lemma star_adjMatrix_apply (g : SU N) (a b : GellMann.Index N) :
    star (adjMatrix g a b) = adjMatrix g a b := by
  rw [adjMatrix_apply, star_div₀, ← trace_conjTranspose]
  simp only [conjTranspose_mul, GellMann.conjTranspose_matrix, val_inv, star_eq_conjTranspose,
    conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [show star (2 : ℂ) = 2 by simp, trace_mul_comm g.1]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (GellMann.matrix b), trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The matrix of the adjoint action of `g⁻¹` is the transpose of that of `g`, by the cyclicity
  of the trace. -/
lemma adjMatrix_inv (g : SU N) : adjMatrix g⁻¹ = (adjMatrix g)ᵀ := by
  ext a b
  rw [transpose_apply, adjMatrix_apply, adjMatrix_apply, inv_inv]
  congr 1
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The matrix of the adjoint action of `g⁻¹` times that of `g` is the identity. -/
lemma adjMatrix_inv_mul (g : SU N) : adjMatrix g⁻¹ * adjMatrix g = 1 := by
  rw [adjMatrix, adjMatrix, ← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one,
    LinearMap.toMatrix_one]

/-!

## C. The trace form and the contraction

-/

variable (N)

/-- The trace form `A ⊗ B ↦ tr (A B)` on the complexified Lie algebra. -/
noncomputable def traceForm : LinearMap.BilinForm ℂ (SUAlgebraComplexified N) :=
  LinearMap.mk₂ ℂ (fun A B => (adjMat N A * adjMat N B).trace)
    (fun A A' B => by simp [add_mul, trace_add])
    (fun a A B => by simp)
    (fun A B B' => by simp [mul_add, trace_add])
    (fun a A B => by simp)

@[simp]
lemma traceForm_apply (A B : SUAlgebraComplexified N) :
    traceForm N A B = (adjMat N A * adjMat N B).trace := rfl

/-- The trace form is symmetric. -/
lemma traceForm_isSymm : (traceForm N).IsSymm :=
  ⟨fun A B => by rw [traceForm_apply, traceForm_apply, trace_mul_comm]⟩

/-- The trace form against a Gell-Mann basis vector is twice the coordinate. -/
lemma traceForm_adjBasis (A : SUAlgebraComplexified N) (a : GellMann.Index N) :
    traceForm N A (adjBasis N a) = 2 * (adjBasis N).repr A a := by
  rw [traceForm_apply, adjMat_adjBasis, adjBasis_repr_apply, trace_mul_comm]
  ring

/-- An element orthogonal to every element under the trace form vanishes: its coordinates are its
  trace pairings with the Gell-Mann basis. -/
lemma traceForm_separatingLeft (A : SUAlgebraComplexified N) (hA : ∀ B, traceForm N A B = 0) :
    A = 0 :=
  (adjBasis N).ext_elem fun a => by
    have h := hA (adjBasis N a)
    rw [traceForm_adjBasis] at h
    simpa using h

/-- The trace form is nondegenerate on the complexified Lie algebra. -/
lemma traceForm_nondegenerate : (traceForm N).Nondegenerate :=
  ⟨traceForm_separatingLeft N, fun B hB => traceForm_separatingLeft N B fun A => by
    rw [(traceForm_isSymm N).eq]
    exact hB A⟩

/-- The contraction of two adjoint indices, the trace form `A ⊗ B ↦ tr (A B)`. -/
noncomputable def adjContr : ((adjRep N).tprod (adjRep N)).IntertwiningMap
    (Representation.trivial ℂ (SU N) ℂ) where
  toLinearMap := TensorProduct.lift (traceForm N)
  isIntertwining' g := TensorProduct.ext' fun A B => by
    change (adjMat N (adjRep N g A) * adjMat N (adjRep N g B)).trace
      = (adjMat N A * adjMat N B).trace
    rw [adjMat_adjRep, adjMat_adjRep, show g.1 * adjMat N A * (g⁻¹).1 * (g.1 * adjMat N B * (g⁻¹).1)
        = g.1 * (adjMat N A * adjMat N B) * (g⁻¹).1 by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (g⁻¹).1, val_inv_mul_val, Matrix.one_mul]]
    rw [Matrix.trace_mul_cycle, val_inv_mul_val, one_mul]

/-- The trace form separates the complexified Lie algebra. -/
lemma adjContr_flip_injective :
    Function.Injective (TensorProduct.curry (adjContr N).toLinearMap).flip := fun w w' h => by
  refine sub_eq_zero.1 ((traceForm_nondegenerate N).2 _ fun x => ?_)
  have hx := LinearMap.congr_fun h x
  simp only [LinearMap.flip_apply, TensorProduct.curry_apply] at hx
  rw [map_sub, sub_eq_zero]
  exact hx

end suTensor
