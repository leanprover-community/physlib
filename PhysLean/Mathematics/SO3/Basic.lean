/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# The group SO(3)

-/

namespace GroupTheory
open Matrix

/-- The group of `3×3` real matrices with determinant 1 and `A * Aᵀ = 1`. -/
def SO3 : Type := {A : Matrix (Fin 3) (Fin 3) ℝ // A.det = 1 ∧ A * Aᵀ = 1}

/-- The instance of a group on `SO3`. -/
@[simps! mul_coe one_coe inv div]
instance SO3Group : Group SO3 where
  mul A B := ⟨A.1 * B.1,
    by
      simp only [det_mul, A.2.1, B.2.1, mul_one],
    by
      simp only [transpose_mul, Matrix.mul_assoc]
      trans A.1 * ((B.1 * (B.1)ᵀ) * (A.1)ᵀ)
      · noncomm_ring
      · simp [B.2.2, A.2.2]⟩
  mul_assoc A B C := Subtype.ext (Matrix.mul_assoc A.1 B.1 C.1)
  one := ⟨1, det_one, by rw [transpose_one, mul_one]⟩
  one_mul A := Subtype.ext (Matrix.one_mul A.1)
  mul_one A := Subtype.ext (Matrix.mul_one A.1)
  inv A := ⟨A.1ᵀ, by simp only [det_transpose, A.2],
    by simp only [transpose_transpose, mul_eq_one_comm.mpr A.2.2]⟩
  inv_mul_cancel A := Subtype.ext (mul_eq_one_comm.mpr A.2.2)

/-- Notation for the group `SO3`. -/
scoped[GroupTheory] notation (name := SO3_notation) "SO(3)" => SO3

/-- SO3 has the subtype topology. -/
instance : TopologicalSpace SO3 := instTopologicalSpaceSubtype

namespace SO3

lemma coe_inv (A : SO3) : (A⁻¹).1 = A.1⁻¹:=
  (inv_eq_left_inv (mul_eq_one_comm.mpr A.2.2)).symm

/-- The inclusion of `SO(3)` into `GL (Fin 3) ℝ`. -/
def toGL : SO(3) →* GL (Fin 3) ℝ where
  toFun A := ⟨A.1, (A⁻¹).1, A.2.2, mul_eq_one_comm.mpr A.2.2⟩
  map_one' := (GeneralLinearGroup.ext_iff _ 1).mpr fun _=> congrFun rfl
  map_mul' _ _ := (GeneralLinearGroup.ext_iff _ _).mpr fun _ => congrFun rfl

lemma subtype_val_eq_toGL : (Subtype.val : SO3 → Matrix (Fin 3) (Fin 3) ℝ) =
    Units.val ∘ toGL.toFun :=
  rfl

/-- The inclusion of `SO(3)` into `GL(3,ℝ)` is an injection. -/
lemma toGL_injective : Function.Injective toGL := by
  refine fun A B h ↦ Subtype.ext ?_
  rwa [@Units.ext_iff] at h

/-- The inclusion of `SO(3)` into the monoid of matrices times the opposite of
  the monoid of matrices. -/
@[simps!]
def toProd : SO(3) →* (Matrix (Fin 3) (Fin 3) ℝ) × (Matrix (Fin 3) (Fin 3) ℝ)ᵐᵒᵖ :=
  MonoidHom.comp (Units.embedProduct _) toGL

lemma toProd_eq_transpose : toProd A = (A.1, ⟨A.1ᵀ⟩) := rfl

lemma toProd_injective : Function.Injective toProd := by
  intro A B h
  rw [toProd_eq_transpose, toProd_eq_transpose, Prod.mk_inj] at h
  exact Subtype.ext h.1

lemma toProd_continuous : Continuous toProd :=
  continuous_prodMk.mpr ⟨continuous_iff_le_induced.mpr fun _ a ↦ a,
    Continuous.comp' (MulOpposite.continuous_op)
      (Continuous.matrix_transpose (continuous_iff_le_induced.mpr fun _ a ↦ a))⟩

open Topology

/-- The embedding of `SO(3)` into the monoid of matrices times the opposite of
  the monoid of matrices. -/
lemma toProd_embedding : IsEmbedding toProd where
  injective := toProd_injective
  eq_induced := (isInducing_iff ⇑toProd).mp (IsInducing.of_comp toProd_continuous
    continuous_fst ((isInducing_iff (Prod.fst ∘ ⇑toProd)).mpr rfl))

/-- The embedding of `SO(3)` into `GL (Fin 3) ℝ`. -/
lemma toGL_embedding : IsEmbedding toGL.toFun where
  injective := toGL_injective
  eq_induced := by
    refine ((fun {X} {t t'} => TopologicalSpace.ext_iff.mpr) ?_).symm
    intro s
    rw [TopologicalSpace.ext_iff.mp toProd_embedding.eq_induced s]
    rw [isOpen_induced_iff, isOpen_induced_iff]
    constructor <;> intro h <;> obtain ⟨U, hU1, hU2⟩ := h
    · rw [isOpen_induced_iff] at hU1
      aesop
    · exact ⟨(Units.embedProduct _) ⁻¹' U, And.intro (isOpen_induced hU1) hU2⟩

/-- The instance of a topological group on `SO(3)`, defined through the embedding of `SO(3)`
  into `GL(n)`. -/
instance : IsTopologicalGroup SO(3) :=
  IsInducing.topologicalGroup toGL toGL_embedding.toIsInducing

/-- The determinant of an `SO(3)` matrix minus the identity is equal to zero. -/
lemma det_minus_id (A : SO(3)) : det (A.1 - 1) = 0 := by
  have h1 : det (A.1 - 1) = - det (A.1 - 1) :=
    calc
      det (A.1 - 1) = det (A.1 - A.1 * A.1ᵀ) := by simp [A.2.2]
      _ = det A.1 * det (1 - A.1ᵀ) := by rw [← det_mul, mul_sub, mul_one]
      _ = det (1 - A.1ᵀ) := by simp [A.2.1]
      _ = det (1 - A.1ᵀ)ᵀ := by rw [det_transpose]
      _ = det (1 - A.1) := rfl
      _ = det (- (A.1 - 1)) := by simp
      _ = (- 1) ^ 3 * det (A.1 - 1) := by simp only [det_neg, Fintype.card_fin]
      _ = - det (A.1 - 1) := by simp [pow_three]
  exact CharZero.eq_neg_self_iff.mp h1

/-- The determinant of the identity minus an `SO(3)` matrix is zero. -/
@[simp]
lemma det_id_minus (A : SO(3)) : det (1 - A.1) = 0 := by
  have h1 : det (1 - A.1) = - det (A.1 - 1) := by
    calc
      det (1 - A.1) = det (- (A.1 - 1)) := by simp
      _ = (- 1) ^ 3 * det (A.1 - 1) := by simp only [det_neg, Fintype.card_fin]
      _ = - det (A.1 - 1) := by simp [pow_three]
  rw [h1, det_minus_id]
  exact neg_zero

/-- For every matrix in `SO(3)`, the real number `1` is in its spectrum. -/
@[simp]
lemma one_in_spectrum (A : SO(3)) : 1 ∈ spectrum ℝ (A.1) := by
  simp [spectrum.mem_iff, _root_.map_one, Matrix.isUnit_iff_isUnit_det]

noncomputable section action
open Module

/-- The endomorphism of `EuclideanSpace ℝ (Fin 3)` associated to a element of `SO(3)`. -/
@[simps!]
def toEnd (A : SO(3)) : End ℝ (EuclideanSpace ℝ (Fin 3)) :=
  Matrix.toLin (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis A.1

/-- Every `SO(3)` matrix has an eigenvalue equal to `1`. -/
lemma one_is_eigenvalue (A : SO(3)) : A.toEnd.HasEigenvalue 1 := by
  rw [End.hasEigenvalue_iff_mem_spectrum]
  erw [AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis) A.1]
  exact one_in_spectrum A

/-- For every element of `SO(3)` there exists a vector which remains unchanged under the
  action of that `SO(3)` element. -/
lemma exists_stationary_vec (A : SO(3)) :
    ∃ (v : EuclideanSpace ℝ (Fin 3)),
    Orthonormal ℝ (({0} : Set (Fin 3)).restrict (fun _ => v))
    ∧ A.toEnd v = v := by
  obtain ⟨v, hv⟩ := End.HasEigenvalue.exists_hasEigenvector $ one_is_eigenvalue A
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  use (1/‖v‖) • v
  constructor
  · rw [@orthonormal_iff_ite]
    intro v1 v2
    simp only [one_div]
    have hveq : v1 = v2 := by aesop
    subst hveq
    rw [Set.restrict_apply, inner_smul_right, inner_smul_left, real_inner_self_eq_norm_sq v]
    simp only [map_inv₀, conj_trivial, Fin.isValue, ↓reduceIte]
    field_simp
  · simp [End.mem_eigenspace_iff.mp hv.1]

/-- For every element of `SO(3)` there exists a basis indexed by `Fin 3` under which the first
  element remains invariant. -/
lemma exists_basis_preserved (A : SO(3)) :
    ∃ (b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))), A.toEnd (b 0) = b 0 := by
  obtain ⟨v, hv⟩ := exists_stationary_vec A
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by aesop) hv.1
  aesop

end action
end SO3

end GroupTheory
