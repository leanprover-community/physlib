/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SL2C.SelfAdjoint
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Physlib.Relativity.LorentzGroup.Restricted.Basic
/-!
# The group SL(2, ℂ) and it's relation to the Lorentz group

The aim of this file is to give the relationship between `SL(2, ℂ)` and the Lorentz group.

-/

@[expose] public section
namespace Lorentz

open Module Matrix
open MatrixGroups
open Complex

namespace SL2C

noncomputable section

/-!

## Some basic properties about SL(2, ℂ)

Possibly to be moved to mathlib at some point.
-/

lemma inverse_coe (M : SL(2, ℂ)) : M.1⁻¹ = (M⁻¹).1 := by
  rw [SpecialLinearGroup.coe_inv, Matrix.inv_def, SpecialLinearGroup.det_coe]
  simp

lemma transpose_coe (M : SL(2, ℂ)) : M.1ᵀ = (M.transpose).1 := rfl
/-!

## Representation of SL(2, ℂ) on spacetime

Through the correspondence between spacetime and self-adjoint matrices,
we can define a representation a representation of `SL(2, ℂ)` on spacetime.

-/

/-- Given an element `M ∈ SL(2, ℂ)` the linear map from `selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)` to
  itself defined by `A ↦ M * A * Mᴴ`. -/
@[simps!]
noncomputable def toSelfAdjointMap (M : SL(2, ℂ)) :
    selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) →ₗ[ℝ] selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun A := ⟨M.1 * A.1 * Matrix.conjTranspose M,
    by
      noncomm_ring [selfAdjoint.mem_iff, star_eq_conjTranspose,
        conjTranspose_mul, conjTranspose_conjTranspose,
        (star_eq_conjTranspose A.1).symm.trans $ selfAdjoint.mem_iff.mp A.2]⟩
  map_add' A B := by
    simp only [AddSubgroup.coe_add, AddMemClass.mk_add_mk, Subtype.mk.injEq]
    noncomm_ring [AddSubmonoid.coe_add, AddSubgroup.coe_toAddSubmonoid, AddSubmonoid.mk_add_mk,
      Subtype.mk.injEq]
  map_smul' r A := by
    noncomm_ring [selfAdjoint.val_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      RingHom.id_apply]

lemma toSelfAdjointMap_apply (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    toSelfAdjointMap M A = ⟨M.1 * A.1 * Matrix.conjTranspose M, by
        noncomm_ring [selfAdjoint.mem_iff, star_eq_conjTranspose,
        conjTranspose_mul, conjTranspose_conjTranspose,
        (star_eq_conjTranspose A.1).symm.trans $ selfAdjoint.mem_iff.mp A.2]⟩ := rfl

lemma toSelfAdjointMap_apply_det (M : SL(2, ℂ)) (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    det ((toSelfAdjointMap M) A).1 = det A.1 := by
  simp [toSelfAdjointMap]

lemma toSelfAdjointMap_apply_pauliBasis'_inl (M : SL(2, ℂ)) :
    toSelfAdjointMap M (PauliMatrix.pauliBasis' (Sum.inl 0)) =
    ((‖M.1 0 0‖ ^ 2 + ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2) •
      PauliMatrix.pauliBasis' (Sum.inl 0) +
    (- ((M.1 0 1).re * (M.1 1 1).re + (M.1 0 1).im * (M.1 1 1).im +
      (M.1 0 0).im * (M.1 1 0).im + (M.1 0 0).re * (M.1 1 0).re)) •
        PauliMatrix.pauliBasis' (Sum.inr 0)
    + ((- (M.1 0 0).re * (M.1 1 0).im + ↑(M.1 1 0).re * (M.1 0 0).im
      - (M.1 0 1).re * (M.1 1 1).im + (M.1 0 1).im * (M.1 1 1).re)) •
        PauliMatrix.pauliBasis' (Sum.inr 1)
    + ((- ‖M.1 0 0‖ ^ 2 - ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2) •
      PauliMatrix.pauliBasis' (Sum.inr 2) := by
  simp only [toSelfAdjointMap, PauliMatrix.pauliBasis', Fin.isValue, Basis.coe_mk,
    PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix, one_fin_two, LinearMap.coe_mk,
    AddHom.coe_mk, neg_add_rev, neg_of, neg_cons, neg_zero, neg_empty, neg_mul, neg_neg]
  ext1
  simp only [Fin.isValue, AddSubgroup.coe_add, selfAdjoint.val_smul, smul_of, smul_cons, real_smul,
    ofReal_div, ofReal_add, ofReal_pow, ofReal_ofNat, mul_one, smul_zero, smul_empty, smul_neg,
    ofReal_neg, ofReal_mul, neg_add_rev, neg_neg, of_add_of, add_cons, head_cons, add_zero,
    tail_cons, zero_add, empty_add_empty, ofReal_sub]
  conv => lhs; erw [← eta_fin_two 1, mul_one]
  conv => lhs; lhs; rw [eta_fin_two M.1]
  conv => lhs; rhs; rw [eta_fin_two M.1ᴴ]
  simp only [Fin.isValue, conjTranspose_apply, RCLike.star_def, cons_mul, Nat.succ_eq_add_one,
    Nat.reduceAdd, vecMul_cons, head_cons, smul_cons, smul_eq_mul, smul_empty, tail_cons,
    empty_vecMul, add_zero, add_cons, empty_add_empty, empty_mul, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rw [mul_conj', mul_conj', mul_conj', mul_conj']
  ext x y
  match x, y with
  | 0, 0 | 1, 1 =>
    simp only [Fin.isValue, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    ring_nf
  | 0, 1 | 1, 0 =>
    simp only [Fin.isValue, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    ring_nf
    rw [← re_add_im (M.1 0 0), ← re_add_im (M.1 0 1), ← re_add_im (M.1 1 0), ← re_add_im (M.1 1 1)]
    simp only [Fin.isValue, map_add, conj_ofReal, _root_.map_mul, conj_I, mul_neg, add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im,
      mul_im, zero_add]
    ring_nf
    simp only [Fin.isValue, I_sq, mul_neg, mul_one, neg_mul, one_mul, sub_neg_eq_add]
    ring

/-- The monoid homomorphisms from `SL(2, ℂ)` to matrices indexed by `Fin 1 ⊕ Fin 3`
  formed by the action `M A Mᴴ`. -/
def toMatrix : SL(2, ℂ) →* Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ where
  toFun M := LinearMap.toMatrix PauliMatrix.pauliBasis' PauliMatrix.pauliBasis' (toSelfAdjointMap M)
  map_one' := by
    simp only [toSelfAdjointMap, SpecialLinearGroup.coe_one, one_mul, conjTranspose_one,
      mul_one, Subtype.coe_eta]
    erw [LinearMap.toMatrix_one]
  map_mul' M N := by
    rw [← LinearMap.toMatrix_mul]
    apply congrArg
    ext1 x
    erw [Module.End.mul_apply]
    simp only [toSelfAdjointMap_apply, SpecialLinearGroup.coe_mul, conjTranspose_mul,
      Subtype.mk.injEq]
    ext1
    noncomm_ring

open Lorentz in
lemma toMatrix_apply_contrMod (M : SL(2, ℂ)) (v : ContrMod 3) :
    (toMatrix M) *ᵥ v = ContrMod.toSelfAdjoint.symm
    ((toSelfAdjointMap M) (ContrMod.toSelfAdjoint v)) := by
  simp only [ContrMod.mulVec, toMatrix, MonoidHom.coe_mk, OneHom.coe_mk]
  obtain ⟨a, ha⟩ := ContrMod.toSelfAdjoint.symm.surjective v
  subst ha
  rw [LinearEquiv.apply_symm_apply]
  simp only [ContrMod.toSelfAdjoint, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply]
  change ContrMod.toFin1dℝEquiv.symm
    ((((LinearMap.toMatrix PauliMatrix.pauliBasis' PauliMatrix.pauliBasis') (toSelfAdjointMap M)))
    *ᵥ (((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin 1 ⊕ Fin 3))
    (PauliMatrix.pauliBasis'.repr a)))) = _
  apply congrArg
  erw [LinearMap.toMatrix_mulVec_repr]
  rfl

lemma toMatrix_mem_lorentzGroup (M : SL(2, ℂ)) : toMatrix M ∈ LorentzGroup 3 := by
  rw [LorentzGroup.mem_iff_norm]
  intro x
  apply ofReal_injective
  rw [Lorentz.contrContrContractField.same_eq_det_toSelfAdjoint, toMatrix_apply_contrMod,
    LinearEquiv.apply_symm_apply, toSelfAdjointMap_apply_det,
    Lorentz.contrContrContractField.same_eq_det_toSelfAdjoint]

/-- The group homomorphism from `SL(2, ℂ)` to the Lorentz group `𝓛`. -/
@[simps!]
def toLorentzGroup : SL(2, ℂ) →* LorentzGroup 3 where
  toFun M := ⟨toMatrix M, toMatrix_mem_lorentzGroup M⟩
  map_one' := by
    simp only [_root_.map_one]
    rfl
  map_mul' M N := by
    ext1
    simp only [_root_.map_mul, lorentzGroupIsGroup_mul_coe]

lemma toLorentzGroup_eq_pauliBasis' (M : SL(2, ℂ)) :
    toLorentzGroup M = LinearMap.toMatrix
    PauliMatrix.pauliBasis' PauliMatrix.pauliBasis' (toSelfAdjointMap M) := by
  rfl

lemma toSelfAdjointMap_basis (i : Fin 1 ⊕ Fin 3) :
    toSelfAdjointMap M (PauliMatrix.pauliBasis' i) =
    ∑ j, (toLorentzGroup M).1 j i • PauliMatrix.pauliBasis' j := by
  rw [toLorentzGroup_eq_pauliBasis']
  simp only [LinearMap.toMatrix_apply]
  nth_rewrite 1 [← (Basis.sum_repr PauliMatrix.pauliBasis'
    ((toSelfAdjointMap M) (PauliMatrix.pauliBasis' i)))]
  rfl

lemma toSelfAdjointMap_pauliBasis (i : Fin 1 ⊕ Fin 3) :
    toSelfAdjointMap M (PauliMatrix.pauliBasis i) =
    ∑ j, (toLorentzGroup M⁻¹).1 i j • PauliMatrix.pauliBasis j := by
  have h1 : (toLorentzGroup M⁻¹).1 = minkowskiMatrix.dual (toLorentzGroup M).1 := by
    simp [LorentzGroup.inv_eq_dual]
  simp only [h1]
  rw [PauliMatrix.pauliBasis_minkowskiMetric_pauliBasis', _root_.map_smul, toSelfAdjointMap_basis,
    Finset.smul_sum]
  apply congrArg
  funext j
  rw [smul_smul, PauliMatrix.pauliBasis_minkowskiMetric_pauliBasis', smul_smul]
  apply congrFun
  apply congrArg
  exact Eq.symm (minkowskiMatrix.dual_apply_minkowskiMatrix ((toLorentzGroup M).1) i j)

/-- The matrix elements of the covering map through the trace pairing:
  `L(M)_{i j} = ½ tr (σ'_i · M σ'_j M†)`. -/
lemma toLorentzGroup_eq_trace (M : SL(2,ℂ)) (i j : Fin 1 ⊕ Fin 3) :
    (((toLorentzGroup M).1 i j : ℝ) : ℂ) =
      Matrix.trace ((PauliMatrix.pauliSelfAdjoint' i).1 *
        (M.1 * (PauliMatrix.pauliSelfAdjoint' j).1 * M.1ᴴ)) / 2 := by
  have h := congrArg (fun A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) =>
    Matrix.trace ((PauliMatrix.pauliSelfAdjoint' i).1 * A.1))
    (toSelfAdjointMap_basis (M := M) j)
  simp only [toSelfAdjointMap_apply_coe, PauliMatrix.pauliBasis',
    Module.Basis.coe_mk, AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_smul,
    Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    PauliMatrix.trace_pauliSelfAdjoint'_mul, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true] at h
  rw [h, real_smul]
  ring

/-- The covering map intertwines conjugate transposition with matrix
  transposition: `L(M†) = L(M)ᵀ`. -/
lemma toLorentzGroup_conjTranspose {M N : SL(2,ℂ)} (hN : N.1 = M.1ᴴ) :
    (toLorentzGroup N).1 = (toLorentzGroup M).1ᵀ := by
  ext l i
  refine Complex.ofReal_injective ?_
  have h1 := toLorentzGroup_eq_trace N l i
  have h2 := toLorentzGroup_eq_trace M i l
  rw [hN] at h1
  rw [Matrix.transpose_apply, h1, h2]
  congr 1
  rw [Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc]

/-- The first column of the Lorentz matrix formed from an element of `SL(2, ℂ)`. -/
lemma toLorentzGroup_fst_col (M : SL(2, ℂ)) :
    (fun μ => (toLorentzGroup M).1 μ (Sum.inl 0)) = fun μ =>
      match μ with
      | Sum.inl 0 => ((‖M.1 0 0‖ ^ 2 + ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2)
      | Sum.inr 0 => (- ((M.1 0 1).re * (M.1 1 1).re + (M.1 0 1).im * (M.1 1 1).im +
        (M.1 0 0).im * (M.1 1 0).im + (M.1 0 0).re * (M.1 1 0).re))
      | Sum.inr 1 => ((- (M.1 0 0).re * (M.1 1 0).im + ↑(M.1 1 0).re * (M.1 0 0).im
        - (M.1 0 1).re * (M.1 1 1).im + (M.1 0 1).im * (M.1 1 1).re))
      | Sum.inr 2 => ((- ‖M.1 0 0‖ ^ 2 - ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2) := by
  let k : Fin 1 ⊕ Fin 3 → ℝ := fun μ =>
    match μ with
    | Sum.inl 0 => ((‖M.1 0 0‖ ^ 2 + ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2)
    | Sum.inr 0 => (- ((M.1 0 1).re * (M.1 1 1).re + (M.1 0 1).im * (M.1 1 1).im +
      (M.1 0 0).im * (M.1 1 0).im + (M.1 0 0).re * (M.1 1 0).re))
    | Sum.inr 1 => ((- (M.1 0 0).re * (M.1 1 0).im + ↑(M.1 1 0).re * (M.1 0 0).im
      - (M.1 0 1).re * (M.1 1 1).im + (M.1 0 1).im * (M.1 1 1).re))
    | Sum.inr 2 => ((- ‖M.1 0 0‖ ^ 2 - ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2)
  change (fun μ => (toLorentzGroup M).1 μ (Sum.inl 0)) = k
  have h1 : toSelfAdjointMap M (PauliMatrix.pauliBasis' (Sum.inl 0)) =
      ∑ μ, k μ • PauliMatrix.pauliBasis' μ := by
    simp only [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, Fin.sum_univ_three]
    rw [toSelfAdjointMap_apply_pauliBasis'_inl]
    abel
  rw [toSelfAdjointMap_basis] at h1
  have h1x := sub_eq_zero_of_eq h1
  rw [← Finset.sum_sub_distrib] at h1x
  funext μ
  refine sub_eq_zero.mp ?_
  refine Fintype.linearIndependent_iff.mp PauliMatrix.pauliBasis'.linearIndependent
    (fun x => ((toLorentzGroup M).1 x (Sum.inl 0) - k x)) ?_ μ
  simp only [sub_smul]
  exact h1x

/-- The first element of the image of `SL(2, ℂ)` in the Lorentz group. -/
lemma toLorentzGroup_inl_inl (M : SL(2, ℂ)) :
    (toLorentzGroup M).1 (Sum.inl 0) (Sum.inl 0) =
    ((‖M.1 0 0‖ ^ 2 + ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2) := by
  exact congrFun (toLorentzGroup_fst_col M) (Sum.inl 0)

/-- The image of `SL(2, ℂ)` in the Lorentz group is orthochronous. -/
lemma toLorentzGroup_isOrthochronous (M : SL(2, ℂ)) :
    LorentzGroup.IsOrthochronous (toLorentzGroup M) := by
  rw [LorentzGroup.IsOrthochronous, toLorentzGroup_inl_inl]
  positivity

/-!

## Homomorphism to the restricted Lorentz group

The homomorphism `toLorentzGroup` restricts to a homomorphism to the restricted Lorentz group.
In this section we will define this homomorphism.

-/

/-- The determinant of the image of `SL(2, ℂ)` in the Lorentz group is one. -/
lemma toLorentzGroup_det_one (M : SL(2, ℂ)) : det (toLorentzGroup M).val = 1 :=
  let U := M.val.schurTriangulationUnitary
  let N := M.val.schurTriangulation.val
  have h : M.val = U * N * star U := M.val.schur_triangulation
  haveI : Invertible U.val := ⟨star U.val, U.property.left, U.property.right⟩
  calc det (toLorentzGroup M).val
    _ = LinearMap.det (toSelfAdjointMap' M) := LinearMap.det_toMatrix ..
    _ = LinearMap.det (toSelfAdjointMap' (U * N * U.val⁻¹)) :=
      suffices star U = U.val⁻¹ by rw [h, this]
      calc star U.val
        _ = star U.val * (U.val * U.val⁻¹) := by simp
        _ = star U.val * U.val * U.val⁻¹ := by noncomm_ring
        _ = U.val⁻¹ := by simp
    _ = LinearMap.det (toSelfAdjointMap' N) := toSelfAdjointMap_similar_det U N
    _ = 1 :=
      suffices N.det = 1 from toSelfAdjointMap_det_one' M.val.schurTriangulation.property this
      calc N.det
        _ = det ((U * star U).val * N) := by simp
        _ = det (U.val * N * star U.val) := det_mul_right_comm ..
        _ = M.val.det := congrArg det h.symm
        _ = 1 := M.property

/-- The homomorphism from `SL(2, ℂ)` to the restricted Lorentz group. -/
@[simps!]
def toRestrictedLorentzGroup : SL(2, ℂ) →* LorentzGroup.restricted 3 :=
  toLorentzGroup.codRestrict (LorentzGroup.restricted 3)
    (fun M => And.intro (toLorentzGroup_det_one M) (toLorentzGroup_isOrthochronous M))
end
end SL2C

end Lorentz
