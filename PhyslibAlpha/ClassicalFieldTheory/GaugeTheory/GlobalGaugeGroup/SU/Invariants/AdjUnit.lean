/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.Invariants.Basic
public import Physlib.Relativity.Tensors.UnitTensor
/-!
# The unit tensor of the adjoint colour of `SU(N)`

Up to scale, the unit tensor is the only invariant with two adjoint indices.

## i. Overview

A tensor with one adjoint index has no invariants but zero (`suTensor.invariants_adj_eq_bot`, with
the adjoint colour). A tensor with two adjoint indices has a matrix of components `C` in the
Gell-Mann basis, moved by `g` to `M C Mᵀ`, where `M` is the matrix of the adjoint action of `g`.
That matrix is real and `Mᵀ` is the matrix of `g⁻¹`, so the components of an invariant tensor are
the matrix of an endomorphism of the complexified Lie algebra commuting with the adjoint action. By
`suTensor.eq_smul_id_of_commute_adjRep` that endomorphism is scalar, and the invariant tensors are
the line through the unit tensor of the adjoint color, `∑ λ_a ⊗ λ_a / 2` (A).

For equivariant maps out of these tensors the invariants of the range reduce to `⊥` for one
adjoint index and to the image of the unit tensor for two (B). A family indexed by the Gell-Mann
labels is the map `liftComponents (T ∘ adjIdx)` or `liftComponents (T ∘ adjPairIdx)`, and for two
indices the image of twice the unit tensor is the trace contraction `∑ a, T ![a, a]` (C). The
invariants of the tensor square of the adjoint representation are the line through the unit
`∑ λ_a ⊗ λ_a / 2` (D).

## ii. Key results

- `suTensor.invariants_adj_adj_eq_span_adjUnitTensor` : the invariant tensors with two adjoint
  indices are the line through the unit tensor.
- `suTensor.invariantReductionToTrace` : the reduction of the invariants of the span of a family
  with two adjoint indices to the trace contraction.
- `suTensor.invariants_tprod_eq_span_adjUnitVal` : the invariants of the tensor square of the
  adjoint representation are the line through the unit.

## iii. Table of contents

- A. Two adjoint indices
- B. The invariants of equivariant maps
- C. Maps from components
- D. The invariants of the tensor square of the adjoint representation

## iv. References

* None.

-/

@[expose] public section

namespace suTensor

open Matrix MatrixGroups TensorSpecies SU TensorProduct
open TensorSpecies.Tensor

variable {N : ℕ}

/-!

## A. Two adjoint indices

-/

/-- The component indices of a tensor with two adjoint indices, as the pair of their Gell-Mann
  labels. -/
def adjPairIdx : ComponentIdx (S := suTensor N) ![.adj, .adj] ≃ (Fin 2 → GellMann.Index N) where
  toFun v := ![v 0, v 1]
  invFun v := fun | 0 => v 0 | 1 => v 1
  left_inv v := by
    funext x
    fin_cases x <;> rfl
  right_inv v := by
    funext x
    fin_cases x <;> rfl

/-- The components of `g • t` for a tensor with two adjoint indices. The matrix of components
  `C` is moved to `M C Mᵀ`. -/
lemma basis_repr_smul_adjPair (g : SU N) (t : SuT[N, .adj, .adj])
    (n : Fin 2 → GellMann.Index N) :
    (Tensor.basis _).repr (g • t) (adjPairIdx.symm n)
      = ∑ x, ∑ y, adjMatrix g (n 0) x * adjMatrix g (n 1) y
        * (Tensor.basis _).repr t (adjPairIdx.symm ![x, y]) := by
  rw [basis_repr_smul, ← adjPairIdx.symm.sum_comp, ← (finTwoArrowEquiv _).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Fin.prod_univ_two]
  rfl

variable (N) in
/-- The unit tensor of the adjoint color, `∑ λ_a ⊗ λ_a / 2`, with two adjoint indices. -/
noncomputable def adjUnitTensor : SuT[N, .adj, .adj] := unitTensor (S := suTensor N) .adj

/-- The unit tensor of the adjoint color is invariant. -/
lemma adjUnitTensor_invariant (g : SU N) : g • adjUnitTensor N = adjUnitTensor N :=
  actionT_fromConstPair ((suTensor N).unit .adj) g

/-- The components of the unit tensor of the adjoint color, `δ / 2`, the Gell-Mann matrices
  being orthogonal with `tr (λ_a λ_b) = 2 δ_ab`. -/
lemma basis_repr_adjUnitTensor (n : Fin 2 → GellMann.Index N) :
    (Tensor.basis _).repr (adjUnitTensor N) (adjPairIdx.symm n)
      = if n 0 = n 1 then 1 / 2 else 0 := by
  refine (unitTensor_basis_repr (S := suTensor N) .adj (adjPairIdx.symm n)).trans ?_
  change (Module.Basis.tensorProduct (adjBasis N) (adjBasis N)).repr
    ((1 : ℂ) • adjUnitVal N) (n 0, n 1) = _
  simp only [one_smul, adjUnitVal, map_sum, Module.Basis.tensorProduct_repr_tmul_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Module.Basis.repr_self]
  rw [Finset.sum_eq_single (n 0) (fun x _ hx => by simp [hx]) (by simp),
    Finsupp.single_eq_same, smul_eq_mul, mul_one]
  have h := LinearMap.BilinForm.apply_dualBasis_right (traceForm_nondegenerate N)
    (traceForm_isSymm N) (adjBasis N) (n 1) (n 0)
  rw [traceForm_apply, adjMat_adjBasis] at h
  rw [adjBasis_repr_apply, h]
  by_cases h01 : n 0 = n 1
  · simp [h01]
  · simp [h01, Ne.symm h01]

/-- The invariant tensors with two adjoint indices are the line through the unit tensor of the
  adjoint color. The matrix of components of an invariant tensor commutes with the matrices of the
  adjoint action, so it is the matrix of an endomorphism commuting with the adjoint action, which
  is scalar. -/
lemma invariants_adj_adj_eq_span_adjUnitTensor :
    ((suTensor N).tensorRep ![.adj, .adj]).invariants = ℂ ∙ adjUnitTensor N := by
  refine invariants_tensorRep_eq_span_singleton adjUnitTensor_invariant fun t ht => ?_
  set C : Matrix (GellMann.Index N) (GellMann.Index N) ℂ :=
    Matrix.of fun a b => (Tensor.basis _).repr t (adjPairIdx.symm ![a, b])
  have hconj : ∀ g : SU N, adjMatrix g * C * (adjMatrix g)ᵀ = C := fun g => by
    ext a b
    have h := basis_repr_smul_adjPair g t ![a, b]
    rw [ht] at h
    simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul, C, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_).trans h.symm
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have hcomm : ∀ g : SU N, C * adjMatrix g = adjMatrix g * C := fun g => by
    conv_lhs => rw [← hconj g, ← adjMatrix_inv]
    rw [Matrix.mul_assoc, adjMatrix_inv_mul, Matrix.mul_one]
  set L := Matrix.toLin (adjBasis N) (adjBasis N) C
  obtain ⟨μ, hμ⟩ := eq_smul_id_of_commute_adjRep (L := L) fun g A => by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply (adjRep N g)]
    congr 1
    apply (LinearMap.toMatrix (adjBasis N) (adjBasis N)).injective
    rw [LinearMap.toMatrix_comp _ (adjBasis N), LinearMap.toMatrix_comp _ (adjBasis N),
      LinearMap.toMatrix_toLin]
    exact hcomm g
  have hC : C = μ • 1 := by
    have hLC : LinearMap.toMatrix (adjBasis N) (adjBasis N) L = C :=
      LinearMap.toMatrix_toLin _ _ C
    rw [← hLC, hμ, map_smul, LinearMap.toMatrix_id]
  refine ⟨2 * μ, (Tensor.basis _).repr.injective (Finsupp.ext fun φ => ?_)⟩
  obtain ⟨n, rfl⟩ := adjPairIdx.symm.surjective φ
  rw [map_smul, Finsupp.smul_apply, basis_repr_adjUnitTensor, smul_eq_mul]
  have h := congrFun (congrFun hC (n 0)) (n 1)
  simp only [C, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  rw [show (![n 0, n 1] : Fin 2 → GellMann.Index N) = n from by funext i; fin_cases i <;> rfl]
    at h
  rw [h]
  split_ifs <;> ring

/-- The invariant tensors with two adjoint indices are the line through twice the unit tensor,
  the tensor whose image under a map of a family is the trace contraction. -/
lemma invariants_adj_adj_eq_span_two_smul_adjUnitTensor :
    ((suTensor N).tensorRep ![.adj, .adj]).invariants = ℂ ∙ ((2 : ℂ) • adjUnitTensor N) :=
  invariants_adj_adj_eq_span_adjUnitTensor.trans
    (Submodule.span_singleton_smul_eq (IsUnit.mk0 _ two_ne_zero) _).symm

/-!

## B. The invariants of equivariant maps

-/

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ (SU N) B}

/-- For an equivariant map out of the tensors with one adjoint index, the invariants of the range
  reduce to `⊥`. -/
lemma reducesInvariantsTo_bot_of_isEquivariant_adj {f : SuT[N, .adj] →ₗ[ℂ] B}
    (hf : (suTensor N).IsEquivariant ![.adj] ρ f) :
    ReducesInvariantsTo (fun g : SU N => ρ g) (LinearMap.range f) ⊥ :=
  hf.reducesInvariantsTo_bot (hasReynolds N _) invariants_adj_eq_bot

/-!

## C. Maps from components

-/

/-- The component indices of a tensor with one adjoint index, as its Gell-Mann label. -/
def adjIdx : ComponentIdx (S := suTensor N) ![.adj] ≃ GellMann.Index N where
  toFun v := v 0
  invFun a := fun | 0 => a
  left_inv v := by
    funext x
    fin_cases x
    rfl
  right_inv a := rfl

/-- A linear map moving a family indexed by one adjoint label by the matrix of the adjoint action
  of `g` intertwines the map of the family with the action of `g`. -/
lemma liftComponents_adj_smul_of_law (T : GellMann.Index N → B) {σ : B →ₗ[ℂ] B} (g : SU N)
    (hσ : ∀ a : GellMann.Index N, σ (T a) = ∑ b, adjMatrix g b a • T b) (t : SuT[N, .adj]) :
    σ (liftComponents (T ∘ adjIdx) t) = liftComponents (T ∘ adjIdx) (g • t) := by
  refine liftComponents_smul_of_law _ g (fun φ => (hσ _).trans ?_) t
  rw [← adjIdx.sum_comp]
  exact Finset.sum_congr rfl fun b _ => by rw [Fin.prod_univ_one]; rfl

/-- The map of a family indexed by one adjoint label is equivariant when the family moves by the
  matrix of the adjoint action, the summed label first. -/
lemma isEquivariant_liftComponents_adj (T : GellMann.Index N → B)
    (hT : ∀ (g : SU N) (a : GellMann.Index N), ρ g (T a) = ∑ b, adjMatrix g b a • T b) :
    (suTensor N).IsEquivariant ![.adj] ρ (liftComponents (T ∘ adjIdx)) :=
  ⟨fun g t => (liftComponents_adj_smul_of_law T g (hT g) t).symm⟩

/-- For a family indexed by one adjoint label whose map is equivariant, the invariants of the
  span of the family reduce to `⊥`. -/
lemma reducesInvariantsTo_bot_span_adj {T : GellMann.Index N → B}
    (hT : (suTensor N).IsEquivariant ![.adj] ρ (liftComponents (T ∘ adjIdx))) :
    ReducesInvariantsTo (fun g : SU N => ρ g) (Submodule.span ℂ (Set.range T)) ⊥ := by
  rw [← range_liftComponents_comp adjIdx T]
  exact reducesInvariantsTo_bot_of_isEquivariant_adj hT

/-- The map of a family relabelled by `adjPairIdx` sends twice the unit tensor to the trace
  contraction `∑ a, T ![a, a]`. -/
lemma liftComponents_two_smul_adjUnitTensor (T : (Fin 2 → GellMann.Index N) → B) :
    liftComponents (T ∘ adjPairIdx) ((2 : ℂ) • adjUnitTensor N) = ∑ a, T ![a, a] := by
  conv_lhs => rw [← (Tensor.basis _).sum_repr (adjUnitTensor N)]
  rw [Finset.smul_sum, map_sum, ← adjPairIdx.symm.sum_comp, ← (finTwoArrowEquiv _).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp [basis_repr_adjUnitTensor, smul_smul]
  · intro b _ hb
    simp [basis_repr_adjUnitTensor, Ne.symm hb]
  · simp

/-- A linear map moving a family indexed by two adjoint labels by the matrix of the adjoint
  action of `g` on each label intertwines the map of the family with the action of `g`. -/
lemma liftComponents_adjPair_smul_of_law (T : (Fin 2 → GellMann.Index N) → B) {σ : B →ₗ[ℂ] B}
    (g : SU N) (hσ : ∀ l : Fin 2 → GellMann.Index N, σ (T l)
      = ∑ a : Fin 2 → GellMann.Index N, (adjMatrix g (a 0) (l 0) * adjMatrix g (a 1) (l 1)) • T a)
    (t : SuT[N, .adj, .adj]) :
    σ (liftComponents (T ∘ adjPairIdx) t) = liftComponents (T ∘ adjPairIdx) (g • t) := by
  refine liftComponents_smul_of_law _ g (fun φ => (hσ _).trans ?_) t
  rw [← adjPairIdx.sum_comp]
  exact Finset.sum_congr rfl fun a _ => by rw [Fin.prod_univ_two]; rfl

/-- The map of a family indexed by two adjoint labels is equivariant when the family moves by the
  matrix of the adjoint action on each label, the summed label first. -/
lemma isEquivariant_liftComponents_adjPair (T : (Fin 2 → GellMann.Index N) → B)
    (hT : ∀ (g : SU N) (l : Fin 2 → GellMann.Index N), ρ g (T l)
      = ∑ a : Fin 2 → GellMann.Index N, (adjMatrix g (a 0) (l 0) * adjMatrix g (a 1) (l 1)) • T a) :
    (suTensor N).IsEquivariant ![.adj, .adj] ρ (liftComponents (T ∘ adjPairIdx)) :=
  ⟨fun g t => (liftComponents_adjPair_smul_of_law T g (hT g) t).symm⟩

/-- For a family indexed by two adjoint labels whose map is equivariant, the invariants of the
  span of the family reduce to the span of the trace contraction `∑ a, T ![a, a]`. -/
noncomputable def invariantReductionToTrace {T : (Fin 2 → GellMann.Index N) → B}
    (hT : (suTensor N).IsEquivariant ![.adj, .adj] ρ (liftComponents (T ∘ adjPairIdx))) :
    InvariantReductionToSpan (fun g : SU N => ρ g) (Submodule.span ℂ (Set.range T)) :=
  hT.invariantReductionToSpanOfEq (hasReynolds N _)
    invariants_adj_adj_eq_span_two_smul_adjUnitTensor (range_liftComponents_comp _ T) _
    (liftComponents_two_smul_adjUnitTensor T)

/-!

## D. The invariants of the tensor square of the adjoint representation

-/

/-- The unit tensor of the adjoint color is the tensor of `∑ b_a ⊗ bᵃ`. -/
lemma adjUnitTensor_eq_fromPairT :
    adjUnitTensor N = fromPairT (S := suTensor N) (c1 := .adj) (c2 := .adj) (adjUnitVal N) := by
  change fromPairT (S := suTensor N) (c1 := .adj) (c2 := .adj) (adjUnit N 1) = _
  rw [adjUnit, unitOf_apply, one_smul]

/-- The invariants of the tensor square of the adjoint representation are the line through the
  unit `∑ b_a ⊗ bᵃ`. -/
lemma invariants_tprod_eq_span_adjUnitVal :
    ((adjRep N).tprod (adjRep N)).invariants = ℂ ∙ adjUnitVal N :=
  invariants_tprod_eq_span_singleton (S := suTensor N) (c1 := .adj) (c2 := .adj)
    (adjUnitTensor_eq_fromPairT (N := N) ▸ invariants_adj_adj_eq_span_adjUnitTensor)

end suTensor
