/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.Mathematics.InnerProductSpace.Submodule
import PhysLean.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
/-!

# Unbounded operators

In this file we define
- `UnboundedOperator`: an unbounded operator with domain a submodule of a generic Hilbert space.
  All unbounded operators are assumed to be both densely defined and closable.
- The closure, `UnboundedOperator.closure`, and adjoint, `UnboundedOperator.adjoint`, with notation
  `U† = U.adjoint`. That `U†` is densely defined is guaranteed by the closability of `U`.
- The concept of a generalized eigenvector in `IsGeneralizedEigenvector`.

We prove some basic relations, making use of the density and closability assumptions:
- `U.closure† = U†` in `closure_adjoint_eq_adjoint`
- `U†† = U.closure` in `adjoint_adjoint_eq_closure`

## References

- K. Schmüdgen, (2012). "Unbounded self-adjoint operators on Hilbert space" (Vol. 265). Springer.
  https://doi.org/10.1007/978-94-007-4753-1

-/

namespace QuantumMechanics

open LinearPMap Submodule

/-- An `UnboundedOperator` is a linear map from a submodule of the Hilbert space
  to the Hilbert space, assumed to be both densely defined and closable. -/
@[ext]
structure UnboundedOperator
    (HS : Type*) [NormedAddCommGroup HS] [InnerProductSpace ℂ HS] [CompleteSpace HS]
    extends LinearPMap ℂ HS HS where
  /-- The domain of an unbounded operator is dense in the Hilbert space. -/
  dense_domain : Dense (domain : Set HS)
  /-- An unbounded operator is closable. -/
  is_closable : toLinearPMap.IsClosable

namespace UnboundedOperator

variable
  {HS : Type*} [NormedAddCommGroup HS] [InnerProductSpace ℂ HS] [CompleteSpace HS]
  (U : UnboundedOperator HS)

lemma ext' (U T : UnboundedOperator HS) (h : U.toLinearPMap = T.toLinearPMap) : U = T := by
  apply UnboundedOperator.ext
  · exact toSubMulAction_inj.mp (congrArg toSubMulAction (congrArg domain h))
  · exact congr_arg_heq toFun h

lemma ext_iff' (U T : UnboundedOperator HS) : U = T ↔ U.toLinearPMap = T.toLinearPMap := by
  refine ⟨?_, UnboundedOperator.ext' U T⟩
  intro h
  rw [h]

/-!
### Construction of unbounded operators
-/

variable {E : Submodule ℂ HS} {hE : Dense (E : Set HS)}

/-- An `UnboundedOperator` constructed from a symmetric linear map on a dense submodule `E`. -/
def ofSymmetric (f : E →ₗ[ℂ] E) (hf : f.IsSymmetric) : UnboundedOperator HS where
  toLinearPMap := LinearPMap.mk E (E.subtype ∘ₗ f)
  dense_domain := hE
  is_closable := by
    refine isClosable_iff_exists_closed_extension.mpr ?_
    use (LinearPMap.mk E (E.subtype ∘ₗ f))†
    exact ⟨adjoint_isClosed hE, IsFormalAdjoint.le_adjoint hE hf⟩

@[simp]
lemma ofSymmetric_apply {f : E →ₗ[ℂ] E} {hf : f.IsSymmetric} (ψ : E) :
    (ofSymmetric (hE := hE) f hf).toLinearPMap ψ = E.subtypeL (f ψ) := rfl

/-!
### Closure
-/

section Closure

/-- The closure of an unbounded operator. -/
noncomputable def closure : UnboundedOperator HS where
  toLinearPMap := U.toLinearPMap.closure
  dense_domain := Dense.mono (HasCore.le_domain (closureHasCore U.toLinearPMap)) U.dense_domain
  is_closable := IsClosed.isClosable (IsClosable.closure_isClosed U.is_closable)

@[simp]
lemma closure_toLinearPMap : U.closure.toLinearPMap = U.toLinearPMap.closure := rfl

/-- An unbounded operator is closed iff the graph of its defining LinearPMap is closed. -/
def IsClosed : Prop := U.toLinearPMap.IsClosed

lemma closure_isClosed : U.closure.IsClosed := IsClosable.closure_isClosed U.is_closable

end Closure

/-!
### Adjoints
-/

section Adjoints

open InnerProductSpaceSubmodule

/-- The adjoint of a densely defined, closable `LinearPMap` is densely defined. -/
lemma adjoint_isClosable_dense (f : LinearPMap ℂ HS HS) (h_dense : Dense (f.domain : Set HS))
    (h_closable : f.IsClosable) : Dense (f†.domain : Set HS) := by
  by_contra hd
  have : ∃ x ∈ f†.domainᗮ, x ≠ 0 := by
    apply not_forall.mp at hd
    rcases hd with ⟨y, hy⟩
    have hnetop : f†.domainᗮᗮ ≠ ⊤ := by
      rw [orthogonal_orthogonal_eq_closure]
      exact Ne.symm (ne_of_mem_of_not_mem' trivial hy)
    have hnebot : f†.domainᗮ ≠ ⊥ := by
      by_contra
      apply hnetop
      rwa [orthogonal_eq_top_iff]
    exact exists_mem_ne_zero_of_ne_bot hnebot
  rcases this with ⟨x, hx, hx'⟩
  apply hx'
  apply graph_fst_eq_zero_snd f.closure _ rfl
  rw [← IsClosable.graph_closure_eq_closure_graph h_closable,
    mem_submodule_closure_iff_mem_submoduleToLp_closure,
    ← orthogonal_orthogonal_eq_closure,
    ← mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal,
    ← LinearPMap.adjoint_graph_eq_graph_adjoint h_dense,
    mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal]
  rintro ⟨y, Uy⟩ hy
  simp only [neg_zero, WithLp.prod_inner_apply, inner_zero_right, add_zero]
  exact hx y (mem_domain_of_mem_graph hy)

/-- The adjoint of an unbounded operator, denoted as `U†`. -/
noncomputable def adjoint : UnboundedOperator HS where
  toLinearPMap := U.toLinearPMap.adjoint
  dense_domain := adjoint_isClosable_dense U.toLinearPMap U.dense_domain U.is_closable
  is_closable := IsClosed.isClosable (adjoint_isClosed U.dense_domain)

@[inherit_doc]
scoped postfix:1024 "†" => UnboundedOperator.adjoint

noncomputable instance instStar : Star (UnboundedOperator HS) where
  star := fun U ↦ U.adjoint

@[simp]
lemma adjoint_toLinearPMap : U†.toLinearPMap = U.toLinearPMap† := rfl

lemma isSelfAdjoint_def : IsSelfAdjoint U ↔ U† = U := Iff.rfl

lemma isSelfAdjoint_iff : IsSelfAdjoint U ↔ IsSelfAdjoint U.toLinearPMap := by
  rw [isSelfAdjoint_def, LinearPMap.isSelfAdjoint_def, ← adjoint_toLinearPMap,
    UnboundedOperator.ext_iff']

lemma adjoint_isClosed : (U†).IsClosed := LinearPMap.adjoint_isClosed U.dense_domain

lemma closure_adjoint_eq_adjoint : U.closure† = U† := by
  -- Reduce to statement about graphs using density and closability assumptions
  apply UnboundedOperator.ext'
  apply LinearPMap.eq_of_eq_graph
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.closure.dense_domain]
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.dense_domain]
  rw [closure_toLinearPMap, ← IsClosable.graph_closure_eq_closure_graph U.is_closable]
  ext f
  rw [mem_submodule_closure_adjoint_iff_mem_submoduleToLp_closure_orthogonal,
    orthogonal_closure, mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal]

lemma adjoint_adjoint_eq_closure : U†† = U.closure := by
  -- Reduce to statement about graphs using density and closability assumptions
  apply UnboundedOperator.ext'
  apply LinearPMap.eq_of_eq_graph
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U†.dense_domain]
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.dense_domain]
  rw [closure_toLinearPMap, ← IsClosable.graph_closure_eq_closure_graph U.is_closable]
  ext f
  rw [mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal,
    orthogonal_orthogonal_eq_closure, mem_submodule_closure_iff_mem_submoduleToLp_closure]

end Adjoints

/-!
### Generalized eigenvectors
-/

/-- A map `F : D(U) →L[ℂ] ℂ` is a generalized eigenvector of an unbounded operator `U`
  if there is an eigenvalue `c` such that for all `ψ ∈ D(U)`, `F (U ψ) = c ⬝ F ψ`. -/
def IsGeneralizedEigenvector (F : U.domain →L[ℂ] ℂ) (c : ℂ) : Prop :=
  ∀ ψ : U.domain, ∃ ψ' : U.domain, ψ' = U.toFun ψ ∧ F ψ' = c • F ψ

lemma isGeneralizedEigenvector_ofSymmetric_iff
    {f : E →ₗ[ℂ] E} (hf : f.IsSymmetric) (F : E →L[ℂ] ℂ) (c : ℂ) :
    IsGeneralizedEigenvector (ofSymmetric (hE := hE) f hf) F c ↔ ∀ ψ : E, F (f ψ) = c • F ψ := by
  constructor <;> intro h ψ
  · obtain ⟨ψ', hψ', hψ''⟩ := h ψ
    apply SetLike.coe_eq_coe.mp at hψ'
    subst hψ'
    exact hψ''
  · use f ψ
    exact ⟨by simp, h ψ⟩

end UnboundedOperator
end QuantumMechanics
