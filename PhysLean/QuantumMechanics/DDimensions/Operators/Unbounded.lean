/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import PhysLean.Mathematics.InnerProductSpace.Submodule
/-!

# Unbounded operators

## i. Overview

In this module we define unbounded operators between Hilbert spaces.

## ii. Key results

Definitions:
- `UnboundedOperator`: Densely defined, closable unbounded operator between Hilbert spaces.
- `partialOrder`: Poset structure for unbounded operators.
- `ofSymmetric`: Construction of an unbounded operator from a symmetric `LinearPMap`.
- `IsGeneralizedEigenvector`: The notion of eigenvectors/values for linear functionals.

(In)equalities:
- `le_closure`: `U ≤ U.closure`
- `adjoint_adjoint_eq_closure`: `U†† = U.closure`
- `adjoint_ge_adjoint_of_le`: `U₁ ≤ U₂ → U₂† ≤ U₁†`
- `closure_mono`: `U₁ ≤ U₂ → U₁.closure ≤ U₂.closure`
- `isSymmetric_iff_le_adjoint`: `IsSymmetric T ↔ T ≤ T†`

## iii. Table of contents

- A. Definition
- B. Partial order
- C. Closure
- D. Adjoint
- E. Symmetric operators
- F. Self-adjoint operators
- G. Generalized eigenvectors

## iv. References

- M. Reed & B. Simon, (1972). "Methods of modern mathematical physics: Vol. 1. Functional analysis".
  Academic Press. https://doi.org/10.1016/B978-0-12-585001-8.X5001-6
- K. Schmüdgen, (2012). "Unbounded self-adjoint operators on Hilbert space" (Vol. 265). Springer.
  https://doi.org/10.1007/978-94-007-4753-1

-/

@[expose] public section

namespace QuantumMechanics

open LinearPMap Submodule
open InnerProductSpace InnerProductSpaceSubmodule

/-!
## A. Definition
-/

/-- An `UnboundedOperator` is a linear map from a submodule of `H` to `H'`,
  assumed to be both densely defined and closable. -/
structure UnboundedOperator
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H' : Type*) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    extends LinearPMap ℂ H H' where
  /-- The domain of an unbounded operator is dense in `H`. -/
  dense_domain : Dense (domain : Set H)
  /-- An unbounded operator is closable. -/
  is_closable : toLinearPMap.IsClosable

namespace UnboundedOperator

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

@[ext]
lemma ext {U₁ U₂ : UnboundedOperator H H'} (h : U₁.toLinearPMap = U₂.toLinearPMap) :
    U₁ = U₂ := by
  cases U₁
  simp_all

instance : CoeFun (UnboundedOperator H H') (fun U ↦ U.domain → H') :=
  ⟨fun U ↦ U.toLinearPMap.toFun'⟩

/-!
## B. Partial order

Unbounded operators inherit the structure of a poset from `LinearPMap`,
but *not* that of a `SemilatticeInf` because `U₁.domain ⊓ U₂.domain` may not be dense.
-/

instance partialOrder : PartialOrder (UnboundedOperator H H') where
  le U₁ U₂ := U₁.toLinearPMap ≤ U₂.toLinearPMap
  le_refl _ := le_refl _
  le_trans _ _ _ h₁₂ h₂₃ := le_trans h₁₂ h₂₃
  le_antisymm _ _ h h' := ext <| le_antisymm h h'

/-!
## C. Closure
-/

section

variable (U : UnboundedOperator H H')

/-- The closure of an unbounded operator. -/
noncomputable def closure : UnboundedOperator H H' where
  toLinearPMap := U.toLinearPMap.closure
  dense_domain := Dense.mono (HasCore.le_domain (closureHasCore U.toLinearPMap)) U.dense_domain
  is_closable := IsClosed.isClosable (IsClosable.closure_isClosed U.is_closable)

@[simp]
lemma closure_toLinearPMap : U.closure.toLinearPMap = U.toLinearPMap.closure := rfl

lemma le_closure : U ≤ U.closure := LinearPMap.le_closure U.toLinearPMap

/-- An unbounded operator is closed iff the graph of its defining LinearPMap is closed. -/
def IsClosed : Prop := U.toLinearPMap.IsClosed

lemma closure_isClosed : U.closure.IsClosed := IsClosable.closure_isClosed U.is_closable

lemma isClosed_def : IsClosed U ↔ U.closure = U := by
  refine ⟨?_, fun h ↦ h ▸ closure_isClosed U⟩
  intro h
  rw [UnboundedOperator.ext_iff, closure_toLinearPMap]
  apply eq_of_eq_graph
  rw [← IsClosable.graph_closure_eq_closure_graph U.is_closable]
  exact IsClosed.submodule_topologicalClosure_eq h

end

/-!
## D. Adjoint
-/

section

variable (U : UnboundedOperator H H')

/-- The adjoint of a densely defined, closable `LinearPMap` is densely defined. -/
lemma adjoint_dense_of_isClosable {f : LinearPMap ℂ H H'} (h_dense : Dense (f.domain : Set H))
    (h_closable : f.IsClosable) : Dense (f†.domain : Set H') := by
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
noncomputable def adjoint : UnboundedOperator H' H where
  toLinearPMap := U.toLinearPMap.adjoint
  dense_domain := adjoint_dense_of_isClosable U.dense_domain U.is_closable
  is_closable := IsClosed.isClosable (adjoint_isClosed U.dense_domain)

@[inherit_doc]
scoped postfix:1024 "†" => UnboundedOperator.adjoint

@[simp]
lemma adjoint_toLinearPMap : U†.toLinearPMap = U.toLinearPMap† := rfl

lemma adjoint_isClosed : U†.IsClosed := LinearPMap.adjoint_isClosed U.dense_domain

lemma adjoint_closure_eq_adjoint : U†.closure = U† := (isClosed_def U†).mp <| adjoint_isClosed U

lemma closure_adjoint_eq_adjoint : U.closure† = U† := by
  -- Reduce to statement about graphs using density and closability assumptions
  apply UnboundedOperator.ext
  apply LinearPMap.eq_of_eq_graph
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.closure.dense_domain]
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.dense_domain]
  rw [closure_toLinearPMap, ← IsClosable.graph_closure_eq_closure_graph U.is_closable]
  ext
  rw [mem_submodule_closure_adjoint_iff_mem_submoduleToLp_closure_orthogonal,
    orthogonal_closure, mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal]

lemma adjoint_adjoint_eq_closure : U†† = U.closure := by
  -- Reduce to statement about graphs using density and closability assumptions
  apply UnboundedOperator.ext
  apply LinearPMap.eq_of_eq_graph
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U†.dense_domain]
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.dense_domain]
  rw [closure_toLinearPMap, ← IsClosable.graph_closure_eq_closure_graph U.is_closable]
  ext
  rw [mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal,
    orthogonal_orthogonal_eq_closure, mem_submodule_closure_iff_mem_submoduleToLp_closure]

lemma le_adjoint_adjoint : U ≤ U†† := adjoint_adjoint_eq_closure U ▸ le_closure U

lemma isClosed_iff : IsClosed U ↔ U†† = U := adjoint_adjoint_eq_closure U ▸ isClosed_def U

lemma adjoint_ge_adjoint_of_le {U₁ U₂ : UnboundedOperator H H'} (h : U₁ ≤ U₂) : U₂† ≤ U₁† := by
  obtain ⟨h_domain, h_agree⟩ := h
  simp only [Subtype.forall] at h_agree
  have heq (x : U₁.domain) (v : U₂†.domain) : ⟪U₂† v, x⟫_ℂ = ⟪(v : H'), U₁ x⟫_ℂ := by
    have hx₂ : ↑x ∈ U₂.domain := h_domain <| coe_mem x
    have h : U₁ x = U₂ ⟨x, hx₂⟩ := h_agree x x.2 x hx₂ rfl
    exact h ▸ adjoint_isFormalAdjoint U₂.dense_domain v ⟨x, hx₂⟩
  constructor
  · intro v hv
    apply mem_adjoint_domain_of_exists v
    use U₂† ⟨v, hv⟩
    exact fun x ↦ heq x ⟨v, hv⟩
  · intro u v huv
    refine (adjoint_apply_eq U₁.dense_domain v ?_).symm
    exact fun x ↦ huv ▸ heq x u

lemma closure_mono {U₁ U₂ : UnboundedOperator H H'} (h : U₁ ≤ U₂) : U₁.closure ≤ U₂.closure := by
  repeat rw [← adjoint_adjoint_eq_closure]
  exact adjoint_ge_adjoint_of_le <| adjoint_ge_adjoint_of_le h

end

/-!
## E. Symmetric operators
-/

section

variable
  {E : Submodule ℂ H} (hE : Dense (E : Set H))
  {f : E →ₗ[ℂ] E} (hf : f.IsSymmetric)
  (T : UnboundedOperator H H)

/-- An `UnboundedOperator` constructed from a symmetric linear map on a dense submodule `E`. -/
def ofSymmetric : UnboundedOperator H H where
  toLinearPMap := LinearPMap.mk E (E.subtype ∘ₗ f)
  dense_domain := hE
  is_closable := by
    refine isClosable_iff_exists_closed_extension.mpr ?_
    use (LinearPMap.mk E (E.subtype ∘ₗ f))†
    exact ⟨LinearPMap.adjoint_isClosed hE, IsFormalAdjoint.le_adjoint hE hf⟩

@[simp]
lemma ofSymmetric_apply (ψ : E) : (ofSymmetric hE hf) ψ = E.subtype (f ψ) := rfl

-- Note that cannot simply co-opt `LinearMap.IsSymmetric` because
-- the domain and codomain of `T` need not be the same.
/-- `T` is symmetric if `⟪T x, y⟫ = ⟪x, T y⟫` for all `x,y ∈ T.domain`. -/
def IsSymmetric : Prop := ∀ x y : T.domain, ⟪T x, y⟫_ℂ = ⟪(x : H), T y⟫_ℂ

lemma inner_map_polarization (x y : T.domain) :
    ⟪T x, ↑y⟫_ℂ = (⟪T (x + y), ↑(x + y)⟫_ℂ - ⟪T (x - y), ↑(x - y)⟫_ℂ
    - Complex.I * ⟪T (x + Complex.I • y), ↑(x + Complex.I • y)⟫_ℂ
    + Complex.I * ⟪T (x - Complex.I • y), ↑(x - Complex.I • y)⟫_ℂ) / 4 := by
  simp only [LinearPMap.map_add, coe_add, inner_add_right, inner_add_left, LinearPMap.map_sub,
    AddSubgroupClass.coe_sub, inner_sub_right, inner_sub_left, LinearPMap.map_smul,
    SetLike.val_smul, inner_smul_left, Complex.conj_I, inner_smul_right]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma inner_map_polarization' (x y : T.domain) :
    ⟪↑x, T y⟫_ℂ = (⟪↑(x + y), T (x + y)⟫_ℂ - ⟪↑(x - y), T (x - y)⟫_ℂ
    - Complex.I * ⟪↑(x + Complex.I • y), T (x + Complex.I • y)⟫_ℂ
    + Complex.I * ⟪↑(x - Complex.I • y), T (x - Complex.I • y)⟫_ℂ) / 4 := by
  simp only [coe_add, LinearPMap.map_add, inner_add_right, inner_add_left, AddSubgroupClass.coe_sub,
    LinearPMap.map_sub, inner_sub_right, inner_sub_left, SetLike.val_smul, LinearPMap.map_smul,
    inner_smul_left, Complex.conj_I, inner_smul_right]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma isSymmetric_iff_inner_map_self_real :
    IsSymmetric T ↔ ∀ x : T.domain, (starRingEnd ℂ) ⟪T x, x⟫_ℂ = ⟪T x, x⟫_ℂ := by
  simp only [inner_conj_symm]
  refine ⟨fun hT x ↦ (hT x x).symm, ?_⟩
  intro h x y
  rw [inner_map_polarization, inner_map_polarization']
  rw [h (x + y), h (x - y), h (x + Complex.I • y), h (x - Complex.I • y)]

lemma isSymmetric_iff_le_adjoint : IsSymmetric T ↔ T ≤ T† := by
  refine ⟨fun hT ↦ IsFormalAdjoint.le_adjoint T.dense_domain <| IsFormalAdjoint.symm hT, ?_⟩
  intro h x y
  obtain ⟨h_domain, h_agree⟩ := h
  simp only [Subtype.forall] at h_agree
  have hy : ↑y ∈ T†.domain := h_domain <| coe_mem y
  have heq := (IsFormalAdjoint.symm <| adjoint_isFormalAdjoint T.dense_domain) x ⟨y, hy⟩
  exact (h_agree y y.2 y hy rfl) ▸ heq

end

/-!
## F. Self-adjoint operators
-/

section

variable (T : UnboundedOperator H H)

noncomputable instance instStar : Star (UnboundedOperator H H) := ⟨adjoint⟩

lemma isSelfAdjoint_def : IsSelfAdjoint T ↔ T† = T := Iff.rfl

lemma isSelfAdjoint_iff : IsSelfAdjoint T ↔ IsSelfAdjoint T.toLinearPMap := by
  rw [isSelfAdjoint_def, LinearPMap.isSelfAdjoint_def, ← adjoint_toLinearPMap,
    UnboundedOperator.ext_iff]

lemma isSelfAdjoint_isClosed {T : UnboundedOperator H H} (hT : IsSelfAdjoint T) : IsClosed T :=
  hT ▸ adjoint_isClosed T

lemma isSelfAdjoint_isSymmetric {T : UnboundedOperator H H} (hT : IsSelfAdjoint T) :
    IsSymmetric T := by
  rw [isSymmetric_iff_le_adjoint]
  exact ge_of_eq hT

/-- `T` is essentially self-adjoint if its closure is self-adjoint. -/
def IsEssentiallySelfAdjoint : Prop := IsSelfAdjoint T.closure

lemma isEssentiallySelfAdjoint_def : IsEssentiallySelfAdjoint T ↔ T† = T.closure := by
  rw [IsEssentiallySelfAdjoint, isSelfAdjoint_def, closure_adjoint_eq_adjoint]

lemma isSelfAdjoint_isEssentiallySelfAdjoint {T : UnboundedOperator H H} (hT : IsSelfAdjoint T) :
    IsEssentiallySelfAdjoint T := by
  rw [isEssentiallySelfAdjoint_def]
  nth_rw 2 [← hT]
  exact Eq.symm <| adjoint_closure_eq_adjoint T

end

/-!
## G. Generalized eigenvectors
-/

section

variable
  {E : Submodule ℂ H} (hE : Dense (E : Set H))
  {f : E →ₗ[ℂ] E} (hf : f.IsSymmetric)
  (T : UnboundedOperator H H)

/-- A map `F : D(T) →L[ℂ] ℂ` is a generalized eigenvector of an unbounded operator `T`
  if there is an eigenvalue `c` such that for all `ψ ∈ D(T)`, `F (T ψ) = c ⬝ F ψ`. -/
def IsGeneralizedEigenvector (F : T.domain →L[ℂ] ℂ) (c : ℂ) : Prop :=
  ∀ ψ : T.domain, ∃ ψ' : T.domain, ψ' = T ψ ∧ F ψ' = c • F ψ

lemma isGeneralizedEigenvector_ofSymmetric_iff (F : E →L[ℂ] ℂ) (c : ℂ) :
    IsGeneralizedEigenvector (ofSymmetric hE hf) F c ↔ ∀ ψ : E, F (f ψ) = c • F ψ := by
  constructor <;> intro h ψ
  · obtain ⟨ψ', hψ', hψ''⟩ := h ψ
    exact (SetLike.coe_eq_coe.mp hψ') ▸ hψ''
  · use f ψ
    exact ⟨by simp, h ψ⟩

end

end UnboundedOperator
end QuantumMechanics
