/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Observable
public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Lie
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.Channel
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.OrderUnit
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Symmetry
public import Mathlib.Algebra.Star.StarAlgHom

/-!

# ⋆-automorphisms and their action on observables

Reversible transformations of a quantum system act on its observable algebra by
⋆-automorphisms `β : A ≃⋆ₐ[ℂ] A`, `a ↦ β a`. This is genuinely abstract-algebra-level content: it
works for any `A` with enough structure to form `Observable A := selfAdjoint A`
(`StarAlgebra/Observable.lean`) and the observable Lie bracket (`StarAlgebra/Lie.lean`) — no norm,
completeness, order, or Hilbert space enters anywhere in this file.

A ⋆-automorphism acts on observables (`StarAlgEquiv.observable`) compatibly with composition,
inverses, and the Lie bracket (`StarAlgEquiv.observable_bracket`). A one-parameter group of such
automorphisms (`AutomorphismGroup A`) can be reindexed by a change of coordinates `β`
(`AutomorphismGroup.conj`). Both are just as algebra-level as the observable action above — neither
mentions a norm or a Hilbert space — so they live here rather than at the Hilbert-space layer,
where `HilbertSpace/Dynamics/Automorphism.lean` specializes `AutomorphismGroup (H →L[ℂ] H)` to
unitarily-implemented dynamics and proves it satisfies (and uniquely solves) the Heisenberg
equation.

## Main definitions

- `StarAlgEquiv.observable` : a ⋆-automorphism acting on observables, `a ↦ β a`.
- `StarAlgEquiv.observable_bracket` : ⋆-automorphisms preserve the observable Lie bracket.
- `AutomorphismGroup A` : a one-parameter group of ⋆-automorphisms of `A`.
- `AutomorphismGroup.transport` : transport of a flow across a ⋆-isomorphism between algebras.
- `AutomorphismGroup.IsIntertwining` : the commuting square for a ⋆-isomorphism and two flows.
- `AutomorphismGroup.conj` : reindexing a flow `α` by a change of coordinates `β`,
  `(conj β α) t = β ∘ (α t) ∘ β⁻¹`.
- `StarAlgEquiv.observableUPLM` : the order-unit channel induced on self-adjoint observables.
- `AutomorphismGroup.toObservableDynamics` : the same dynamics in the existing state/effect API.

-/

@[expose] public section

/-! ## Action on observables -/

section StarAlgEquivObservable

open scoped selfAdjoint

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]

omit [StarModule ℂ A] in
/-- A ⋆-automorphism `β` acts on observables by `a ↦ β a`. -/
def StarAlgEquiv.observable (β : A ≃⋆ₐ[ℂ] A) (a : Observable A) : Observable A :=
  ⟨β (a : A), by
    show star (β (a : A)) = β (a : A)
    rw [← map_star, a.2]⟩

omit [StarModule ℂ A] in
/-- Unfolds `StarAlgEquiv.observable` to its underlying algebra element. -/
@[simp]
lemma StarAlgEquiv.observable_coe (β : A ≃⋆ₐ[ℂ] A) (a : Observable A) :
    (β.observable a : A) = β (a : A) := rfl

omit [StarModule ℂ A] in
/-- The identity automorphism acts trivially on observables. -/
@[simp]
lemma StarAlgEquiv.refl_observable :
    (StarAlgEquiv.refl (R := ℂ) (A := A)).observable = id := by
  funext a
  exact Subtype.ext rfl

omit [StarModule ℂ A] in
/-- Composing `β` then `γ` acts on observables as `γ ∘ β`. -/
@[simp]
lemma StarAlgEquiv.trans_observable (β γ : A ≃⋆ₐ[ℂ] A) (a : Observable A) :
    (β.trans γ).observable a = γ.observable (β.observable a) :=
  Subtype.ext (StarAlgEquiv.trans_apply β γ (a : A))

omit [StarModule ℂ A] in
/-- Undoing `β.observable` by `β.symm.observable` recovers the original observable. -/
@[simp]
lemma StarAlgEquiv.symm_observable_observable (β : A ≃⋆ₐ[ℂ] A) (a : Observable A) :
    β.symm.observable (β.observable a) = a :=
  Subtype.ext (β.symm_apply_apply (a : A))

omit [StarModule ℂ A] in
/-- Applying `β.observable` after `β.symm.observable` recovers the original observable. -/
@[simp]
lemma StarAlgEquiv.observable_symm_observable (β : A ≃⋆ₐ[ℂ] A) (a : Observable A) :
    β.observable (β.symm.observable a) = a :=
  Subtype.ext (β.apply_symm_apply (a : A))

/-- Star automorphisms preserve the observable Lie bracket. -/
lemma StarAlgEquiv.observable_bracket (β : A ≃⋆ₐ[ℂ] A) (a b : Observable A) :
    β.observable ⁅a, b⁆ = ⁅β.observable a, β.observable b⁆ := by
  apply Subtype.ext
  simp only [observable_coe, selfAdjoint.coe_bracket, map_smul, map_sub, map_mul]

end StarAlgEquivObservable

/-! ## C⋆-automorphisms as channels and order-unit symmetries -/

section StarAlgEquivChannel

open scoped selfAdjoint

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A C⋆-⋆-automorphism is a unital completely positive channel. -/
noncomputable def StarAlgEquiv.toChannel (β : A ≃⋆ₐ[ℂ] A) : Channel A A where
  toCompletelyPositiveMap := β.toStarAlgHom
  map_one' := β.map_one

/-- The order-unit channel obtained by restricting a C⋆-⋆-automorphism to self-adjoint elements.
This is the bridge from algebraic reversible dynamics to Basic's states, effects, and covariant
channel API. -/
noncomputable def StarAlgEquiv.observableUPLM (β : A ≃⋆ₐ[ℂ] A) :
    selfAdjoint A →ₚ₁[ℝ] selfAdjoint A :=
  .ofLinearMap
    { toFun := β.observable
      map_add' := fun a b => Subtype.ext <| by
        change β ((a : A) + b) = β (a : A) + β b
        rw [map_add]
      map_smul' := fun r a => Subtype.ext <| by
        change β ((r : ℂ) • (a : A)) = (r : ℂ) • β (a : A)
        exact map_smulₛₗ β.toStarAlgHom (r : ℂ) (a : A) }
    (fun a ha => by
      show (0 : A) ≤ β (a : A)
      exact map_nonneg β.toStarAlgHom ha)
    (by
      ext
      change β (1 : A) = (1 : A)
      exact β.map_one)

/-- The observable channel induced by `β` has the expected pointwise action. -/
@[simp]
lemma StarAlgEquiv.observableUPLM_apply (β : A ≃⋆ₐ[ℂ] A) (a : selfAdjoint A) :
    β.observableUPLM a = β.observable a := rfl

/-- Every C⋆-⋆-automorphism induces an order-unit symmetry of the self-adjoint observables. -/
noncomputable def StarAlgEquiv.observableSymmetry (β : A ≃⋆ₐ[ℂ] A) : Symmetry (selfAdjoint A) :=
  ⟨β.observableUPLM, β.symm.observableUPLM, by
      apply UnitalPositiveLinearMap.ext
      intro a
      change β.symm.observable (β.observable a) = a
      exact β.symm_observable_observable a,
    by
      apply UnitalPositiveLinearMap.ext
      intro a
      change β.observable (β.symm.observable a) = a
      exact β.observable_symm_observable a⟩

/-- The observable symmetry induced by `β` is its restricted order-unit channel. -/
@[simp]
lemma StarAlgEquiv.val_observableSymmetry (β : A ≃⋆ₐ[ℂ] A) :
    (β.observableSymmetry : selfAdjoint A →ₚ₁[ℝ] selfAdjoint A) = β.observableUPLM := rfl

end StarAlgEquivChannel

section StarAlgEquivInterSystemChannel

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The UCP channel determined by a ⋆-isomorphism between two C⋆-algebras. -/
noncomputable def StarAlgEquiv.toInterSystemChannel (β : A ≃⋆ₐ[ℂ] B) : Channel A B where
  toCompletelyPositiveMap := β.toStarAlgHom
  map_one' := β.map_one

/-- The order-unit channel induced by a ⋆-isomorphism between two observable algebras. -/
noncomputable def StarAlgEquiv.toObservableUPLM (β : A ≃⋆ₐ[ℂ] B) :
    selfAdjoint A →ₚ₁[ℝ] selfAdjoint B :=
  .ofLinearMap
    { toFun := fun a => ⟨β (a : A), by
          show star (β (a : A)) = β (a : A)
          rw [← map_star, a.2]⟩
      map_add' := fun a b => Subtype.ext <| by
        change β ((a : A) + b) = β (a : A) + β b
        rw [map_add]
      map_smul' := fun r a => Subtype.ext <| by
        change β ((r : ℂ) • (a : A)) = (r : ℂ) • β (a : A)
        exact map_smulₛₗ β.toStarAlgHom (r : ℂ) (a : A) }
    (fun a ha => by
      show (0 : B) ≤ β (a : A)
      exact map_nonneg β.toStarAlgHom ha)
    (by
      ext
      change β (1 : A) = (1 : B)
      exact β.map_one)

/-- The inter-system observable channel is pointwise the original ⋆-isomorphism. -/
@[simp]
lemma StarAlgEquiv.coe_toObservableUPLM (β : A ≃⋆ₐ[ℂ] B) (a : selfAdjoint A) :
    (β.toObservableUPLM a : B) = β (a : A) := rfl

end StarAlgEquivInterSystemChannel

/-! ## Reversible one-parameter dynamics -/

/-- A one-parameter group of star-algebra automorphisms. -/
structure AutomorphismGroup (A : Type*) [Ring A] [StarRing A] [Module ℂ A] where
  /-- The automorphism at time `t`. -/
  toFun : ℝ → (A ≃⋆ₐ[ℂ] A)
  /-- Evolution at time zero is the identity. -/
  map_zero_apply : ∀ a : A, toFun 0 a = a
  /-- The group law, with evolution by `t` followed by evolution by `s`. -/
  map_add_apply : ∀ (s t : ℝ) (a : A), toFun (s + t) a = toFun s (toFun t a)

/-- An automorphism group is determined by its action at every time. -/
@[ext]
lemma AutomorphismGroup.ext {A : Type*} [Ring A] [StarRing A] [Module ℂ A]
    {α β : AutomorphismGroup A} (h : ∀ t a, α.toFun t a = β.toFun t a) : α = β := by
  have hfun : α.toFun = β.toFun := funext fun t => StarAlgEquiv.ext (h t)
  cases α
  cases β
  cases hfun
  rfl

/-! ## Order-unit dynamics induced by C⋆-automorphisms -/

section AutomorphismGroupObservableDynamics

open scoped selfAdjoint

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- View a C⋆-algebra automorphism group as the existing order-unit automorphism group of its
self-adjoint observables. Its induced `stateEvolution` and symmetry action on effects are therefore
the project's standard ones, rather than parallel constructions. -/
noncomputable def AutomorphismGroup.toObservableDynamics (α : AutomorphismGroup A) :
    OneParameterAutomorphismGroup (selfAdjoint A) where
  toFun t := (α.toFun t).observableUPLM
  map_zero' := by
    apply UnitalPositiveLinearMap.ext
    intro a
    change (α.toFun 0).observable a = a
    apply Subtype.ext
    exact α.map_zero_apply (a : A)
  map_add' s t := by
    apply UnitalPositiveLinearMap.ext
    intro a
    change (α.toFun (s + t)).observable a =
      (α.toFun s).observable ((α.toFun t).observable a)
    apply Subtype.ext
    exact α.map_add_apply s t (a : A)

/-- The observable dynamics is the restriction of the algebraic dynamics at each time. -/
@[simp]
lemma AutomorphismGroup.toObservableDynamics_apply (α : AutomorphismGroup A) (t : ℝ)
    (a : selfAdjoint A) : α.toObservableDynamics t a = (α.toFun t).observable a := rfl

end AutomorphismGroupObservableDynamics

/-! ## Transporting and conjugating automorphism groups

A ⋆-isomorphism `β : A ≃⋆ₐ[ℂ] B` transports a dynamics on `A` to one on `B`. The defining
commuting square says that applying `β` after evolving in `A` agrees with evolving after applying
`β`. This is the dynamics-level counterpart of the channel covariance API: it is the form used by
a quadratic normal-form equivalence, and it also applies to any later change of algebraic
description.

Conjugation is the special case `A = B`. -/

section AutomorphismGroupTransport

variable {A B C : Type*} [Ring A] [StarRing A] [Module ℂ A]
  [Ring B] [StarRing B] [Module ℂ B] [Ring C] [StarRing C] [Module ℂ C]

/-- Transport a one-parameter ⋆-automorphism group across a ⋆-isomorphism. -/
def AutomorphismGroup.transport (β : A ≃⋆ₐ[ℂ] B) (α : AutomorphismGroup A) :
    AutomorphismGroup B where
  toFun t := (β.symm.trans (α.toFun t)).trans β
  map_zero_apply b := by
    simp [StarAlgEquiv.trans_apply, α.map_zero_apply]
  map_add_apply s t b := by
    simp only [StarAlgEquiv.trans_apply, α.map_add_apply, β.symm_apply_apply]

/-- Unfolds transported dynamics: evolve after pulling back through the ⋆-isomorphism. -/
@[simp]
lemma AutomorphismGroup.transport_apply (β : A ≃⋆ₐ[ℂ] B) (α : AutomorphismGroup A)
    (t : ℝ) (b : B) :
    (α.transport β).toFun t b = β (α.toFun t (β.symm b)) := by
  simp [AutomorphismGroup.transport, StarAlgEquiv.trans_apply]

/-- A ⋆-isomorphism intertwines two dynamics when its square commutes at every time. -/
def AutomorphismGroup.IsIntertwining (α : AutomorphismGroup A) (γ : AutomorphismGroup B)
    (β : A ≃⋆ₐ[ℂ] B) : Prop :=
  ∀ (t : ℝ) (a : A), β (α.toFun t a) = γ.toFun t (β a)

/-- Transported dynamics is intertwined with the original dynamics by the transporting
⋆-isomorphism. -/
lemma AutomorphismGroup.isIntertwining_transport (β : A ≃⋆ₐ[ℂ] B)
    (α : AutomorphismGroup A) :
    α.IsIntertwining (α.transport β) β := by
  intro t a
  simp

/-- A ⋆-isomorphism intertwines a flow with precisely the dynamics transported along it. -/
lemma AutomorphismGroup.isIntertwining_iff_eq_transport (α : AutomorphismGroup A)
    (γ : AutomorphismGroup B) (β : A ≃⋆ₐ[ℂ] B) :
    α.IsIntertwining γ β ↔ γ = α.transport β := by
  constructor
  · intro h
    apply AutomorphismGroup.ext
    intro t b
    simpa using (h t (β.symm b)).symm
  · rintro rfl
    exact α.isIntertwining_transport β

/-- Intertwining squares compose along composable ⋆-isomorphisms. -/
lemma AutomorphismGroup.IsIntertwining.trans {α : AutomorphismGroup A} {γ : AutomorphismGroup B}
    {δ : AutomorphismGroup C} {β : A ≃⋆ₐ[ℂ] B} {χ : B ≃⋆ₐ[ℂ] C}
    (hβ : α.IsIntertwining γ β) (hχ : γ.IsIntertwining δ χ) :
    α.IsIntertwining δ (β.trans χ) := by
  intro t a
  change χ (β (α.toFun t a)) = δ.toFun t (χ (β a))
  rw [hβ t a, hχ t (β a)]

/-- Transport through the identity ⋆-isomorphism leaves a flow unchanged. -/
@[simp]
lemma AutomorphismGroup.transport_refl (α : AutomorphismGroup A) :
    α.transport (StarAlgEquiv.refl (R := ℂ) (A := A)) = α := by
  apply AutomorphismGroup.ext
  intro t a
  simp

/-- Successive changes of algebraic coordinates transport a flow by their composite. -/
lemma AutomorphismGroup.transport_trans (α : AutomorphismGroup A) (β : A ≃⋆ₐ[ℂ] B)
    (γ : B ≃⋆ₐ[ℂ] C) :
    (α.transport β).transport γ = α.transport (β.trans γ) := by
  apply AutomorphismGroup.ext
  intro t c
  simp only [AutomorphismGroup.transport_apply, StarAlgEquiv.trans_apply,
    StarAlgEquiv.symm_trans_apply]

/-- Transporting back through the inverse ⋆-isomorphism recovers the original flow. -/
@[simp]
lemma AutomorphismGroup.transport_symm_transport (α : AutomorphismGroup A) (β : A ≃⋆ₐ[ℂ] B) :
    (α.transport β).transport β.symm = α := by
  apply AutomorphismGroup.ext
  intro t a
  simp

end AutomorphismGroupTransport

/-! ## Conjugating an automorphism group by a star automorphism

Changing which ⋆-automorphism `β` identifies the algebra with itself conjugates a flow `α`:
`(conj β α) t = β ∘ α t ∘ β⁻¹`. -/

section AutomorphismGroupConj

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A]

/-- The automorphism group `α`, viewed through the change of coordinates `β`:
`(conj β α) t = β ∘ (α t) ∘ β⁻¹`. -/
def AutomorphismGroup.conj (β : A ≃⋆ₐ[ℂ] A) (α : AutomorphismGroup A) : AutomorphismGroup A where
  toFun := (α.transport β).toFun
  map_zero_apply := (α.transport β).map_zero_apply
  map_add_apply := (α.transport β).map_add_apply

/-- Unfolds `AutomorphismGroup.conj` to `(conj β α) t a = β (α t (β⁻¹ a))`. -/
@[simp]
lemma AutomorphismGroup.conj_apply (β : A ≃⋆ₐ[ℂ] A) (α : AutomorphismGroup A) (t : ℝ) (a : A) :
    (α.conj β).toFun t a = β (α.toFun t (β.symm a)) := by
  simp [AutomorphismGroup.conj]

/-- Conjugating by the identity automorphism changes nothing. -/
@[simp]
lemma AutomorphismGroup.conj_refl (α : AutomorphismGroup A) :
    α.conj (StarAlgEquiv.refl (R := ℂ) (A := A)) = α := by
  apply AutomorphismGroup.ext
  intro t a
  simp

/-- Conjugating successively by `β` then `γ` is the same as conjugating once by `β.trans γ`. -/
lemma AutomorphismGroup.conj_conj (α : AutomorphismGroup A) (β γ : A ≃⋆ₐ[ℂ] A) :
    (α.conj β).conj γ = α.conj (β.trans γ) := by
  apply AutomorphismGroup.ext
  intro t a
  simp only [AutomorphismGroup.conj_apply, StarAlgEquiv.trans_apply, StarAlgEquiv.symm_trans_apply]

/-- Conjugating by `β` and then undoing it with `β.symm` recovers the original flow. -/
@[simp]
lemma AutomorphismGroup.conj_symm_conj (α : AutomorphismGroup A) (β : A ≃⋆ₐ[ℂ] A) :
    (α.conj β).conj β.symm = α := by
  apply AutomorphismGroup.ext
  intro t a
  simp

/-- Conjugating by `β.symm` and then undoing it with `β` recovers the original flow. -/
@[simp]
lemma AutomorphismGroup.conj_conj_symm (α : AutomorphismGroup A) (β : A ≃⋆ₐ[ℂ] A) :
    (α.conj β.symm).conj β = α := by
  apply AutomorphismGroup.ext
  intro t a
  simp

end AutomorphismGroupConj
