/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Basic.StarAlgebra.Observable
public import PhyslibAlpha.QuantumMechanics.Basic.StarAlgebra.Lie
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
- `AutomorphismGroup.conj` : reindexing a flow `α` by a change of coordinates `β`,
  `(conj β α) t = β ∘ (α t) ∘ β⁻¹`.

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

/-! ## Conjugating an automorphism group by a star automorphism

Changing which ⋆-automorphism `β` identifies the algebra with itself conjugates a flow `α`:
`(conj β α) t = β ∘ α t ∘ β⁻¹`. -/

section AutomorphismGroupConj

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A]

/-- The automorphism group `α`, viewed through the change of coordinates `β`:
`(conj β α) t = β ∘ (α t) ∘ β⁻¹`. -/
def AutomorphismGroup.conj (β : A ≃⋆ₐ[ℂ] A) (α : AutomorphismGroup A) : AutomorphismGroup A where
  toFun t := (β.symm.trans (α.toFun t)).trans β
  map_zero_apply a := by
    simp [StarAlgEquiv.trans_apply, α.map_zero_apply]
  map_add_apply s t a := by
    simp only [StarAlgEquiv.trans_apply, α.map_add_apply, β.symm_apply_apply]

/-- Unfolds `AutomorphismGroup.conj` to `(conj β α) t a = β (α t (β⁻¹ a))`. -/
@[simp]
lemma AutomorphismGroup.conj_apply (β : A ≃⋆ₐ[ℂ] A) (α : AutomorphismGroup A) (t : ℝ) (a : A) :
    (α.conj β).toFun t a = β (α.toFun t (β.symm a)) := by
  simp [AutomorphismGroup.conj, StarAlgEquiv.trans_apply]

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
