/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.SelfAdjoint
public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Restrict
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic

/-!

# Observables

An observable is a self-adjoint element of a space with an additive involution.
This definition needs neither multiplication nor a norm. In particular, the
self-adjoint part of a complex operator algebra is already an observable space
before any C⋆-algebraic structure is used.

A complex state on a starred space restricts to a real state on its observables.
Thus the expectation-value functional is itself an instance of the general
state notion `𝓢[ℝ, Observable A]`; it does not require a separate definition of
linearity, positivity, or normalization.

## The abstract order-unit case

When `E` already is a real ordered vector space (rather than the self-adjoint part of a complex
one), no restriction is needed at all: `Observable E ⊆ E` directly, and a state `s : 𝓢[ℝ, E]` is
already linear and positive on all of `E`, so it pairs with an observable `a : Observable E` by
simply evaluating `s (a : E)`. Linearity (`map_add`, `map_smul`), positivity of a positive
observable's expectation (`map_nonneg`), and the expectation of the unit observable (`map_one`)
are consequently not new facts about states meeting observables — they are the same generic
`UnitalPositiveLinearMap` lemmas already used everywhere else, applied at `a : E`. The examples
below witness this; no bespoke `expectation` definition is needed.

## Main definitions

- `Observable A`, `PositiveObservable A`
- `UnitalPositiveLinearMap.onObservables` : the real state on observables induced by a complex
  state on the ambient starred space.

-/

@[expose] public section

/-- An observable in a space with an additive involution. -/
abbrev Observable (A : Type*) [AddGroup A] [StarAddMonoid A] := selfAdjoint A

/-- A positive observable in an ordered space with an additive involution. -/
abbrev PositiveObservable (A : Type*) [AddGroup A] [StarAddMonoid A] [PartialOrder A] :=
  {a : Observable A // 0 ≤ (a : A)}

open scoped ComplexOrder

namespace UnitalPositiveLinearMap

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A]
    [SelfAdjointDecompose A] [Module ℂ A] [StarModule ℂ A]

/-- The real state on observables induced by a complex state on the ambient starred space. -/
noncomputable def onObservables (ω : 𝓢[A]) : 𝓢[ℝ, Observable A] :=
  ω.restrictSAC

/-- Restricting a state to observables does not change its values, after regarding the real
expectation value as a complex number. -/
@[simp, norm_cast]
lemma coe_onObservables_apply (ω : 𝓢[A]) (a : Observable A) :
    ((ω.onObservables a : ℝ) : ℂ) = ω (a : A) := by
  exact coe_restrictSAC_apply ω a

end UnitalPositiveLinearMap

section OrderUnit

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsOrderUnit E] [StarAddMonoid E] [StarModule ℝ E]

example (s : 𝓢[ℝ, E]) (a b : Observable E) :
    s ((a : E) + (b : E)) = s (a : E) + s (b : E) := map_add s (a : E) (b : E)

example (s : 𝓢[ℝ, E]) (c : ℝ) (a : Observable E) :
    s (c • (a : E)) = c * s (a : E) := by
  rw [map_smul]; rfl

example (s : 𝓢[ℝ, E]) {a : Observable E} (ha : 0 ≤ (a : E)) : 0 ≤ s (a : E) := s.map_nonneg ha

example (s : 𝓢[ℝ, E]) (h1 : IsSelfAdjoint (1 : E)) : s ((⟨1, h1⟩ : Observable E) : E) = 1 :=
  map_one s

end OrderUnit
