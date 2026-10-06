/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.SelfAdjoint
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Restrict
public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.PositiveDual
public import PhyslibAlpha.ProbabilisticTheory.State.Basic

/-!

# Observables

Observables as self-adjoint elements, and the real state on observables of a complex state.

## i. Overview

An observable is a self-adjoint element of a space with an involution. A complex state on the space
restricts to a real state on its observables, the expectation-value functional.

## ii. Key results

- `Observable`, `PositiveObservable` : observables and positive observables.
- `UnitalPositiveLinearMap.onObservables` : the real state on observables of a complex state.

## iii. Table of contents

- A. Observables
- B. The real state on observables
- C. Examples: states on observables

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. Observables -/

/-- An observable in a space with an additive involution. -/
abbrev Observable (A : Type*) [AddGroup A] [StarAddMonoid A] := selfAdjoint A

/-- A positive observable in an ordered space with an additive involution. -/
abbrev PositiveObservable (A : Type*) [AddGroup A] [StarAddMonoid A] [PartialOrder A] :=
  {a : Observable A // 0 ≤ (a : A)}

/-! ## B. The real state on observables -/

open scoped ComplexOrder

namespace UnitalPositiveLinearMap

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A]
    [SelfAdjointDecompose A] [Module ℂ A] [StarModule ℂ A]

/-- The real state on observables induced by a complex state on the ambient starred space. -/
noncomputable def onObservables (ω : 𝓢[ℂ, A]) : 𝓢[ℝ, Observable A] :=
  ω.restrictSAC

/-- Restricting a state to observables does not change its values, after regarding the real
expectation value as a complex number. -/
@[simp, norm_cast]
lemma coe_onObservables_apply (ω : 𝓢[ℂ, A]) (a : Observable A) :
    ((ω.onObservables a : ℝ) : ℂ) = ω (a : A) := by
  exact coe_restrictSAC_apply ω a

end UnitalPositiveLinearMap

/-! ## C. Examples: states on observables -/

section OrderUnit

variable {E : Type*} [OrderUnitSpace E] [StarAddMonoid E] [StarModule ℝ E]

example (s : 𝓢[ℝ, E]) (a b : Observable E) :
    s ((a : E) + (b : E)) = s (a : E) + s (b : E) := map_add s (a : E) (b : E)

example (s : 𝓢[ℝ, E]) (c : ℝ) (a : Observable E) :
    s (c • (a : E)) = c * s (a : E) := by
  rw [map_smul]; rfl

example (s : 𝓢[ℝ, E]) {a : Observable E} (ha : 0 ≤ (a : E)) : 0 ≤ s (a : E) := s.map_nonneg ha

example (s : 𝓢[ℝ, E]) (h1 : IsSelfAdjoint (1 : E)) : s ((⟨1, h1⟩ : Observable E) : E) = 1 :=
  map_one s

end OrderUnit

end ProbabilisticTheory
