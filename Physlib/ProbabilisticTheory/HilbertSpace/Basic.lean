/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Physlib.ProbabilisticTheory.CStarAlgebra.OrderUnit
public import Physlib.ProbabilisticTheory.StarAlgebra.State

/-!
# Hilbert-space quantum systems

States assign expectations to the bounded observables of a Hilbert space.

## i. Overview

For a complex Hilbert space `H`, `Operator H` is the unital C⋆-algebra `B(H)`. Composition is
multiplication and the adjoint is the involution. Mathlib supplies these structures.
`Observable H` is its real order-unit space of self-adjoint operators.

A state is a positive unital complex-linear functional on `B(H)`. Positivity gives continuity.
A bounded observable has a real expectation. Bounds on its outcomes bound its expectation.
These expectations determine the state on the whole algebra. The definition includes all
states. Normal states and their trace-class representations require further results.

## ii. Key results

- `ProbabilisticTheory.HilbertSpace.Operator` : the bounded-operator algebra.
- `ProbabilisticTheory.HilbertSpace.Observable` : the bounded observables.
- `ProbabilisticTheory.HilbertSpace.State` : states of `B(H)`.
- `ProbabilisticTheory.HilbertSpace.State.toDual` : a state as a bounded functional.
- `ProbabilisticTheory.HilbertSpace.State.expectation_mem_Icc` : bounds on expectations.
- `ProbabilisticTheory.HilbertSpace.State.ext` : observable expectations determine a state.

## iii. Table of contents

- A. Operators and observables
- B. States and bounded functionals
- C. Observable expectations
  - C.1. Bounds and determination

## iv. References
-/

@[expose] public section

open ComplexOrder

namespace ProbabilisticTheory.HilbertSpace

/-!
## A. Operators and observables
-/

/-- The bounded operators on a complex inner product space. For complete `H` this is `B(H)`. -/
abbrev Operator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] := H →L[ℂ] H

/-- The bounded observables: the self-adjoint part of `B(H)` as a real order-unit space. -/
noncomputable abbrev Observable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] :=
  _root_.Observable (Operator H)

/-!
## B. States and bounded functionals
-/

/-- A state on the bounded operators: a positive unital complex-linear functional. -/
abbrev State (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] := 𝓢[ℂ, Operator H]

namespace State

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A state is a bounded functional on `B(H)`. -/
def toDual (ω : State H) : (Operator H) →L[ℂ] ℂ :=
  { ω.toLinearMap with cont := map_continuous ω }

@[simp]
lemma toDual_apply (ω : State H) (A : Operator H) : ω.toDual A = ω A := rfl

/-!
## C. Observable expectations
-/

/-- The real expectation value of a bounded observable. -/
noncomputable def expectation (ω : State H) (A : Observable H) : ℝ := ω.onObservables A

@[simp]
lemma coe_expectation (ω : State H) (A : Observable H) :
    (ω.expectation A : ℂ) = ω (A : Operator H) := ω.coe_onObservables_apply A

/-!
### C.1. Bounds and determination
-/

/-- Bounds on the outcomes of an observable also bound its expectation. -/
lemma expectation_mem_Icc (ω : State H) (A : Observable H) {a b : ℝ}
    (ha : a • (1 : Observable H) ≤ A) (hb : A ≤ b • (1 : Observable H)) :
    ω.expectation A ∈ Set.Icc a b := by
  constructor
  · calc
      a = ω.onObservables (a • (1 : Observable H)) := by simp
      _ ≤ ω.expectation A := ω.onObservables.monotone ha
  · calc
      ω.expectation A ≤ ω.onObservables (b • (1 : Observable H)) := ω.onObservables.monotone hb
      _ = b := by simp

/-- Agreement on the expectation of every bounded observable determines the whole state. -/
@[ext]
lemma ext {ω η : State H} (h : ∀ A : Observable H, ω.expectation A = η.expectation A) : ω = η := by
  have hobs (A : Observable H) : ω (A : Operator H) = η (A : Operator H) := by
    simpa only [coe_expectation] using congrArg Complex.ofReal (h A)
  apply UnitalPositiveLinearMap.ext
  funext A
  change ω A = η A
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart A]
  conv_rhs => rw [← realPart_add_I_smul_imaginaryPart A]
  simp only [map_add, map_smul, hobs]

end State

end ProbabilisticTheory.HilbertSpace
