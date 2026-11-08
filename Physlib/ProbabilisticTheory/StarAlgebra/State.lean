/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Physlib.ProbabilisticTheory.State.Basic
public import Physlib.ProbabilisticTheory.StarAlgebra.Traciality

/-!
# Observables and states of a star algebra

A positive map sends observables to observables. A state gives observables real expectation
values. A tracial state does not see the order of a product.

## i. Overview

The observables of a quantum system are the self-adjoint operators of its algebra. A state gives
every operator a complex expectation value.

A state is tracial if the expectation value of a product does not depend on the order of the
factors: `ω (a b) = ω (b a)`. Then `ω` vanishes on every commutator. A tracial state gives the
same expectation value after a change of frame by a unitary `u`: `ω (u x u⋆) = ω x`.

A state has a real expectation value on every observable. Its real part is a state of the
observables.

A positive map sends the operators of one system to operators of another. It sends observables to
observables. A unital positive map restricts to a channel between the observables.

## ii. Key results

- `Observable` : the self-adjoint elements, such as Hermitian operators.
- `UnitalPositiveLinearMap.IsTracial` : a tracial state.
- `UnitalPositiveLinearMap.IsTracial.map_commutator` : a tracial state vanishes on commutators.
- `UnitalPositiveLinearMap.IsTracial.map_conj` : a tracial state is invariant under
  `x ↦ u * x * u⋆` for a unitary `u`.
- `UnitalPositiveLinearMap.isTracial_iff_star_mul_self_eq_mul_star_self` : `ω` is tracial if and
  only if `ω (a⋆ * a) = ω (a * a⋆)` for all `a`.
- `UnitalPositiveLinearMap.onObservables` : a state restricted to a state of the observables.
- `UnitalPositiveLinearMap.coe_onObservables_apply` : the expectation value of an observable is
  real.
- `UnitalPositiveLinearMap.restrictObservables` : a unital positive map restricted to a channel
  between observables.

## iii. Table of contents

- A. Observables and tracial states
- B. States of observables
- C. Channels between observables

## iv. References

-/

@[expose] public section

open ComplexOrder

/-!

## A. Observables and tracial states

-/

/-- An observable: a self-adjoint element, such as a Hermitian operator. -/
abbrev Observable (𝒜 : Type*) [AddGroup 𝒜] [StarAddMonoid 𝒜] := selfAdjoint 𝒜

namespace UnitalPositiveLinearMap

variable {𝒜 : Type*} [Ring 𝒜] [PartialOrder 𝒜] [Module ℂ 𝒜]

/-- A state `ω` is tracial if `ω (a * b) = ω (b * a)` for all `a` and `b`. -/
def IsTracial (ω : 𝓢[ℂ, 𝒜]) : Prop :=
  ω.toLinearMap.IsTracial

/-- A tracial state does not see the order of a product. -/
lemma IsTracial.map_mul_comm {ω : 𝓢[ℂ, 𝒜]} (h : ω.IsTracial) (a b : 𝒜) :
    ω (a * b) = ω (b * a) :=
  h a b

/-- A tracial state vanishes on commutators. -/
lemma IsTracial.map_commutator {ω : 𝓢[ℂ, 𝒜]} (h : ω.IsTracial) (a b : 𝒜) :
    ω (a * b - b * a) = 0 := by
  rw [map_sub, h.map_mul_comm a b, sub_self]

variable [StarRing 𝒜]

/-- A tracial state is invariant under the change of frame `x ↦ u * x * u⋆` by a unitary. -/
lemma IsTracial.map_conj {ω : 𝓢[ℂ, 𝒜]} (h : ω.IsTracial) (u : unitary 𝒜) (x : 𝒜) :
    ω (u * x * star (u : 𝒜)) = ω x := by
  simpa [← mul_assoc] using h.map_mul_comm (u * x) (star (u : 𝒜))

variable [StarModule ℂ 𝒜]

section

variable [IsScalarTower ℂ 𝒜 𝒜] [SMulCommClass ℂ 𝒜 𝒜]

/-- A state is tracial if and only if `ω (a⋆ * a) = ω (a * a⋆)` for all `a`. -/
lemma isTracial_iff_star_mul_self_eq_mul_star_self (ω : 𝓢[ℂ, 𝒜]) :
    ω.IsTracial ↔ ∀ a : 𝒜, ω (star a * a) = ω (a * star a) :=
  LinearMap.isTracial_iff_star_mul_self_eq_mul_star_self ω.toLinearMap

end

/-!

## B. States of observables

-/

variable [SelfAdjointDecompose 𝒜]

/-- The real part of a state is a state of the observables. Its value is the expectation value
(`coe_onObservables_apply`). -/
noncomputable def onObservables (ω : 𝓢[ℂ, 𝒜]) : 𝓢[ℝ, Observable 𝒜] where
  toFun x := (ω x).re
  map_add' x y := by simp
  map_smul' r x := by simp [← Complex.coe_smul]
  monotone' _ _ h := (Complex.le_def.mp (ω.monotone h)).1
  map_one' := by simp

/-- The expectation value of an observable is real. It equals its real part. -/
@[simp, norm_cast]
lemma coe_onObservables_apply (ω : 𝓢[ℂ, 𝒜]) (x : Observable 𝒜) :
    ((ω.onObservables x : ℝ) : ℂ) = ω (x : 𝒜) :=
  Complex.conj_eq_iff_re.mp (by rw [← Complex.star_def]; exact (x.2.map' ω).star_eq)

/-!

## C. Channels between observables

-/

variable {ℬ : Type*} [Ring ℬ] [PartialOrder ℬ] [Module ℂ ℬ] [StarRing ℬ] [StarModule ℂ ℬ]
  [StarOrderedRing ℬ]

/-- A unital positive map restricts to a channel between observables. -/
noncomputable def restrictObservables (f : 𝒜 →ₚ₁[ℂ] ℬ) : Observable 𝒜 →ₚ₁[ℝ] Observable ℬ where
  toFun x := ⟨f x, x.2.map' f⟩
  map_add' x y := Subtype.ext (map_add f (x : 𝒜) y)
  map_smul' r x := Subtype.ext (map_smul f (r : ℂ) (x : 𝒜))
  monotone' _ _ h := f.monotone h
  map_one' := Subtype.ext (map_one f)

/-- The restricted channel acts as the original map. -/
@[simp]
lemma coe_restrictObservables_apply (f : 𝒜 →ₚ₁[ℂ] ℬ) (x : Observable 𝒜) :
    (f.restrictObservables x : ℬ) = f x := rfl

end UnitalPositiveLinearMap
