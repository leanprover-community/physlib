/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.QuasiLocal.AlgebraNet
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.GNS

/-!

# States of the quasi-local algebra from compatible local states

A family of local states, each the restriction of the next, is a state of the quasi-local algebra.

## i. Overview

A state of an infinite system is determined by the expectation values of the local observables.
A *compatible family* assigns to each finite region `X` a state of its algebra `A X` such that the
state of a larger region restricts to the state of the smaller: `ω_Y (incl a) = ω_X (a)`. Such a
family defines a linear functional on the quasi-local algebra, which is a state: normalized,
Hermitian and positive. Every element of the quasi-local algebra is local, and positivity of
`a* a` is positivity of local states.

## ii. Key results

- `LocalStateFamily` : a compatible family of local states.
- `LocalStateFamily.toAlgState` : the state of the quasi-local algebra.
- `LocalStateFamily.toAlgState_of` : its value on a local observable is the local expectation.

## iii. Table of contents

- A. Compatible families
- B. The state of the quasi-local algebra

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1,
  Section 2.6.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

namespace QuasiLocal

open scoped ComplexOrder

variable {S : Type*} [DecidableEq S] (N : AlgebraNet S)

/-! ## A. Compatible families -/

/-- A compatible family of local states of a net of algebras. -/
structure LocalStateFamily where
  /-- The local functionals. -/
  state : ∀ X : Finset S, N.A X →ₗ[ℂ] ℂ
  /-- The functional of a larger region restricts to that of a smaller one. -/
  compat : ∀ {X Y : Finset S} (h : X ≤ Y) (a : N.A X), state Y (N.incl h a) = state X a
  /-- The local functionals are normalized. -/
  map_one : ∀ X, state X 1 = 1
  /-- The local functionals are Hermitian. -/
  map_star : ∀ X (a : N.A X), state X (star a) = star (state X a)
  /-- The local functionals are positive. -/
  nonneg : ∀ X (a : N.A X), 0 ≤ state X (star a * a)

variable {N}

/-! ## B. The state of the quasi-local algebra -/

/-- The linear functional on the quasi-local algebra defined by a compatible family. -/
def LocalStateFamily.lift (ω : LocalStateFamily N) : N.Quasilocal →ₗ[ℂ] ℂ :=
  DirectLimit.Module.lift ℂ (Finset S) N.A (fun X Y (h : X ≤ Y) => N.incl h)
    ω.state (fun _X _Y h a => ω.compat h a)

omit [DecidableEq S] in
lemma LocalStateFamily.lift_of (ω : LocalStateFamily N) (X : Finset S) (a : N.A X) :
    ω.lift (N.of X a) = ω.state X a := rfl

/-- **The state of the quasi-local algebra** defined by a compatible family. -/
def LocalStateFamily.toAlgState (ω : LocalStateFamily N) : AlgState N.Quasilocal where
  toLinearMap := ω.lift
  map_one' := by
    have h : (1 : N.Quasilocal) = N.of ∅ 1 := (_root_.map_one (N.of ∅)).symm
    rw [h, LocalStateFamily.lift_of, ω.map_one]
  map_star' x := by
    obtain ⟨X, a, rfl⟩ := N.exists_of x
    rw [← StarHomClass.map_star (N.of X), LocalStateFamily.lift_of, LocalStateFamily.lift_of,
      ω.map_star]
  nonneg' x := by
    obtain ⟨X, a, rfl⟩ := N.exists_of x
    rw [← StarHomClass.map_star (N.of X), ← _root_.map_mul, LocalStateFamily.lift_of]
    exact ω.nonneg X a

omit [DecidableEq S] in
/-- The state of a compatible family on a local observable is the local expectation. -/
lemma LocalStateFamily.toAlgState_of (ω : LocalStateFamily N) (X : Finset S) (a : N.A X) :
    ω.toAlgState (N.of X a) = ω.state X a := rfl

end QuasiLocal

end ProbabilisticTheory

end
