/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Basic.StarAlgebra.SelfAdjoint

/-!

# Observables

An observable is a self-adjoint element of a space with an additive involution.
This definition needs neither multiplication nor a norm. In particular, the
self-adjoint part of a complex operator algebra is already an observable space
before any C⋆-algebraic structure is used.

-/

@[expose] public section

/-- An observable in a space with an additive involution. -/
abbrev Observable (A : Type*) [AddGroup A] [StarAddMonoid A] := selfAdjoint A

/-- A positive observable in an ordered space with an additive involution. -/
abbrev PositiveObservable (A : Type*) [AddGroup A] [StarAddMonoid A] [PartialOrder A] :=
  {a : Observable A // 0 ≤ (a : A)}
