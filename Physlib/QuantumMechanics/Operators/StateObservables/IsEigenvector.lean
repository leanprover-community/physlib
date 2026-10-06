/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Krystian Nowakowski
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Complex.Basic
/-!
# Eigenvectors of partial linear maps

## Main definitions

- `LinearPMap.IsEigenvector`: a nonzero domain vector satisfying `T ψ = μ • ψ`.

-/

@[expose] public section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A nonzero vector in the domain of `T` satisfying `T ψ = μ • ψ`. -/
def IsEigenvector (T : H →ₗ.[ℂ] H) (ψ : T.domain) (μ : ℂ) : Prop :=
  T ψ = μ • (ψ : H) ∧ (ψ : H) ≠ 0

/-- The eigenvalue equation for a partial-map eigenvector. -/
lemma IsEigenvector.apply_eq {T : H →ₗ.[ℂ] H} {ψ : T.domain} {μ : ℂ}
    (hψ : T.IsEigenvector ψ μ) :
    T ψ = μ • (ψ : H) :=
  hψ.1

/-- A partial-map eigenvector is nonzero. -/
lemma IsEigenvector.ne_zero {T : H →ₗ.[ℂ] H} {ψ : T.domain} {μ : ℂ}
    (hψ : T.IsEigenvector ψ μ) :
    (ψ : H) ≠ 0 :=
  hψ.2

end LinearPMap
