/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Physlib.SpaceAndTime.Space.Module
public import Physlib.Meta.TODO.Basic
/-!

# Position states

## i. Overview

Informally, the position "state" at `x : Space d` has a non-normalizable wavefunction which is
a Dirac-delta function centered at `x`. More precisely, the position "state" lives in the _rigged_
Hilbert space `𝓢(Space d, ℂ) < SpaceDHilbertSpace d μ < StrongDual ℂ 𝓢(Space d, ℂ)` as the element
of the dual of `𝓢(Space d, ℂ)` defined by evaluation at `x`.

## ii. Key results

## iii. Table of contents

## iv. References

* https://en.wikipedia.org/wiki/Rigged_Hilbert_space. [ref: wiki_rigged_hilbert_space]
-/

@[expose] public section

TODO "Prove that position states are generalized eigenvectors of every multiplication operator."

namespace QuantumMechanics
namespace SpaceDHilbertSpace

noncomputable section

open scoped SchwartzMap

variable {d : ℕ}

/-- Position state as a member of the strong dual of the Schwartz space.

  For a given `x` this corresponds to the non-normalizable wavefunction `ψ(y) = δᵈ(y - x) -/
def positionState (x : Space d) : StrongDual ℂ 𝓢(Space d, ℂ) := TemperedDistribution.delta x

/-- The defining property of position states. -/
@[simp]
lemma positionState_apply (x : Space d) (f : 𝓢(Space d, ℂ)) : positionState x f = f x := rfl

/-- Two Schwartz maps are equal if they are equal on all position states. -/
lemma eq_of_eq_positionState {f g : 𝓢(Space d, ℂ)}
    (h : ∀ x, positionState x f = positionState x g) : f = g := by
  ext x
  exact h x

end
end SpaceDHilbertSpace
end QuantumMechanics
