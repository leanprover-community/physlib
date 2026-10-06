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

# Momentum states

## i. Overview

Informally, the momentum "state" corresponding to momentum `p` is the non-normalizable
plane wave `exp (I p ⬝ᵥ x)`. More precisely, the momentum "state" lives in the _rigged_ Hilbert
space `𝓢(Space d, ℂ) < SpaceDHilbertSpace d μ < StrongDual ℂ 𝓢(Space d, ℂ)` as the element
of the dual of `𝓢(Space d, ℂ)` defined by evaluation of the Fourier transform at `p`.

## ii. Key results

## iii. Table of contents

## iv. References

* https://en.wikipedia.org/wiki/Rigged_Hilbert_space. [ref: wiki_rigged_hilbert_space]
-/

@[expose] public section

TODO "Prove that momentum states are generalized eigenvectors of every derivative operator."

namespace QuantumMechanics

namespace SpaceDHilbertSpace

noncomputable section

open scoped Real SchwartzMap
open FourierTransform

variable {d : ℕ}

/-- Momentum state as a member of the strong dual of the Schwartz space.

  For a given `p` this corresponds to the non-normalizable plane wave `exp (I p ⬝ᵥ x)`. -/
def momentumState (p : Space d) : StrongDual ℂ 𝓢(Space d, ℂ) :=
  TemperedDistribution.delta ((2 * π)⁻¹ • p) ∘L fourierCLM ℂ 𝓢(Space d, ℂ)

/-- The defining property of momentum states. -/
@[simp]
lemma momentumState_apply (p : Space d) (ψ : 𝓢(Space d, ℂ)) :
    momentumState p ψ = 𝓕 ψ ((2 * π)⁻¹ • p) := rfl

/-- Two Schwartz maps are equal if they are equal on all momentum states. -/
lemma eq_of_eq_momentumState {ψ φ : 𝓢(Space d, ℂ)}
    (h : ∀ p, momentumState p ψ = momentumState p φ) : ψ = φ :=
  fourierCLE ℂ 𝓢(Space d, ℂ) |>.injective <| SchwartzMap.ext
    fun k ↦ by simpa [smul_smul, ← mul_rotate] using h ((2 * π) • k)

end
end SpaceDHilbertSpace
end QuantumMechanics
