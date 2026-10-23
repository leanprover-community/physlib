/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.SpaceAndTime.Space.Module
public import Physlib.Meta.TODO.Basic
/-!

# Momentum states

## i. Overview

Informally, the momentum "state" corresponding to the wave vector `p`, of momentum `ℏ p`, is the
non-normalizable plane wave `exp (I p ⬝ᵥ x)`. More precisely, the momentum "state" lives in the
_rigged_ Hilbert space `𝓢(Space d, ℂ) < SpaceDHilbertSpace d μ < StrongDual ℂ 𝓢(Space d, ℂ)`
as the bra `⟨p|`. This is the linear functional `ψ ↦ ⟨exp (I p ⬝ᵥ x), ψ⟩ = 𝓕 ψ ((2π)⁻¹ • p)`.

An operator `A` acts on `momentumState p` by precomposition, `⟨p| A = momentumState p ∘L A`.

## ii. Key results

- `momentumState` : the momentum state as a member of the strong dual of the Schwartz space.
- `momentumState_comp_momentumCLM` : the momentum state `momentumState p` is a generalized
  eigenvector of `𝐩 i` with eigenvalue `ℏ pᵢ`.

## iii. Table of contents

- A. Momentum states
- B. Momentum states as generalized eigenvectors

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

/-!

## A. Momentum states

-/

/-- Momentum state as a member of the strong dual of the Schwartz space.

  For a given wave vector `p` this is the bra `⟨p|` of the non-normalizable plane wave
  `exp (I p ⬝ᵥ x)`, that is `ψ ↦ ⟨exp (I p ⬝ᵥ x), ψ⟩`. -/
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

/-!

## B. Momentum states as generalized eigenvectors

-/

open Constants Complex Space SchwartzMap LineDeriv in
/-- The momentum state `momentumState p` is a generalized eigenvector of `𝐩 i` with eigenvalue
`ℏ pᵢ`, in the bra form `⟨p| 𝐩ᵢ = ℏ pᵢ ⟨p|` as functionals on Schwartz space. Since `𝐩 i` is
symmetric and `ℏ pᵢ` is real, this is equivalent to the ket form `𝐩ᵢ |p⟩ = ℏ pᵢ |p⟩`. -/
lemma momentumState_comp_momentumCLM (p : Space d) (i : Fin d) :
    momentumState p ∘L 𝐩 i = (ℏ * p i : ℂ) • momentumState p := by
  ext ψ
  change momentumState p ((-I * ℏ) • ∂_{basis i} ψ) = _
  have : (fun x : Space d ↦ x.val i).HasTemperateGrowth := by fun_prop
  simp [fourier_lineDerivOp_eq, smulLeftCLM_apply_apply this]
  field_simp
  ring_nf
  simp [I_sq]

end
end SpaceDHilbertSpace
end QuantumMechanics
