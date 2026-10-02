/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem, Adam Bornemann
-/
module

public import Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!

# The essential spectrum

## i. Overview

A real number `λ` is in the essential spectrum of a self-adjoint operator `A` when there is a
singular sequence for `λ`: vectors `ψₙ` in the domain of `A` with `‖ψₙ‖ → 1`, `⟪g, ψₙ⟫ → 0` for
every `g`, and `‖A ψₙ - λ ψₙ‖ → 0`. Orthonormal approximate eigenvectors are singular sequences.

## ii. Key results

- `essSpectrum` : the essential spectrum of a self-adjoint operator.
- `mem_essSpectrum_of_seq` : membership from a singular sequence.

## iii. References

- Adapted from `adambornemann-glitch/Spectra`, `SpectralTheory/Essential/Defs.lean` (Apache 2.0).

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open Filter Topology
open scoped InnerProductSpace

namespace QuantumMechanics.Essential

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **essential spectrum** of a self-adjoint operator `A`, defined by singular (Weyl)
sequences: `λ ∈ essSpectrum hA` iff there is `ψ : ℕ → A.domain` with `‖ψ n‖ → 1`, `ψ` weakly null,
and `‖A ψ n − λ ψ n‖ → 0`. (`hA` is carried for discoverability; the set depends only on `A`.) -/
def essSpectrum {A : H →ₗ.[ℂ] H} (_hA : IsSelfAdjoint A) : Set ℝ :=
  { lam | ∃ ψ : ℕ → A.domain,
      Tendsto (fun n => ‖(ψ n : H)‖) atTop (𝓝 1) ∧
      (∀ g : H, Tendsto (fun n => ⟪g, (ψ n : H)⟫_ℂ) atTop (𝓝 0)) ∧
      Tendsto (fun n => ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖) atTop (𝓝 0) }

/-- Membership in `essSpectrum` from an `H`-valued Weyl sequence together with a domain-membership
witness. This packages the `ℕ → A.domain` data so callers can work with plain vectors. -/
lemma mem_essSpectrum_of_seq {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (lam : ℝ)
    (φ : ℕ → H) (hmem : ∀ n, φ n ∈ A.domain)
    (hnorm : Tendsto (fun n => ‖φ n‖) atTop (𝓝 1))
    (hweak : ∀ g : H, Tendsto (fun n => ⟪g, φ n⟫_ℂ) atTop (𝓝 0))
    (heig : Tendsto (fun n => ‖A ⟨φ n, hmem n⟩ - (lam : ℂ) • φ n‖) atTop (𝓝 0)) :
    lam ∈ essSpectrum hA :=
  ⟨fun n => ⟨φ n, hmem n⟩, hnorm, hweak, heig⟩

end QuantumMechanics.Essential

end ProbabilisticTheory
