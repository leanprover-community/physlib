/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem, Adam Bornemann
-/
module

public import Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!

# The essential spectrum (singular/Weyl-sequence definition)

Ported from `adambornemann-glitch/Spectra`'s `SpectralTheory/Essential/Defs.lean` (Apache 2.0),
restated against this repo's own unbounded self-adjoint operator type `H →ₗ.[ℂ] H` /
`LinearPMap.IsSelfAdjoint` (`Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint`)
instead of introducing a parallel one. See `EXTERNAL_INTEGRATION_PLAN.md` §3.4.

For a self-adjoint operator `A` (an unbounded `LinearPMap`) we define the **essential spectrum**
`essSpectrum hA : Set ℝ` by *singular (Weyl) sequences*: `λ ∈ essSpectrum hA` iff there is a
sequence `ψ : ℕ → A.domain` that is

* asymptotically normalized (`‖ψ n‖ → 1`),
* weakly null (`⟪g, ψ n⟫ → 0` for every `g`), and
* an approximate eigensequence (`‖A ψ n − λ ψ n‖ → 0`).

Weak nullness is exactly what is needed for the perturbation theorem (Weyl's theorem, see
`Weyl.lean`): a relatively compact perturbation does not see a weakly-null approximate-eigenvector
sequence. An *orthonormal* approximate eigensequence is a special case — orthonormal sequences are
weakly null (`WeakCompact.lean`) — so this matches the classical Weyl-criterion definition.

- `essSpectrum` : the essential spectrum of a self-adjoint `LinearPMap`.
- `mem_essSpectrum_of_seq` : build membership from an `H`-valued Weyl sequence.
- `essSpectrum_subset_spectrum` : the essential spectrum is contained in the spectrum.

-/

@[expose] public section

noncomputable section

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
theorem mem_essSpectrum_of_seq {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (lam : ℝ)
    (φ : ℕ → H) (hmem : ∀ n, φ n ∈ A.domain)
    (hnorm : Tendsto (fun n => ‖φ n‖) atTop (𝓝 1))
    (hweak : ∀ g : H, Tendsto (fun n => ⟪g, φ n⟫_ℂ) atTop (𝓝 0))
    (heig : Tendsto (fun n => ‖A ⟨φ n, hmem n⟩ - (lam : ℂ) • φ n‖) atTop (𝓝 0)) :
    lam ∈ essSpectrum hA :=
  ⟨fun n => ⟨φ n, hmem n⟩, hnorm, hweak, heig⟩

end QuantumMechanics.Essential
