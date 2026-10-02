/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.BoundedIntegralAlgebra
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Cayley.Measure

/-!

# Spectral data of bounded normal and unitary operators

## i. Overview

`BoundedNormalSpectralData` is a spectral measure on `ℂ` whose integral of the identity is a given
bounded normal operator. `BoundedUnitarySpectralData` is the same for a unitary whose spectral
measure is supported on the unit circle away from `1`. Pulling such a measure back along the Cayley
transform gives a spectral measure on `ℝ`, which is determined by its Cayley pushforward.

## ii. Key results

- `BoundedNormalSpectralData` : a spectral measure reconstructing a bounded normal operator.
- `BoundedUnitarySpectralData` : a spectral measure reconstructing a unitary, supported away from
  `1`.
- `BoundedUnitarySpectralData.realSpectralMeasure` : the pulled-back spectral measure on `ℝ`.
- `BoundedUnitarySpectralData.realSpectralMeasure_eq_of_cayleyMap_eq` : a real spectral measure is
  determined by its Cayley pushforward.

## iii. Table of contents

- A. Bounded normal spectral data
- B. Bounded unitary spectral data

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped InnerProductSpace

namespace QuantumMechanics
namespace WOTSpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. Bounded normal spectral data -/

/-- A spectral measure on `ℂ` whose integral of the identity is the bounded normal operator `U`. -/
structure BoundedNormalSpectralData (U : H →L[ℂ] H) where
  /-- The spectral measure. -/
  spectralMeasure : WOTSpectralMeasure ℂ H
  reconstruction : ∀ x y : H,
    spectralMeasure.complexWeakIntegral id x y = ⟪y, U x⟫_ℂ

namespace BoundedNormalSpectralData

variable {U : H →L[ℂ] H}

@[ext]
lemma ext {D E : BoundedNormalSpectralData U}
    (h : D.spectralMeasure = E.spectralMeasure) : D = E := by
  cases D with
  | mk μ hμ =>
    cases E with
    | mk ν hν =>
      cases h
      rfl

/- A bounded-integral equality is a convenient representation-independent uniqueness criterion.
The stronger hypothesis is intentional: reconstruction of only the identity multiplier does not
by itself expose the spectral projections, whereas equality for all bounded Borel multipliers does.
    -/
lemma ext_of_boundedIntegral_eq {D E : BoundedNormalSpectralData U}
    (h : ∀ (f : ℂ → ℂ) (hf : Measurable f)
      (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C),
      D.spectralMeasure.boundedIntegral f hf hfb =
        E.spectralMeasure.boundedIntegral f hf hfb) :
    D = E := by
  apply ext
  exact WOTSpectralMeasure.ext_of_boundedIntegral_eq h

end BoundedNormalSpectralData

/-! ## B. Bounded unitary spectral data -/

/-- A spectral measure of the unitary `u`, supported on the unit circle and giving no mass to `1`.
-/
structure BoundedUnitarySpectralData (u : H ≃ₗᵢ[ℂ] H) where
  /-- The spectral measure. -/
  spectralMeasure : WOTSpectralMeasure ℂ H
  support_away_one : ∀ S : Set ℂ, MeasurableSet S →
    spectralMeasure S = spectralMeasure (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1})
  reconstruction : ∀ x y : H,
    spectralMeasure.complexWeakIntegral id x y = ⟪y, u x⟫_ℂ

namespace BoundedUnitarySpectralData

variable {u : H ≃ₗᵢ[ℂ] H}

@[ext]
lemma ext {D E : BoundedUnitarySpectralData u}
    (h : D.spectralMeasure = E.spectralMeasure) : D = E := by
  cases D with
  | mk μ hμ hμ' =>
    cases E with
    | mk ν hν hν' =>
      cases h
      rfl

lemma ext_of_boundedIntegral_eq {D E : BoundedUnitarySpectralData u}
    (h : ∀ (f : ℂ → ℂ) (hf : Measurable f)
      (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C),
      D.spectralMeasure.boundedIntegral f hf hfb =
        E.spectralMeasure.boundedIntegral f hf hfb) :
    D = E := by
  apply ext
  exact WOTSpectralMeasure.ext_of_boundedIntegral_eq h

variable {u : H ≃ₗᵢ[ℂ] H} (D : BoundedUnitarySpectralData u)

/-- Pull the bounded unitary measure back to the real line. -/
def realSpectralMeasure : WOTSpectralMeasure ℝ H :=
  WOTSpectralMeasure.cayleyInverseMap D.spectralMeasure

lemma cayleyMap_realSpectralMeasure :
    WOTSpectralMeasure.cayleyMap D.realSpectralMeasure = D.spectralMeasure := by
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  change ((D.realSpectralMeasure.map cayley measurable_cayley) S) = D.spectralMeasure S
  rw [D.realSpectralMeasure.map_apply cayley measurable_cayley hS]
  change ((D.spectralMeasure.map cayleyInverse measurable_cayleyInverse)
      (cayley ⁻¹' S)) = D.spectralMeasure S
  rw [D.spectralMeasure.map_apply cayleyInverse measurable_cayleyInverse
    (hS.preimage measurable_cayley)]
  have hL : MeasurableSet (cayleyInverse ⁻¹' cayley ⁻¹' S) :=
    (hS.preimage measurable_cayley).preimage measurable_cayleyInverse
  rw [D.support_away_one _ hL, D.support_away_one S hS]
  congr 1
  ext z
  constructor
  · rintro ⟨hz, hunit⟩
    refine ⟨?_, hunit⟩
    simpa [Set.mem_preimage, cayley_cayleyInverse hunit.1 hunit.2] using hz
  · rintro ⟨hz, hunit⟩
    have hz' : cayley (cayleyInverse z) = z := cayley_cayleyInverse hunit.1 hunit.2
    refine ⟨?_, hunit⟩
    simpa [Set.mem_preimage, hz'] using hz

/-- The real measure recovered from bounded Cayley data is unique among real measures with the
same Cayley pushforward. -/
lemma realSpectralMeasure_eq_of_cayleyMap_eq
    {μS : WOTSpectralMeasure ℝ H}
    (hμ : WOTSpectralMeasure.cayleyMap μS = D.spectralMeasure) :
    D.realSpectralMeasure = μS := by
  apply WOTSpectralMeasure.cayleyMap_injective
  calc
    WOTSpectralMeasure.cayleyMap D.realSpectralMeasure = D.spectralMeasure :=
      D.cayleyMap_realSpectralMeasure
    _ = WOTSpectralMeasure.cayleyMap μS := hμ.symm

end BoundedUnitarySpectralData
end WOTSpectralMeasure
end QuantumMechanics

end ProbabilisticTheory

end
