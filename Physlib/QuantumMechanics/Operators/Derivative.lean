/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.Fourier
public import Physlib.QuantumMechanics.Operators.Multiplication
public import Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint
/-!

# Derivative operators

## i. Overview

Every constant-coefficient differential operator is unitarily equivalent, via the Fourier transform,
to a multiplication operator. In this module we take that as a definition: for a symbol
`f : Space d → ℂ`, a function of the wavenumber `k`, the derivative operator `derivOperator f` is
the conjugate `𝓕⁻¹ ∘ 𝓜 (f ∘ 2π•) ∘ 𝓕` of the multiplication operator by the Fourier unitary,
through `LinearPMap.unitaryConj`.

The explicit factors of `2π` implement the change of variables between mathlib's Fourier
convention and the physics one: mathlib's `𝓕` pairs position with the frequency `ξ` through
`e^(-2πi ⟨x, ξ⟩)`, while physics symbols are written in the wavenumber `k = 2πξ`. Rather than
introduce a rescaled transform, we rescale the symbol once and for all: `derivOperator f`
multiplies `𝓕ψ` at frequency `ξ` by `f (2πξ)`, so `f` itself is always a function of the
wavenumber.

## ii. Key results

- `derivOperator` : the derivative operator with wavenumber symbol `f`, with notation `𝓓 f`.
- `derivOperator_hasDenseDomain` : it is densely defined for a.e.-strongly-measurable `f`.
- `derivOperator_adjoint` : its adjoint is the derivative operator of the conjugate symbol.
- `derivOperator_isSelfAdjoint` : it is self-adjoint for real-valued `f`.
- `schwartzSubmodule_le_derivOperator_domain` : the Schwartz submodule lies in the domain for
    temperate-growth `f`.

## iii. Table of contents

- A. Definitions
- B. Basic properties
  - B.1. Domain
  - B.2. Adjoints

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace
noncomputable section

open MeasureTheory ComplexConjugate
open LinearPMap Real FourierTransform

/-!
## A. Definition
-/

variable {d : ℕ} {f : Space d → ℂ}

/-- The derivative operator with symbol `f : Space d → ℂ`, interpreted as a function of the
wavenumber `k`. -/
def derivOperator (f : Space d → ℂ) : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d :=
  (𝓜 volume (f ∘ fun k ↦ (2 * π) • k)).unitaryConj (fourierUnitary d).symm

@[inherit_doc derivOperator]
notation "𝓓" => derivOperator

/-- The defining equation: `𝓓 f` is the multiplication operator by the rescaled symbol
`f ∘ 2π•`, conjugated through the inverse Fourier unitary. -/
lemma derivOperator_eq (f : Space d → ℂ) :
    𝓓 f = (𝓜 volume (f ∘ fun k ↦ (2 * π) • k)).unitaryConj (fourierUnitary d).symm := rfl

/-- a.e.-strong measurability of symbols is preserved under composition with scalar
multiplication: nonzero scaling is quasi-measure-preserving for the Haar measure, and zero
scaling gives a constant function. -/
lemma aestronglyMeasurable_comp_const_smul {μ : Measure (Space d)} [μ.IsAddHaarMeasure]
    (hf : AEStronglyMeasurable f μ) (c : ℝ) :
    AEStronglyMeasurable (f ∘ fun k ↦ c • k) μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa [Function.comp_def] using aestronglyMeasurable_const
  · exact hf.comp_quasiMeasurePreserving
      ⟨measurable_const_smul _, by
        rw [Measure.map_addHaar_smul μ hc]
        exact Measure.smul_absolutelyContinuous⟩

/-- Membership: `ψ ∈ D(𝓓 f)` iff `𝓕ψ` lies in the domain of multiplication by the
rescaled symbol. -/
lemma mem_derivOperator_domain_iff {ψ : SpaceDHilbertSpace d} :
    ψ ∈ (𝓓 f).domain ↔ 𝓕 ψ ∈ (𝓜 volume (f ∘ fun k ↦ (2 * π) • k)).domain := Iff.rfl

/-- The defining formula: `𝓓 f ψ = 𝓕⁻¹ ((f ∘ 2π•) · 𝓕ψ)`. -/
lemma derivOperator_apply (ψ : (𝓓 f).domain) :
    𝓓 f ψ =
      𝓕⁻ ((𝓜 volume (f ∘ fun k ↦ (2 * π) • k)) ⟨𝓕 ψ.1, mem_derivOperator_domain_iff.mp ψ.2⟩) := rfl

/-!
## B.1. Domain
-/

/-- The derivative operator is densely defined. -/
lemma derivOperator_hasDenseDomain (hf : AEStronglyMeasurable f volume) :
    (𝓓 f).HasDenseDomain :=
  (mulOperator_hasDenseDomain
    (aestronglyMeasurable_comp_const_smul hf (2 * π))).unitaryConj_dense_domain

/-- For a temperate-growth symbol the Schwartz submodule lies in the domain of the derivative
operator. -/
lemma schwartzSubmodule_le_derivOperator_domain (hf : f.HasTemperateGrowth) :
    SchwartzSubmodule d ≤ (𝓓 f).domain :=
  fun _ hψ => mem_derivOperator_domain_iff.mpr
    (mulOperator_domain_ge_of_hasTemperateGrowth (by fun_prop) volume
      (fourierUnitary_map_schwartzSubmodule ▸ Submodule.mem_map_of_mem hψ))

/-!
## B.2. Adjoints
-/

/-- The adjoint of a derivative operator is the derivative operator of the conjugate symbol:
`(𝓓 f)† = 𝓓 (conj ∘ f)`. -/
lemma derivOperator_adjoint (hf : AEStronglyMeasurable f volume) :
    (𝓓 f)† = 𝓓 (conj ∘ f) := by
  simp only [derivOperator_eq, aestronglyMeasurable_comp_const_smul hf, unitaryConj_adjoint,
    mulOperator_adjoint_eq_conj, Function.comp_assoc]

/-- The derivative operator of a real-valued symbol is self-adjoint on its maximal domain. -/
lemma derivOperator_isSelfAdjoint (hf : AEStronglyMeasurable f volume)
    (hf' : conj ∘ f = f) : IsSelfAdjoint (𝓓 f) :=
  LinearPMap.unitaryConj_isSelfAdjoint (fourierUnitary d).symm
    (mulOperator_isSelfAdjoint_ofReal (aestronglyMeasurable_comp_const_smul hf (2 * π))
      (funext fun ξ => congrFun hf' ((2 * π) • ξ)))

end
end SpaceDHilbertSpace
end QuantumMechanics
