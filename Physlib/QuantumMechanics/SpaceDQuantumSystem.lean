/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.Operators.Multiplication
/-!

# Single-particle quantum system on `Space d`

## i. Overview

In this module we introduce the general notion of a single-particle quantum system on `Space d`.

The structure `SpaceDQuantumSystem` encompasses the basic information needed to specify the system,
namely the number of spatial dimensions, the particle's mass and the potential function.

## ii. Key results

## iii. Table of contents

- A. Basic properties
- B. Operators
  - B.1. Kinetic energy
  - B.2. Potential energy
  - B.3. Hamiltonian
- C. Reflectionless systems in one dimension

## iv. References

* None.
-/

@[expose] public section

namespace QuantumMechanics

open Complex
open MeasureTheory
open SpaceDHilbertSpace

/-- A single-particle quantum system with Hilbert space `SpaceDHilbertSpace d`,
  characterized by the particle's mass `m > 0` and potential function `potential : Space d → ℝ`. -/
@[ext]
structure SpaceDQuantumSystem (d : ℕ) where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The potential function. -/
  potential : Space d → ℝ

variable {d : ℕ} {Q : SpaceDQuantumSystem d}

namespace SpaceDQuantumSystem
noncomputable section

/-- The Hilbert space, `SpaceDHilbertSpace d`. -/
abbrev HS (_ : SpaceDQuantumSystem d) := SpaceDHilbertSpace d

/-!
## A. Basic properties
-/

@[simp]
lemma m_pos : 0 < Q.m := Q.hm

@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le

@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'

/-!
## B. Operators
-/

section
open SchwartzMap
open LinearPMap

/-!
### B.1. Kinetic energy
-/

/-- The kinetic operator `(2m)⁻¹𝐩²` as a continuous linear map on Schwartz space. -/
def kineticCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := (2 * Q.m)⁻¹ • (𝐩 ⬝ᵥ 𝐩)

lemma kineticCLM_eq : Q.kineticCLM = (2 * Q.m)⁻¹ • (𝐩 ⬝ᵥ 𝐩) := rfl

/-- The kinetic operator as an unbounded operator with domain `schwartzSubmodule Q.d`. -/
def kineticOperator : Q.HS →ₗ.[ℂ] Q.HS := ofReal (2 * Q.m)⁻¹ • momentumSqOperator

lemma kineticOperator_eq : Q.kineticOperator = ofReal (2 * Q.m)⁻¹ • momentumSqOperator := rfl

/-!
### B.2. Potential energy
-/

/-- The potential operator as a continuous linear map on Schwartz space,
  where `Q.potential` is a function of temperate growth. -/
def potentialCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := smulLeftCLM ℂ (ofReal ∘ Q.potential)

lemma potentialCLM_eq : Q.potentialCLM = smulLeftCLM ℂ (ofReal ∘ Q.potential) := rfl

lemma potentialCLM_apply (h_HTG : Q.potential.HasTemperateGrowth) (ψ : 𝓢(Space d, ℂ)) :
    Q.potentialCLM ψ = fun x ↦ Q.potential x • ψ x := by
  rw [potentialCLM_eq, smulLeftCLM_apply (by fun_prop)]
  simp

@[simp]
lemma potentialCLM_apply_apply
    (h_HTG : Q.potential.HasTemperateGrowth) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    Q.potentialCLM ψ x = Q.potential x • ψ x := by
  rw [potentialCLM_apply h_HTG]

/-- The potential operator as a self-adjoint, unbounded multiplication operator
  with domain `{ψ ∈ Q.HS | Q.potential • ψ ∈ Q.HS}`. -/
def potentialOperator : Q.HS →ₗ.[ℂ] Q.HS := 𝓜 volume (ofReal ∘ Q.potential)

lemma potentialOperator_eq : Q.potentialOperator = 𝓜 volume (ofReal ∘ Q.potential) := rfl

lemma potentialOperator_isSelfAdjoint (h_AESM : AEStronglyMeasurable Q.potential) :
    IsSelfAdjoint Q.potentialOperator :=
  mulOperator_isSelfAdjoint_ofReal (by fun_prop) (by ext; simp)

lemma potentialOperator_domain_ge (h_HTG : Q.potential.HasTemperateGrowth) :
    SchwartzSubmodule d ≤ Q.potentialOperator.domain :=
  mulOperator_domain_ge_of_hasTemperateGrowth (by fun_prop) volume

/-!
### B.3. Hamiltonian
-/

/-- The Hamiltonian operator as a continuous linear map on Schwartz space,
  where `Q.potential` is a function of temperate growth. -/
def hamiltonianCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := Q.kineticCLM + Q.potentialCLM

lemma hamiltonianCLM_eq : Q.hamiltonianCLM = Q.kineticCLM + Q.potentialCLM := rfl

/-- The Hamilontian operator as a symmetric unbounded operator. -/
def hamiltonianOperator : Q.HS →ₗ.[ℂ] Q.HS := Q.kineticOperator + Q.potentialOperator

lemma hamiltonianOperator_eq : Q.hamiltonianOperator = Q.kineticOperator + Q.potentialOperator :=
  rfl

end

/-!
## C. Reflectionless systems in one dimension
-/

open Constants Filter Topology SchwartzMap
open scoped ComplexConjugate

/-- A system in one dimension is reflectionless if for every wavenumber `k ≠ 0` there is a
  continuous wavefunction `ψ` which solves the time-independent Schrödinger equation at energy
  `ℏ² k² / (2 m)` against all Schwartz maps, `∫ ψ̄ (H φ) = E ∫ ψ̄ φ`, and which tends to non-zero
  multiples of the plane wave `e^{i k x}` both as `x → ∞` and as `x → -∞`. No reflected wave
  `e^{-i k x}` appears. -/
def IsReflectionless (Q : SpaceDQuantumSystem 1) : Prop :=
  ∀ k : ℝ, k ≠ 0 → ∃ ψ : ℝ → ℂ, Continuous ψ ∧
    (∀ φ : 𝓢(Space 1, ℂ), ∫ x, conj (ψ (x 0)) * Q.hamiltonianCLM φ x =
      ((ℏ ^ 2 * k ^ 2 / (2 * Q.m) : ℝ) : ℂ) * ∫ x, conj (ψ (x 0)) * φ x) ∧
    ∃ T T' : ℂ, T ≠ 0 ∧ T' ≠ 0 ∧
      Tendsto (fun x => ψ x - T * exp (k * x * I)) atTop (𝓝 0) ∧
      Tendsto (fun x => ψ x - T' * exp (k * x * I)) atBot (𝓝 0)

end
end SpaceDQuantumSystem
end QuantumMechanics
