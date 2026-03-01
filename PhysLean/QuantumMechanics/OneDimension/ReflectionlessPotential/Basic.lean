/-
Copyright (c) 2025 Afiq Hatta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Afiq Hatta
-/
import PhysLean.QuantumMechanics.OneDimension.Operators.Parity
import PhysLean.QuantumMechanics.OneDimension.Operators.Momentum
import PhysLean.QuantumMechanics.OneDimension.Operators.Position
import PhysLean.SpaceAndTime.Time.Basic
import PhysLean.Mathematics.Trigonometry.Tanh
/-!

# 1d Reflectionless Potential

The quantum reflectionless potential in 1d.
This file contains
- the definition of the reflectionless potential as defined https://arxiv.org/pdf/2411.14941
- properties of reflectionless potentials

## TODO
- Define creation and annihilation operators for reflectionless potentials
- Write the proof of the general solution of the reflectionless potential using the creation and
annihilation operators
- Show reflectionless properties
-/

namespace QuantumMechanics
open Real
open Space
open SchwartzMap
open HilbertSpace
open NNReal
open Field
namespace OneDimension

/-- A reflectionless potential is specified by three
  real parameters: the mass of the particle `m`, a value of Planck's constant `ℏ`, the
  parameter `κ`, as well as a positive integer family number `N`.
  All of these parameters are assumed to be positive. --/
structure ReflectionlessPotential where
  /-- mass of the particle -/
  m : ℝ
  /-- parameter of the reflectionless potential -/
  κ : ℝ
  /-- Planck's constant -/
  ℏ : ℝ
  /-- family number, positive integer -/
  N : ℕ
  m_pos : 0 < m -- mass of the particle is positive
  κ_pos : 0 < κ -- parameter of the reflectionless potential is positive
  N_pos : 0 < N -- family number is positive
  ℏ_pos : 0 < ℏ -- Planck's constant is positive

namespace ReflectionlessPotential

variable (Q : ReflectionlessPotential)

/-!
## Theorems
TODO: Add theorems about reflectionless potential - the main result is the actual 1d solution
-/

/-- Define the reflectionless potential as
  V(x) = - (ℏ^2 * κ^2 * N * (N + 1)) / (2 * m * (cosh (κ * x)) ^ 2) --/
noncomputable def reflectionlessPotential (x : ℝ) : ℝ :=
  - (Q.ℏ^2 * Q.κ^2 * Q.N * (Q.N + 1)) / ((2 : ℝ) * Q.m * (Real.cosh (Q.κ * x)) ^ 2)

/-- Define tanh(κ X) operator -/
noncomputable def tanhOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => Real.tanh (Q.κ * x) * ψ x

/-- Pointwise multiplication by a function of temperate growth -/
noncomputable def mulByTemperateGrowth {g : ℝ → ℂ} (hg : g.HasTemperateGrowth) :
    𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hg

-- First, you need a theorem that the scaled tanh has temperate growth
lemma scaled_tanh_hasTemperateGrowth (κ : ℝ) :
    Function.HasTemperateGrowth (fun x => (Real.tanh (κ * x))) := by
  exact tanh_const_mul_hasTemperateGrowth κ

/-- This is a helper lemma to show that the embedding of a real function with temperate growth in ℂ
  also has temperate growth -/
private lemma complex_embedding_of_temperate_growth (f : ℝ → ℝ)
    (h : Function.HasTemperateGrowth f) : Function.HasTemperateGrowth (fun x => (f x : ℂ)) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · apply ContDiff.fun_comp
    apply ContinuousLinearMap.contDiff Complex.ofRealCLM
    apply h1
  · intro n
    obtain ⟨k, C, j⟩ := h2 n
    use k, C
    intro x
    change ‖iteratedFDeriv ℝ n (RCLike.ofRealLI ∘ f) x‖ ≤ C * (1 + ‖x‖) ^ k
    rw [LinearIsometry.norm_iteratedFDeriv_comp_left (g := RCLike.ofRealLI (K := ℂ))
        (hf := h1.contDiffAt)]
    exact j x
    · apply ENat.natCast_le_of_coe_top_le_withTop
      simp only [le_refl]

-- Scaled tanh embedded into the complex numbers has temperate growth
lemma scaled_tanh_complex_hasTemperateGrowth (κ : ℝ) :
    Function.HasTemperateGrowth (fun x => (Real.tanh (κ * x) : ℂ)) := by
  apply complex_embedding_of_temperate_growth
  apply scaled_tanh_hasTemperateGrowth

/-- Define tanh(κ X) multiplication pointwise as a Schwartz map -/
noncomputable def tanhOperatorSchwartz (Q : ReflectionlessPotential) :
    𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  -- We need to handle the Real → Complex coercion
  let scaled_tanh_complex : ℝ → ℂ := fun x => (Real.tanh (Q.κ * x) : ℂ)
  have h2 : Function.HasTemperateGrowth scaled_tanh_complex :=
    scaled_tanh_complex_hasTemperateGrowth Q.κ
  bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) h2

/-- Creation operator: a† as defined in https://arxiv.org/pdf/2411.14941
  a† = 1/√(2m) (P + iℏκ tanh(κX)) -/
noncomputable def creationOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  let factor : ℝ := 1 / Real.sqrt (2 * Q.m)
  fun x => factor * (momentumOperator ψ x + Complex.I * Q.ℏ * Q.κ * Q.tanhOperator ψ x)

/-- Annihilation operator: a as defined in https://arxiv.org/pdf/2411.14941
  a = 1/√(2m) (P - iℏκ tanh(κX)) -/
noncomputable def annihilationOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  let factor : ℝ := 1 / Real.sqrt (2 * Q.m)
  fun x => factor * (momentumOperator ψ x - Complex.I * Q.ℏ * Q.κ * Q.tanhOperator ψ x)

/-- creation operator defined as a Schwartz map -/
noncomputable def creationOperatorSchwartz (Q : ReflectionlessPotential) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
(1 / Real.sqrt (2 * Q.m)) • momentumOperatorSchwartz +
    ((Complex.I * Q.ℏ * Q.κ) / Real.sqrt (2 * Q.m)) • Q.tanhOperatorSchwartz

/-- annihilation operator defined as a Schwartz map -/
noncomputable def annihilationOperatorSchwartz (Q : ReflectionlessPotential) :
  𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
(1 / Real.sqrt (2 * Q.m)) • momentumOperatorSchwartz +
    ((-Complex.I * Q.ℏ * Q.κ) / Real.sqrt (2 * Q.m)) • Q.tanhOperatorSchwartz

end ReflectionlessPotential
end OneDimension
end QuantumMechanics
