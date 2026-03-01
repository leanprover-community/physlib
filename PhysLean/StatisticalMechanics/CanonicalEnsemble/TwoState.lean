/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Finite
import PhysLean.Meta.Informal.Basic
/-!

# Two-state canonical ensemble

This module contains the definitions and properties related to the two-state
canonical ensemble.

-/

namespace CanonicalEnsemble

open Temperature
open Real MeasureTheory

/-- The canonical ensemble corresponding to state system, with one state of energy
  `E₀` and the other state of energy `E₁`. -/
noncomputable def twoState (E₀ E₁ : ℝ) : CanonicalEnsemble (Fin 2) where
  energy := fun | 0 => E₀ | 1 => E₁
  dof := 0
  μ := Measure.count
  energy_measurable := by fun_prop

instance {E₀ E₁} : IsFinite (twoState E₀ E₁) where
  μ_eq_count := rfl
  dof_eq_zero := rfl
  phase_space_unit_eq_one := rfl

lemma twoState_partitionFunction_apply (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).partitionFunction T = exp (- β T * E₀) + exp (- β T * E₁) := by
  rw [partitionFunction_of_fintype, twoState]
  simp [Fin.sum_univ_two]

lemma twoState_partitionFunction_apply_eq_cosh (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).partitionFunction T =
    2 * exp (- β T * (E₀ + E₁) / 2) * cosh (β T * (E₁ - E₀) / 2) := by
  rw [twoState_partitionFunction_apply, Real.cosh_eq]
  field_simp
  simp only [mul_add, ← exp_add]
  ring_nf

@[simp]
lemma twoState_energy_fst (E₀ E₁ : ℝ) : (twoState E₀ E₁).energy 0 = E₀ := by
  rfl

@[simp]
lemma twoState_energy_snd (E₀ E₁ : ℝ) : (twoState E₀ E₁).energy 1 = E₁ := by
  rfl

/-- Probability of the first state (energy `E₀`) in closed form. -/
lemma twoState_probability_fst (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).probability T 0 = 1 / 2 * (1 + Real.tanh (β T * (E₁ - E₀) / 2)) := by
  set x := β T * (E₁ - E₀) / 2
  set C := β T * (E₀ + E₁) / 2
  have hE0 : - β T * E₀ = x - C := by
    simp [x, C]; ring
  have hE1 : - β T * E₁ = -x - C := by
    simp [x, C]; ring
  rw [probability, mathematicalPartitionFunction_of_fintype]
  simp only [twoState, Fin.sum_univ_two, Fin.isValue]
  rw [hE0, hE1]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  simp only [Real.exp_sub, Real.exp_neg]
  field_simp
  ring

/-- Probability of the second state (energy `E₁`) in closed form. -/
lemma twoState_probability_snd (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).probability T 1 = 1 / 2 * (1 - Real.tanh (β T * (E₁ - E₀) / 2)) := by
  set x := β T * (E₁ - E₀) / 2
  set C := β T * (E₀ + E₁) / 2
  have hE0 : - β T * E₀ = x - C := by
    simp [x, C]; ring
  have hE1 : - β T * E₁ = -x - C := by
    simp [x, C]; ring
  rw [probability, mathematicalPartitionFunction_of_fintype]
  simp only [twoState, Fin.sum_univ_two, Fin.isValue]
  rw [hE0, hE1]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  simp only [Real.exp_sub, Real.exp_neg]
  field_simp
  ring

lemma twoState_meanEnergy_eq (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).meanEnergy T =
    (E₀ + E₁) / 2 - (E₁ - E₀) / 2 * Real.tanh (β T * (E₁ - E₀) / 2) := by
  rw [meanEnergy_of_fintype]
  simp [Fin.sum_univ_two, twoState_probability_fst, twoState_probability_snd]
  ring

/-- A simplification of the `entropy` of the two-state canonical ensemble. -/
informal_lemma twoState_entropy_eq where
  tag := "EVJJI"
  deps := [``twoState, ``thermodynamicEntropy]

/-- A simplification of the `helmholtzFreeEnergy` of the two-state canonical ensemble. -/
informal_lemma twoState_helmholtzFreeEnergy_eq where
  tag := "EVMPR"
  deps := [``twoState]

end CanonicalEnsemble
