/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.Candidate
public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.Planar

/-!
# Geometry of the Lagrange triangle
The explicit triangle preserves its pairwise distances and oriented area.

## i. Overview

The three explicit initial vertices have equal distances. Translation to the mass
barycentre followed by rotation preserves the distances and oriented area.

## ii. Key results

- `trajectory_equidistant` gives the main result of this module.

## iii. Table of contents

- A. Distances and oriented area

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
namespace ClassicalMechanics.LagrangeThreeBody

/-!
## A. Distances and oriented area
-/

lemma sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := by
  exact Real.sq_sqrt (by norm_num)

lemma rawTriangle_normSq_sub (ℓ : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    Complex.normSq (rawTriangle ℓ i - rawTriangle ℓ j) = ℓ ^ 2 := by
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals
    norm_num [rawTriangle, Complex.normSq_apply, Matrix.cons_val_succ]
    all_goals ring_nf
    all_goals norm_num [sqrt_three_sq]
    all_goals ring

lemma rawTriangle_equidistant (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Equidistant (rawTriangle ℓ) ℓ := by
  intro i j hij
  have hsq := rawTriangle_normSq_sub ℓ i j hij
  rw [Complex.normSq_eq_norm_sq] at hsq
  have hn := norm_nonneg (rawTriangle ℓ i - rawTriangle ℓ j)
  nlinarith

lemma initialConfig_equidistant (p : Parameters) :
    Equidistant (initialConfig p) p.side := by
  intro i j hij
  change ‖centeredPositions p.mass (rawTriangle p.side) i -
    centeredPositions p.mass (rawTriangle p.side) j‖ = p.side
  rw [centeredPositions_sub]
  exact rawTriangle_equidistant p.side p.side_pos i j hij

lemma initialConfig_injective (p : Parameters) : Function.Injective (initialConfig p) := by
  exact equidistant_injective (initialConfig p) p.side
    (initialConfig_equidistant p) p.side_pos

lemma trajectory_eq_rotate (p : Parameters) (t : ℝ) (i : Fin 3) :
    trajectory p t i = rotate (angularSpeed p * t) (initialConfig p i) := rfl

lemma velocity_eq_rotateVelocity (p : Parameters) (t : ℝ) (i : Fin 3) :
    velocity p t i =
      rotateVelocity (angularSpeed p) (angularSpeed p * t) (initialConfig p i) := by
  exact coordinateVelocity_eq_tangent (angularSpeed p) t (initialConfig p i)

lemma velocity_eq_tangent (p : Parameters) (t : ℝ) (i : Fin 3) :
    velocity p t i = tangent (angularSpeed p) (trajectory p t i) := by
  rw [velocity_eq_rotateVelocity, trajectory_eq_rotate]
  rfl

@[simp] lemma trajectory_zero (p : Parameters) (i : Fin 3) :
    trajectory p 0 i = initialConfig p i := by
  rw [trajectory_eq_rotate]
  simp

lemma velocity_zero (p : Parameters) (i : Fin 3) :
    velocity p 0 i = tangent (angularSpeed p) (initialConfig p i) := by
  rw [velocity_eq_tangent, trajectory_zero]

lemma trajectory_equidistant (p : Parameters) (t : ℝ) :
    Equidistant (trajectory p t) p.side := by
  intro i j hij
  rw [trajectory_eq_rotate, trajectory_eq_rotate, rotate_pair_distance]
  exact initialConfig_equidistant p i j hij

lemma trajectory_firstMoment (p : Parameters) (t : ℝ) :
    firstMoment p.mass (trajectory p t) = 0 := by
  change firstMoment p.mass
    (fun i => rotate (angularSpeed p * t) (initialConfig p i)) = 0
  rw [firstMoment_rotate, initialConfig_firstMoment, rotate_zero_vector]

lemma trajectory_centerOfMass (p : Parameters) (t : ℝ) :
    centerOfMass p.mass (trajectory p t) = 0 := by
  rw [centerOfMass, trajectory_firstMoment, smul_zero]

lemma trajectory_noCollision (p : Parameters) (t : ℝ) :
    Function.Injective (trajectory p t) := by
  exact equidistant_injective (trajectory p t) p.side
    (trajectory_equidistant p t) p.side_pos

lemma trajectory_denominator_pos (p : Parameters) (t : ℝ)
    (i j : Fin 3) (hji : j ≠ i) : 0 < ‖trajectory p t j - trajectory p t i‖ ^ 3 := by
  exact denominator_pos (trajectory p t) p.side (trajectory_equidistant p t)
    p.side_pos i j hji

lemma trajectory_radius (p : Parameters) (t : ℝ) (i : Fin 3) :
    ‖trajectory p t i‖ = ‖initialConfig p i‖ := by
  rw [trajectory_eq_rotate, norm_rotate]

lemma initialConfig_doubleArea (p : Parameters) :
    cross (initialConfig p 1 - initialConfig p 0)
      (initialConfig p 2 - initialConfig p 0) = Real.sqrt 3 * p.side ^ 2 / 2 := by
  simp only [initialConfig, centeredPositions_sub]
  change cross ((p.side : ℂ) - 0) ((⟨p.side / 2, Real.sqrt 3 * p.side / 2⟩ : ℂ) - 0) =
    Real.sqrt 3 * p.side ^ 2 / 2
  simp [cross]
  ring

lemma trajectory_doubleArea (p : Parameters) (t : ℝ) :
    cross (trajectory p t 1 - trajectory p t 0)
      (trajectory p t 2 - trajectory p t 0) = Real.sqrt 3 * p.side ^ 2 / 2 := by
  simp only [trajectory_eq_rotate, ← rotate_sub]
  rw [cross_rotate, initialConfig_doubleArea]

end ClassicalMechanics.LagrangeThreeBody
