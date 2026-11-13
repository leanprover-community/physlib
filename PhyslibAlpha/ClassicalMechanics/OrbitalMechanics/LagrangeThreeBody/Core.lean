/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Equidistant gravitational configurations
The algebraic force reduction used by the Lagrange triangular circular solution.

## i. Overview
Work in a real normed space and explicitly exclude each particle's self-force.
The central-force identity is conditional on equal pair distances and zero first
mass moment. The explicit orbit supplies both geometric properties in the subsequent modules.

## ii. Key results
* `weightedDisplacements_eq`: the mass-weighted displacement identity
* `firstMoment_centered`: translation to the mass centre
* `gravityAcceleration_eq_of_equidistant`: reduction to one common denominator
* `gravityAcceleration_eq_of_centered`: the centred gravitational acceleration
* `equidistant_injective`: positive equal distances exclude collisions

## iii. Table of contents
- A. Definitions
- B. Centre-of-mass algebra
- C. Gravitational acceleration
- D. Positivity and collision exclusion

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
open scoped BigOperators

namespace ClassicalMechanics.LagrangeThreeBody

variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-!
## A. Definitions
-/

/-- Total mass of a finite collection of particles. -/
def totalMass (m : ι → ℝ) : ℝ := ∑ i, m i

/-- First mass moment about the chosen coordinate origin. -/
def firstMoment (m : ι → ℝ) (q : ι → V) : V := ∑ i, m i • q i

/-- Centre of mass; physical uses below require nonzero total mass. -/
def centerOfMass (m : ι → ℝ) (q : ι → V) : V :=
  (totalMass m)⁻¹ • firstMoment m q

/-- Positions translated by the mass centre, not the geometric centroid. -/
def centeredPositions (m : ι → ℝ) (q : ι → V) (i : ι) : V :=
  q i - centerOfMass m q

/-- All distinct labelled particles are separated by the same distance. -/
def Equidistant (q : ι → V) (ℓ : ℝ) : Prop :=
  ∀ i j, i ≠ j → ‖q i - q j‖ = ℓ

/-- Newtonian gravitational acceleration, with the self-interaction omitted.
It is algebraically defined everywhere; its physical use requires no collisions.
The scalar inverse-cube factor times displacement is the inverse-square law. -/
def gravityAcceleration [DecidableEq ι] (G : ℝ) (m : ι → ℝ)
    (q : ι → V) (i : ι) : V :=
  ∑ j, if j = i then 0 else (G * m j / ‖q j - q i‖ ^ 3) • (q j - q i)

/-!
## B. Centre-of-mass algebra
-/

/-- Sum of mass-weighted relative displacements, before imposing centring. -/
lemma weightedDisplacements_eq (m : ι → ℝ) (q : ι → V) (i : ι) :
    (∑ j, m j • (q j - q i)) = firstMoment m q - totalMass m • q i := by
  simp only [firstMoment, totalMass, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul]

/-- Translating by the actual mass centre makes the first mass moment zero. -/
lemma firstMoment_centered (m : ι → ℝ) (q : ι → V)
    (hM : totalMass m ≠ 0) :
    firstMoment m (centeredPositions m q) = 0 := by
  unfold firstMoment centeredPositions
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  change firstMoment m q - totalMass m •
    ((totalMass m)⁻¹ • firstMoment m q) = 0
  rw [smul_smul, mul_inv_cancel₀ hM, one_smul, sub_self]

/-- Moving to the mass-centred frame does not change a pair displacement. -/
lemma centeredPositions_sub (m : ι → ℝ) (q : ι → V) (i j : ι) :
    centeredPositions m q i - centeredPositions m q j = q i - q j := by
  unfold centeredPositions
  abel

/-!
## C. Gravitational acceleration
-/

/-- In an equidistant configuration all non-self denominators agree. -/
lemma gravityAcceleration_eq_of_equidistant [DecidableEq ι]
    (G ℓ : ℝ) (m : ι → ℝ) (q : ι → V) (hshape : Equidistant q ℓ) (i : ι) :
    gravityAcceleration G m q i =
      (G / ℓ ^ 3) • (firstMoment m q - totalMass m • q i) := by
  calc
    gravityAcceleration G m q i =
        ∑ j, (G / ℓ ^ 3) • (m j • (q j - q i)) := by
      unfold gravityAcceleration
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp
      · rw [ite_eq_right hji, hshape j i hji, smul_smul]
        congr 1
        ring
    _ = (G / ℓ ^ 3) • (∑ j, m j • (q j - q i)) := by
      rw [Finset.smul_sum]
    _ = (G / ℓ ^ 3) • (firstMoment m q - totalMass m • q i) := by
      rw [weightedDisplacements_eq]

/-- At zero first mass moment, the force field is a scalar multiple of position.
This is an acceleration identity, not yet a theorem about time-dependent orbits. -/
lemma gravityAcceleration_eq_of_centered [DecidableEq ι]
    (G ℓ : ℝ) (m : ι → ℝ) (q : ι → V)
    (hshape : Equidistant q ℓ) (hcenter : firstMoment m q = 0) (i : ι) :
    gravityAcceleration G m q i = -(G * totalMass m / ℓ ^ 3) • q i := by
  rw [gravityAcceleration_eq_of_equidistant G ℓ m q hshape i, hcenter]
  simp only [zero_sub, smul_neg, smul_smul]
  rw [show G / ℓ ^ 3 * totalMass m = G * totalMass m / ℓ ^ 3 by ring]
  simp only [neg_smul]

/-!
## D. Positivity and collision exclusion
-/

/-- Positive masses give positive total mass for a nonempty particle set. -/
lemma totalMass_pos [Nonempty ι] (m : ι → ℝ) (hm : ∀ i, 0 < m i) :
    0 < totalMass m := by
  exact Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty

omit [Fintype ι] [NormedSpace ℝ V] in
/-- Positive equal pair distances imply that no two labelled bodies coincide. -/
lemma equidistant_injective (q : ι → V) (ℓ : ℝ)
    (hshape : Equidistant q ℓ) (hℓ : 0 < ℓ) : Function.Injective q := by
  intro i j hq
  by_contra hij
  have hdist := hshape i j hij
  have hzero : ℓ = 0 := by simpa [hq] using hdist.symm
  exact (ne_of_gt hℓ) hzero

omit [Fintype ι] [NormedSpace ℝ V] in
/-- Every included gravitational denominator is strictly positive. -/
lemma denominator_pos (q : ι → V) (ℓ : ℝ)
    (hshape : Equidistant q ℓ) (hℓ : 0 < ℓ) (i j : ι) (hji : j ≠ i) :
    0 < ‖q j - q i‖ ^ 3 := by
  rw [hshape j i hji]
  exact pow_pos hℓ 3

end ClassicalMechanics.LagrangeThreeBody
