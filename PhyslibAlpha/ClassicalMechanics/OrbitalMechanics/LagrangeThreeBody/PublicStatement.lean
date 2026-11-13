/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.Nondegeneracy

/-!
# Lagrange’s circular equilateral solution
Three positive masses admit a nonstationary circular equilateral Newtonian orbit.

## i. Overview

The positions and velocities are defined at every real time. Their derivatives satisfy
the pairwise Newtonian law. The construction also gives a positive period, collision
exclusion, zero first mass moment, and positive oriented area.

## ii. Key results

- `exists_nondegenerate_lagrange_orbit` gives the main result of this module.

## iii. Table of contents

- A. Existence for arbitrary positive masses

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace ClassicalMechanics.LagrangeThreeBody

/-!
## A. Existence for arbitrary positive masses
-/

/-- Exact Newton equation with the complete sum visible in the statement. -/
lemma explicit_newton_equation (p : Parameters) (t : ℝ) (i : Fin 3) :
    deriv (deriv (fun s => trajectory p s i)) t =
      ∑ j : Fin 3, if j = i then 0 else
        (p.G * p.mass j / ‖trajectory p t j - trajectory p t i‖ ^ 3) •
          (trajectory p t j - trajectory p t i) := by
  exact second_deriv_trajectory p t i

/-- Arbitrary positive input data admit a nonstationary, equilateral periodic
Newtonian orbit for all real time. The existence statement includes a positive period. -/
theorem exists_nondegenerate_lagrange_orbit
    (G : ℝ) (m : Fin 3 → ℝ) (ℓ : ℝ)
    (hG : 0 < G) (hm : ∀ i, 0 < m i) (hℓ : 0 < ℓ) :
    ∃ (r v : ℝ → Fin 3 → ℂ) (T : ℝ),
      0 < T ∧
      (∀ t i, HasDerivAt (fun s => r s i) (v t i) t) ∧
      (∀ t i, HasDerivAt (fun s => v s i)
        (∑ j : Fin 3, if j = i then 0 else
          (G * m j / ‖r t j - r t i‖ ^ 3) • (r t j - r t i)) t) ∧
      (∀ t i, deriv (deriv (fun s => r s i)) t =
        ∑ j : Fin 3, if j = i then 0 else
          (G * m j / ‖r t j - r t i‖ ^ 3) • (r t j - r t i)) ∧
      (∀ t i j, i ≠ j → ‖r t i - r t j‖ = ℓ) ∧
      (∀ t, Function.Injective (r t)) ∧
      (∀ t, (∑ i : Fin 3, m i • r t i) = 0) ∧
      (∀ i, Function.Periodic (fun t => r t i) T) ∧
      (∀ i, Function.Periodic (fun t => v t i) T) ∧
      (∀ t, r (t + T / 2) ≠ r t) ∧
      (∀ t, 0 < (r t 1 - r t 0).re * (r t 2 - r t 0).im -
        (r t 1 - r t 0).im * (r t 2 - r t 0).re) ∧
      T ^ 2 * (G * ∑ i : Fin 3, m i) = 4 * Real.pi ^ 2 * ℓ ^ 3 := by
  let p : Parameters := ⟨G, m, ℓ, hG, hm, hℓ⟩
  refine ⟨trajectory p, velocity p, orbitPeriod p, orbitPeriod_pos p, ?_⟩
  refine ⟨hasDerivAt_trajectory p, ?_, ?_, trajectory_equidistant p,
    trajectory_noCollision p, trajectory_firstMoment p,
    trajectory_periodic p, velocity_periodic p, trajectory_half_period_ne p,
    ?_, kepler_period_law p⟩
  · intro t i
    exact hasDerivAt_velocity p t i
  · intro t i
    exact explicit_newton_equation p t i
  · intro t
    exact trajectory_doubleArea_pos p t

end ClassicalMechanics.LagrangeThreeBody
