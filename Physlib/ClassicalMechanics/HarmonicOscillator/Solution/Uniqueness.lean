/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.Basic

/-!
# Uniqueness

## i. Overview

We show that the trajectories are the unique solutions to the equation of motion
for the given initial conditions.

## ii. Key results

- `trajectories_unique`: The soluition trajectory is unique given a set of initial conditions.

## iii. Table of contents
- A. Uniqueness

## iv. References

* Landau and Lifshitz, Mechanics, Section 32. [ref: landau_mechanics]
-/

@[expose] public

noncomputable section

namespace ClassicalMechanics.HarmonicOscillator

open Time ContDiff

variable (S : HarmonicOscillator)

namespace InitialConditions

/-!
## A. Uniqueness

We show that the trajectories are the unique solutions to the equation of motion
for the given initial conditions.

-/
/-- The trajectories to the equation of motion for a given set of initial conditions
  are unique.

  Given any smooth `x` satisfying the equation of motion with the same initial
  position and velocity, the difference `y = x - IC.trajectory S` also solves the
  equation of motion with zero initial conditions; energy conservation then forces
  its energy, and hence `y`, to vanish identically, so `x = IC.trajectory S`. -/
lemma trajectories_unique (IC : InitialConditions) (x : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) :
    S.EquationOfMotion x ∧ x 0 = IC.x₀ ∧ ∂ₜ x 0 = IC.v₀ →
    x = IC.trajectory S := by
  rintro ⟨hEOM, hx0, hv0⟩
  have hTraj : ContDiff ℝ ∞ (IC.trajectory S) := by fun_prop
  -- Time-derivative of a difference of differentiable functions, used below on `x - traj`.
  have dsub : ∀ f g : Time → EuclideanSpace ℝ (Fin 1),
      Differentiable ℝ f → Differentiable ℝ g →
      ∂ₜ (fun t => f t - g t) = fun t => ∂ₜ f t - ∂ₜ g t := by
    intro f g hf hg
    funext t
    simp only [Time.deriv_eq, fderiv_fun_sub (hf t) (hg t), sub_apply]
  -- The difference `y := x - traj` is smooth, again solves the equation of motion (the force is
  -- linear), and has vanishing initial data; energy conservation then forces `y = 0`.
  set y : Time → EuclideanSpace ℝ (Fin 1) := fun t => x t - IC.trajectory S t with hydef
  have hyContDiff : ContDiff ℝ ∞ y := hx.sub hTraj
  have hy_deriv : ∂ₜ y = fun t => ∂ₜ x t - ∂ₜ (IC.trajectory S) t :=
    dsub x _ (hx.differentiable (by simp)) (hTraj.differentiable (by simp))
  have hy_deriv2 : ∂ₜ (∂ₜ y) = fun t => ∂ₜ (∂ₜ x) t - ∂ₜ (∂ₜ (IC.trajectory S)) t := by
    rw [hy_deriv]
    exact dsub _ _ (deriv_differentiable_of_contDiff _ hx)
      (deriv_differentiable_of_contDiff _ hTraj)
  have hNewt_x := (S.equationOfMotion_iff_newtons_2nd_law x hx).1 hEOM
  have hNewt_traj := (S.equationOfMotion_iff_newtons_2nd_law (IC.trajectory S) hTraj).1
    (trajectory_equationOfMotion S IC)
  have hEOM_y : S.EquationOfMotion y :=
    (S.equationOfMotion_iff_newtons_2nd_law y hyContDiff).2 fun t => by
      rw [hy_deriv2]
      simp [smul_sub, hNewt_x, hNewt_traj, hydef, force_eq_linear]
  have hE : ∀ t, S.energy y t = 0 := fun t =>
    (S.energy_conservation_of_equationOfMotion' y hyContDiff hEOM_y t).trans <| by
      have hy0 : y 0 = 0 := by simp [hydef, hx0]
      have hyv0 : ∂ₜ y 0 = 0 := by
        rw [congrFun hy_deriv 0, hv0, trajectory_velocity_at_zero S IC]; simp
      simp [HarmonicOscillator.energy, HarmonicOscillator.kineticEnergy,
        HarmonicOscillator.potentialEnergy, hy0, hyv0, one_div, smul_eq_mul]
  -- Both energies are nonnegative, so a vanishing total energy forces `y t = 0`.
  funext t
  have hk : 0 ≤ S.kineticEnergy y t := by
    simp only [HarmonicOscillator.kineticEnergy]
    exact mul_nonneg (mul_nonneg (by norm_num) S.m_pos.le) real_inner_self_nonneg
  have hp : 0 ≤ S.potentialEnergy (y t) := by
    simp only [HarmonicOscillator.potentialEnergy, smul_eq_mul]
    exact mul_nonneg (by norm_num) (mul_nonneg S.k_pos.le real_inner_self_nonneg)
  have hpe : S.potentialEnergy (y t) = 0 := ((add_eq_zero_iff_of_nonneg hk hp).mp (hE t)).2
  simp only [HarmonicOscillator.potentialEnergy, smul_eq_mul] at hpe
  rcases mul_eq_zero.mp hpe with h | h
  · norm_num at h
  · have hyt : x t - IC.trajectory S t = 0 :=
      inner_self_eq_zero.mp ((mul_eq_zero.mp h).resolve_left S.k_ne_zero)
    exact sub_eq_zero.mp hyt

end InitialConditions

end ClassicalMechanics.HarmonicOscillator
