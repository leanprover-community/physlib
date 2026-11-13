/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.Existence

/-!
# Nondegeneracy of the Lagrange orbit
The orbit has positive area, positive separation, and a changing labelled configuration.

## i. Overview

At least one body is away from the barycentre, so the antipodal configurations
half a period apart are distinct.

## ii. Key results

- `trajectory_half_period_ne` gives the main result of this module.

## iii. Table of contents

- A. Area, separation, and nonstationarity

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
namespace ClassicalMechanics.LagrangeThreeBody

/-!
## A. Area, separation, and nonstationarity
-/

lemma sqrt_three_pos : 0 < Real.sqrt (3 : ℝ) := by
  exact Real.sqrt_pos.2 (by norm_num)

/-- The triangle has strictly positive oriented double area at every time. -/
lemma trajectory_doubleArea_pos (p : Parameters) (t : ℝ) :
    0 < cross (trajectory p t 1 - trajectory p t 0)
      (trajectory p t 2 - trajectory p t 0) := by
  rw [trajectory_doubleArea]
  exact div_pos (mul_pos sqrt_three_pos (pow_pos p.side_pos 2)) (by norm_num)

lemma trajectory_doubleArea_ne_zero (p : Parameters) (t : ℝ) :
    cross (trajectory p t 1 - trajectory p t 0)
      (trajectory p t 2 - trajectory p t 0) ≠ 0 :=
  ne_of_gt (trajectory_doubleArea_pos p t)

/-- A single positive lower bound works for every distinct pair and every time. -/
lemma trajectory_uniform_separation (p : Parameters) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t i j, i ≠ j →
      δ ≤ ‖trajectory p t i - trajectory p t j‖ := by
  refine ⟨p.side, p.side_pos, ?_⟩
  intro t i j hij
  simpa only [trajectory_equidistant p t i j hij] using (le_refl p.side)

/-- At least one position is nonzero; this follows already from injectivity. -/
lemma trajectory_exists_ne_zero (p : Parameters) (t : ℝ) :
    ∃ i : Fin 3, trajectory p t i ≠ 0 := by
  by_cases h0 : trajectory p t 0 = 0
  · refine ⟨1, ?_⟩
    intro h1
    have heq : trajectory p t 0 = trajectory p t 1 := h0.trans h1.symm
    have hidx : (0 : Fin 3) = 1 := trajectory_noCollision p t heq
    exact (by decide : (0 : Fin 3) ≠ 1) hidx
  · exact ⟨0, h0⟩

/-- Elementary complex-plane fact, avoiding any torsion-group API dependency. -/
lemma complex_eq_zero_of_neg_eq {z : ℂ} (h : -z = z) : z = 0 := by
  apply Complex.ext
  · have hr := congrArg Complex.re h
    simp only [Complex.neg_re] at hr
    simp only [Complex.zero_re]
    linarith
  · have hi := congrArg Complex.im h
    simp only [Complex.neg_im] at hi
    simp only [Complex.zero_im]
    linarith

/-- The labelled configuration genuinely changes; it is not a static witness. -/
lemma trajectory_half_period_ne (p : Parameters) (t : ℝ) :
    trajectory p (t + orbitPeriod p / 2) ≠ trajectory p t := by
  intro h
  obtain ⟨i, hi⟩ := trajectory_exists_ne_zero p t
  have heq : -trajectory p t i = trajectory p t i :=
    (trajectory_antipodal p t i).symm.trans (congrFun h i)
  exact hi (complex_eq_zero_of_neg_eq heq)

/-- No single fixed configuration equals the entire trajectory. -/
lemma trajectory_not_constant (p : Parameters) :
    ¬ ∃ q : Fin 3 → ℂ, ∀ t, trajectory p t = q := by
  rintro ⟨q, hq⟩
  apply trajectory_half_period_ne p 0
  exact (hq (0 + orbitPeriod p / 2)).trans (hq 0).symm

end ClassicalMechanics.LagrangeThreeBody
