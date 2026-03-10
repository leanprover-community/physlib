/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import PhysLean.SpaceAndTime.SpaceTime.Basic
public import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.LightLike
public import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.TimeLike
/-!
# Proper Time

This file introduces 4d Minkowski spacetime.

-/

@[expose] public section

noncomputable section

namespace SpaceTime

open Manifold
open Matrix
open Real
open ComplexConjugate
open Lorentz
open Vector

/-- The proper time from `q` to `p`. Defaults to zero if `p` and `q`
  have a space-like separation. -/
def properTime {d : ℕ} (q p : SpaceTime d) : ℝ :=
  √⟪p - q, p - q⟫ₘ

lemma properTime_pos_ofTimeLike {d : ℕ} (q p : SpaceTime d)
    (h : causalCharacter (p - q) = .timeLike) :
    0 < properTime q p := by
  rw [properTime]
  refine sqrt_pos_of_pos ?_
  exact (timeLike_iff_norm_sq_pos (p - q)).mp h

lemma properTime_zero_ofLightLike {d : ℕ} (q p : SpaceTime d)
    (h : causalCharacter (p - q) = .lightLike) :
    properTime q p = 0 := by
  rw [properTime]
  rw [lightLike_iff_norm_sq_zero] at h
  simp only [h, sqrt_zero]

lemma properTime_zero_ofSpaceLike {d : ℕ} (q p : SpaceTime d)
    (h : causalCharacter (p - q) = .spaceLike) :
    properTime q p = 0 := by
  rw [properTime]
  rw [spaceLike_iff_norm_sq_neg] at h
  exact sqrt_eq_zero'.mpr (le_of_lt h)

end SpaceTime

end
