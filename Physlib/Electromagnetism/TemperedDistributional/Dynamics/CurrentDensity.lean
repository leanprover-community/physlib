/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.TimeSlice
/-!

# The Lorentz Current Density

## i. Overview

In this module we define the Lorentz current density
and its decomposition into charge density and current density.
The Lorentz current density is often called the four-current and given then the symbol `J`.

The current density is given in terms of the charge density `ρ` and the current density
` \vec j` as `J = (c ρ, \vec j)`.

## ii. Key results

- `DistLorentzCurrentDensity` : The type of Lorentz current densities
  as distributions.

## iii. Table of contents

- A. The Lorentz current density as a distribution
  - A.1. The underlying charge density
  - A.2. The underlying current density

## iv. References

* None.
-/

@[expose] public section

namespace Electromagnetism
open TensorSpecies
open SpaceTime
open TensorProduct
open minkowskiMatrix
open InnerProductSpace

attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. The Lorentz current density as a distribution

-/
/-- The Lorentz current density, also called four-current as a distribution. -/
abbrev DistLorentzCurrentDensity (d : ℕ := 3) := (SpaceTime d) →d[ℝ] Lorentz.Vector d

namespace DistLorentzCurrentDensity

/-!

### A.1. The underlying charge density

-/

/-- The charge density underlying a Lorentz current density which is a distribution. -/
noncomputable def chargeDensity {d : ℕ} (c : SpeedOfLight) :
    (DistLorentzCurrentDensity d) →ₗ[ℝ] (Time × Space d) →d[ℝ] ℝ where
  toFun J := (1 / (c : ℝ)) • (Lorentz.Vector.temporalCLM d ∘L distTimeSlice c J)
  map_add' J1 J2 := by
    simp
  map_smul' r J := by
    simp only [one_div, map_smul, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply]
    rw [smul_comm]

/-!

### A.2. The underlying current density

-/

/-- The underlying (non-Lorentz) current density associated with a distributive
  Lorentz current density. -/
noncomputable def currentDensity (c : SpeedOfLight) :
    DistLorentzCurrentDensity d →ₗ[ℝ] (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun J := Lorentz.Vector.spatialCLM d ∘L distTimeSlice c J
  map_add' J1 J2 := by
    simp
  map_smul' r J := by
    simp

end DistLorentzCurrentDensity
end Electromagnetism
