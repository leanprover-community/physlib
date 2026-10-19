/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Cosmology.FLRW.Basic
/-!

# Energy conditions of the cosmic fluid

## i. Overview

The null, weak, strong and dominant energy conditions of a cosmic fluid `F : CosmicFluid`
(`Physlib.Cosmology.FLRW.Basic`), described by its total energy density `F.ρ` and its pressure
`F.p`, at one time `t`, `c` being the speed of light, and the implications between them. They are
used in `Physlib.Cosmology.FLRW.FriedmannSolution` to state the acceleration criterion.

## ii. Key results

- `CosmicFluid.NullEnergyCondition`, `CosmicFluid.WeakEnergyCondition`,
  `CosmicFluid.StrongEnergyCondition`, `CosmicFluid.DominantEnergyCondition`: the four energy
  conditions.
- `CosmicFluid.DominantEnergyCondition.weakEnergyCondition`,
  `CosmicFluid.WeakEnergyCondition.nullEnergyCondition`,
  `CosmicFluid.StrongEnergyCondition.nullEnergyCondition`: the implications between them.

## iii. Table of contents

- A. The energy conditions
- B. Implications between the energy conditions

## iv. References

* None.

-/

@[expose] public section

namespace Cosmology

namespace CosmicFluid

/-!

## A. The energy conditions

-/

variable (F : CosmicFluid) (c : ℝ) (t : Time)

/-- The null energy condition at time `t`, `0 ≤ ρ + p / c²`, for the total energy density `ρ`
  and the pressure `p` of the cosmic fluid, `c` being the speed of light. -/
def NullEnergyCondition : Prop := 0 ≤ F.ρ t + F.p t / c ^ 2

/-- The weak energy condition at time `t`, `0 ≤ ρ ∧ 0 ≤ ρ + p / c²`, for the total energy density
  `ρ` and the pressure `p` of the cosmic fluid, `c` being the speed of light. -/
def WeakEnergyCondition : Prop := 0 ≤ F.ρ t ∧ 0 ≤ F.ρ t + F.p t / c ^ 2

/-- The strong energy condition at time `t`, `0 ≤ ρ + p / c² ∧ 0 ≤ ρ + 3 p / c²`, for the total
  energy density `ρ` and the pressure `p` of the cosmic fluid, `c` being the speed of light. -/
def StrongEnergyCondition : Prop := 0 ≤ F.ρ t + F.p t / c ^ 2 ∧ 0 ≤ F.ρ t + 3 * F.p t / c ^ 2

/-- The dominant energy condition at time `t`, `0 ≤ ρ ∧ |p| ≤ ρ c²`, for the total energy density
  `ρ` and the pressure `p` of the cosmic fluid, `c` being the speed of light. -/
def DominantEnergyCondition : Prop := 0 ≤ F.ρ t ∧ |F.p t| ≤ F.ρ t * c ^ 2

/-!

## B. Implications between the energy conditions

-/

variable {F c t}

/-- For `c ≠ 0`, the dominant energy condition implies the weak energy condition. -/
lemma DominantEnergyCondition.weakEnergyCondition (hc : c ≠ 0)
    (h : F.DominantEnergyCondition c t) : F.WeakEnergyCondition c t := by
  obtain ⟨h0, h1⟩ := h
  have hc2 : 0 < c ^ 2 := by positivity
  have h2 : -(F.ρ t * c ^ 2) ≤ F.p t := (abs_le.mp h1).1
  refine ⟨h0, ?_⟩
  have : -(F.ρ t) ≤ F.p t / c ^ 2 := by
    rw [le_div_iff₀ hc2]
    linarith
  linarith

/-- The weak energy condition implies the null energy condition. -/
lemma WeakEnergyCondition.nullEnergyCondition (h : F.WeakEnergyCondition c t) :
    F.NullEnergyCondition c t :=
  h.2

/-- The strong energy condition implies the null energy condition. -/
lemma StrongEnergyCondition.nullEnergyCondition (h : F.StrongEnergyCondition c t) :
    F.NullEnergyCondition c t :=
  h.1

end CosmicFluid

end Cosmology
