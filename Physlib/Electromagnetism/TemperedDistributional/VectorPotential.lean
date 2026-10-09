/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.TemperedDistributional.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
/-!

# The vector Potential

## i. Overview

The electromagnetic potential is given by
`A = (1/c φ, \vec A)`
where `φ` is the scalar potential and `\vec A` is the vector potential.

In this module we define the vector potential, and prove lemmas about it.

Since `A` is relativistic it is a distribution of `SpaceTime d`, whilst
the vector potential is non-relativistic and is therefore a distribution of `Time` and `Space d`.

## ii. Key results

- `DistElectromagneticPotential.vectorPotential` : The vector potential from an
  electromagnetic potential which is a distribution.

## iii. Table of contents

- A. Vector potential for distributions

## iv. References

* None.
-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor

/-!

## A. Vector potential for distributions

-/

namespace DistElectromagneticPotential
open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix SchwartzMap
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-- The vector potential of an electromagnetic potential which is a distribution. -/
noncomputable def vectorPotential {d} (c : SpeedOfLight) :
    DistElectromagneticPotential d →ₗ[ℝ]
    (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun A := Lorentz.Vector.spatialCLM d ∘L distTimeSlice c A
  map_add' A₁ A₂ := by
    simp [distTimeSlice]
  map_smul' r A := by
    simp [distTimeSlice]

end DistElectromagneticPotential

end Electromagnetism
