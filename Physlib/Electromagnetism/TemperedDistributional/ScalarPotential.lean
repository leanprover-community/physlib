/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.TemperedDistributional.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
/-!

# The Scalar Potential

## i. Overview

The electromagnetic potential is given by
`A = (1/c φ, \vec A)`
where `φ` is the scalar potential and `\vec A` is the vector potential.

In this module we define the scalar potential, and prove lemmas about it.

Since `A` is relativistic it is a distribution of `SpaceTime d`, whilst
the scalar potential is non-relativistic and is therefore a distribution of `Time` and `Space d`.

## ii. Key results

- `DistElectromagneticPotential.scalarPotential` : The scalar potential from an
  electromagnetic potential which is a distribution.

## iii. Table of contents

- A. Scalar potential for distributions

## iv. References

* None.
-/

@[expose] public section
namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor

/-!

## A. Scalar potential for distributions

-/

namespace DistElectromagneticPotential
open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-- The scalar potential of an electromagnetic potential which is a distribution. -/
noncomputable def scalarPotential {d} (c : SpeedOfLight) :
    DistElectromagneticPotential d →ₗ[ℝ]
    (Time × Space d) →d[ℝ] ℝ where
  toFun A := Lorentz.Vector.temporalCLM d ∘L distTimeSlice c (c.val • A)
  map_add' A₁ A₂ := by
    ext ε
    simp [distTimeSlice]
  map_smul' r A := by
    ext ε
    simp [distTimeSlice, mul_left_comm]

end DistElectromagneticPotential
end Electromagnetism
