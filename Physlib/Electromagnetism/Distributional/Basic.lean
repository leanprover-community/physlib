/-
Copyright (c) 2026 Cameron Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Lee
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Physlib.SpaceAndTime.TimeAndSpace.ConstantTimeDist
public import Physlib.SpaceAndTime.SpaceTime.TimeSlice


/-!

# The Electromagnetic Potential

## i. Overview

The electromagnetic potential `A^μ` is the fundamental objects in
electromagnetism. Mathematically it is related to a connection
on a `U(1)`-bundle.

We define the electromagnetic potential as a distribution from
spacetime to contravariant Lorentz vectors. The notation "𝓓'(Ω, F)" is used for the
space of `F`-valued distributions on the open set `Ω`. It is also worth noting here that this
definition of distribution is over the reals ℝ.

## ii. Key results

- `DistElectromagneticPotential` : the type of electromagnetic potentials as distributions.

## iii. Table of contents

- A. The electromagnetic potential as a distribution
  - A.1. Equivalence to Distributions

## iv. References

* https://www.dpmms.cam.ac.uk/~cmw50/resources/M3P18/M3P18Ch2.pdf [ref: cambridge_m3p18_ch2]
* L. Schwartz, Théorie des distributions [ref: schwartz1950]
-/

@[expose] public section

namespace Electromagnetism
open Distributions
open Module realLorentzTensor
open TensorSpecies
open Tensor

/-!

## A. The electromagnetic potential as a distribution

-/

/-- The electromagnetic potential as a distribution and as a tensor `A^μ`. -/
structure DistElectromagneticPotential (d : ℕ := 3) where
  /-- The underlying spacetime distribution. -/
  val : 𝓓'(⟨Set.univ (α := SpaceTime d), isOpen_univ⟩, Lorentz.Vector d)

namespace DistElectromagneticPotential

/-!

### A.1. Equivalence to Distributions

-/

/-- The equivalence between an electromagnetic potential and its underlying distribution. -/
def valEquiv {d : ℕ} :
    DistElectromagneticPotential d ≃
      𝓓'(⟨Set.univ (α := SpaceTime d), isOpen_univ⟩, Lorentz.Vector d) where
  toFun := DistElectromagneticPotential.val
  invFun := fun T => ⟨T⟩
  left_inv := by
    rintro ⟨T⟩
    rfl
  right_inv := by
    intro T
    rfl

noncomputable instance {d : ℕ} : AddCommGroup (DistElectromagneticPotential d) :=
  Equiv.addCommGroup valEquiv

noncomputable instance {d : ℕ} : Module ℝ (DistElectromagneticPotential d) :=
  AddEquiv.module ℝ { valEquiv with map_add' _ _ := rfl }

/-- The linear equivalence between an electromagnetic potential and its underlying distribution. -/
noncomputable def valLinearEquiv {d : ℕ} :
    DistElectromagneticPotential d ≃ₗ[ℝ]
      𝓓'(⟨Set.univ (α := SpaceTime d), isOpen_univ⟩, Lorentz.Vector d) :=
  AddEquiv.linearEquiv ℝ { valEquiv with map_add' _ _ := rfl }

end DistElectromagneticPotential
