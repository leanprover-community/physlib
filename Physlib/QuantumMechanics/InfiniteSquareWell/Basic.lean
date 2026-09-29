/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Meta.Informal.Basic
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.Basic
/-!

# The infinite square well

## i. Overview

The particle in an infinite square well is one of the simplest quantum systems.
The domain is an axis-aligned cuboid (the well) and energy eigenstates are (products of)
trigonometric functions satisfying appropriate boundary conditions.

## ii. Key results

## iii. Table of contents

- A. Basic properties
- B. Domain
- C. Hilbert space
- D. Hamiltonian
- E. As a quantum system

## iv. References

* None.
-/

@[expose] public section

noncomputable section
namespace QuantumMechanics

open Set MeasureTheory

/-- A spinless quantum particle with mass `m > 0` confined to a cuboid in `Space d`.

  The bounds of the well are specified by two functions `lower upper : Fin d → ℝ`
  satisfying `∀ i, lower i < upper i`. -/
structure InfiniteSquareWell (d : ℕ) where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The lower bounds of the well. -/
  lower : Fin d → ℝ
  /-- The upper bounds of the well. -/
  upper : Fin d → ℝ
  /-- The well is a non-empty set. -/
  h_bounds : ∀ i, lower i < upper i

variable {d : ℕ} (Q : InfiniteSquareWell d)

namespace InfiniteSquareWell

/-!
## A. Basic properties
-/

@[simp]
lemma m_pos : 0 < Q.m := Q.hm

@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le

@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'

/-!
## B. Domain
-/

/-- The domain of the infinite square well as a Cartesian product of closed intervals. -/
def well : Set (Space d) := Space.val ⁻¹' Icc Q.lower Q.upper

/-!
## C. Hilbert space
-/

/-- The measure associated with the domain of the infinite square well. -/
def measure : Measure (Space d) := volume.restrict Q.well

/-- The Hilbert space for the infinite square well. -/
abbrev HS : Type _ := SpaceDHilbertSpace d Q.measure

/-!
## D. Hamiltonian
-/

/-- The Hamiltonian for the infinite square well is `(2m)⁻¹momentumSqOperator` with respect
  to `InfiniteSquareWell.measure`. This requires first generalizing `momentumSqOperator`
  to `Space d` measures other than `volume`. -/
informal_definition hamiltonian where
  deps := [``InfiniteSquareWell]
  tag := "QM-ISW-ham"

/-- The Hamiltonian for the infinite square well is essentially self-adjoint. -/
informal_lemma hamiltonian_essentially_self_adjoint where
  deps := [``InfiniteSquareWell]
  tag := "QM-ISW-hamESA"

/-!
## E. As a quantum system
-/

/-- The particle in an infinite square well as a quantum system
  (self-adjoint Hamiltonian acting on a Hilbert space). -/
informal_definition toQuantumSystem where
  deps := [``InfiniteSquareWell]
  tag := "QM-ISW-sys"

end InfiniteSquareWell
end QuantumMechanics
end
