/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean
public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.PositiveDual
public import PhyslibAlpha.Mathematics.Order.Freudenthal
public import PhyslibAlpha.Mathematics.Order.PositiveDual.RieszKantorovich
public import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!
# Lattice-ordered observables

## i. Overview

An order-unit lattice is a space of observables in which any two observables have a least upper
bound. Classical observables form such a lattice, with the pointwise maximum. Quantum observables do
not: two self-adjoint matrices usually have no least upper bound.

An order-unit lattice is a vector lattice in which the unit is a strong unit, so the order theory
of vector lattices applies to it: an observable below a sum of two positive observables splits into
two pieces, one below each summand, and every observable is close to a step function.

## ii. Key results

- `OrderUnitLattice E` is an Archimedean order-unit space whose order is a lattice.
- `OrderUnitLattice.map_sup_of_map_inf` : a positive functional preserving minima preserves maxima.

## iii. Table of contents

- A. Order-unit lattices

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. Order-unit lattices

-/

/-- An Archimedean order-unit space whose order is a lattice. -/
class OrderUnitLattice (E : Type*) extends ArchimedeanOrderUnitSpace E, Lattice E

namespace OrderUnitLattice

variable {E : Type*} [OrderUnitLattice E]

/-- A positive functional preserves suprema whenever it preserves infima. -/
lemma map_sup_of_map_inf {ω : E →ₚ[ℝ] ℝ} (h : ∀ f g, ω (f ⊓ g) = min (ω f) (ω g)) (f g : E) :
    ω (f ⊔ g) = max (ω f) (ω g) := by
  have := congrArg ω (inf_add_sup f g)
  rw [map_add, map_add, h] at this
  linarith [min_add_max (ω f) (ω g)]

end OrderUnitLattice

end ProbabilisticTheory
