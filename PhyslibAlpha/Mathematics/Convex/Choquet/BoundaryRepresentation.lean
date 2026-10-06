/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.MeasureTheory.RegularMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Representations by measures on a boundary

Boundary representations of points by regular probability measures, and simplices.

## i. Overview

A family of real-valued tests observes points of a space `X`. A boundary representation of a
point `x` is a regular probability measure on a boundary space `B` whose averages agree with the
tests at `x`. This formulation contains no physical structure: the tests may later be observables,
the points states, and the boundary points pure states.

A point has a boundary decomposition when at least one such measure exists, and a unique boundary
decomposition when exactly one exists. The tested space is a simplex when every point has a unique
boundary decomposition.

## ii. Key results

- `Choquet.IsBoundaryRepresentation` states that a boundary measure represents a point.
- `Choquet.HasBoundaryDecomposition` states existence of a boundary representation.
- `Choquet.HasUniqueBoundaryDecomposition` states existence and uniqueness.
- `Choquet.IsSimplexRepresentation` states that every point has a unique representation.

## iii. Table of contents

- A. Boundary representations
- B. Simplices

## iv. References

* None.

-/

@[expose] public section

open MeasureTheory

namespace Choquet

variable {A B X : Type*} [MeasurableSpace B] [TopologicalSpace B]

/-! ## A. Boundary representations -/

/-- A regular probability measure on `B` represents `x` when the average of every test over the
boundary agrees with its value at `x`. -/
def IsBoundaryRepresentation (test : A → X → ℝ) (boundary : B → X) (x : X)
    (μ : Measure B) : Prop :=
  μ.Regular ∧ IsProbabilityMeasure μ ∧
    ∀ a, ∫ b, test a (boundary b) ∂μ = test a x

/-- A point has a boundary decomposition when some regular probability measure on the boundary
represents it. -/
def HasBoundaryDecomposition (test : A → X → ℝ) (boundary : B → X) (x : X) : Prop :=
  ∃ μ : Measure B, IsBoundaryRepresentation test boundary x μ

/-- A point has a unique boundary decomposition when exactly one regular probability measure on
the boundary represents it. -/
def HasUniqueBoundaryDecomposition (test : A → X → ℝ) (boundary : B → X)
    (x : X) : Prop :=
  ∃! μ : Measure B, IsBoundaryRepresentation test boundary x μ

/-! ## B. Simplices -/

/-- A tested space is a simplex with boundary `B` when every point has a unique boundary
decomposition. -/
def IsSimplexRepresentation (test : A → X → ℝ) (boundary : B → X) : Prop :=
  ∀ x, HasUniqueBoundaryDecomposition test boundary x

end Choquet
