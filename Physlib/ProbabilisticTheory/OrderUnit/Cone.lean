/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean

/-!
# Ordered positive cones

## i. Overview

`PosCone P` collects the positive observables of `P`. In quantum mechanics, `P.Observables` is
the real vector space of self-adjoint matrices, whose spectra are real. Its positive cone
consists exactly of those matrices whose spectra are nonnegative.
These elements form a cone: they are closed under addition and scaling by nonnegative reals.

## ii. Key results

- `PosCone` : the cone of positive observables, `PointedCone.positive ℝ P.Observables`. Its
  carrier is exactly `{A | 0 ≤ A}` (`PointedCone.mem_positive`) and it is convex
  (`PointedCone.convex`).
- `PosCone.isClosed` : the positive cone is closed in the order-unit-norm topology of an
  Archimedean order-unit space.

## iii. Table of contents

- A. The positive cone
- B. Topological closedness
- C. The order unit

-/

@[expose] public section

open ProbabilisticTheory

open scoped NNReal

/-!

## A. The positive cone

-/

/-- The positive pointed cone of an ordered real module. -/
abbrev ProbabilisticTheory.PosCone (P : ProbabilisticTheory) : PointedCone ℝ P.Observables :=
  PointedCone.positive ℝ P.Observables

namespace ProbabilisticTheory.PosCone

variable {P : ProbabilisticTheory}

/-- The positive cone carries a nonnegative-real scalar action. -/
instance instModule : Module ℝ≥0 (PosCone P) :=
  inferInstanceAs (Module {c : ℝ // 0 ≤ c} (PointedCone.positive ℝ P.Observables))

/-!

## B. Topological closedness

-/

/-- The positive cone is closed in the topology induced by the order-unit norm. -/
lemma isClosed : IsClosed (PosCone P : Set P.Observables) := isClosed_Ici_zero

/-!

## C. The order unit

-/

@[simp]
lemma coe_nnreal_smul (t : ℝ≥0) (p : PosCone P) :
    ((t • p : PosCone P) : P.Observables) = (t : ℝ) • (p : P.Observables) :=
  rfl

/-- The order unit, regarded as a point of the positive cone. -/
instance instOne : One (PosCone P) := ⟨⟨1, one_nonneg⟩⟩

@[simp]
lemma coe_one : ((1 : PosCone P) : P.Observables) = (1 : P.Observables) := rfl

end ProbabilisticTheory.PosCone
