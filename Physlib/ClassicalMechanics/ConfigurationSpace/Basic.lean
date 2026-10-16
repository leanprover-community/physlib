/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Configuration spaces

Smooth manifolds without boundary.

## i. Overview

The configuration space of a mechanical system is the manifold of its configurations.

## ii. Key results

- `IsConfigurationSpace` : a smooth manifold without boundary; holds for every such manifold.

## iii. Table of contents

- A. Configuration spaces

## iv. References

* V. I. Arnold, Mathematical Methods of Classical Mechanics. [ref: arnold_mechanics]
-/

@[expose] public section

namespace ClassicalMechanics

open scoped ContDiff

/-!
## A. Configuration spaces
-/

/-- A smooth manifold without boundary. -/
class IsConfigurationSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*}
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Prop extends IsManifold I ∞ M, BoundarylessManifold I M

/-- A smooth manifold without boundary is a configuration space. -/
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [BoundarylessManifold I M] : IsConfigurationSpace I M where

end ClassicalMechanics
