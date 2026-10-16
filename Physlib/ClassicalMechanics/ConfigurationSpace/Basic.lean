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

- `ConfigurationSpace` : a smooth manifold without boundary.

## iii. Table of contents

- A. Configuration spaces

## iv. References

* V. I. Arnold, Mathematical Methods of Classical Mechanics. [ref: arnold_mechanics]
-/

@[expose] public section

namespace ClassicalMechanics

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]

/-!
## A. Configuration spaces
-/

/-- A smooth manifold without boundary. -/
structure ConfigurationSpace (I : ModelWithCorners ℝ E H) where
  /-- The configurations. -/
  carrier : Type*
  [topologicalSpace : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace H carrier]
  [isManifold : IsManifold I ∞ carrier]
  [boundarylessManifold : BoundarylessManifold I carrier]

variable {I : ModelWithCorners ℝ E H}

instance : CoeSort (ConfigurationSpace I) (Type _) := ⟨ConfigurationSpace.carrier⟩

attribute [instance] ConfigurationSpace.topologicalSpace ConfigurationSpace.chartedSpace
  ConfigurationSpace.isManifold ConfigurationSpace.boundarylessManifold

end ClassicalMechanics
