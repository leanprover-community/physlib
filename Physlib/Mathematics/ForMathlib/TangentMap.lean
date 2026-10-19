/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Tangent maps of maps agreeing near a point

The tangent map at a point only depends on the germ of the map.

## i. Overview

The tangent-map analogue of `Filter.EventuallyEq.mfderiv_eq`.

## ii. Key results

- `Filter.EventuallyEq.tangentMap_eq`

## iii. Table of contents

- A. Germs

## iv. References

* None.
-/

@[expose] public section

open Topology
open scoped Manifold

/-!
## A. Germs
-/

/-- The tangent map at a point only depends on the germ of the map at that point. -/
lemma Filter.EventuallyEq.tangentMap_eq {E E' H H' M M' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H}
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace M'] [ChartedSpace H' M'] {f g : M → M'} {x : M} (h : f =ᶠ[𝓝 x] g)
    (v : TangentSpace I x) : tangentMap I I' f ⟨x, v⟩ = tangentMap I I' g ⟨x, v⟩ := by
  refine Bundle.TotalSpace.ext h.eq_of_nhds ?_
  simp only [tangentMap]
  rw [h.mfderiv_eq]
  rfl
