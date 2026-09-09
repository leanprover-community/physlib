/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.StringTheory.Holography.RyuTakayanagi
/-!
# Holographic complexity

## i. Overview

Circuit complexity measures how difficult it is to prepare a quantum state from a simple
reference state using elementary unitary operations. Holographic complexity proposals assign
to a state of the boundary theory a bulk geometric quantity conjectured to compute this
complexity; unlike entanglement entropy, which is blind to the interior growth of black
holes, complexity is conjectured to probe bulk regions that RT surfaces cannot reach.

The best studied proposal is *complexity equals volume* (CV):

`C_V = max_Σ Vol(Σ) / (G_N ℓ_bulk)`

where the maximum is over bulk codimension-one slices `Σ` anchored on the boundary time
slice, and `ℓ_bulk` is a bulk length scale. For a static background the maximal slice is the
constant-time slice, and the complexity reduces to the regulated volume of the bulk time
slice — a quantity sensitive to the entire infrared geometry, complementary to the
entanglement entropy computed by minimal surfaces.

The definition in this module is background-independent, in the same spirit as
`Holography.StaticHolographicBackground`.

## ii. Key results

- `Holography.complexityVolume` : the complexity-equals-volume proposal.

## iii. Table of contents

- A. The complexity-equals-volume proposal

## iv. References

- D. Stanford and L. Susskind, *Complexity and Shock Wave Geometries*, arXiv:1406.2678.
- S. Chapman and G. Policastro, *Quantum Computational Complexity — From Quantum Information
  to Black Holes and Back*, arXiv:2110.14672.

-/

@[expose] public section

namespace Holography

/-!

## A. The complexity-equals-volume proposal

-/

/-- The complexity-equals-volume (CV) proposal: the holographic complexity of the boundary
state on a time slice is

`C_V = max_Σ Vol(Σ) / (G_N ℓ_bulk)`

where the maximum is over bulk codimension-one slices `Σ` anchored on the boundary time
slice, the volume is computed with the Einstein-frame metric, and `ℓ_bulk` is a bulk length
scale (for AdS, the AdS radius). For a static background the maximal slice is the
constant-time slice. Like the entanglement entropy, the complexity is UV divergent and is
regulated by evaluating the volume inside the cutoff surface `r = r_uv`. -/
informal_definition complexityVolume where
  deps := [``StaticHolographicBackground]
  tag := "GF3P2"

end Holography

end
