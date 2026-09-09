/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.StringTheory.DBranes.CoulombBranch.Shell
public import PhyslibAlpha.StringTheory.Holography.Complexity
/-!
# Holographic complexity of shell geometries

## i. Overview

This module is built around the complexity-equals-volume complexity of a Coulomb-branch shell
state, `DBrane.CoulombBranch.shellComplexityVolume`: the shell geometry is static, so the
maximal bulk slice of the CV proposal is the constant-time slice, and the complexity is its
regulated volume. The volume splits into a throat contribution from `R < r < r_uv`, identical
to the throat vacuum, and a flat-bubble contribution from `r < R`.

The bubble contributes less volume than the throat region it replaces, so the complexity of
the Coulomb-branch state is reduced relative to the throat vacuum at the same cutoff, with a
deficit growing with the shell radius. Complexity thus shows the same infrared depletion as
the entanglement entropy of the shell state: by every holographic measure of degrees of
freedom considered here, the flat-space bubble is poorer than the throat it replaces.

## ii. Key results

- `DBrane.CoulombBranch.shellComplexityVolume` : the CV complexity of the shell state.
- `DBrane.CoulombBranch.shellComplexity_suppressed` : the complexity of the shell state is
  reduced relative to the throat vacuum.

## iii. Table of contents

- A. The complexity of the shell state

## iv. References

- E. Jørstad, R. C. Myers and S. Pasterski, *Flat Space Entanglement: A Coulomb Branch
  Perspective*, arXiv:2606.13889, section 5.
- D. Stanford and L. Susskind, *Complexity and Shock Wave Geometries*, arXiv:1406.2678.

-/

@[expose] public section

namespace DBrane

namespace CoulombBranch

/-!

## A. The complexity of the shell state

-/

/-- The complexity-equals-volume complexity of the Coulomb-branch shell state: the volume of
the constant-time slice of the shell geometry inside the cutoff surface `r = r_uv`, computed
with the Einstein-frame metric and divided by `G_N` and the appropriate bulk length scale, as
in `Holography.complexityVolume`. Since the shell geometry is static, the maximal slice is
the constant-time slice, and the volume splits into a throat contribution from `R < r < r_uv`
and a flat-bubble contribution from `r < R`. -/
informal_definition shellComplexityVolume where
  deps := [``shellMetric, ``Holography.complexityVolume]
  tag := "GF3P4"

/-- The holographic complexity of the Coulomb-branch shell state is reduced relative to the
Dp-brane throat vacuum at the same cutoff: the flat-space bubble contributes less volume than
the throat region it replaces, the deficit growing with the shell radius. Holographic
complexity thus exhibits the same qualitative infrared depletion as the entanglement entropy
of the shell state: the flat-space region carries fewer effective degrees of freedom than the
throat. See section 5 of arXiv:2606.13889. -/
informal_lemma shellComplexity_suppressed where
  deps := [``shellComplexityVolume]
  tag := "GF3P6"

end CoulombBranch

end DBrane

end
