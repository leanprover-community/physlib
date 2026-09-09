/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.StringTheory.DBranes.CoulombBranch.Shell
/-!
# Target space entanglement in shell geometries

## i. Overview

Entanglement in a gauge theory need not be between spatial regions. In a theory of matrices —
such as the maximally supersymmetric Yang-Mills theories dual to Dp-branes — one can instead
partition the *target space*: the moduli space in which the eigenvalues of the adjoint
scalars live. The entanglement between eigenvalues lying in different regions of target space
is called target space entanglement, and for a Coulomb-branch vacuum, whose eigenvalues are
distributed on a sphere in moduli space, it is a natural measure of correlations among the
constituent branes.

This module is built around the definition of *internal RT surfaces* in a Coulomb-branch
shell geometry, `DBrane.CoulombBranch.InternalRTSurface`: extremal surfaces anchored on the
brane shell itself rather than on the asymptotic boundary, lying entirely inside the
flat-space bubble. Their areas, in units of `4 G_N`, are proposed to compute the target space
entanglement of regions of the shell, mirroring how ordinary RT surfaces compute spatial
entanglement. The remaining declarations are properties of these surfaces: their areas grow
monotonically with the depth to which they penetrate the bubble, and for `p ≠ 3` the
adjustable shell radius controls the competition between internal surfaces and surfaces
exiting into the throat, exhibiting in target space the same infrared entanglement depletion
that the strip and sphere calculations exhibit in position space.

## ii. Key results

- `DBrane.CoulombBranch.InternalRTSurface` : extremal surfaces anchored on the shell.
- `DBrane.CoulombBranch.targetSpaceEntanglementEntropy` : the proposed target space
  entanglement entropy computed by internal surfaces.
- `DBrane.CoulombBranch.internalRTSurface_area_monotone` : monotonicity of the internal
  surface area in its turning radius.
- `DBrane.CoulombBranch.internalRTSurface_dominance` : for `p ≠ 3` the shell radius controls
  which internal surfaces dominate.

## iii. Table of contents

- A. Internal RT surfaces
- B. Target space entanglement
- C. Monotonicity and dominance

## iv. References

- E. A. Mazenc and D. Ranard, *Target Space Entanglement Entropy*, arXiv:1910.07449.
- E. Jørstad, R. C. Myers and S. Pasterski, *Flat Space Entanglement: A Coulomb Branch
  Perspective*, arXiv:2606.13889, section 4 and appendices C, D.

-/

@[expose] public section

namespace DBrane

namespace CoulombBranch

/-!

## A. Internal RT surfaces

-/

/-- An internal RT surface of the shell geometry: an extremal surface anchored on the shell
`r = R` (rather than on the asymptotic boundary), lying entirely inside the flat-space
bubble `r ≤ R`, and homologous to a region of the shell. Such a surface is characterized by
the region of the shell on which it is anchored and by its turning radius inside the bubble.
The asymptotic behavior of these surfaces can be understood by recasting the extremal
surface equation as the motion of a classical particle in a potential, as in appendix D of
arXiv:2606.13889. -/
informal_definition InternalRTSurface where
  deps := [``shellMetric, ``shellMetric_interior_flat]
  tag := "GF3PS"

/-!

## B. Target space entanglement

-/

/-- The target space entanglement entropy of the Coulomb-branch state associated with a
region of the shell: the area of the corresponding internal RT surface divided by `4 G_N`.
This computes the entanglement between subsets of the matrix (moduli space) degrees of
freedom of the dual gauge theory, the shell being the locus of the scalar field expectation
values of `DBrane.CoulombBranch.CoulombBranchVacuum`. See section 4 of arXiv:2606.13889 and
the target space entanglement proposal of arXiv:1910.07449. -/
informal_definition targetSpaceEntanglementEntropy where
  deps := [``InternalRTSurface, ``CoulombBranchVacuum]
  tag := "GF3PU"

/-!

## C. Monotonicity and dominance

-/

/-- The area of an internal RT surface of the shell geometry is a monotonic function of its
turning radius inside the flat bubble: deeper surfaces subtend larger anchoring regions on
the shell with correspondingly larger area. This monotonicity guarantees that the map from
anchoring regions to minimal internal surfaces is well behaved. See appendix C of
arXiv:2606.13889 for the proof. -/
informal_lemma internalRTSurface_area_monotone where
  deps := [``InternalRTSurface]
  tag := "GF3PW"

/-- For `p ≠ 3` the shell radius `R` is an adjustable modulus of the shell geometry, and
tuning it controls the competition between internal RT surfaces and surfaces exiting into
the throat: the target space entanglement of the shell state exhibits the same qualitative
depletion in the flat-space bubble as the spatial entanglement entropy. For `p = 3` the
proper shell size is fixed (`DBrane.CoulombBranch.properShellRadius_p3_fixed`) and no such
tuning is available. See section 4 of arXiv:2606.13889. -/
informal_lemma internalRTSurface_dominance where
  deps := [``InternalRTSurface, ``targetSpaceEntanglementEntropy, ``properShellRadius_p3_fixed]
  tag := "GF3PY"

end CoulombBranch

end DBrane

end
