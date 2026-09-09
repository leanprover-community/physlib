/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.StringTheory.DBranes.DecouplingLimit
/-!
# Coulomb-branch shell geometries

## i. Overview

Maximally supersymmetric Yang-Mills theory has a moduli space of vacua — the Coulomb branch —
on which the adjoint scalars acquire expectation values, breaking `U(N)` to `U(1)^N`.
Holographically, moving onto the Coulomb branch corresponds to separating the `N` Dp-branes
in the transverse space. Distributing them uniformly on a sphere of radius `R` produces the
*shell geometry*: by the linearity of the supergravity solution in the brane distribution,
its harmonic function is the electrostatic potential of a uniformly charged spherical shell,

`H(r) = (r_p/r)^(7-p)` for `r ≥ R`, and `H(r) = (r_p/R)^(7-p)` for `r ≤ R`.

Outside the shell the background is exactly the Dp-brane throat; inside, `H` is constant and
the geometry is a bubble of flat ten-dimensional Minkowski space with constant dilaton. The
shell geometry therefore embeds a flat-space region in the infrared of a standard holographic
background, with the ultraviolet dictionary of the throat left untouched. This makes it a
controlled, top-down setting for questions about flat-space holography: any boundary
observable that probes deep enough in the infrared becomes a probe of flat space.

The scales of the geometry are as follows. The proper size of the shell is
`R_shell ∝ r_p^((7-p)(p+1)/16) R^((p-3)²/16)`; for `p ≠ 3` it is adjustable through the
modulus `R`, while for `p = 3` it is frozen at the AdS scale, a reflection of the conformal
invariance of `𝒩 = 4` super Yang-Mills. Entanglement entropy, target space entanglement and
holographic complexity in these backgrounds are developed in the sibling modules
`StripEntanglement`, `SphereEntanglement`, `TargetSpaceEntanglement` and `Complexity`.

## ii. Key results

- `DBrane.CoulombBranch.shellHarmonicFunction` : the piecewise harmonic function of a
  spherical shell of Dp-branes.
- `DBrane.CoulombBranch.shellMetric` : the corresponding shell geometry.
- `DBrane.CoulombBranch.shellMetric_interior_flat` : the interior of the shell is a bubble of
  flat Minkowski space.
- `DBrane.CoulombBranch.shellMetric_solves_supergravity` : the shell geometry solves the
  supergravity equations with a brane source on the shell.
- `DBrane.CoulombBranch.CoulombBranchVacuum` : the dual description as a Coulomb-branch
  vacuum of maximally supersymmetric Yang-Mills theory.
- `DBrane.CoulombBranch.properShellRadius` : the proper size of the shell.
- `DBrane.CoulombBranch.properShellRadius_p3_fixed` : for `p = 3` the proper shell size is
  independent of the shell radius `R`.
- `DBrane.CoulombBranch.uvCutoffOfRadialCutoff` : the map between the bulk radial cutoff and
  the gauge theory UV cutoff.

## iii. Table of contents

- A. The shell geometry
- B. The flat-space bubble
- C. The dual Coulomb-branch vacuum
- D. Scales of the shell geometry

## iv. References

- P. Kraus, F. Larsen and S. P. Trivedi, *The Coulomb branch of gauge theory from rotating
  branes*, arXiv:hep-th/9811120.
- E. Jørstad, R. C. Myers and S. Pasterski, *Flat Space Entanglement: A Coulomb Branch
  Perspective*, arXiv:2606.13889, section 2.2.

-/

@[expose] public section

namespace DBrane

namespace CoulombBranch

/-!

## A. The shell geometry

-/

/-- The harmonic function of `N` Dp-branes distributed uniformly on a sphere of radius `R` in
the transverse space, in the decoupling limit:

`H(r) = (r_p/r)^(7-p)` for `r ≥ R`, and `H(r) = (r_p/R)^(7-p)` for `r ≤ R`.

This is the electrostatic potential of a uniformly charged spherical shell: it agrees with
the throat harmonic function outside the shell and is constant inside. It is continuous but
not differentiable at `r = R`, where the brane source is located. -/
informal_definition shellHarmonicFunction where
  deps := [``DBrane.dpBraneHarmonicFunction, ``DBrane.dpBraneScale]
  tag := "GF3OF"

/-- The shell geometry: the Dp-brane background (Einstein-frame metric, dilaton and
Ramond-Ramond flux) built from the piecewise harmonic function
`DBrane.CoulombBranch.shellHarmonicFunction`. For `r > R` it coincides with the Dp-brane
throat `DBrane.dpBraneThroatMetric`; for `r < R` the harmonic function is constant and the
geometry is flat. -/
informal_definition shellMetric where
  deps := [``shellHarmonicFunction, ``DBrane.dpBraneMetric, ``DBrane.dpBraneDilaton]
  tag := "GF3OH"

/-- The shell geometry solves the equations of motion of type II supergravity everywhere away
from the shell `r = R`, and across the shell the discontinuity in the derivative of the
harmonic function is accounted for by the stress tensor and charge of the `N` Dp-branes
distributed on the shell. In particular the Israel junction conditions at `r = R` are
satisfied by the brane source. -/
informal_lemma shellMetric_solves_supergravity where
  deps := [``shellMetric, ``DBrane.dpBraneMetric_solves_supergravity]
  tag := "GF3OK"

/-!

## B. The flat-space bubble

-/

/-- The interior region `r < R` of the shell geometry is isometric to a region of flat
ten-dimensional Minkowski space, with constant dilaton. The constant value
`H = (r_p/R)^(7-p)` of the harmonic function inside the shell rescales the worldvolume and
transverse coordinates but produces no curvature. The shell geometry thus contains a bubble
of flat space in its infrared region, glued to the Dp-brane throat across the shell. -/
informal_lemma shellMetric_interior_flat where
  deps := [``shellMetric]
  tag := "GF3OI"

/-!

## C. The dual Coulomb-branch vacuum

-/

/-- The state of `(p+1)`-dimensional maximally supersymmetric `U(N)` Yang-Mills theory dual
to the shell geometry: a vacuum on the Coulomb branch in which the expectation values of the
adjoint scalars break `U(N)` to `U(1)^N`, with the `N` eigenvalue vectors distributed
uniformly on a sphere in the `(9-p)`-dimensional moduli space whose radius corresponds to the
shell radius `R` under the holographic dictionary. The W-bosons connecting the branes have
masses set by the shell radius, and the deep infrared physics is that of the surviving
`U(1)^N` degrees of freedom. -/
informal_definition CoulombBranchVacuum where
  deps := [``shellMetric]
  tag := "GF3OM"

/-!

## D. Scales of the shell geometry

-/

/-- The proper size of the shell in the shell geometry: the proper radius of the transverse
sphere `r = R` measured with the Einstein-frame metric,

`R_shell = r_p^((7-p)(p+1)/16) R^((p-3)²/16)`

up to a numerical constant. See section 2.2 of arXiv:2606.13889. -/
informal_definition properShellRadius where
  deps := [``shellMetric]
  tag := "GF3OO"

/-- For `p = 3` the proper shell radius `DBrane.CoulombBranch.properShellRadius` is
independent of the shell radius `R`, being fixed at the AdS scale `r_3`: the exponent
`(p-3)²/16` vanishes. This reflects the conformal invariance of four-dimensional `𝒩 = 4`
super Yang-Mills, for which the modulus `R` is a flat direction changing no proper scale of
the geometry. For `p ≠ 3` the proper shell size is instead a genuinely adjustable modulus,
which controls the competition between extremal surfaces in holographic entanglement
calculations. -/
informal_lemma properShellRadius_p3_fixed where
  deps := [``properShellRadius]
  tag := "GF3OQ"

/-- The relation between the bulk radial cutoff `r = r_uv` of the shell (or throat) geometry
and the short-distance cutoff `δ` of the dual gauge theory: `δ` is the proper length in the
gauge theory directions corresponding to the bulk cutoff surface, scaling as

`δ ∝ (r_p/r_uv)^((5-p)/2) r_p`

so that `r_uv → ∞` corresponds to `δ → 0` for `p < 5`. This map is used to express the UV
divergences of holographic entanglement entropies in gauge theory terms. See section 2.2 of
arXiv:2606.13889. -/
informal_definition uvCutoffOfRadialCutoff where
  deps := [``shellMetric]
  tag := "GF3OS"

end CoulombBranch

end DBrane

end
