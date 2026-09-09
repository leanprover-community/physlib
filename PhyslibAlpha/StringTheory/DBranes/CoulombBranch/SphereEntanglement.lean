/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.StringTheory.DBranes.CoulombBranch.Shell
public import PhyslibAlpha.StringTheory.Holography.RyuTakayanagi
/-!
# Spherical entanglement entropy in shell geometries

## i. Overview

This module is built around the area functional for RT surfaces anchored on a ball-shaped
boundary region — bounded by a `(p-1)`-sphere of radius `P` in the gauge theory directions —
in a Coulomb-branch shell geometry, `DBrane.CoulombBranch.sphereAreaFunctional`; its other
declarations are properties of the extremal surfaces of this functional.

Unlike the strip, the spherical problem has no conserved momentum and is not integrable: the
extremal surfaces satisfy a nonlinear second-order differential equation for a curve
`(r(σ), ρ(σ))` relating the bulk radial coordinate to the boundary radius. Surfaces are
classified by how they close off — in the throat, inside the flat bubble, along an exact cone
through the origin, or through the degenerate transverse sphere at `r = 0` at finite boundary
radius. The cone

`r ∝ (R/r_p)^((7-p)/2) ρ`

is an exact extremal surface of the flat-region functional and governs the asymptotic shape
of surfaces probing the deep interior of the bubble.

For the conformal case `p = 3` the throat is `AdS₅ × S⁵` and small boundary spheres have the
familiar hemispherical RT surfaces of anti-de Sitter space, closing off at `r_a = L²/P`. As
`P` grows the RT surface descends into the flat bubble; in contrast with the strip, this
happens as a smooth crossover rather than a first-order transition, the minimal surface
deforming continuously through the closure classes. The growth of the regulated entropy with
`P` is suppressed once the surface enters the bubble, so the spherical entangling surface
sees the same infrared depletion of degrees of freedom as the strip, without the sharp
transition.

## ii. Key results

- `DBrane.CoulombBranch.sphereAreaFunctional` : the piecewise area functional for spherical
  surfaces in the shell geometry.
- `DBrane.CoulombBranch.SphereClosureClasses` : the four ways candidate surfaces close off.
- `DBrane.CoulombBranch.coneSurface`, `DBrane.CoulombBranch.coneSurface_extremal` : the exact
  cone solution inside the flat bubble.
- `DBrane.CoulombBranch.adsHemisphere_is_rt_surface` : for `p = 3` and small `P`, the RT
  surfaces are the AdS₅ hemispheres.
- `DBrane.CoulombBranch.sphereEntropy_transition_continuous` : the crossover to flat-space
  probing surfaces is continuous.
- `DBrane.CoulombBranch.sphereEntropy_large_radius_expansion` : the perturbative expansion of
  the entropy at large `P`.

## iii. Table of contents

- A. The area functional for spherical surfaces
- B. Closure classes and the cone solution
- C. The conformal case
- D. The crossover to the flat bubble

## iv. References

- E. Jørstad, R. C. Myers and S. Pasterski, *Flat Space Entanglement: A Coulomb Branch
  Perspective*, arXiv:2606.13889, section 3.2 and appendices A, B.

-/

@[expose] public section

namespace DBrane

namespace CoulombBranch

/-!

## A. The area functional for spherical surfaces

-/

/-- The area functional for rotationally invariant surfaces in the shell geometry anchored on
a `(p-1)`-sphere of radius `P` in the gauge theory directions, described by a curve
`(r(σ), ρ(σ))` in the plane of the bulk radial coordinate `r` and the boundary radial
coordinate `ρ`. It is the sum of a throat piece, of the schematic form

`A_throat = Ω_{8-p} Ω_{p-1} r_p^(7-p) ∫ dσ r ρ^(p-1) √(r'² + (r/r_p)^(7-p) ρ'²)`,

and a flat piece for the part of the surface at `r < R`, with the harmonic function frozen at
its shell value. Extremal curves satisfy a nonlinear second-order ODE, matched across the
shell by continuity of the curve and its first derivative. See section 3.2 of
arXiv:2606.13889 for the precise expressions. -/
informal_definition sphereAreaFunctional where
  deps := [``shellMetric, ``Holography.BoundaryRegion]
  tag := "GF3PF"

/-!

## B. Closure classes and the cone solution

-/

/-- The four ways a candidate extremal surface anchored on the `(p-1)`-sphere can close off
in the shell geometry:

- *throat closure*: the boundary sphere shrinks to a point, `ρ = 0`, at a radius `r_a > R` in
  the throat;
- *flat closure*: the boundary sphere shrinks to a point at a radius `0 < r_b < R` inside the
  bubble;
- *cone*: the surface approaches the origin `r = 0` and `ρ = 0` simultaneously along the
  cone of `DBrane.CoulombBranch.coneSurface`;
- *interior extension*: the surface reaches `r = 0` at a nonzero boundary radius `ρ_0 > 0`,
  closing through the degenerate transverse sphere.

The boundary conditions appropriate to each class, needed for the numerical integration of
the extremal surface ODE, are detailed in appendix A of arXiv:2606.13889. -/
informal_definition SphereClosureClasses where
  deps := [``sphereAreaFunctional]
  tag := "GF3PH"

/-- The cone surface inside the flat bubble: the surface on which the bulk radial coordinate
is proportional to the boundary radial coordinate,

`r = √((8-p)/(p-1)) (R/r_p)^((7-p)/2) ρ`,

passing through the origin `r = 0`, `ρ = 0` of the flat region. See section 3.2 of
arXiv:2606.13889. -/
informal_definition coneSurface where
  deps := [``sphereAreaFunctional, ``shellMetric_interior_flat]
  tag := "GF3PJ"

/-- The cone surface `DBrane.CoulombBranch.coneSurface` is an exact extremal surface of the
flat-region area functional: the powers of `r` and `ρ` in the area element balance precisely
on the cone, so the nonlinear extremal surface equation is solved exactly. It plays the role
for the sphere that the flat-sheeted surfaces play for the strip, governing the asymptotic
shape of surfaces which probe the deep interior of the bubble. -/
informal_lemma coneSurface_extremal where
  deps := [``coneSurface]
  tag := "GF3PL"

/-!

## C. The conformal case

-/

/-- For `p = 3`, where the throat is AdS₅ × S⁵ with AdS radius `L = r_3`, the extremal
surfaces anchored on a sphere of radius `P` which close in the throat are the hemispheres

`ρ(r) = √(P² - L⁴/r²)`,

closing off at `r_a = L²/P`. These are the RT surfaces of the shell state whenever
`r_a > R`, i.e. for boundary spheres of radius `P < L²/R`, and the entanglement entropy then
agrees with the AdS₅ vacuum result. -/
informal_lemma adsHemisphere_is_rt_surface where
  deps := [``sphereAreaFunctional, ``SphereClosureClasses]
  tag := "GF3PN"

/-!

## D. The crossover to the flat bubble

-/

/-- As the boundary sphere radius `P` increases, the RT surface of the shell geometry deforms
continuously from throat-closing surfaces to surfaces probing the flat bubble: in contrast
with the strip, there is no first-order exchange of dominance between disconnected families,
the minimal surface instead passing smoothly through the closure classes of
`DBrane.CoulombBranch.SphereClosureClasses`. The growth of the regulated entanglement entropy
with `P` is suppressed once the surface enters the bubble, in qualitative agreement with the
strip result `DBrane.CoulombBranch.stripEntropy_saturates`. See section 3.2 of
arXiv:2606.13889, where this is established analytically for `p = 3` and numerically for
`p = 2`. -/
informal_lemma sphereEntropy_transition_continuous where
  deps := [``SphereClosureClasses, ``adsHemisphere_is_rt_surface]
  tag := "GF3PP"

/-- For boundary spheres of large radius `P`, the entanglement entropy of the shell state
admits a perturbative expansion around the limiting surface built from the cone
`DBrane.CoulombBranch.coneSurface`, with corrections suppressed by inverse powers of `P`. The
expansion confirms the suppression of the `P`-dependence of the regulated entropy found
numerically. See appendix B of arXiv:2606.13889, where it is carried out for the `S²`
entangling surface at `p = 3` and the `S¹` entangling surface at `p = 2`. -/
informal_lemma sphereEntropy_large_radius_expansion where
  deps := [``coneSurface_extremal, ``sphereEntropy_transition_continuous]
  tag := "GF3PQ"

end CoulombBranch

end DBrane

end
