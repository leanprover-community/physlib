/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.StringTheory.DBranes.CoulombBranch.Shell
public import PhyslibAlpha.StringTheory.Holography.EntropicCFunction
/-!
# Strip entanglement entropy in shell geometries

## i. Overview

This module is built around the area functional for strip-shaped RT surfaces in a
Coulomb-branch shell geometry, `DBrane.CoulombBranch.stripAreaFunctional`; its other
declarations are properties of the extremal surfaces of this functional and of the
entanglement entropy they compute.

Because the shell geometry consists of a Dp-brane throat glued to a flat bubble across the
shell `r = R`, the variational problem for a strip of half-width `ℓ` is piecewise: surfaces
extremize the throat area functional outside the shell and the flat-space one inside, and
refract across the shell like light rays at an interface. The extremal surfaces fall into
three classes — throat-confined, flat-bubble, and flat-sheeted — distinguished by how they
close off, and the entanglement entropy is governed by the least-area class at each `ℓ`.

The competition between the classes is resolved by a first-order transition at a critical
width `ℓ_c ∝ (r_p/R)^((7-p)/2) R`, the boundary length scale dual to the shell radius. Narrow
strips, `ℓ < ℓ_c`, have throat-confined RT surfaces and entanglement identical to the throat
vacuum; wide strips, `ℓ > ℓ_c`, have flat-sheeted RT surfaces whose regulated area no longer
depends on `ℓ`. The entropic c-function makes the physics of this saturation sharp: it runs
with the throat vacuum value, of order `N²`, for `ℓ < ℓ_c` and vanishes identically for
`ℓ > ℓ_c`. At scales where the boundary theory probes the flat-space bubble, it has only
`O(1)` degrees of freedom in the large-`N` expansion — the flat infrared region of a
Coulomb-branch vacuum is entanglement-depleted relative to the throat it replaces.

## ii. Key results

- `DBrane.CoulombBranch.stripAreaFunctional` : the piecewise area functional for strip
  surfaces in the shell geometry.
- `DBrane.CoulombBranch.stripRefractionCondition` : the matching of extremal surfaces across
  the shell.
- `DBrane.CoulombBranch.StripSurfaceClasses` : the three classes of candidate extremal
  surfaces.
- `DBrane.CoulombBranch.criticalStripWidth` : the critical half-width `ℓ_c`.
- `DBrane.CoulombBranch.stripEntropy_phase_transition` : the first-order transition at `ℓ_c`.
- `DBrane.CoulombBranch.stripEntropy_saturates` : the regulated entropy is `ℓ`-independent
  for `ℓ > ℓ_c`.
- `DBrane.CoulombBranch.stripEntropy_uv_divergence` : the leading UV divergence is an area
  law matching the throat vacuum.
- `DBrane.CoulombBranch.entropicCFunction_throat_running` : the running of the c-function in
  the throat regime.
- `DBrane.CoulombBranch.entropicCFunction_vanishes_in_bubble` : the c-function vanishes for
  `ℓ > ℓ_c`.

## iii. Table of contents

- A. The area functional for strip surfaces
- B. Candidate extremal surfaces
- C. The entanglement phase transition
- D. UV divergences
- E. The entropic c-function of the shell state

## iv. References

- E. Jørstad, R. C. Myers and S. Pasterski, *Flat Space Entanglement: A Coulomb Branch
  Perspective*, arXiv:2606.13889, section 3.1.
- S. Ryu and T. Takayanagi, *Aspects of Holographic Entanglement Entropy*,
  arXiv:hep-th/0605073.

-/

@[expose] public section

namespace DBrane

namespace CoulombBranch

/-!

## A. The area functional for strip surfaces

-/

/-- The area functional for translationally invariant surfaces in the shell geometry anchored
on a strip `-ℓ ≤ x_1 ≤ ℓ` of the boundary, described by a profile `x_1(r)`. It is the sum of
a throat piece, for the part of the surface at `r > R`, of the schematic form

`A_throat = Ω_{8-p} V_{p-1} r_p^(7-p) ∫ dr r √(1 + (r_p/r)^(7-p) x'(r)²)`

and a flat piece, for the part at `r < R`, in which the harmonic function is frozen at its
value on the shell. Extremizing this functional over profiles with the given boundary
conditions yields the candidate RT surfaces of the strip. See section 3.1 of
arXiv:2606.13889 for the precise expressions. -/
informal_definition stripAreaFunctional where
  deps := [``shellMetric, ``Holography.StripRegion]
  tag := "GF3OU"

/-- An extremal surface of `DBrane.CoulombBranch.stripAreaFunctional` crossing the shell
`r = R` is continuous with continuous first derivative of its profile across the shell, the
conserved momentum conjugate to `x_1` matching between the throat and flat pieces. For the
strip this matching relates the turning points of the two pieces by an explicit power law in
`R`; the surface refracts across the shell like a light ray crossing an interface. See
section 3.1 of arXiv:2606.13889. -/
informal_lemma stripRefractionCondition where
  deps := [``stripAreaFunctional]
  tag := "GF3OW"

/-!

## B. Candidate extremal surfaces

-/

/-- The three classes of candidate extremal surfaces for the strip in the shell geometry,
labeled by how the surface closes off:

- *throat-confined* surfaces, which turn around at a radius `r_a ≥ R` and remain entirely in
  the throat, as for the pure throat geometry;
- *flat-bubble* surfaces, which cross the shell and turn around smoothly at a radius
  `0 < r_b < R` inside the flat bubble;
- *flat-sheeted* surfaces, two parallel planar sheets which cross the shell and drop straight
  to the origin `r = 0`, connected there through the degenerate transverse sphere.

The RT surface for a given half-width `ℓ` is the least-area member among these classes. -/
informal_definition StripSurfaceClasses where
  deps := [``stripAreaFunctional, ``stripRefractionCondition]
  tag := "GF3OY"

/-!

## C. The entanglement phase transition

-/

/-- The critical half-width `ℓ_c` of the strip in the shell geometry, at which the areas of
the dominant throat-confined surface and the flat-sheeted surface coincide. It scales with
the shell parameters as

`ℓ_c ∝ (r_p/R)^((7-p)/2) R`

with an explicit `p`-dependent numerical coefficient given in section 3.1 of
arXiv:2606.13889. Up to this coefficient, `ℓ_c` is the boundary length scale dual to the
shell radius. -/
informal_definition criticalStripWidth where
  deps := [``StripSurfaceClasses]
  tag := "GF3O2"

/-- The entanglement entropy of the strip in the shell geometry undergoes a first-order
phase transition at the critical width `DBrane.CoulombBranch.criticalStripWidth`: for
`ℓ < ℓ_c` the RT surface is throat-confined and the entropy agrees with that of the pure
Dp-brane throat, while for `ℓ > ℓ_c` the RT surface is the flat-sheeted one. The derivative
`dS/dℓ` jumps discontinuously at `ℓ = ℓ_c`. The flat-bubble surfaces never dominate:
whenever they exist they have larger area than one of the other two classes. See section 3.1
of arXiv:2606.13889. -/
informal_lemma stripEntropy_phase_transition where
  deps := [``criticalStripWidth, ``Holography.stripEntanglementEntropy]
  tag := "GF3O3"

/-- For `ℓ > ℓ_c` the regulated entanglement entropy of the strip in the shell geometry is
independent of `ℓ`: the flat-sheeted RT surface consists of two rigid sheets whose regulated
area does not change as the strip widens, so `dS/dℓ = 0`. The entanglement of the shell
state saturates once the strip is wide enough to probe the flat-space bubble. -/
informal_lemma stripEntropy_saturates where
  deps := [``stripEntropy_phase_transition, ``Holography.regulatedArea]
  tag := "GF3O5"

/-!

## D. UV divergences

-/

/-- The leading UV divergence of the strip entanglement entropy in the shell geometry is an
area law: expressed in terms of the gauge theory cutoff `δ` of
`DBrane.CoulombBranch.uvCutoffOfRadialCutoff`, it takes the schematic form

`S ∝ N² ĝ_eff(1/δ)^(2(p-3)/(5-p)) V_{p-1}/δ^(p-1)`

proportional to the area `2 V_{p-1}` of the entangling surface. It agrees with the
divergence in the Dp-brane throat vacuum, since the shell only modifies the geometry in the
infrared. See section 3.1 of arXiv:2606.13889 for the precise coefficient. -/
informal_lemma stripEntropy_uv_divergence where
  deps := [``stripAreaFunctional, ``uvCutoffOfRadialCutoff, ``DBrane.effectiveCoupling]
  tag := "GF3O7"

/-!

## E. The entropic c-function of the shell state

-/

/-- In the throat regime `ℓ < ℓ_c` the entropic c-function of the shell state agrees with
that of the Dp-brane throat vacuum,

`c̃_p(ℓ) = N² ĝ_eff(1/(2ℓ))^(2(p-3)/(5-p))`

up to a normalization: it counts `O(N²)` degrees of freedom, weighted by the running
effective coupling at the scale of the strip. For `p = 3` this is constant, `c̃_3 ∝ N²`,
consistent with `Holography.entropicCFunction_constant_of_cft`; for `p ≠ 3` it runs
monotonically with `ℓ`. See section 3.1 of arXiv:2606.13889. -/
informal_lemma entropicCFunction_throat_running where
  deps := [``Holography.entropicCFunction, ``stripEntropy_phase_transition,
    ``DBrane.effectiveCoupling]
  tag := "GF3PB"

/-- For `ℓ > ℓ_c` the entropic c-function of the shell state vanishes: since the regulated
entropy saturates, `dS/dℓ = 0` and hence `c̃_p(ℓ) = 0`. The infrared degrees of freedom of
the Coulomb-branch state are thus depleted relative to the throat vacuum: the flat-space
bubble carries only `O(1)` degrees of freedom in the large-`N` expansion, compared with the
`O(N²)` counted by the c-function in the throat regime. See section 3.1 of
arXiv:2606.13889. -/
informal_lemma entropicCFunction_vanishes_in_bubble where
  deps := [``entropicCFunction_throat_running, ``stripEntropy_saturates]
  tag := "GF3PD"

end CoulombBranch

end DBrane

end
