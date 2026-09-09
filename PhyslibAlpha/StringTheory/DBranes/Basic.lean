/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.Informal.Basic
/-!
# Dp-brane supergravity backgrounds

## i. Overview

Dp-branes are `(p+1)`-dimensional extended objects of type II string theory which carry tension
and Ramond-Ramond charge. At low energies, a stack of `N` coincident Dp-branes sources a
classical solution of type II supergravity — an extremal black `p`-brane — which is determined
entirely by a single function `H`, harmonic on the `(9-p)`-dimensional space transverse to the
branes. In the Einstein frame the background is

`ds²_E = H^((p-7)/8) (-dt² + dx²_∥) + H^((p+1)/8) (dr² + r² dΩ²_{8-p})`,

`e^φ = g_s H^((3-p)/4)`,

together with `N` units of Ramond-Ramond flux through the transverse sphere. For branes
stacked at the origin the harmonic function is `H(r) = 1 + (r_p/r)^(7-p)`, where the scale
`r_p` is set by `g_s N` in string units.

The linearity of Laplace's equation makes this family of backgrounds highly reusable: *any*
distribution of branes in the transverse space yields a solution, with `H` the corresponding
electrostatic potential. Multi-center solutions, continuous distributions, and the spherical
shells of `PhyslibAlpha.StringTheory.DBranes.CoulombBranch.Shell` all arise this way. The
near-horizon limit of the stacked solution, and the gauge/gravity duality it supports, are
developed in `PhyslibAlpha.StringTheory.DBranes.DecouplingLimit`.

## ii. Key results

- `DBrane.dpBraneScale` : the length scale `r_p` of the background sourced by `N` Dp-branes.
- `DBrane.dpBraneHarmonicFunction` : the harmonic function `H(r) = 1 + (r_p/r)^(7-p)` of a
  stack of branes at the origin.
- `DBrane.dpBraneMetric` : the Einstein-frame metric determined by a transverse-harmonic
  function.
- `DBrane.dpBraneDilaton` : the corresponding dilaton profile.
- `DBrane.dpBraneMetric_solves_supergravity` : these backgrounds solve the type II
  supergravity equations of motion.

## iii. Table of contents

- A. The brane scale and harmonic function
- B. The background fields
- C. The supergravity equations

## iv. References

- G. T. Horowitz and A. Strominger, *Black strings and p-branes*, Nucl. Phys. B360 (1991) 197.
- K. S. Stelle, *BPS branes in supergravity*, arXiv:hep-th/9803116.
- E. Jørstad, R. C. Myers and S. Pasterski, *Flat Space Entanglement: A Coulomb Branch
  Perspective*, arXiv:2606.13889, section 2.2.

-/

@[expose] public section

namespace DBrane

/-!

## A. The brane scale and harmonic function

-/

/-- The length scale `r_p` of the supergravity background sourced by a stack of `N` coincident
Dp-branes, determined by

`r_p^(7-p) = 2^(5-p) π^((5-p)/2) Γ((7-p)/2) g_s N ℓ_s^(7-p)`

where `g_s` is the string coupling and `ℓ_s` the string length. This is the scale at which the
harmonic function of the stacked-brane background transitions between its asymptotically flat
and near-horizon behaviors; it is the gravitational analogue of the charge radius of the
stack. -/
informal_definition dpBraneScale where
  deps := []
  tag := "GF3NV"

/-- The harmonic function of the background sourced by `N` coincident Dp-branes at the origin
of the transverse space:

`H(r) = 1 + (r_p/r)^(7-p)`

where `r` is the radial coordinate in the `(9-p)`-dimensional transverse space and `r_p` is
`DBrane.dpBraneScale`. It is harmonic away from the origin, where the branes sit as a
delta-function source, and tends to `1` at infinity, where the background becomes flat
ten-dimensional Minkowski space. More general brane distributions are described by the
harmonic function equal to the electrostatic potential of the corresponding charge
distribution. -/
informal_definition dpBraneHarmonicFunction where
  deps := [``dpBraneScale]
  tag := "GF3NX"

/-!

## B. The background fields

-/

/-- The Einstein-frame metric of the background sourced by Dp-branes with transverse-harmonic
function `H`:

`ds²_E = H^((p-7)/8) (-dt² + dx²_∥) + H^((p+1)/8) (dr² + r² dΩ²_{8-p})`

where `x_∥` are the `p` spatial worldvolume directions and `dΩ²_{8-p}` is the round metric on
the unit `(8-p)`-sphere of the transverse space. For a stack of `N` branes at the origin, `H`
is `DBrane.dpBraneHarmonicFunction`; any other transverse-harmonic `H` gives the metric of the
corresponding brane distribution. -/
informal_definition dpBraneMetric where
  deps := [``dpBraneHarmonicFunction]
  tag := "GF3NZ"

/-- The dilaton profile of a Dp-brane background with transverse-harmonic function `H`:

`e^φ = g_s H^((3-p)/4)`.

For `p < 3` the dilaton grows where `H` grows (near the branes), for `p > 3` it decreases
there, and for `p = 3` it is constant — the special feature of D3-branes underlying the
conformal invariance of their worldvolume theory. -/
informal_definition dpBraneDilaton where
  deps := [``dpBraneHarmonicFunction]
  tag := "GF3N3"

/-!

## C. The supergravity equations

-/

/-- The Dp-brane background — the metric `DBrane.dpBraneMetric`, the dilaton
`DBrane.dpBraneDilaton` and the Ramond-Ramond `(p+1)`-form potential `C_{01…p} ∝ H⁻¹` with `N`
units of flux through the transverse sphere — solves the equations of motion of type II
supergravity (type IIA for `p` even, type IIB for `p` odd) for *any* function `H` harmonic on
the transverse space, with brane sources located where `H` fails to be harmonic. This
linearity in the source distribution underlies multi-center and shell solutions. -/
informal_lemma dpBraneMetric_solves_supergravity where
  deps := [``dpBraneMetric, ``dpBraneDilaton]
  tag := "GF3N5"

end DBrane

end
