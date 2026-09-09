/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.StringTheory.DBranes.Basic
/-!
# The decoupling limit of Dp-branes

## i. Overview

The worldvolume theory of `N` coincident Dp-branes is `(p+1)`-dimensional maximally
supersymmetric `U(N)` Yang-Mills theory. In the decoupling limit — energies far below the
string scale, with the Yang-Mills coupling held fixed — this gauge theory decouples from the
bulk closed strings, and is conjectured to be dual to string theory in the *throat* region of
the Dp-brane background: the near-horizon geometry obtained by dropping the constant term in
the harmonic function,

`H(r) = (r_p/r)^(7-p)`.

For `p = 3` the throat is `AdS₅ × S⁵` and the duality is the AdS/CFT correspondence with
`𝒩 = 4` super Yang-Mills; for `p ≠ 3` the throat is conformal to `AdS_{p+2} × S^{8-p}` with a
running dilaton, dual to a non-conformal gauge theory.

Because the Yang-Mills coupling `g²_YM` has mass dimension `3 - p`, the strength of the gauge
dynamics at an energy scale `E` is measured by the dimensionless effective coupling

`ĝ²_eff(E) = g²_YM N E^(p-3)`,

which runs with the scale for `p ≠ 3`. Under the holographic dictionary `E` maps to a radial
position in the throat, and the supergravity description is valid only in the window of radii
where the curvature is small in string units and the local string coupling is small. The
throat is therefore a good dual of the gauge theory in an intermediate range of scales,
matching onto other descriptions (perturbative Yang-Mills, M-theory lifts, …) outside that
window.

## ii. Key results

- `DBrane.dpBraneThroatMetric` : the near-horizon throat geometry of `N` Dp-branes.
- `DBrane.effectiveCoupling` : the running effective coupling `ĝ²_eff(E) = g²_YM N E^(p-3)` of
  the dual gauge theory.
- `DBrane.SupergravityRegime` : the window of scales in which the supergravity description of
  the throat is valid.

## iii. Table of contents

- A. The throat geometry
- B. The dual gauge theory coupling
- C. Validity of the supergravity description

## iv. References

- N. Itzhaki, J. M. Maldacena, J. Sonnenschein and S. Yankielowicz, *Supergravity and the
  large N limit of theories with sixteen supercharges*, arXiv:hep-th/9802042.
- O. Aharony, S. S. Gubser, J. M. Maldacena, H. Ooguri and Y. Oz, *Large N field theories,
  string theory and gravity*, arXiv:hep-th/9905111.
- E. Jørstad, R. C. Myers and S. Pasterski, *Flat Space Entanglement: A Coulomb Branch
  Perspective*, arXiv:2606.13889, section 2.2.

-/

@[expose] public section

namespace DBrane

/-!

## A. The throat geometry

-/

/-- The throat (near-horizon) metric of `N` coincident Dp-branes: the background
`DBrane.dpBraneMetric` with harmonic function

`H(r) = (r_p/r)^(7-p)`,

obtained from the stacked-brane harmonic function by dropping the constant term, as is
appropriate at radii `r ≪ r_p` or in the decoupling limit. For `p = 3` the throat is
`AdS₅ × S⁵` with AdS radius `L = r_3`; for `p ≠ 3` it is conformal to `AdS_{p+2} × S^{8-p}`
with a nontrivial dilaton profile. The throat is the region of the geometry dual to
`(p+1)`-dimensional maximally supersymmetric `U(N)` Yang-Mills theory. -/
informal_definition dpBraneThroatMetric where
  deps := [``dpBraneMetric]
  tag := "GF3N7"

/-!

## B. The dual gauge theory coupling

-/

/-- The dimensionless effective coupling of `(p+1)`-dimensional maximally supersymmetric
`U(N)` Yang-Mills theory at energy scale `E`:

`ĝ²_eff(E) = g²_YM N E^(p-3)`

where `g²_YM` is the Yang-Mills coupling, of mass dimension `3 - p`. For `p < 3` the coupling
grows toward the infrared, for `p > 3` toward the ultraviolet, and for `p = 3` it is the
't Hooft coupling, constant by conformal invariance. Under the holographic dictionary the
energy scale `E` corresponds to a radial position in the throat
`DBrane.dpBraneThroatMetric`. -/
informal_definition effectiveCoupling where
  deps := [``dpBraneThroatMetric]
  tag := "GF3OB"

/-!

## C. Validity of the supergravity description

-/

/-- The regime of validity of the supergravity description of the Dp-brane throat: the window
of energy scales in which both the string-frame curvature is small in string units, requiring
`ĝ²_eff(E) ≫ 1`, and the local string coupling is small, requiring an upper bound on
`ĝ²_eff(E)` growing with a positive power of `N`. For `p ≠ 3` this window covers a wide but
bounded range of scales, so the supergravity throat describes the gauge theory only at
intermediate energies; for `p = 3` the condition is the scale-independent `1 ≪ g²_YM N ≪ N`.

See arXiv:hep-th/9802042, and section 2.2 of arXiv:2606.13889. -/
informal_definition SupergravityRegime where
  deps := [``effectiveCoupling, ``dpBraneThroatMetric]
  tag := "GF3OD"

end DBrane

end
