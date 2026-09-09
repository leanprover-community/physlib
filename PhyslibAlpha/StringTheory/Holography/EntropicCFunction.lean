/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.StringTheory.Holography.RyuTakayanagi
/-!
# Entropic c-functions

## i. Overview

The entanglement entropy of a strip-shaped region probes a quantum field theory at a single
length scale: the width of the strip. Its UV divergences are independent of the width, so the
derivative of the entropy with respect to the width is cutoff-independent, and suitably
normalized it defines an *entropic c-function*

`c̃_p(ℓ) = β_p (ℓ^p / V_{p-1}) dS(ℓ)/dℓ`

for a `(p+1)`-dimensional theory, with `ℓ` the half-width of the strip and `V_{p-1}` the
regulated volume of its cross-section. The c-function measures the number of effective
degrees of freedom at the scale `ℓ`: for a conformal theory it is constant and proportional
to the central charge, while along a renormalization group flow it interpolates between the
ultraviolet and infrared degrees of freedom. In `d = 2` the Casini-Huerta entropic c-theorem
shows the interpolation is monotonic, giving an entanglement proof of Zamolodchikov's
c-theorem.

In a holographic theory the strip entropy `S(ℓ)` is computed by the RT prescription, and the
c-function becomes a diagnostic of the dual geometry: it is sensitive to the bulk region
reached by the RT surface of a strip of width `2ℓ`, so its running with `ℓ` traces how the
number of degrees of freedom changes with depth in the bulk. A c-function which vanishes
beyond some width signals an infrared region of the geometry carrying parametrically fewer
degrees of freedom than the ultraviolet.

## ii. Key results

- `Holography.StripRegion` : the strip-shaped boundary region of half-width `ℓ`.
- `Holography.stripEntanglementEntropy` : the entanglement entropy of the strip as a function
  of `ℓ`.
- `Holography.entropicCFunction` : the entropic c-function built from the strip entanglement
  entropy.
- `Holography.entropicCFunction_constant_of_cft` : for a conformal boundary theory the
  entropic c-function is constant, proportional to the central charge.

## iii. Table of contents

- A. Strip regions and their entanglement entropy
- B. The entropic c-function

## iv. References

- H. Casini and M. Huerta, *A c-theorem for the entanglement entropy*,
  arXiv:cond-mat/0610375.
- S. Ryu and T. Takayanagi, *Aspects of Holographic Entanglement Entropy*,
  arXiv:hep-th/0605073.
- E. Jørstad, R. C. Myers and S. Pasterski, *Flat Space Entanglement: A Coulomb Branch
  Perspective*, arXiv:2606.13889, section 3.1.

-/

@[expose] public section

namespace Holography

/-!

## A. Strip regions and their entanglement entropy

-/

/-- The strip region of half-width `ℓ` on a `d`-dimensional boundary theory: on a fixed time
slice with spatial coordinates `(x_1, …, x_{d-1})`, the region

`A = {-ℓ ≤ x_1 ≤ ℓ}`

with the remaining coordinates unrestricted (or regulated to have finite volume `V_{d-2}`).
The entangling surface consists of the two parallel planes `x_1 = ±ℓ`, so the strip probes
the theory at the single length scale `2ℓ`. -/
informal_definition StripRegion where
  deps := [``BoundaryRegion]
  tag := "GF3NK"

/-- The entanglement entropy `S(ℓ)` of the strip region of half-width `ℓ`, obtained from the
RT prescription applied to `Holography.StripRegion`, as a function of `ℓ`. Because the strip
is translationally invariant along the entangling surface, the RT surface is determined by a
single profile function `x_1(r)` of the bulk radial coordinate, and `S(ℓ)` reduces to a
one-dimensional variational problem with a conserved momentum, integrable by quadrature. -/
informal_definition stripEntanglementEntropy where
  deps := [``StripRegion, ``holographicEntanglementEntropy]
  tag := "GF3NM"

/-!

## B. The entropic c-function

-/

/-- The entropic c-function of a `(p+1)`-dimensional boundary theory: for a strip of
half-width `ℓ` and regulated transverse volume `V_{p-1}`,

`c̃_p(ℓ) = β_p (ℓ^p / V_{p-1}) dS(ℓ)/dℓ`

where `β_p` is a `p`-dependent normalization constant. The UV divergences of `S(ℓ)` are
`ℓ`-independent, so `c̃_p` is cutoff-independent; it measures the number of effective degrees
of freedom of the boundary theory at the length scale `ℓ`. -/
informal_definition entropicCFunction where
  deps := [``stripEntanglementEntropy]
  tag := "GF3NO"

/-- For a conformal boundary theory the entropic c-function is independent of the strip width
`ℓ`, and with a suitable choice of the normalization `β_p` it equals a multiple of the
central charge `C_T` of the conformal field theory. For example, for `p = 3`
(four-dimensional `𝒩 = 4` super Yang-Mills) one finds `c̃_3 = 4 C_T ∝ N²`. -/
informal_lemma entropicCFunction_constant_of_cft where
  deps := [``entropicCFunction]
  tag := "GF3NQ"

end Holography

end
