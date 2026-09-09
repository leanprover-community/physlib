/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.Informal.Basic
/-!
# The Ryu-Takayanagi prescription

## i. Overview

In a holographic duality, the entanglement entropy of a spatial region `A` of the boundary
theory is computed by a purely geometric quantity in the bulk. The Ryu-Takayanagi (RT)
prescription states that

`S(A) = min_{γ ∼ A} Area(γ) / (4 G_N)`

where the minimum is over bulk codimension-two surfaces `γ` anchored on the entangling surface
`∂A` and homologous to `A`, and `G_N` is the bulk Newton constant. The formula generalizes the
Bekenstein-Hawking entropy of horizons to arbitrary boundary regions, and reduces questions
about the entanglement structure of strongly coupled states to variational problems for
minimal surfaces in the dual geometry.

Several structural features follow directly from the prescription. The entropy is UV
divergent, the divergence governed by the geometry near the cutoff surface on which `A` is
specified. Several extremal surfaces may satisfy the anchoring and homology conditions, and
exchanges of dominance between them as `A` is varied produce entanglement analogues of phase
transitions. Both features carry physical information: the divergence structure encodes the
local degrees of freedom of the boundary theory, and dominance exchanges diagnose scales at
which its infrared structure changes.

The definitions in this module are deliberately independent of any particular bulk solution
and of the shape of the boundary region, so that they can be instantiated for anti-de Sitter
space, Dp-brane throats, Coulomb-branch shell geometries, or any other static holographic
background.

## ii. Key results

- `Holography.StaticHolographicBackground` : the bulk data on which the RT prescription is
  evaluated.
- `Holography.BoundaryRegion` : a region of a fixed time slice of the boundary theory.
- `Holography.RTSurface` : the minimal-area bulk surface anchored on, and homologous to, a
  boundary region.
- `Holography.holographicEntanglementEntropy` : the entanglement entropy assigned to a
  boundary region by the RT prescription.
- `Holography.regulatedArea` : the area of an RT surface with its UV-divergent part
  subtracted.

## iii. Table of contents

- A. The holographic background
- B. Boundary regions
- C. Ryu-Takayanagi surfaces
- D. Holographic entanglement entropy

## iv. References

- S. Ryu and T. Takayanagi, *Holographic derivation of entanglement entropy from AdS/CFT*,
  arXiv:hep-th/0603001.
- T. Nishioka, S. Ryu and T. Takayanagi, *Holographic Entanglement Entropy: An Overview*,
  arXiv:0905.0932.
- M. Rangamani and T. Takayanagi, *Holographic Entanglement Entropy*, arXiv:1609.01287.

-/

@[expose] public section

namespace Holography

/-!

## A. The holographic background

-/

/-- The data of a static holographic background on which the Ryu-Takayanagi prescription is
evaluated. This consists of:

- a Riemannian manifold `M`, the constant-time slice of a static bulk spacetime (possibly
  including compact internal directions, as for ten-dimensional brane geometries);
- a bulk Newton constant `G_N`;
- a distinguished radial coordinate `r` together with a cutoff surface `r = r_uv` near the
  asymptotic region, on which boundary regions are specified.

Staticity ensures that the covariant (HRT) prescription reduces to a minimal-surface problem
on the time slice. The asymptotic region may be anti-de Sitter, a Dp-brane throat, or flat
space; the cutoff surface regulates the infinite volume near it in all three cases. -/
informal_definition StaticHolographicBackground where
  deps := []
  tag := "GF3M5"

/-!

## B. Boundary regions

-/

/-- A region `A` of the cutoff surface of a static holographic background, specified on a
fixed time slice. The boundary `∂A` of the region within the cutoff surface is called the
*entangling surface*. Typical examples are the strip, bounded by two parallel planes, and the
ball, bounded by a sphere; the shape of `A` determines the symmetry of the associated minimal
surface problem. -/
informal_definition BoundaryRegion where
  deps := [``StaticHolographicBackground]
  tag := "GF3NC"

/-!

## C. Ryu-Takayanagi surfaces

-/

/-- The Ryu-Takayanagi surface of a boundary region `A` in a static holographic background:
the codimension-two bulk surface `γ` (codimension one in the constant-time slice) of minimal
area among surfaces which

- are anchored on the entangling surface, `∂γ = ∂A`, and
- are homologous to `A`, i.e. there is a bulk region whose boundary is `γ ∪ A`.

The area is computed with the Einstein-frame bulk metric restricted to the time slice. In
general several extremal surfaces satisfy these conditions, and the RT surface is the one of
least area; as `A` is varied, exchanges of dominance between competing extremal surfaces
produce non-analytic behavior of the entanglement entropy. -/
informal_definition RTSurface where
  deps := [``StaticHolographicBackground, ``BoundaryRegion]
  tag := "GF3NE"

/-!

## D. Holographic entanglement entropy

-/

/-- The holographic entanglement entropy of a boundary region `A`:

`S(A) = Area(γ_A) / (4 G_N)`

where `γ_A` is the RT surface of `A`. Via the Ryu-Takayanagi conjecture this equals the von
Neumann entropy of the reduced state of the boundary theory on `A`. -/
informal_definition holographicEntanglementEntropy where
  deps := [``RTSurface]
  tag := "GF3NG"

/-- The regulated area of an RT surface: the area evaluated with the anchoring moved to the
cutoff surface `r = r_uv`, with the divergent terms as `r_uv → ∞` subtracted. For
asymptotically AdS backgrounds the leading divergence is an area law in the entangling
surface; for asymptotically flat regions it is instead a volume law in the boundary region
(see `Holography.flat_cap_entropy_volume_law`). The regulated area isolates the
cutoff-independent information in the entanglement entropy. -/
informal_definition regulatedArea where
  deps := [``RTSurface, ``holographicEntanglementEntropy]
  tag := "GF3NI"

end Holography

end
