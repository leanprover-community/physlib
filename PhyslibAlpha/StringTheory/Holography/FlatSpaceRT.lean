/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.StringTheory.Holography.RyuTakayanagi
/-!
# Ryu-Takayanagi surfaces in flat space

## i. Overview

Minkowski space can be treated as a static holographic background by placing boundary regions
on a large sphere of radius `r_uv` and applying the Ryu-Takayanagi prescription. The outcome
differs sharply from the asymptotically anti-de Sitter case, for a simple geometric reason: a
constant-time slice of Minkowski space is flat Euclidean space, so there is no gravitational
potential to bend minimal surfaces, and the minimal surface anchored on the boundary of a
region of the cutoff sphere is a flat hyperplane.

Two consequences follow. First, the entanglement entropy of a spherical cap scales with the
*volume* of the cap on the cutoff sphere,

`S(A) ∝ r_uv^(d-1) Ω_A / G_N`,

a volume law, in contrast with the area law `S(A) ∝ Area(∂A)` of asymptotically AdS
backgrounds. Second, the flat hyperplane surfaces hug the cutoff sphere and never descend far
into the interior, so holographic entanglement entropy in flat space is a poor probe of deep
infrared bulk physics. Both features are recurring puzzles for any attempt at flat-space
holography, and both are made quantitative by the definitions in this module. A controlled
setting in which a flat region arises as the infrared of a standard holographic background is
provided by the Coulomb-branch shell geometries of
`PhyslibAlpha.StringTheory.DBranes.CoulombBranch.Shell`.

## ii. Key results

- `Holography.MinkowskiBackground` : Minkowski space as a static holographic background.
- `Holography.rtSurface_flat_hyperplane` : minimal surfaces in a flat time slice are flat
  hyperplanes.
- `Holography.flat_cap_entropy_volume_law` : the RT entropy of a spherical cap in flat space
  obeys a volume law in the cutoff radius.

## iii. Table of contents

- A. Minkowski space as a holographic background
- B. Minimal surfaces in flat space
- C. The volume law

## iv. References

- W. Li and T. Takayanagi, *Holography and Entanglement in Flat Spacetime*,
  arXiv:1010.3700.
- E. Jørstad, R. C. Myers and S. Pasterski, *Flat Space Entanglement: A Coulomb Branch
  Perspective*, arXiv:2606.13889, section 2.1.

-/

@[expose] public section

namespace Holography

/-!

## A. Minkowski space as a holographic background

-/

/-- `(d+1)`-dimensional Minkowski space regarded as a static holographic background: the
constant-time slice is flat Euclidean space, with metric in polar coordinates

`ds² = dr² + r² (dθ² + cos²θ dΩ²_{d-2})`,

the cutoff surface is the sphere `r = r_uv`, and boundary regions are regions of this sphere.
This is the setting in which the Ryu-Takayanagi prescription is applied directly to flat
space. -/
informal_definition MinkowskiBackground where
  deps := [``StaticHolographicBackground]
  tag := "GF3QB"

/-!

## B. Minimal surfaces in flat space

-/

/-- In the flat background `Holography.MinkowskiBackground`, a minimal surface anchored on
the boundary of a spherical cap of the cutoff sphere `r = r_uv` is a flat hyperplane: with no
gravitational potential to bend the surface, the variational problem for the RT surface is
solved by totally geodesic hyperplanes. In particular the surface remains at distances of
order `r_uv` from the origin and does not probe the deep interior of the bulk. -/
informal_lemma rtSurface_flat_hyperplane where
  deps := [``MinkowskiBackground, ``RTSurface]
  tag := "GF3NS"

/-!

## C. The volume law

-/

/-- For a spherical cap `A` of opening angle `θ_0` on the cutoff sphere `r = r_uv` of the
flat background `Holography.MinkowskiBackground`, the RT entropy scales as

`S(A) ∝ r_uv^(d-1) Ω_A / G_N`

where `Ω_A` is the solid angle subtended by `A`. This is a *volume law* in the boundary
region `A`, in contrast with the area law of asymptotically AdS backgrounds: the leading
divergence is proportional to the volume of `A` rather than the area of the entangling
surface `∂A`. See section 2.1 of arXiv:2606.13889. -/
informal_lemma flat_cap_entropy_volume_law where
  deps := [``MinkowskiBackground, ``rtSurface_flat_hyperplane, ``holographicEntanglementEntropy]
  tag := "GF3NU"

end Holography

end
