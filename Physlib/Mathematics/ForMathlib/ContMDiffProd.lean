/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothness on products of normed spaces

Manifold smoothness on a product of normed spaces is the usual smoothness.

## i. Overview

Extends Mathlib's `contMDiff_iff_contDiff` to the product manifold structure.

## ii. Key results

- `contMDiffAt_prod_self_iff`
- `contMDiff_prod_self_iff`

## iii. Table of contents

- A. Products of normed spaces

## iv. References

* None.
-/

@[expose] public section

open scoped Manifold ContDiff

/-!
## A. Products of normed spaces
-/

/-- On a product of normed spaces, `C^n` at a point in the manifold sense is the usual one. -/
lemma contMDiffAt_prod_self_iff {𝕜 F G K : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    {f : F × G → K} {n : ℕ∞ω} {p : F × G} :
    ContMDiffAt (𝓘(𝕜, F).prod 𝓘(𝕜, G)) 𝓘(𝕜, K) n f p ↔ ContDiffAt 𝕜 n f p := by
  rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]

/-- On a product of normed spaces, `C^n` in the manifold sense is `C^n` in the usual sense. -/
lemma contMDiff_prod_self_iff {𝕜 F G K : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    {f : F × G → K} {n : ℕ∞ω} :
    ContMDiff (𝓘(𝕜, F).prod 𝓘(𝕜, G)) 𝓘(𝕜, K) n f ↔ ContDiff 𝕜 n f :=
  ⟨fun h ↦ contDiff_iff_contDiffAt.2 fun _ ↦ contMDiffAt_prod_self_iff.1 (h _),
    fun h _ ↦ contMDiffAt_prod_self_iff.2 h.contDiffAt⟩
