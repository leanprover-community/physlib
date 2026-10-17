/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.JetPointFiber
/-!
# Regularity and support for jet-coordinate maps

Smoothness of jet-coordinate maps of smooth fields and their vanishing outside the support.

## i. Overview

This module collects the analytic facts about coordinate-level jet maps that are needed later in
the local variational argument.

At this stage, it provides:

- smoothness of jet-coordinate maps of smooth fields,
- smoothness of the base-plus-coordinate jet map,
- and vanishing of jet coordinates outside topological support.

## ii. Key results

- `ClassicalFieldTheory.Local.jetCoordinatesAt_contDiff`
- `ClassicalFieldTheory.Local.jetBaseCoordinates_contDiff`
- `ClassicalFieldTheory.Local.jetCoordinatesAt_eq_zero_of_notMem_tsupport`
- `ClassicalFieldTheory.Local.jetDirectionAt_eq_zero_of_notMem_tsupport`

## iii. Table of contents

- A. Smoothness of jet-coordinate maps
- B. Support and vanishing lemmas

## iv. References

* None.
-/

@[expose] public section

open Physlib
open scoped ContDiff Topology

namespace ClassicalFieldTheory
namespace Local

/-!
## A. Smoothness of jet-coordinate maps

-/

/-- Smoothness of the jet-coordinate map of a smooth field. -/
lemma jetCoordinatesAt_contDiff (k : ℕ) (g : Space d → EuclideanSpace ℝ (Fin m))
    (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (jetCoordinatesAt k g) := by
  refine contDiff_pi.2 ?_
  intro I
  refine contDiff_pi.2 ?_
  intro a
  have hga : ContDiff ℝ ∞ (fun y => (g y) a) := by
    exact (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) (p := 2)
      (E := fun _ : Fin m => ℝ) (i := a)).comp hg
  simpa [jetCoordinatesAt] using Space.iteratedDeriv_contDiff I.1 hga

/-- Smoothness of the base-plus-coordinate jet map of a smooth field. -/
lemma jetBaseCoordinates_contDiff (k : ℕ) (g : Space d → EuclideanSpace ℝ (Fin m))
    (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x : Space d => (x, jetCoordinatesAt k g x)) := by
  exact contDiff_id.prodMk (jetCoordinatesAt_contDiff k g hg)

/-!
## B. Support and vanishing lemmas

-/

private lemma notMem_tsupport_coord {g : Space d → EuclideanSpace ℝ (Fin m)} {x : Space d}
    (hx : x ∉ tsupport g) (a : Fin m) :
    x ∉ tsupport (fun y => (g y) a) := by
  rw [notMem_tsupport_iff_eventuallyEq] at hx ⊢
  filter_upwards [hx] with y hy
  simp [hy]

/-- Outside the topological support of a field, all of its jet coordinates vanish. -/
lemma jetCoordinatesAt_eq_zero_of_notMem_tsupport (k : ℕ)
    (g : Space d → EuclideanSpace ℝ (Fin m)) {x : Space d}
    (hx : x ∉ tsupport g) :
    jetCoordinatesAt k g x = 0 := by
  funext I
  funext a
  exact Space.iteratedDeriv_eq_zero_of_notMem_tsupport I.1 (notMem_tsupport_coord hx a)

/-- Outside the topological support of a field, the corresponding jet-fiber direction vanishes. -/
lemma jetDirectionAt_eq_zero_of_notMem_tsupport (k : ℕ)
    (g : Space d → EuclideanSpace ℝ (Fin m)) {x : Space d}
    (hx : x ∉ tsupport g) :
    jetDirectionAt k g x = 0 := by
  ext I a
  exact Space.iteratedDeriv_eq_zero_of_notMem_tsupport I.1 (notMem_tsupport_coord hx a)

end Local
end ClassicalFieldTheory
