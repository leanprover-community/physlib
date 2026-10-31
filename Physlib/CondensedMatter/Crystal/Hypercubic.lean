/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.CondensedMatter.Crystal.BondLength
public import Physlib.CondensedMatter.Crystal.Bravais.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hypercubic lattices

The hypercubic lattice of every dimension, with unit bonds along the coordinate axes.

## i. Overview

The hypercubic lattice is the Bravais lattice of dimension `d` embedded along the coordinate
axes, with one bond along each axis. Its edges have length one, and each site has `2 d`
neighbors. For `d = 1, 2, 3` this is the chain, the square lattice and the simple cubic lattice.

## ii. Key results

- `Crystal.hypercubicEmbedding`, `Crystal.hypercubicGraph` : the hypercubic lattice of dimension
  `d`.
- `Crystal.hypercubicGraph_dist_position` : every edge of the hypercubic graph has length one.
- `Crystal.hypercubicGraph_degree` : each site has `2 d` neighbors.

## iii. Table of contents

- A. Hypercubic lattices
- B. Coordination number

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 4.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

/-! ## A. Hypercubic lattices -/

/-- The hypercubic lattice of dimension `d` embedded along the coordinate axes, with unit
spacing. -/
noncomputable def hypercubicEmbedding (d : ℕ) :
    Embedding (bravais d) (EuclideanSpace ℝ (Fin d)) :=
  Embedding.ofVectors fun j => EuclideanSpace.single j 1

/-- One bond along each coordinate axis. -/
def hypercubicBonds (d : ℕ) : Finset (Bond (bravais d)) :=
  Finset.univ.image fun j : Fin d => ⟨(), (), Pi.single j 1⟩

/-- The graph that connects each site to its neighbors along the coordinate axes. -/
def hypercubicGraph (d : ℕ) : PeriodicGraph (bravais d) :=
  PeriodicGraph.ofBonds (hypercubicBonds d)

/-- Every edge of the hypercubic graph has length one, in any dimension. -/
lemma hypercubicGraph_dist_position (d : ℕ) {x y : (bravais d).Site}
    (h : (hypercubicGraph d).toSimpleGraph.Adj x y) :
    Dist.dist ((hypercubicEmbedding d).position x) ((hypercubicEmbedding d).position y) = 1 := by
  refine (hypercubicEmbedding d).dist_position_of_adj (hypercubicBonds d) ?_
    (by simpa only [hypercubicGraph] using h)
  intro b hb
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hb
  simp [Embedding.bondVector, hypercubicEmbedding, Embedding.ofVectors, Pi.single_apply]

/-! ## B. Coordination number -/

/-- The steps of the hypercubic lattice are the unit vectors along the axes, in both directions. -/
lemma steps_hypercubicBonds (d : ℕ) :
    PeriodicGraph.steps (hypercubicBonds d) =
      Finset.univ.image (Pi.single · 1) ∪ Finset.univ.image fun j => -Pi.single j 1 := by
  rw [PeriodicGraph.steps, Finset.erase_eq_of_notMem]
  all_goals simp [hypercubicBonds, Finset.image_image, Function.comp_def]

/-- Each site of the hypercubic lattice of dimension `d` has `2 d` neighbors. -/
lemma hypercubicGraph_degree (d : ℕ) (x : (bravais d).Site) :
    (hypercubicGraph d).toSimpleGraph.degree x = 2 * d := by
  have hinj : Function.Injective fun j : Fin d => (Pi.single j 1 : Fin d → ℤ) := fun j k h => by
    simpa [Pi.single_apply] using congrFun h j
  rw [hypercubicGraph, PeriodicGraph.degree_ofBonds_of_unique, steps_hypercubicBonds,
    Finset.card_union_of_disjoint, Finset.card_image_of_injective _ hinj,
    Finset.card_image_of_injective _ (fun j k h => hinj (neg_injective h))]
  · simp [two_mul]
  · simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_univ, true_and,
      forall_exists_index, forall_apply_eq_imp_iff]
    rintro j ⟨k, h⟩
    have := congrFun h j
    by_cases hjk : k = j <;> simp [hjk] at this

end Physlib.CondensedMatter.Crystal
