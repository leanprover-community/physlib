/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.CondensedMatter.Crystal.Hypercubic

/-!
# Triangular and hexagonal lattices

The triangular lattice and the primitive hexagonal lattice, with their bond graphs.

## i. Overview

The triangular lattice is the Bravais lattice of dimension two with two unit primitive vectors at
sixty degrees. Three bonds, along the two primitive vectors and along their difference, generate
the graph with six neighbors per site, all at distance one.

The primitive hexagonal lattice stacks triangular layers of spacing `a` at distance `c`. Three
bonds in the plane have length `a`, and one bond along the stacking axis has length `c`, so each
site has eight neighbors.

## ii. Key results

- `Crystal.triangularEmbedding`, `Crystal.triangularGraph` : the triangular lattice.
- `Crystal.triangularGraph_dist_position` : every edge of the triangular graph has length one.
- `Crystal.triangularGraph_degree` : each site has six neighbors.
- `Crystal.hexagonalEmbedding`, `Crystal.hexagonalGraph` : the primitive hexagonal lattice.
- `Crystal.hexagonalGraph_dist_position` : each edge has length `a` or `c`.
- `Crystal.hexagonalGraph_degree` : each site has eight neighbors.

## iii. Table of contents

- A. Triangular lattice
- B. Primitive hexagonal lattice

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 4.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

/-! ## A. Triangular lattice -/

/-- The triangular lattice embedded with unit primitive vectors at sixty degrees. -/
noncomputable def triangularEmbedding : Embedding (bravais 2) (EuclideanSpace ℝ (Fin 2)) :=
  Embedding.ofVectors ![!₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]]

/-- Three bonds generate the six neighbors of the triangular lattice. -/
def triangularBonds : Finset (Bond (bravais 2)) :=
  {⟨(), (), ![1, 0]⟩, ⟨(), (), ![0, 1]⟩, ⟨(), (), ![1, -1]⟩}

/-- The graph that connects each site to its six neighbors. -/
def triangularGraph : PeriodicGraph (bravais 2) :=
  PeriodicGraph.ofBonds triangularBonds

/-- Every edge of the triangular graph has length one. -/
lemma triangularGraph_dist_position {x y : (bravais 2).Site}
    (h : triangularGraph.toSimpleGraph.Adj x y) :
    Dist.dist (triangularEmbedding.position x) (triangularEmbedding.position y) = 1 := by
  refine triangularEmbedding.dist_position_of_adj triangularBonds ?_
    (by simpa only [triangularGraph] using h)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  intro b hb
  simp only [triangularBonds, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl <;>
    simp [triangularEmbedding, Embedding.bondVector_ofVectors, Fin.sum_univ_two,
      EuclideanSpace.norm_eq] <;>
    linear_combination (1 / 4 : ℝ) * h3

/-- Each site of the triangular lattice has six neighbors. -/
lemma triangularGraph_degree (x : (bravais 2).Site) :
    triangularGraph.toSimpleGraph.degree x = 6 := by
  rw [triangularGraph, PeriodicGraph.degree_ofBonds_of_unique]
  decide

/-! ## B. Primitive hexagonal lattice -/

/-- The primitive hexagonal lattice with in-plane length `a` and layer spacing `c`. -/
noncomputable def hexagonalEmbedding (a c : ℝ) :
    Embedding (bravais 3) (EuclideanSpace ℝ (Fin 3)) :=
  Embedding.ofVectors ![!₂[a, 0, 0], !₂[a / 2, a * Real.sqrt 3 / 2, 0], !₂[0, 0, c]]

/-- Three bonds in the plane and one along the stacking axis generate the eight neighbors. -/
def hexagonalBonds : Finset (Bond (bravais 3)) :=
  {⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![1, -1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩}

/-- The graph that connects each site to its eight neighbors. -/
def hexagonalGraph : PeriodicGraph (bravais 3) :=
  PeriodicGraph.ofBonds hexagonalBonds

/-- Each bond of the hexagonal lattice has length `a` in the plane or `c` along the stacking
axis. -/
lemma hexagonalBonds_norm {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    ∀ b ∈ hexagonalBonds,
      ‖(hexagonalEmbedding a c).bondVector b‖ = a ∨
        ‖(hexagonalEmbedding a c).bondVector b‖ = c := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  intro b hb
  simp only [hexagonalBonds, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp [hexagonalEmbedding, Embedding.bondVector_ofVectors, Fin.sum_univ_three,
      EuclideanSpace.norm_eq]
  all_goals
    first
    | (left; exact Real.sqrt_sq ha)
    | (right; exact Real.sqrt_sq hc)
    | (left
       rw [Real.sqrt_eq_iff_eq_sq (by positivity) ha]
       linear_combination (a ^ 2 / 4) * h3)

/-- Every edge of the hexagonal graph has length `a` in the plane or `c` along the stacking
axis. -/
lemma hexagonalGraph_dist_position {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    {x y : (bravais 3).Site} (h : hexagonalGraph.toSimpleGraph.Adj x y) :
    Dist.dist ((hexagonalEmbedding a c).position x) ((hexagonalEmbedding a c).position y) = a ∨
    Dist.dist ((hexagonalEmbedding a c).position x) ((hexagonalEmbedding a c).position y) = c := by
  obtain ⟨-, b, hb, hl | hl⟩ := (PeriodicGraph.adj_ofBonds hexagonalBonds x y).1
    (by simpa only [hexagonalGraph] using h)
  · rw [(hexagonalEmbedding a c).dist_position_of_links hl]
    exact hexagonalBonds_norm ha hc b hb
  · rw [dist_comm, (hexagonalEmbedding a c).dist_position_of_links hl]
    exact hexagonalBonds_norm ha hc b hb

/-- Each site of the primitive hexagonal lattice has eight neighbors. -/
lemma hexagonalGraph_degree (x : (bravais 3).Site) :
    hexagonalGraph.toSimpleGraph.degree x = 8 := by
  rw [hexagonalGraph, PeriodicGraph.degree_ofBonds_of_unique]
  decide

end Physlib.CondensedMatter.Crystal
