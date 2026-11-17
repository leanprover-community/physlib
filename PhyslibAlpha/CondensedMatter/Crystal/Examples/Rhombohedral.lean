/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Examples.ThreeDimensional

/-!

# The rhombohedral lattice

The rhombohedral lattice, with its embedding and the bonds of its first two neighbour shells.

## i. Overview

A rhombohedral lattice has three primitive vectors of the same length with the same angle `α`
between any two of them. Up to a rotation they are `(p, q, q)`, `(q, p, q)` and `(q, q, p)`,
with `cos α = (2 p q + q ²) / (p ² + 2 q ²)`. The six bonds `±aᵢ` of the first shell are those of
the simple cubic lattice, so the first shell alone does not see the threefold axis. When
`-1 / 4 < cos α < 0` the second shell is made of the six vectors `±(aᵢ + aⱼ)`, and the graph with
both shells has twelve neighbours. This holds for instance for `(p, q) = (10, -1)`, with
`cos α = -19 / 102`. The graph is defined by these twelve bonds and does not depend on `p`
and `q`: that they form the two nearest shells is the statement above, not yet a lemma.

## ii. Key results

- `rhombohedral` : the lattice, with one site per cell.
- `rhombohedralVectors` : the primitive vectors `(p, q, q)`, `(q, p, q)`, `(q, q, p)`.
- `rhombohedralGeometry` : the embedding, for `p ≠ q` and `p + 2 q ≠ 0`.
- `rhombohedral_neighbors_card` : the coordination number `12`.

## iii. Table of contents

- A. The lattice and its embedding
- B. Bonds and coordination number

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

/-! ## A. The lattice and its embedding -/

/-- One site per primitive cell of the rhombohedral lattice. -/
@[reducible]
def rhombohedral := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- The primitive vectors `(p, q, q)`, `(q, p, q)` and `(q, q, p)` of a rhombohedral lattice. -/
noncomputable def rhombohedralVectors (p q : ℝ) : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[p, q, q], !₂[q, p, q], !₂[q, q, p]]

/-- The primitive vectors are independent when `p ≠ q` and `p + 2 q ≠ 0`. -/
lemma rhombohedralVectors_independent {p q : ℝ} (hpq : p ≠ q) (hp : p + 2 * q ≠ 0) :
    LinearIndependent ℝ (rhombohedralVectors p q) := by
  rw [Fintype.linearIndependent_iff]
  intro x h j
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
  simp [rhombohedralVectors, Fin.sum_univ_three] at h0 h1 h2
  have hpq' : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have e01 : x 0 = x 1 := sub_eq_zero.mp ((mul_eq_zero.mp (by linear_combination h0 - h1 :
    (p - q) * (x 0 - x 1) = 0)).resolve_left hpq')
  have e12 : x 1 = x 2 := sub_eq_zero.mp ((mul_eq_zero.mp (by linear_combination h1 - h2 :
    (p - q) * (x 1 - x 2) = 0)).resolve_left hpq')
  have e0 : x 0 = 0 := (mul_eq_zero.mp (by rw [← e12, ← e01] at h0; linear_combination h0 :
    (p + 2 * q) * x 0 = 0)).resolve_left hp
  fin_cases j <;> dsimp <;> linarith

/-- The rhombohedral lattice embedded with the primitive vectors `rhombohedralVectors p q`. -/
noncomputable def rhombohedralGeometry (p q : ℝ) (hpq : p ≠ q) (hp : p + 2 * q ≠ 0) :
    Geometry rhombohedral (EuclideanSpace ℝ (Fin 3)) :=
  Geometry.ofLattice (latticeMap (rhombohedralVectors p q))
    (latticeMap_injective (rhombohedralVectors_independent hpq hp))

/-! ## B. Bonds and coordination number -/

/-- The bonds of the first two shells for `-1 / 4 < cos α < 0`, up to sign: the three primitive
vectors and their pairwise sums. -/
def rhombohedralBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩,
    ⟨(), (), ![1, 1, 0]⟩, ⟨(), (), ![0, 1, 1]⟩, ⟨(), (), ![1, 0, 1]⟩]

/-- The twelve-neighbour rhombohedral graph. -/
def rhombohedralGraph : PeriodicGraph rhombohedral := PeriodicGraph.ofBonds rhombohedralBonds

/-- Each site of the rhombohedral lattice has twelve neighbours. -/
lemma rhombohedral_neighbors_card (x : rhombohedral.Site) :
    (rhombohedralGraph.neighbors x).card = 12 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (rhombohedralGraph.neighbors ⟨0, ()⟩).card = 12 := by decide
  exact (rhombohedralGraph.card_neighbors_cell n ()).trans h

end CondensedMatter.Crystal
