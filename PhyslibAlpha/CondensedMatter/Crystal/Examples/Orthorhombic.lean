/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Examples.ThreeDimensional

/-!

# Orthorhombic lattices

The primitive, base-centred, body-centred and face-centred orthorhombic lattices, with their
embeddings and the bonds of their first neighbour shells.

## i. Overview

An orthorhombic lattice has three different lengths `a`, `b`, `c` along three orthogonal axes.
The bonds of the first shell alone do not see the three axes as different. For the primitive
lattice the six bonds `±x, ±y, ±z` are those of the simple cubic lattice. A graph with
orthorhombic symmetry needs the shells up to the first ones that tell each axis from the other
two. With the lengths below these are:

- primitive, `(a, b, c) = (3, 4, 7)`: the shells at `3, 4, 5, 6, 7`, twelve neighbours, namely
  `±a x`, `±b y`, `±c z`, the in-plane diagonals `±a x ± b y` and `±2a x`;
- base-centred, `(a, b, c) = (3, 6, 5)`: twelve neighbours, namely `(±a / 2, ±b / 2, 0)`,
  `±a x`, `±c z` and `(±3a / 2, ±b / 2, 0)`;
- body-centred, `(a, b, c) = (2, 7, 5)`: fourteen neighbours, namely the eight
  `(±a / 2, ±b / 2, ±c / 2)`, `±a x`, `±2a x` and `±c z`;
- face-centred, `(a, b, c) = (2, 4, 5)`: eighteen neighbours, namely the twelve face diagonals,
  `±a x` and `(±3a / 2, ±b / 2, 0)`.

As for the cubic lattices, the graph does not depend on the lengths and the embedding does.

## ii. Key results

- `orthorhombic`, `baseCentredOrthorhombic`, `bodyCentredOrthorhombic`,
  `faceCentredOrthorhombic` : the lattices, with one site per cell.
- `baseCentredVectors` : the primitive vectors of the base-centred lattice.
- `orthorhombic_neighbors_card`, `baseCentredOrthorhombic_neighbors_card`,
  `bodyCentredOrthorhombic_neighbors_card`, `faceCentredOrthorhombic_neighbors_card` : the
  coordination numbers `12`, `12`, `14` and `18`.

## iii. Table of contents

- A. Primitive orthorhombic lattice
- B. Base-centred orthorhombic lattice
- C. Body-centred and face-centred orthorhombic lattices
- D. Coordination numbers

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

/-! ## A. Primitive orthorhombic lattice -/

/-- One site per primitive cell of the primitive orthorhombic lattice. -/
@[reducible]
def orthorhombic := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- The bonds of the first shells for `(a, b, c) = (3, 4, 7)`, up to sign: the three axes, the
two in-plane diagonals and twice the shortest axis. -/
def orthorhombicBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩,
    ⟨(), (), ![1, 1, 0]⟩, ⟨(), (), ![1, -1, 0]⟩, ⟨(), (), ![2, 0, 0]⟩]

/-- The twelve-neighbour primitive orthorhombic graph. -/
def orthorhombicGraph : PeriodicGraph orthorhombic := PeriodicGraph.ofBonds orthorhombicBonds

/-! ## B. Base-centred orthorhombic lattice -/

/-- One site per primitive cell of the base-centred orthorhombic lattice. -/
@[reducible]
def baseCentredOrthorhombic := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- Primitive vectors from a corner to the centres of the two adjacent `a`–`b` faces of a box with
sides `a`, `b`, `c` that share an edge along `x`, and along the third axis. -/
noncomputable def baseCentredVectors (a b c : ℝ) : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[a / 2, -b / 2, 0], !₂[a / 2, b / 2, 0], !₂[0, 0, c]]

/-- The primitive vectors of the base-centred lattice are independent for positive lengths. -/
lemma baseCentredVectors_independent {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    LinearIndependent ℝ (baseCentredVectors a b c) := by
  rw [Fintype.linearIndependent_iff]
  intro x h j
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
  simp [baseCentredVectors, Fin.sum_univ_three] at h0 h1 h2
  have e0 : x 0 + x 1 = 0 := (mul_eq_zero.mp (by linear_combination h0 :
    a / 2 * (x 0 + x 1) = 0)).resolve_left (by positivity)
  have e1 : x 1 - x 0 = 0 := (mul_eq_zero.mp (by linear_combination h1 :
    b / 2 * (x 1 - x 0) = 0)).resolve_left (by positivity)
  have e2 : x 2 = 0 := h2.resolve_right hc.ne'
  fin_cases j <;> dsimp <;> linarith

/-- The base-centred orthorhombic lattice embedded with a box of sides `a`, `b`, `c`. -/
noncomputable def baseCentredOrthorhombicGeometry (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) : Geometry baseCentredOrthorhombic (EuclideanSpace ℝ (Fin 3)) :=
  Geometry.ofLattice (latticeMap (baseCentredVectors a b c))
    (latticeMap_injective (baseCentredVectors_independent ha hb hc))

/-- The bonds of the first shells for `(a, b, c) = (3, 6, 5)`, up to sign: the two primitive
vectors in the plane, the third axis, their sum `a x` and the two vectors `(3a / 2, ±b / 2, 0)`. -/
def baseCentredOrthorhombicBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩,
    ⟨(), (), ![1, 1, 0]⟩, ⟨(), (), ![1, 2, 0]⟩, ⟨(), (), ![2, 1, 0]⟩]

/-- The twelve-neighbour base-centred orthorhombic graph. -/
def baseCentredOrthorhombicGraph : PeriodicGraph baseCentredOrthorhombic :=
  PeriodicGraph.ofBonds baseCentredOrthorhombicBonds

/-! ## C. Body-centred and face-centred orthorhombic lattices -/

/-- One site per primitive cell of the body-centred orthorhombic lattice. -/
@[reducible]
def bodyCentredOrthorhombic := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- The bonds of the first shells for `(a, b, c) = (2, 7, 5)` in the basis `bccVectors a b c`,
up to sign: the four body diagonals, `a x`, `2a x` and `c z`. -/
def bodyCentredOrthorhombicBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩, ⟨(), (), ![1, 1, 1]⟩,
    ⟨(), (), ![0, 1, 1]⟩, ⟨(), (), ![0, 2, 2]⟩, ⟨(), (), ![1, 1, 0]⟩]

/-- The fourteen-neighbour body-centred orthorhombic graph, embedded by `bccGeometry a b c`. -/
def bodyCentredOrthorhombicGraph : PeriodicGraph bodyCentredOrthorhombic :=
  PeriodicGraph.ofBonds bodyCentredOrthorhombicBonds

/-- One site per primitive cell of the face-centred orthorhombic lattice. -/
@[reducible]
def faceCentredOrthorhombic := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- The bonds of the first shells for `(a, b, c) = (2, 4, 5)` in the basis `fccVectors a b c`,
up to sign: the six face diagonals, `a x` and the two vectors `(3a / 2, ±b / 2, 0)`. -/
def faceCentredOrthorhombicBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩, ⟨(), (), ![0, 1, -1]⟩,
    ⟨(), (), ![1, -1, 0]⟩, ⟨(), (), ![1, 0, -1]⟩, ⟨(), (), ![1, -1, -1]⟩,
    ⟨(), (), ![1, -1, -2]⟩, ⟨(), (), ![2, -2, -1]⟩]

/-- The eighteen-neighbour face-centred orthorhombic graph, embedded by `fccGeometry a b c`. -/
def faceCentredOrthorhombicGraph : PeriodicGraph faceCentredOrthorhombic :=
  PeriodicGraph.ofBonds faceCentredOrthorhombicBonds

/-! ## D. Coordination numbers -/

/-- Each site of the primitive orthorhombic lattice has twelve neighbours. -/
lemma orthorhombic_neighbors_card (x : orthorhombic.Site) :
    (orthorhombicGraph.neighbors x).card = 12 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (orthorhombicGraph.neighbors ⟨0, ()⟩).card = 12 := by decide
  exact (orthorhombicGraph.card_neighbors_cell n ()).trans h

/-- Each site of the base-centred orthorhombic lattice has twelve neighbours. -/
lemma baseCentredOrthorhombic_neighbors_card (x : baseCentredOrthorhombic.Site) :
    (baseCentredOrthorhombicGraph.neighbors x).card = 12 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (baseCentredOrthorhombicGraph.neighbors ⟨0, ()⟩).card = 12 := by decide
  exact (baseCentredOrthorhombicGraph.card_neighbors_cell n ()).trans h

/-- Each site of the body-centred orthorhombic lattice has fourteen neighbours. -/
lemma bodyCentredOrthorhombic_neighbors_card (x : bodyCentredOrthorhombic.Site) :
    (bodyCentredOrthorhombicGraph.neighbors x).card = 14 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (bodyCentredOrthorhombicGraph.neighbors ⟨0, ()⟩).card = 14 := by decide
  exact (bodyCentredOrthorhombicGraph.card_neighbors_cell n ()).trans h

/-- Each site of the face-centred orthorhombic lattice has eighteen neighbours. -/
lemma faceCentredOrthorhombic_neighbors_card (x : faceCentredOrthorhombic.Site) :
    (faceCentredOrthorhombicGraph.neighbors x).card = 18 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (faceCentredOrthorhombicGraph.neighbors ⟨0, ()⟩).card = 18 := by decide
  exact (faceCentredOrthorhombicGraph.card_neighbors_cell n ()).trans h

end CondensedMatter.Crystal
