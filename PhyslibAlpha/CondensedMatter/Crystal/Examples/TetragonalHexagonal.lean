/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Examples.ThreeDimensional

/-!

# Tetragonal and hexagonal lattices

The primitive and body-centred tetragonal lattices and the primitive hexagonal lattice, with
their embeddings and the bonds of their first neighbour shells.

## i. Overview

A tetragonal lattice is a cubic lattice stretched along one axis: the in-plane length `a` and the
period `c` differ. The bonds of the first shell alone do not see this. For the primitive lattice
the six bonds `±x, ±y, ±z` are those of the simple cubic lattice, and for the body-centred
lattice with `c = a √2` the twelve nearest neighbours are those of the face-centred cubic lattice.
A graph with tetragonal symmetry needs the shells up to the first one that tells `z` from `x`:

- primitive tetragonal, `a < c < a √2`: the shells at `a`, `c` and `a √2`, ten neighbours;
- body-centred tetragonal, `a √2 < c < a √6`: the shells at `a`, `√(a² / 2 + c² / 4)` and
  `a √2`, sixteen neighbours.

The primitive hexagonal lattice has six neighbours at `a` in the plane and two at `c` along the
axis. For `c < a √3` these are the first shells, whatever the order of `a` and `c`.

As for the cubic lattices, the graph does not depend on the lengths and the embedding does.

## ii. Key results

- `tetragonal`, `bodyCentredTetragonal`, `hexagonal` : the lattices, with one site per cell.
- `tetragonalGeometry`, `bodyCentredTetragonalGeometry`, `hexagonalGeometry` : their embeddings.
- `tetragonalGraph`, `bodyCentredTetragonalGraph`, `hexagonalGraph` : their bond graphs.
- `tetragonal_neighbors_card`, `bodyCentredTetragonal_neighbors_card`,
  `hexagonal_neighbors_card` : the coordination numbers `10`, `16` and `8`.

## iii. Table of contents

- A. Primitive tetragonal lattice
- B. Body-centred tetragonal lattice
- C. Primitive hexagonal lattice
- D. Coordination numbers

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

/-! ## A. Primitive tetragonal lattice -/

/-- One site per primitive cell of the primitive tetragonal lattice. -/
@[reducible]
def tetragonal := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- The primitive tetragonal lattice embedded with in-plane length `a` and period `c`. -/
noncomputable def tetragonalGeometry (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    Geometry tetragonal (EuclideanSpace ℝ (Fin 3)) :=
  orthorhombicGeometry ![a, a, c] fun i => by fin_cases i <;> simpa

/-- The bonds of the first three shells for `a < c < a √2`, up to sign: the two in-plane axes,
the period, and the two in-plane diagonals. -/
def tetragonalBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩,
    ⟨(), (), ![1, 1, 0]⟩, ⟨(), (), ![1, -1, 0]⟩]

/-- The ten-neighbour primitive tetragonal graph. -/
def tetragonalGraph : PeriodicGraph tetragonal := PeriodicGraph.ofBonds tetragonalBonds

/-! ## B. Body-centred tetragonal lattice -/

/-- One site per primitive cell of the body-centred tetragonal lattice. -/
@[reducible]
def bodyCentredTetragonal := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- The body-centred tetragonal lattice embedded with in-plane length `a` and period `c`, with
the primitive vectors `bccVectors a a c`. -/
noncomputable def bodyCentredTetragonalGeometry (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    Geometry bodyCentredTetragonal (EuclideanSpace ℝ (Fin 3)) :=
  bccGeometry a a c ha ha hc

/-- The bonds of the first three shells for `a √2 < c < a √6`, up to sign: the four body
diagonals, the two in-plane axes and the two in-plane diagonals. In the basis `bccVectors a a c`
the in-plane axes are `![0, 1, 1]` and `![1, 0, 1]`. -/
def bodyCentredTetragonalBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩, ⟨(), (), ![1, 1, 1]⟩,
    ⟨(), (), ![0, 1, 1]⟩, ⟨(), (), ![1, 0, 1]⟩, ⟨(), (), ![1, 1, 2]⟩, ⟨(), (), ![-1, 1, 0]⟩]

/-- The sixteen-neighbour body-centred tetragonal graph. -/
def bodyCentredTetragonalGraph : PeriodicGraph bodyCentredTetragonal :=
  PeriodicGraph.ofBonds bodyCentredTetragonalBonds

/-! ## C. Primitive hexagonal lattice -/

/-- One site per primitive cell of the primitive hexagonal lattice. -/
@[reducible]
def hexagonal := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- The primitive hexagonal lattice embedded with in-plane length `a` and period `c`, with the
primitive vectors `hcpVectors a c`. -/
noncomputable def hexagonalGeometry (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    Geometry hexagonal (EuclideanSpace ℝ (Fin 3)) :=
  Geometry.ofLattice (latticeMap (hcpVectors a c))
    (latticeMap_injective (hcpVectors_independent ha hc))

/-- The bonds of the first shells for `c < a √3`, up to sign: three in the plane, at `120°`
from each other, and the period. -/
def hexagonalBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![1, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩]

/-- The eight-neighbour primitive hexagonal graph. -/
def hexagonalGraph : PeriodicGraph hexagonal := PeriodicGraph.ofBonds hexagonalBonds

/-! ## D. Coordination numbers -/

/-- Each site of the primitive tetragonal lattice has ten neighbours. -/
lemma tetragonal_neighbors_card (x : tetragonal.Site) :
    (tetragonalGraph.neighbors x).card = 10 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (tetragonalGraph.neighbors ⟨0, ()⟩).card = 10 := by decide
  exact (tetragonalGraph.card_neighbors_cell n ()).trans h

/-- Each site of the body-centred tetragonal lattice has sixteen neighbours. -/
lemma bodyCentredTetragonal_neighbors_card (x : bodyCentredTetragonal.Site) :
    (bodyCentredTetragonalGraph.neighbors x).card = 16 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (bodyCentredTetragonalGraph.neighbors ⟨0, ()⟩).card = 16 := by decide
  exact (bodyCentredTetragonalGraph.card_neighbors_cell n ()).trans h

/-- Each site of the primitive hexagonal lattice has eight neighbours. -/
lemma hexagonal_neighbors_card (x : hexagonal.Site) :
    (hexagonalGraph.neighbors x).card = 8 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (hexagonalGraph.neighbors ⟨0, ()⟩).card = 8 := by decide
  exact (hexagonalGraph.card_neighbors_cell n ()).trans h

end CondensedMatter.Crystal
