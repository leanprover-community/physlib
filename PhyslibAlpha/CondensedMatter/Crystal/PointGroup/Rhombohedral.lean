/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Orthorhombic
public import PhyslibAlpha.CondensedMatter.Crystal.Examples.Rhombohedral

/-!

# The point group of the rhombohedral lattice

The point group of the rhombohedral lattice has order twelve: it permutes the three primitive
vectors and may reverse all of them, the holohedry `-3m`.

## i. Overview

The admissible triples are located by tests, as for the orthorhombic lattices. A neighbour `a`
goes to a neighbour, and the sums `a + b`, `a + c`, `b + c` and `2a + 2b + c` decide which
triples of neighbours are images of the basis. Exactly twelve triples pass: the six permutations
of the primitive vectors, and the same with all signs reversed. The permutations are the
rotations about the threefold axis `a₁ + a₂ + a₃` and the reflections in the planes through it;
the sign reversal is the inversion.

## ii. Key results

- `rhombohedral_admissible_iff` : the twelve admissible triples.
- `rhombohedral_card_pointGroup` : order `12`.

## iii. Table of contents

- A. The admissible triples
- B. The order

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

open PeriodicGraph

/-! ## A. The admissible triples -/

/-- The images of the basis vectors under the twelve point operations of the rhombohedral
lattice: the permutations of the primitive vectors, with or without the inversion. -/
def rhombohedralPointTriples : Finset (Fin 3 → Fin 3 → ℤ) :=
  {![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![1, 0, 0], ![0, 0, 1], ![0, 1, 0]],
    ![![0, 1, 0], ![1, 0, 0], ![0, 0, 1]], ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]],
    ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]],
    ![![-1, 0, 0], ![0, -1, 0], ![0, 0, -1]], ![![-1, 0, 0], ![0, 0, -1], ![0, -1, 0]],
    ![![0, -1, 0], ![-1, 0, 0], ![0, 0, -1]], ![![0, -1, 0], ![0, 0, -1], ![-1, 0, 0]],
    ![![0, 0, -1], ![-1, 0, 0], ![0, -1, 0]], ![![0, 0, -1], ![0, -1, 0], ![-1, 0, 0]]}

/-- The point operations of the rhombohedral lattice are the twelve of
`rhombohedralPointTriples`. -/
lemma rhombohedral_admissible_iff (v : Fin 3 → Fin 3 → ℤ) :
    Admissible (bondNeighbors rhombohedralBonds) v ↔ v ∈ rhombohedralPointTriples :=
  admissible_iff_of_tests (fun j => by fin_cases j <;> decide) [] [(-1, -1)]
    [![-1, 0, -1], ![0, -1, -1], ![-2, -2, -1]] (by decide +kernel) (by decide +kernel) v

/-! ## B. The order -/

/-- **The point group of the rhombohedral lattice has order `12`.** -/
lemma rhombohedral_card_pointGroup : Nat.card rhombohedralGraph.pointGroup = 12 :=
  (card_pointGroup_ofBonds rhombohedralBonds (fun j => by fin_cases j <;> decide)
    rhombohedral_admissible_iff).trans (by decide)

end CondensedMatter.Crystal
