/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Orthorhombic
public import PhyslibAlpha.CondensedMatter.Crystal.Examples.Monoclinic

/-!

# The point groups of the monoclinic and triclinic lattices

The point groups of the two monoclinic lattices have order four, the holohedry `2/m`, and the
point group of the triclinic lattice has order two, the holohedry `-1`.

## i. Overview

The admissible triples are located by tests, as for the orthorhombic lattices. For the primitive
monoclinic lattice the four point operations are the identity, the reflection `b ↦ -b` in the
plane of `a` and `c`, the rotation by `π` about `b`, and the inversion. For the base-centred
lattice the reflection exchanges the two primitive vectors in the `a`–`b` plane. The triclinic
lattice keeps only the identity and the inversion, the symmetry of every lattice.

## ii. Key results

- `monoclinic_admissible_iff`, `baseCentredMonoclinic_admissible_iff`,
  `triclinic_admissible_iff` : the admissible triples.
- `monoclinic_card_pointGroup`, `baseCentredMonoclinic_card_pointGroup` : order `4`.
- `triclinic_card_pointGroup` : order `2`.

## iii. Table of contents

- A. The admissible triples
- B. The orders

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

open PeriodicGraph

/-! ## A. The admissible triples -/

/-- The four point operations of the primitive monoclinic lattice: the identity, the reflection
`b ↦ -b`, the rotation by `π` about `b` and the inversion. -/
def monoclinicPointTriples : Finset (Fin 3 → Fin 3 → ℤ) :=
  {![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![1, 0, 0], ![0, -1, 0], ![0, 0, 1]],
    ![![-1, 0, 0], ![0, 1, 0], ![0, 0, -1]], ![![-1, 0, 0], ![0, -1, 0], ![0, 0, -1]]}

/-- The point operations of the primitive monoclinic lattice are the four of
`monoclinicPointTriples`. -/
lemma monoclinic_admissible_iff (v : Fin 3 → Fin 3 → ℤ) :
    Admissible (bondNeighbors monoclinicBonds) v ↔ v ∈ monoclinicPointTriples :=
  admissible_iff_of_tests (fun j => by fin_cases j <;> decide) [] [(-1, 1), (-2, 1)]
    [![-2, 0, 1], ![-1, 0, -1], ![0, -1, -1]] (by decide +kernel) (by decide +kernel) v

/-- The four point operations of the base-centred monoclinic lattice, in the basis
`baseCentredMonoclinicVectors`. -/
def baseCentredMonoclinicPointTriples : Finset (Fin 3 → Fin 3 → ℤ) :=
  {![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![0, 1, 0], ![1, 0, 0], ![0, 0, 1]],
    ![![0, -1, 0], ![-1, 0, 0], ![0, 0, -1]], ![![-1, 0, 0], ![0, -1, 0], ![0, 0, -1]]}

/-- The point operations of the base-centred monoclinic lattice are the four of
`baseCentredMonoclinicPointTriples`. -/
lemma baseCentredMonoclinic_admissible_iff (v : Fin 3 → Fin 3 → ℤ) :
    Admissible (bondNeighbors baseCentredMonoclinicBonds) v ↔
      v ∈ baseCentredMonoclinicPointTriples :=
  admissible_iff_of_tests (fun j => by fin_cases j <;> decide) [] [(-2, 1), (-1, 2)]
    [![0, -1, 1], ![-1, 1, -1], ![-1, 0, -1]] (by decide +kernel) (by decide +kernel) v

/-- The two point operations of the triclinic lattice: the identity and the inversion. -/
def triclinicPointTriples : Finset (Fin 3 → Fin 3 → ℤ) :=
  {![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-1, 0, 0], ![0, -1, 0], ![0, 0, -1]]}

/-- The point operations of the triclinic lattice are the identity and the inversion. -/
lemma triclinic_admissible_iff (v : Fin 3 → Fin 3 → ℤ) :
    Admissible (bondNeighbors triclinicBonds) v ↔ v ∈ triclinicPointTriples :=
  admissible_iff_of_tests (fun j => by fin_cases j <;> decide) [-2] [(-1, -1)]
    [![0, -1, 1], ![-1, -1, 1], ![-1, 1, -1], ![-1, 0, -1]] (by decide +kernel)
    (by decide +kernel) v

/-! ## B. The orders -/

/-- **The point group of the primitive monoclinic lattice has order `4`.** -/
lemma monoclinic_card_pointGroup : Nat.card monoclinicGraph.pointGroup = 4 :=
  (card_pointGroup_ofBonds monoclinicBonds (fun j => by fin_cases j <;> decide)
    monoclinic_admissible_iff).trans (by decide)

/-- **The point group of the base-centred monoclinic lattice has order `4`.** -/
lemma baseCentredMonoclinic_card_pointGroup :
    Nat.card baseCentredMonoclinicGraph.pointGroup = 4 :=
  (card_pointGroup_ofBonds baseCentredMonoclinicBonds (fun j => by fin_cases j <;> decide)
    baseCentredMonoclinic_admissible_iff).trans (by decide)

/-- **The point group of the triclinic lattice has order `2`.** -/
lemma triclinic_card_pointGroup : Nat.card triclinicGraph.pointGroup = 2 :=
  (card_pointGroup_ofBonds triclinicBonds (fun j => by fin_cases j <;> decide)
    triclinic_admissible_iff).trans (by decide)

end CondensedMatter.Crystal
