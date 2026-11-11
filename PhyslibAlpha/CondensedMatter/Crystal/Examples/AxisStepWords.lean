/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Examples.ThreeDimensional

/-!

# The nearest neighbours of fcc and bcc are words of axis steps

## i. Overview

The bonds `fccBonds` and `bccBonds` are written in the basis of primitive vectors. In the
coordinates of the box, in units of half its sides, a site of the fcc lattice is a point of `ℤ³`
and a nearest neighbour is the sum of two steps of length one along different axes: a face
diagonal. A nearest neighbour of the bcc lattice is the sum of three steps along the three axes:
a body diagonal. Here the converse: every such sum is a nearest neighbour.

A step along an axis is forward or backward, so there are two steps per axis. Steps along
different axes commute, so the two orders of a pair of steps reach the same site. Each face
diagonal is reached by `2` words of two steps and each body diagonal by `6` words of three steps.

## ii. Key results

- `fccBonds_eq_twoStepWords` : the nearest neighbours of fcc, up to sign, are the sums of two
  steps along different axes.
- `bccBonds_eq_threeStepWords` : the nearest neighbours of bcc, up to sign, are the sums of three
  steps along the three axes.
- `card_twoStepWords_fiber`, `card_threeStepWords_fiber` : each neighbour is reached by exactly
  `2`, respectively `6`, words.

## iii. Table of contents

- A. Axis steps and their words
- B. Coordinates of the box
- C. The neighbours as words

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 4.

-/

@[expose] public section

namespace CondensedMatter.Crystal

/-! ## A. Axis steps and their words -/

/-- The step of length one along the axis `i`, forward or backward. -/
def axisStep (i : Fin 3) (s : Bool) : Fin 3 → ℤ := Pi.single i (if s then 1 else -1)

/-- The words of two steps along different axes. -/
def twoStepWords : Finset ((Fin 3 × Bool) × (Fin 3 × Bool)) :=
  Finset.univ.filter fun w => w.1.1 ≠ w.2.1

/-- The words of three steps along the three different axes. -/
def threeStepWords : Finset ((Fin 3 × Bool) × (Fin 3 × Bool) × (Fin 3 × Bool)) :=
  Finset.univ.filter fun w => w.1.1 ≠ w.2.1.1 ∧ w.1.1 ≠ w.2.2.1 ∧ w.2.1.1 ≠ w.2.2.1

/-- The displacement of a word of two steps. -/
def twoStepSum (w : (Fin 3 × Bool) × (Fin 3 × Bool)) : Fin 3 → ℤ :=
  axisStep w.1.1 w.1.2 + axisStep w.2.1 w.2.2

/-- The displacement of a word of three steps. -/
def threeStepSum (w : (Fin 3 × Bool) × (Fin 3 × Bool) × (Fin 3 × Bool)) : Fin 3 → ℤ :=
  axisStep w.1.1 w.1.2 + axisStep w.2.1.1 w.2.1.2 + axisStep w.2.2.1 w.2.2.2

/-- Steps along different axes commute: both orders of a word of two steps reach the same
site. -/
lemma twoStepSum_swap (w : (Fin 3 × Bool) × (Fin 3 × Bool)) :
    twoStepSum (w.2, w.1) = twoStepSum w := add_comm _ _

/-! ## B. Coordinates of the box -/

/-- The coordinates in the box, in units of half its sides, of the cell `n` of the fcc lattice. -/
def fccCoord (n : Fin 3 → ℤ) : Fin 3 → ℤ := ![n 1 + n 2, n 0 + n 2, n 0 + n 1]

/-- The coordinates in the box, in units of half its sides, of the cell `n` of the bcc lattice. -/
def bccCoord (n : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![-n 0 + n 1 + n 2, n 0 - n 1 + n 2, n 0 + n 1 - n 2]

/-- The displacements of the bonds of a list, with both signs. -/
def signedDisplacements (bonds : List (Bond (Fin 3 → ℤ) Unit)) : Finset (Fin 3 → ℤ) :=
  (bonds.map (·.displacement)).toFinset ∪ (bonds.map (-·.displacement)).toFinset

/-- The physical position of a cell of the fcc lattice is `fccCoord` in units of half the sides
of the box. -/
lemma latticeMap_fccVectors (a b c : ℝ) (n : Fin 3 → ℤ) (k : Fin 3) :
    latticeMap (fccVectors a b c) n k = ![a, b, c] k / 2 * (fccCoord n k : ℝ) := by
  simp only [latticeMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.sum_univ_three, fccVectors,
    fccCoord]
  fin_cases k <;> simp <;> ring

/-- The physical position of a cell of the bcc lattice is `bccCoord` in units of half the sides
of the box. -/
lemma latticeMap_bccVectors (a b c : ℝ) (n : Fin 3 → ℤ) (k : Fin 3) :
    latticeMap (bccVectors a b c) n k = ![a, b, c] k / 2 * (bccCoord n k : ℝ) := by
  simp only [latticeMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.sum_univ_three, bccVectors,
    bccCoord]
  fin_cases k <;> simp <;> ring

/-! ## C. The neighbours as words -/

/-- The nearest neighbours of the fcc lattice, up to sign, are the sums of two steps along
different axes. -/
lemma fccBonds_eq_twoStepWords :
    (signedDisplacements fccBonds).image fccCoord = twoStepWords.image twoStepSum := by
  decide +kernel

/-- The nearest neighbours of the bcc lattice, up to sign, are the sums of three steps along the
three axes. -/
lemma bccBonds_eq_threeStepWords :
    (signedDisplacements bccBonds).image bccCoord = threeStepWords.image threeStepSum := by
  decide +kernel

/-- Each nearest neighbour of the fcc lattice is reached by exactly two words of two steps. -/
lemma card_twoStepWords_fiber :
    ∀ v ∈ twoStepWords.image twoStepSum, (twoStepWords.filter (twoStepSum · = v)).card = 2 := by
  decide +kernel

/-- Each nearest neighbour of the bcc lattice is reached by exactly six words of three steps. -/
lemma card_threeStepWords_fiber :
    ∀ v ∈ threeStepWords.image threeStepSum,
      (threeStepWords.filter (threeStepSum · = v)).card = 6 := by
  decide +kernel

end CondensedMatter.Crystal
