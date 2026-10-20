/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Examples.ThreeDimensional

/-!

# Monoclinic and triclinic lattices

The primitive and base-centred monoclinic lattices and the triclinic lattice, with their
embeddings and the bonds of their first neighbour shells.

## i. Overview

A monoclinic lattice has two axes `a = (a, 0, 0)` and `b = (0, b, 0)` and a third axis
`c = (c₁, 0, c₃)` in the plane of `a` and perpendicular to `b`, at an angle `β ≠ π / 2` with
`a`. The base-centred lattice adds the centres of the `a`–`b` faces. A triclinic lattice has
three axes with no relation between their lengths and angles. Here they are
`(a, 0, 0)`, `(b₁, b₂, 0)`, `(c₁, c₂, c₃)`. As for the orthorhombic lattices, the first shell
alone sees more symmetry than the lattice, and the graph keeps the shells up to the first ones
that pin the point group down. With the lengths below these are:

- primitive monoclinic, `a = 3`, `b = 5`, `c = (1, 0, 3)`: twenty neighbours, the shells at
  squared lengths `9, 10, 13, 25, 34, 35`;
- base-centred monoclinic, `a = 4`, `b = 2`, `c = (1, 0, 3)`: sixteen neighbours, the shells at
  squared lengths `4, 5, 10, 11, 13`;
- triclinic, `(3, 0, 0)`, `(1, 4, 0)`, `(1, 1, 5)`: sixteen neighbours, the shells at squared
  lengths `9, 17, 20, 27, 30, 32, 34, 36`.

## ii. Key results

- `monoclinic`, `baseCentredMonoclinic`, `triclinic` : the lattices, with one site per cell.
- `monoclinicVectors`, `baseCentredMonoclinicVectors`, `triclinicVectors` : primitive vectors.
- `monoclinic_neighbors_card`, `baseCentredMonoclinic_neighbors_card`,
  `triclinic_neighbors_card` : the coordination numbers `20`, `16` and `16`.

## iii. Table of contents

- A. Primitive monoclinic lattice
- B. Base-centred monoclinic lattice
- C. Triclinic lattice
- D. Coordination numbers

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

/-! ## A. Primitive monoclinic lattice -/

/-- One site per primitive cell of the primitive monoclinic lattice. -/
@[reducible]
def monoclinic := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- The primitive vectors `(a, 0, 0)`, `(0, b, 0)` and `(c₁, 0, c₃)`. -/
noncomputable def monoclinicVectors (a b c₁ c₃ : ℝ) : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[a, 0, 0], !₂[0, b, 0], !₂[c₁, 0, c₃]]

/-- The primitive vectors are independent for nonzero `a`, `b` and `c₃`. -/
lemma monoclinicVectors_independent {a b c₁ c₃ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c₃ ≠ 0) :
    LinearIndependent ℝ (monoclinicVectors a b c₁ c₃) := by
  rw [Fintype.linearIndependent_iff]
  intro x h j
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
  simp [monoclinicVectors, Fin.sum_univ_three] at h0 h1 h2
  have e2 : x 2 = 0 := h2.resolve_right hc
  have e1 : x 1 = 0 := h1.resolve_right hb
  have e0 : x 0 = 0 := by
    rw [e2, zero_mul, add_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_right ha
  fin_cases j <;> assumption

/-- The bonds of the first shells for `a = 3`, `b = 5`, `c = (1, 0, 3)`, up to sign. -/
def monoclinicBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩,
    ⟨(), (), ![1, 0, 1]⟩, ⟨(), (), ![1, 0, -1]⟩, ⟨(), (), ![2, 0, -1]⟩,
    ⟨(), (), ![1, 1, 0]⟩, ⟨(), (), ![1, -1, 0]⟩, ⟨(), (), ![0, 1, 1]⟩,
    ⟨(), (), ![0, 1, -1]⟩]

/-- The twenty-neighbour primitive monoclinic graph. -/
def monoclinicGraph : PeriodicGraph monoclinic := PeriodicGraph.ofBonds monoclinicBonds

/-! ## B. Base-centred monoclinic lattice -/

/-- One site per primitive cell of the base-centred monoclinic lattice. -/
@[reducible]
def baseCentredMonoclinic := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- The primitive vectors `(a / 2, -b / 2, 0)`, `(a / 2, b / 2, 0)` and `(c₁, 0, c₃)`. -/
noncomputable def baseCentredMonoclinicVectors (a b c₁ c₃ : ℝ) :
    Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[a / 2, -b / 2, 0], !₂[a / 2, b / 2, 0], !₂[c₁, 0, c₃]]

/-- The primitive vectors are independent for nonzero `a`, `b` and `c₃`. -/
lemma baseCentredMonoclinicVectors_independent {a b c₁ c₃ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c₃ ≠ 0) : LinearIndependent ℝ (baseCentredMonoclinicVectors a b c₁ c₃) := by
  rw [Fintype.linearIndependent_iff]
  intro x h j
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
  simp [baseCentredMonoclinicVectors, Fin.sum_univ_three] at h0 h1 h2
  have e2 : x 2 = 0 := h2.resolve_right hc
  rw [e2, zero_mul, add_zero] at h0
  have e0 : x 0 + x 1 = 0 := (mul_eq_zero.mp (by linear_combination h0 :
    a / 2 * (x 0 + x 1) = 0)).resolve_left (div_ne_zero ha two_ne_zero)
  have e1 : x 1 - x 0 = 0 := (mul_eq_zero.mp (by linear_combination h1 :
    b / 2 * (x 1 - x 0) = 0)).resolve_left (div_ne_zero hb two_ne_zero)
  fin_cases j <;> dsimp <;> linarith

/-- The bonds of the first shells for `a = 4`, `b = 2`, `c = (1, 0, 3)`, up to sign, in the
basis `baseCentredMonoclinicVectors`. -/
def baseCentredMonoclinicBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩,
    ⟨(), (), ![1, -1, 0]⟩, ⟨(), (), ![2, -1, 0]⟩, ⟨(), (), ![1, -2, 0]⟩,
    ⟨(), (), ![1, 0, -1]⟩, ⟨(), (), ![0, 1, -1]⟩]

/-- The sixteen-neighbour base-centred monoclinic graph. -/
def baseCentredMonoclinicGraph : PeriodicGraph baseCentredMonoclinic :=
  PeriodicGraph.ofBonds baseCentredMonoclinicBonds

/-! ## C. Triclinic lattice -/

/-- One site per primitive cell of the triclinic lattice. -/
@[reducible]
def triclinic := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- The primitive vectors `(a, 0, 0)`, `(b₁, b₂, 0)` and `(c₁, c₂, c₃)`. -/
noncomputable def triclinicVectors (a b₁ b₂ c₁ c₂ c₃ : ℝ) : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[a, 0, 0], !₂[b₁, b₂, 0], !₂[c₁, c₂, c₃]]

/-- The primitive vectors are independent for nonzero `a`, `b₂` and `c₃`. -/
lemma triclinicVectors_independent {a b₁ b₂ c₁ c₂ c₃ : ℝ} (ha : a ≠ 0) (hb : b₂ ≠ 0)
    (hc : c₃ ≠ 0) : LinearIndependent ℝ (triclinicVectors a b₁ b₂ c₁ c₂ c₃) := by
  rw [Fintype.linearIndependent_iff]
  intro x h j
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
  simp [triclinicVectors, Fin.sum_univ_three] at h0 h1 h2
  have e2 : x 2 = 0 := h2.resolve_right hc
  have e1 : x 1 = 0 := by
    rw [e2, zero_mul, add_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right hb
  have e0 : x 0 = 0 := by
    rw [e1, e2, zero_mul, zero_mul, add_zero, add_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_right ha
  fin_cases j <;> assumption

/-- The bonds of the first shells for `(3, 0, 0)`, `(1, 4, 0)`, `(1, 1, 5)`, up to sign. -/
def triclinicBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩,
    ⟨(), (), ![2, 0, 0]⟩, ⟨(), (), ![1, 1, 0]⟩, ⟨(), (), ![1, -1, 0]⟩,
    ⟨(), (), ![1, 0, -1]⟩, ⟨(), (), ![0, 1, -1]⟩]

/-- The sixteen-neighbour triclinic graph. -/
def triclinicGraph : PeriodicGraph triclinic := PeriodicGraph.ofBonds triclinicBonds

/-! ## D. Coordination numbers -/

/-- Each site of the primitive monoclinic lattice has twenty neighbours. -/
lemma monoclinic_neighbors_card (x : monoclinic.Site) :
    (monoclinicGraph.neighbors x).card = 20 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (monoclinicGraph.neighbors ⟨0, ()⟩).card = 20 := by decide
  exact (monoclinicGraph.card_neighbors_cell n ()).trans h

/-- Each site of the base-centred monoclinic lattice has sixteen neighbours. -/
lemma baseCentredMonoclinic_neighbors_card (x : baseCentredMonoclinic.Site) :
    (baseCentredMonoclinicGraph.neighbors x).card = 16 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (baseCentredMonoclinicGraph.neighbors ⟨0, ()⟩).card = 16 := by decide
  exact (baseCentredMonoclinicGraph.card_neighbors_cell n ()).trans h

/-- Each site of the triclinic lattice has sixteen neighbours. -/
lemma triclinic_neighbors_card (x : triclinic.Site) :
    (triclinicGraph.neighbors x).card = 16 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (triclinicGraph.neighbors ⟨0, ()⟩).card = 16 := by decide
  exact (triclinicGraph.card_neighbors_cell n ()).trans h

end CondensedMatter.Crystal
