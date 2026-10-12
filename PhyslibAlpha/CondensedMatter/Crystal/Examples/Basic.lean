/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Geometry

/-!

# Standard crystals

## i. Overview

These examples specify the same three ingredients: a repeated unit cell, its physical
positions and its bonds. The crystal, geometry and graph remain separately accessible.

The hypercubic lattice has one site per cell in any dimension. The chain and square
lattice are its one- and two-dimensional cases. The triangular lattice has six neighbors
per site. The honeycomb lattice has two sites per cell, each with three neighbors.
Their Euclidean geometries use unit nearest-neighbor spacing.

The finite periodic chain places equally spaced sites on a circle of circumference one.
Its bonds connect consecutive cells modulo the period.

## ii. Key results

- `hypercubic`, `square`, `chain` : one site per cell.
- `triangular`, `honeycomb`, `diamond` : standard lattices with their geometries and bond graphs.
- `periodicChain` : a finite periodic chain.
- `honeycomb_neighbors_card`, `diamond_neighbors_card` : coordination numbers.

## iii. Table of contents

- A. Hypercubic lattices
- B. Triangular lattice
- C. Honeycomb lattice
- D. Diamond lattice
- E. Finite periodic chain
- F. Coordination numbers
- G. Bond lengths

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 4.

-/

@[expose] public section

namespace CondensedMatter.Crystal

/-! ## A. Hypercubic lattices -/

/-- One site per integer-indexed cell in `d` dimensions. -/
@[reducible]
def hypercubic (d : ℕ) := Crystal.ofUnitCell (Fin d → ℤ) Unit

/-- Unit orthogonal cell displacements in Cartesian coordinates. -/
noncomputable def hypercubicDisplacement (d : ℕ) :
    (Fin d → ℤ) →+ EuclideanSpace ℝ (Fin d) :=
  latticeMap (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

/-- The hypercubic lattice embedded with unit spacing along each Cartesian axis. -/
noncomputable def hypercubicGeometry (d : ℕ) : Geometry (hypercubic d) (EuclideanSpace ℝ (Fin d)) :=
  Geometry.ofLattice (hypercubicDisplacement d)
    (latticeMap_injective (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.linearIndependent)

/-- One positive-axis bond for each direction generates all hypercubic connections. -/
def hypercubicBonds (d : ℕ) : List (Bond (Fin d → ℤ) Unit) :=
  List.ofFn (fun j : Fin d => ⟨(), (), Pi.single j 1⟩)

/-- The graph connecting each site to its neighboring cells along the coordinate axes. -/
def hypercubicGraph (d : ℕ) : PeriodicGraph (hypercubic d) :=
  PeriodicGraph.ofBonds (hypercubicBonds d)

/-- The infinite chain with one site per cell. -/
@[reducible]
def chain := hypercubic 1

/-- Unit-spaced positions of the infinite chain. -/
noncomputable def chainGeometry := hypercubicGeometry 1

/-- Consecutive sites of the infinite chain are connected. -/
def chainGraph := hypercubicGraph 1

/-- The square lattice with one site per cell. -/
@[reducible]
def square := hypercubic 2

/-- Cartesian positions of the unit-spaced square lattice. -/
noncomputable def squareGeometry := hypercubicGeometry 2

/-- The four-neighbor square-lattice graph. -/
def squareGraph := hypercubicGraph 2

/-! ## B. Triangular lattice -/

/-- One site per cell of the triangular lattice. -/
@[reducible]
def triangular := Crystal.ofUnitCell (Fin 2 → ℤ) Unit

/-- Unit primitive vectors meeting at an angle of sixty degrees. -/
noncomputable def triangularVectors : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]]

/-- The two primitive translations of the triangular lattice are independent. -/
lemma triangularVectors_independent : LinearIndependent ℝ triangularVectors := by
  rw [Fintype.linearIndependent_iff]
  intro c h j
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
  simp [triangularVectors, Fin.sum_univ_two] at h0 h1
  fin_cases j <;> dsimp <;> simp_all

/-- The triangular lattice embedded with unit bond lengths. -/
noncomputable def triangularGeometry : Geometry triangular (EuclideanSpace ℝ (Fin 2)) :=
  Geometry.ofLattice (latticeMap triangularVectors)
    (latticeMap_injective triangularVectors_independent)

/-- Three cell displacements generate the six triangular-lattice neighbors. -/
def triangularBonds : List (Bond (Fin 2 → ℤ) Unit) :=
  [⟨(), (), ![1, 0]⟩, ⟨(), (), ![0, 1]⟩, ⟨(), (), ![1, -1]⟩]

/-- The six-neighbor triangular-lattice graph. -/
def triangularGraph : PeriodicGraph triangular := PeriodicGraph.ofBonds triangularBonds

/-! ## C. Honeycomb lattice -/

/-- The two sites in a honeycomb unit cell. -/
inductive HoneycombLabel
  /-- The site at the reference-cell origin. -/
  | A
  /-- The site one unit above the reference-cell origin. -/
  | B
  deriving DecidableEq, Repr

instance : Fintype HoneycombLabel where
  elems := {.A, .B}
  complete x := by cases x <;> simp

/-- A honeycomb crystal has two sites per integer-indexed cell. -/
@[reducible]
def honeycomb := Crystal.ofUnitCell (Fin 2 → ℤ) HoneycombLabel

/-- Primitive cell translations for a honeycomb lattice with unit bond lengths. -/
noncomputable def honeycombVectors : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[Real.sqrt 3 / 2, 3 / 2], !₂[-Real.sqrt 3 / 2, 3 / 2]]

/-- The primitive cell translations of the honeycomb lattice are independent. -/
lemma honeycombVectors_independent : LinearIndependent ℝ honeycombVectors := by
  rw [Fintype.linearIndependent_iff]
  intro c h j
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
  simp [honeycombVectors, Fin.sum_univ_two] at h0 h1
  have he : c 0 = c 1 := by
    have hm : (Real.sqrt 3 / 2) * (c 0 - c 1) = 0 := by nlinarith [h0]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (ne_of_gt (by positivity)))
  fin_cases j <;> dsimp <;> linarith

/-- Physical positions of A and B within the reference honeycomb cell. -/
noncomputable def honeycombBasis : HoneycombLabel → EuclideanSpace ℝ (Fin 2)
  | .A => 0
  | .B => !₂[0, 1]

/-- The honeycomb reference positions and their translated copies are all distinct. -/
lemma honeycomb_positions_injective : Function.Injective
    (fun x : CellSite (Fin 2 → ℤ) HoneycombLabel =>
      latticeMap honeycombVectors x.cell + honeycombBasis x.label) := by
  rintro ⟨n, i⟩ ⟨m, j⟩ h
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
  have hinj := latticeMap_injective honeycombVectors_independent
  cases i <;> cases j
  · exact CellSite.ext (hinj (by simpa [honeycombBasis] using h)) rfl
  · simp [latticeMap, honeycombVectors, honeycombBasis, Fin.sum_univ_two] at h0 h1
    have he : (3 : ℤ) * (n 0 - m 0) = 1 := by
      have hs : (Real.sqrt 3 / 2) *
          ((n 0 : ℝ) - m 0 - ((n 1 : ℝ) - m 1)) = 0 := by nlinarith [h0]
      have hn := (mul_eq_zero.mp hs).resolve_left (ne_of_gt (by positivity))
      exact_mod_cast (show (3 : ℝ) * ((n 0 : ℝ) - m 0) = 1 by nlinarith [h1, hn])
    omega
  · simp [latticeMap, honeycombVectors, honeycombBasis, Fin.sum_univ_two] at h0 h1
    have he : (3 : ℤ) * (n 0 - m 0) = -1 := by
      have hs : (Real.sqrt 3 / 2) *
          ((n 0 : ℝ) - m 0 - ((n 1 : ℝ) - m 1)) = 0 := by nlinarith [h0]
      have hn := (mul_eq_zero.mp hs).resolve_left (ne_of_gt (by positivity))
      exact_mod_cast (show (3 : ℝ) * ((n 0 : ℝ) - m 0) = -1 by nlinarith [h1, hn])
    omega
  · exact CellSite.ext (hinj (by simpa [honeycombBasis] using h)) rfl

/-- The honeycomb crystal embedded with distinct A and B sites and unit bond spacing. -/
noncomputable def honeycombGeometry : Geometry honeycomb (EuclideanSpace ℝ (Fin 2)) :=
  Geometry.ofDisplacements (latticeMap honeycombVectors) honeycombBasis
    honeycomb_positions_injective

/-- Each A site connects to B in its own cell and in two adjacent cells. -/
def honeycombBonds : List (Bond (Fin 2 → ℤ) HoneycombLabel) :=
  [⟨.A, .B, 0⟩, ⟨.A, .B, ![-1, 0]⟩, ⟨.A, .B, ![0, -1]⟩]

/-- The three-neighbor honeycomb graph. -/
def honeycombGraph : PeriodicGraph honeycomb := PeriodicGraph.ofBonds honeycombBonds

/-! ## D. Diamond lattice -/

/-- The two atoms in a diamond unit cell. -/
inductive DiamondLabel
  /-- The atom at the reference-cell origin. -/
  | A
  /-- The atom displaced by a quarter of the body diagonal of the cubic cell. -/
  | B
  deriving DecidableEq, Repr

instance : Fintype DiamondLabel where
  elems := {.A, .B}
  complete x := by cases x <;> simp

/-- A diamond crystal has two atoms per integer-indexed cell of its face-centered cubic lattice. -/
@[reducible]
def diamond := Crystal.ofUnitCell (Fin 3 → ℤ) DiamondLabel

/-- Primitive translations of the face-centered cubic lattice, in units of the cubic lattice
constant. -/
noncomputable def diamondVectors : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[0, 1 / 2, 1 / 2], !₂[1 / 2, 0, 1 / 2], !₂[1 / 2, 1 / 2, 0]]

/-- The primitive translations of the face-centered cubic lattice are independent. -/
lemma diamondVectors_independent : LinearIndependent ℝ diamondVectors := by
  rw [Fintype.linearIndependent_iff]
  intro c h j
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
  simp [diamondVectors, Fin.sum_univ_three] at h0 h1 h2
  fin_cases j <;> dsimp <;> linarith

/-- Physical positions of the two atoms within the reference diamond cell. -/
noncomputable def diamondBasis : DiamondLabel → EuclideanSpace ℝ (Fin 3)
  | .A => 0
  | .B => !₂[1 / 4, 1 / 4, 1 / 4]

/-- The positions of the two diamond sublattices are distinct, and so are all translated copies. -/
lemma diamond_positions_injective : Function.Injective
    (fun x : CellSite (Fin 3 → ℤ) DiamondLabel =>
      latticeMap diamondVectors x.cell + diamondBasis x.label) := by
  rintro ⟨n, i⟩ ⟨m, j⟩ h
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
  have hinj := latticeMap_injective diamondVectors_independent
  cases i <;> cases j
  · exact CellSite.ext (hinj (by simpa [diamondBasis] using h)) rfl
  · simp [latticeMap, diamondVectors, diamondBasis, Fin.sum_univ_three] at h0
    have : (2 : ℝ) * ((n 1 - m 1 + (n 2 - m 2) : ℤ) : ℝ) = 1 := by push_cast; linarith
    have : (2 : ℤ) * (n 1 - m 1 + (n 2 - m 2)) = 1 := by exact_mod_cast this
    omega
  · simp [latticeMap, diamondVectors, diamondBasis, Fin.sum_univ_three] at h0
    have : (2 : ℝ) * ((n 1 - m 1 + (n 2 - m 2) : ℤ) : ℝ) = -1 := by push_cast; linarith
    have : (2 : ℤ) * (n 1 - m 1 + (n 2 - m 2)) = -1 := by exact_mod_cast this
    omega
  · exact CellSite.ext (hinj (by simpa [diamondBasis] using h)) rfl

/-- The diamond crystal embedded with distinct atoms in three-dimensional space. -/
noncomputable def diamondGeometry : Geometry diamond (EuclideanSpace ℝ (Fin 3)) :=
  Geometry.ofDisplacements (latticeMap diamondVectors) diamondBasis diamond_positions_injective

/-- Each A atom connects to the B atom of its own cell and of the three cells reached by
subtracting one primitive translation: its four tetrahedral neighbors. -/
def diamondBonds : List (Bond (Fin 3 → ℤ) DiamondLabel) :=
  [⟨.A, .B, 0⟩, ⟨.A, .B, ![-1, 0, 0]⟩, ⟨.A, .B, ![0, -1, 0]⟩, ⟨.A, .B, ![0, 0, -1]⟩]

/-- The four-neighbor tetrahedral diamond graph. -/
def diamondGraph : PeriodicGraph diamond := PeriodicGraph.ofBonds diamondBonds

/-! ## E. Finite periodic chain -/

/-- A finite chain whose cell indices are taken modulo `m`. -/
@[reducible]
def periodicChain (m : ℕ) := Crystal.ofUnitCell (ZMod m) Unit

/-- Equally spaced sites on a circle of circumference one. -/
noncomputable def periodicChainGeometry (m : ℕ) [NeZero m] :
    Geometry (periodicChain m) UnitAddCircle :=
  Geometry.ofLattice ZMod.toAddCircle (ZMod.toAddCircle_injective m)

/-- Connect consecutive cells around the periodic chain. -/
def periodicChainBonds (m : ℕ) : List (Bond (ZMod m) Unit) := [⟨(), (), 1⟩]

/-- The undirected graph of consecutive cells modulo `m`. -/
def periodicChainGraph (m : ℕ) : PeriodicGraph (periodicChain m) :=
  PeriodicGraph.ofBonds (periodicChainBonds m)

/-! ## F. Coordination numbers -/

/-- Each site of the infinite chain has two neighbors. -/
lemma chain_neighbors_card (x : chain.Site) : (chainGraph.neighbors x).card = 2 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (chainGraph.neighbors ⟨0, ()⟩).card = 2 := by decide
  exact (chainGraph.card_neighbors_cell n ()).trans h

/-- Each site of the square lattice has four neighbors. -/
lemma square_neighbors_card (x : square.Site) : (squareGraph.neighbors x).card = 4 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (squareGraph.neighbors ⟨0, ()⟩).card = 4 := by decide
  exact (squareGraph.card_neighbors_cell n ()).trans h

/-- Each site of the triangular lattice has six neighbors. -/
lemma triangular_neighbors_card (x : triangular.Site) : (triangularGraph.neighbors x).card = 6 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (triangularGraph.neighbors ⟨0, ()⟩).card = 6 := by decide
  exact (triangularGraph.card_neighbors_cell n ()).trans h

/-- Both honeycomb site labels have three neighbors in every cell. -/
lemma honeycomb_neighbors_card (x : honeycomb.Site) : (honeycombGraph.neighbors x).card = 3 := by
  rcases x with ⟨n, i⟩
  have h : (honeycombGraph.neighbors ⟨0, i⟩).card = 3 := by cases i <;> decide
  exact (honeycombGraph.card_neighbors_cell n i).trans h

/-- Both diamond site labels have four neighbors in every cell. -/
lemma diamond_neighbors_card (x : diamond.Site) : (diamondGraph.neighbors x).card = 4 := by
  rcases x with ⟨n, i⟩
  have h : (diamondGraph.neighbors ⟨0, i⟩).card = 4 := by cases i <;> decide
  exact (diamondGraph.card_neighbors_cell n i).trans h

/-! ## G. Bond lengths -/

/-- Every hypercubic graph edge has unit physical length, in any dimension. -/
lemma hypercubic_bond_length (d : ℕ) {x y : (hypercubic d).Site}
    (h : (hypercubicGraph d).toSimpleGraph.Adj x y) :
    (hypercubicGeometry d).distance x y = 1 := by
  apply (hypercubicGeometry d).distance_eq_of_adj (hypercubicBonds d) 1 _ h
  intro b hb
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
  change dist (hypercubicDisplacement d 0 + 0)
    (hypercubicDisplacement d (Pi.single j 1) + 0) = 1
  simp [hypercubicDisplacement, latticeMap, Pi.single_apply, dist_zero_left]

/-- All square-lattice graph edges have unit physical length. -/
lemma square_bond_length {x y : square.Site} (h : squareGraph.toSimpleGraph.Adj x y) :
    squareGeometry.distance x y = 1 := hypercubic_bond_length 2 h

/-- All triangular-lattice graph edges have unit physical length. -/
lemma triangular_bond_length {x y : triangular.Site}
    (h : triangularGraph.toSimpleGraph.Adj x y) : triangularGeometry.distance x y = 1 := by
  apply triangularGeometry.distance_eq_of_adj triangularBonds 1 _ h
  intro b hb
  simp only [triangularBonds, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;>
    norm_num [triangularGeometry, Geometry.distance, Geometry.position_ofLattice,
      latticeMap, triangularVectors, EuclideanSpace.dist_eq, Fin.sum_univ_two] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- All honeycomb graph edges have unit physical length. -/
lemma honeycomb_bond_length {x y : honeycomb.Site}
    (h : honeycombGraph.toSimpleGraph.Adj x y) : honeycombGeometry.distance x y = 1 := by
  apply honeycombGeometry.distance_eq_of_adj honeycombBonds 1 _ h
  intro b hb
  simp only [honeycombBonds, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;>
    norm_num [honeycombGeometry, Geometry.distance, Geometry.position_ofDisplacements,
      latticeMap, honeycombVectors, honeycombBasis, EuclideanSpace.dist_eq,
      Fin.sum_univ_two] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

end CondensedMatter.Crystal
