/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Examples.Basic

/-!

# Orthorhombic, cubic and hexagonal close-packed crystals

The orthorhombic lattice and the face-centred cubic, body-centred cubic and hexagonal
close-packed crystals, with embeddings that allow different lengths along the coordinate axes.

## i. Overview

A cubic lattice has one length, the lattice constant. Stretching the three axes independently
gives the orthorhombic lattice with lengths `a`, `b`, `c`. The face-centred cubic (fcc) lattice
has one site per primitive cell, with primitive vectors from a corner of the conventional cell to
the centres of the three adjacent faces. Each site has twelve nearest neighbours. The body-centred
cubic (bcc) lattice has one site per primitive cell, with primitive vectors from a corner to the
centres of three conventional cells, and eight nearest neighbours. The hexagonal close-packed
(hcp) crystal has two sites per primitive cell, on two interpenetrating hexagonal lattices, and
twelve nearest neighbours for the ideal ratio `c / a = √(8 / 3)`.

Each crystal is a graph, given by the bonds of its nearest neighbours, together with an embedding
in three-dimensional space. The graph does not depend on the lengths. The embedding depends on
`a`, `b` and `c` in the cubic cases, and on `a` and `c` for hcp, and any positive values give an
embedding in which distinct sites have distinct positions. Only for the cubic values `a = b = c`
and the ideal ratio do all bonds of the graph have equal length, so that the graph is the
nearest-neighbour graph of the embedding.

## ii. Key results

- `orthorhombicGeometry` : the hypercubic crystal with a separate length for each axis.
- `fcc`, `bcc`, `hcp` : the crystals, with `fccGraph`, `bccGraph`, `hcpGraph` their bond graphs.
- `fccGeometry`, `bccGeometry`, `hcpGeometry` : their embeddings with free lengths.
- `fcc_neighbors_card`, `bcc_neighbors_card`, `hcp_neighbors_card` : the coordination numbers
  `12`, `8` and `12`.
- `fcc_bond_length`, `bcc_bond_length`, `hcp_bond_length` : bond lengths of the cubic and ideal
  lattices.

## iii. Table of contents

- A. Orthorhombic lattices
- B. Face-centred cubic lattice
- C. Body-centred cubic lattice
- D. Hexagonal close-packed crystal
- E. Coordination numbers
- F. Bond lengths

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 4.

-/

@[expose] public section

namespace CondensedMatter.Crystal

/-! ## A. Orthorhombic lattices -/

/-- The primitive vectors of an orthorhombic lattice: `l i` along the `i`-th coordinate axis. -/
noncomputable def orthorhombicVectors {d : ℕ} (l : Fin d → ℝ) : Fin d → EuclideanSpace ℝ (Fin d) :=
  fun i => l i • EuclideanSpace.single i 1

/-- The primitive vectors of an orthorhombic lattice are independent when no length vanishes. -/
lemma orthorhombicVectors_independent {d : ℕ} {l : Fin d → ℝ} (hl : ∀ i, 0 < l i) :
    LinearIndependent ℝ (orthorhombicVectors l) := by
  rw [Fintype.linearIndependent_iff]
  intro c h j
  have := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v j) h
  simp [orthorhombicVectors, Pi.single_apply, (hl j).ne'] at this
  exact this

/-- The hypercubic crystal embedded with the length `l i` along the `i`-th axis. -/
noncomputable def orthorhombicGeometry {d : ℕ} (l : Fin d → ℝ) (hl : ∀ i, 0 < l i) :
    Geometry (hypercubic d) (EuclideanSpace ℝ (Fin d)) :=
  Geometry.ofLattice (latticeMap (orthorhombicVectors l))
    (latticeMap_injective (orthorhombicVectors_independent hl))

/-! ## B. Face-centred cubic lattice -/

/-- One site per primitive cell of the face-centred cubic lattice. -/
@[reducible]
def fcc := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- Primitive vectors from a corner to the centres of the three adjacent faces of a box with
sides `a`, `b`, `c`. -/
noncomputable def fccVectors (a b c : ℝ) : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[0, b / 2, c / 2], !₂[a / 2, 0, c / 2], !₂[a / 2, b / 2, 0]]

/-- The primitive vectors of the face-centred lattice are independent for positive lengths. -/
lemma fccVectors_independent {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    LinearIndependent ℝ (fccVectors a b c) := by
  rw [Fintype.linearIndependent_iff]
  intro x h j
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
  simp [fccVectors, Fin.sum_univ_three] at h0 h1 h2
  have e0 : x 1 + x 2 = 0 := (mul_eq_zero.mp (by linear_combination h0 :
    a / 2 * (x 1 + x 2) = 0)).resolve_left (by positivity)
  have e1 : x 0 + x 2 = 0 := (mul_eq_zero.mp (by linear_combination h1 :
    b / 2 * (x 0 + x 2) = 0)).resolve_left (by positivity)
  have e2 : x 0 + x 1 = 0 := (mul_eq_zero.mp (by linear_combination h2 :
    c / 2 * (x 0 + x 1) = 0)).resolve_left (by positivity)
  fin_cases j <;> dsimp <;> linarith

/-- The face-centred cubic lattice embedded with a box of sides `a`, `b`, `c`. -/
noncomputable def fccGeometry (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Geometry fcc (EuclideanSpace ℝ (Fin 3)) :=
  Geometry.ofLattice (latticeMap (fccVectors a b c))
    (latticeMap_injective (fccVectors_independent ha hb hc))

/-- The twelve nearest neighbours, up to sign: along the three primitive vectors and along their
differences. -/
def fccBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩,
    ⟨(), (), ![1, -1, 0]⟩, ⟨(), (), ![0, 1, -1]⟩, ⟨(), (), ![-1, 0, 1]⟩]

/-- The twelve-neighbour face-centred cubic graph. -/
def fccGraph : PeriodicGraph fcc := PeriodicGraph.ofBonds fccBonds

/-! ## C. Body-centred cubic lattice -/

/-- One site per primitive cell of the body-centred cubic lattice. -/
@[reducible]
def bcc := Crystal.ofUnitCell (Fin 3 → ℤ) Unit

/-- Primitive vectors from a corner to the centres of three adjacent boxes of sides `a`, `b`,
`c`. -/
noncomputable def bccVectors (a b c : ℝ) : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[-a / 2, b / 2, c / 2], !₂[a / 2, -b / 2, c / 2], !₂[a / 2, b / 2, -c / 2]]

/-- The primitive vectors of the body-centred lattice are independent for positive lengths. -/
lemma bccVectors_independent {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    LinearIndependent ℝ (bccVectors a b c) := by
  rw [Fintype.linearIndependent_iff]
  intro x h j
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
  simp [bccVectors, Fin.sum_univ_three] at h0 h1 h2
  have e0 : -x 0 + x 1 + x 2 = 0 := (mul_eq_zero.mp (by linear_combination h0 :
    a / 2 * (-x 0 + x 1 + x 2) = 0)).resolve_left (by positivity)
  have e1 : x 0 - x 1 + x 2 = 0 := (mul_eq_zero.mp (by linear_combination h1 :
    b / 2 * (x 0 - x 1 + x 2) = 0)).resolve_left (by positivity)
  have e2 : x 0 + x 1 - x 2 = 0 := (mul_eq_zero.mp (by linear_combination h2 :
    c / 2 * (x 0 + x 1 - x 2) = 0)).resolve_left (by positivity)
  fin_cases j <;> dsimp <;> linarith

/-- The body-centred cubic lattice embedded with a box of sides `a`, `b`, `c`. -/
noncomputable def bccGeometry (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Geometry bcc (EuclideanSpace ℝ (Fin 3)) :=
  Geometry.ofLattice (latticeMap (bccVectors a b c))
    (latticeMap_injective (bccVectors_independent ha hb hc))

/-- The eight nearest neighbours, up to sign: along the three primitive vectors and along their
sum, the body diagonal of the box. -/
def bccBonds : List (Bond (Fin 3 → ℤ) Unit) :=
  [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩, ⟨(), (), ![1, 1, 1]⟩]

/-- The eight-neighbour body-centred cubic graph. -/
def bccGraph : PeriodicGraph bcc := PeriodicGraph.ofBonds bccBonds

/-! ## D. Hexagonal close-packed crystal -/

/-- The two layers of an hcp crystal: the sites of the second layer are shifted within the plane
and raised by half a period. -/
inductive HcpLabel
  /-- The site at the origin of the cell. -/
  | A
  /-- The site of the other layer. -/
  | B
  deriving DecidableEq, Repr

instance : Fintype HcpLabel where
  elems := {.A, .B}
  complete x := by cases x <;> simp

/-- Two sites per primitive cell of the hexagonal close-packed crystal. -/
@[reducible]
def hcp := Crystal.ofUnitCell (Fin 3 → ℤ) HcpLabel

/-- Primitive vectors of the hexagonal lattice with in-plane length `a` and period `c`. -/
noncomputable def hcpVectors (a c : ℝ) : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[a, 0, 0], !₂[-a / 2, a * Real.sqrt 3 / 2, 0], !₂[0, 0, c]]

/-- The primitive vectors of the hexagonal lattice are independent for positive lengths. -/
lemma hcpVectors_independent {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    LinearIndependent ℝ (hcpVectors a c) := by
  rw [Fintype.linearIndependent_iff]
  intro x h j
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
  simp [hcpVectors, Fin.sum_univ_three] at h0 h1 h2
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have e1 : x 1 = 0 := h1.resolve_right ha.ne'
  have e0 : x 0 = 0 := by
    have : a * x 0 = 0 := by rw [e1] at h0; linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left ha.ne'
  have e2 : x 2 = 0 := h2.resolve_right hc.ne'
  fin_cases j <;> assumption

/-- Positions of the two sites in the reference cell. -/
noncomputable def hcpBasis (a c : ℝ) : HcpLabel → EuclideanSpace ℝ (Fin 3)
  | .A => 0
  | .B => !₂[a / 2, a * Real.sqrt 3 / 6, c / 2]

/-- The two layers occupy distinct positions. -/
lemma hcp_positions_injective {a c : ℝ} (ha : 0 < a) (hc : 0 < c) : Function.Injective
    (fun x : CellSite (Fin 3 → ℤ) HcpLabel =>
      latticeMap (hcpVectors a c) x.cell + hcpBasis a c x.label) := by
  rintro ⟨n, i⟩ ⟨m, j⟩ h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
  have hinj := latticeMap_injective (hcpVectors_independent ha hc)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  cases i <;> cases j
  · exact CellSite.ext (hinj (by simpa [hcpBasis] using h)) rfl
  · simp [latticeMap, hcpVectors, hcpBasis, Fin.sum_univ_three] at h1
    have hs : a * Real.sqrt 3 / 6 * (3 * ((n 1 : ℝ) - m 1) - 1) = 0 := by linear_combination h1
    have := (mul_eq_zero.mp hs).resolve_left (by positivity)
    have h4 : (3 : ℤ) * (n 1 - m 1) = 1 := by exact_mod_cast (by linarith : 3 *
      ((n 1 : ℝ) - m 1) = 1)
    omega
  · simp [latticeMap, hcpVectors, hcpBasis, Fin.sum_univ_three] at h1
    have hs : a * Real.sqrt 3 / 6 * (3 * ((m 1 : ℝ) - n 1) - 1) = 0 := by linear_combination -h1
    have := (mul_eq_zero.mp hs).resolve_left (by positivity)
    have h4 : (3 : ℤ) * (m 1 - n 1) = 1 := by exact_mod_cast (by linarith : 3 *
      ((m 1 : ℝ) - n 1) = 1)
    omega
  · exact CellSite.ext (hinj (by simpa [hcpBasis] using h)) rfl

/-- The hexagonal close-packed crystal with in-plane length `a` and layer period `c`. -/
noncomputable def hcpGeometry (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    Geometry hcp (EuclideanSpace ℝ (Fin 3)) :=
  Geometry.ofDisplacements (latticeMap (hcpVectors a c)) (hcpBasis a c)
    (hcp_positions_injective ha hc)

/-- The nearest neighbours: six in the plane of each layer, and three in each adjacent layer. -/
def hcpBonds : List (Bond (Fin 3 → ℤ) HcpLabel) :=
  [⟨.A, .A, ![1, 0, 0]⟩, ⟨.A, .A, ![0, 1, 0]⟩, ⟨.A, .A, ![1, 1, 0]⟩,
    ⟨.B, .B, ![1, 0, 0]⟩, ⟨.B, .B, ![0, 1, 0]⟩, ⟨.B, .B, ![1, 1, 0]⟩,
    ⟨.A, .B, 0⟩, ⟨.A, .B, ![-1, 0, 0]⟩, ⟨.A, .B, ![-1, -1, 0]⟩,
    ⟨.A, .B, ![0, 0, -1]⟩, ⟨.A, .B, ![-1, 0, -1]⟩, ⟨.A, .B, ![-1, -1, -1]⟩]

/-- The twelve-neighbour hexagonal close-packed graph. -/
def hcpGraph : PeriodicGraph hcp := PeriodicGraph.ofBonds hcpBonds

/-! ## E. Coordination numbers -/

/-- Each site of the face-centred cubic lattice has twelve neighbours. -/
lemma fcc_neighbors_card (x : fcc.Site) : (fccGraph.neighbors x).card = 12 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (fccGraph.neighbors ⟨0, ()⟩).card = 12 := by decide
  exact (fccGraph.card_neighbors_cell n ()).trans h

/-- Each site of the body-centred cubic lattice has eight neighbours. -/
lemma bcc_neighbors_card (x : bcc.Site) : (bccGraph.neighbors x).card = 8 := by
  rcases x with ⟨n, i⟩
  cases i
  have h : (bccGraph.neighbors ⟨0, ()⟩).card = 8 := by decide
  exact (bccGraph.card_neighbors_cell n ()).trans h

/-- Both sites of the hexagonal close-packed crystal have twelve neighbours. -/
lemma hcp_neighbors_card (x : hcp.Site) : (hcpGraph.neighbors x).card = 12 := by
  rcases x with ⟨n, i⟩
  have h : (hcpGraph.neighbors ⟨0, i⟩).card = 12 := by
    rw [hcpGraph, PeriodicGraph.neighbors_ofBonds]
    cases i <;> simp [hcpBonds, neighborsFromBonds, bondEndpoints, Bond.endpoints] <;> decide
  exact (hcpGraph.card_neighbors_cell n i).trans h


/-! ## F. Bond lengths -/

private lemma sqrt_eq_of_eq_sq {s L : ℝ} (hL : 0 ≤ L) (h : s = L ^ 2) : Real.sqrt s = L := by
  rw [h]
  exact Real.sqrt_sq hL

/-- In the face-centred cubic lattice with cube side `a`, every edge has length `a √2 / 2`. -/
lemma fcc_bond_length {a : ℝ} (ha : 0 < a) {x y : fcc.Site}
    (h : fccGraph.toSimpleGraph.Adj x y) :
    (fccGeometry a a a ha ha ha).distance x y = a * Real.sqrt 2 / 2 := by
  apply (fccGeometry a a a ha ha ha).distance_eq_of_adj fccBonds _ _ h
  intro b hb
  simp only [fccBonds, List.mem_cons, List.not_mem_nil, or_false] at hb
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · norm_num [fccGeometry, Geometry.distance, Geometry.position_ofLattice, latticeMap,
      fccVectors, EuclideanSpace.dist_eq, Fin.sum_univ_three]
    refine sqrt_eq_of_eq_sq (by positivity) ?_
    rw [show (a * Real.sqrt 2 / 2) ^ 2 = a ^ 2 * Real.sqrt 2 ^ 2 / 4 by ring, h2]
    ring

/-- In the body-centred cubic lattice with cube side `a`, every edge has length `a √3 / 2`. -/
lemma bcc_bond_length {a : ℝ} (ha : 0 < a) {x y : bcc.Site}
    (h : bccGraph.toSimpleGraph.Adj x y) :
    (bccGeometry a a a ha ha ha).distance x y = a * Real.sqrt 3 / 2 := by
  apply (bccGeometry a a a ha ha ha).distance_eq_of_adj bccBonds _ _ h
  intro b hb
  simp only [bccBonds, List.mem_cons, List.not_mem_nil, or_false] at hb
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  rcases hb with rfl | rfl | rfl | rfl <;>
  · norm_num [bccGeometry, Geometry.distance, Geometry.position_ofLattice, latticeMap,
      bccVectors, EuclideanSpace.dist_eq, Fin.sum_univ_three]
    refine sqrt_eq_of_eq_sq (by positivity) ?_
    rw [show (a * Real.sqrt 3 / 2) ^ 2 = a ^ 2 * Real.sqrt 3 ^ 2 / 4 by ring, h2]
    ring

/-- In the ideal hexagonal close-packed crystal, with `c ^ 2 = 8 a ^ 2 / 3`, every edge has
length `a`. -/
lemma hcp_bond_length {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hideal : c ^ 2 = 8 * a ^ 2 / 3)
    {x y : hcp.Site} (h : hcpGraph.toSimpleGraph.Adj x y) :
    (hcpGeometry a c ha hc).distance x y = a := by
  apply (hcpGeometry a c ha hc).distance_eq_of_adj hcpBonds a _ h
  intro b hb
  simp only [hcpBonds, List.mem_cons, List.not_mem_nil, or_false] at hb
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h3a : a ^ 2 * Real.sqrt 3 ^ 2 = 3 * a ^ 2 := by rw [h3]; ring
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · norm_num [hcpGeometry, Geometry.distance, Geometry.position_ofDisplacements, latticeMap,
      hcpVectors, hcpBasis, EuclideanSpace.dist_eq, EuclideanSpace.norm_eq, Real.norm_eq_abs,
      sq_abs, Fin.sum_univ_three]
    refine sqrt_eq_of_eq_sq ha.le ?_
    nlinarith [h3a, hideal]

end CondensedMatter.Crystal
