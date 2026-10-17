/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Cubic
public import PhyslibAlpha.CondensedMatter.Crystal.Examples.Orthorhombic

/-!

# The point groups of the orthorhombic lattices

The point groups of the four orthorhombic lattices have order eight: they are the reflections in
the three coordinate planes and their products, the holohedry `mmm`.

## i. Overview

An element of the point group is determined by the images of the three basis vectors, an
admissible triple. Instead of checking all triples of neighbour displacements, each basis vector
is located by a few tests: a displacement `d` is a neighbour exactly when its image is. For the
primitive lattice:

- `x` is the only neighbour, up to sign, whose double is a neighbour, so it goes to `±x`;
- `y` is the only neighbour on both diagonals `x ± y` through `x`, so it goes to `±y`;
- `z` is on no diagonal through `x`, so it goes to `±z`.

The centred lattices are located in the same way by sums of two and three basis vectors. Each
lattice then has exactly eight admissible triples, listed explicitly in the basis of its graph.

## ii. Key results

- `PeriodicGraph.admissible_iff_of_tests` : the admissible triples are a given set, if only its
  triples pass the tests.
- `orthorhombic_admissible_iff`, `baseCentredOrthorhombic_admissible_iff`,
  `bodyCentredOrthorhombic_admissible_iff`, `faceCentredOrthorhombic_admissible_iff` : the eight
  admissible triples of each lattice.
- `orthorhombic_card_pointGroup`, `baseCentredOrthorhombic_card_pointGroup`,
  `bodyCentredOrthorhombic_card_pointGroup`, `faceCentredOrthorhombic_card_pointGroup` :
  order `8`.

## iii. Table of contents

- A. Tests on admissible triples
- B. The admissible triples
- C. The orders

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

namespace PeriodicGraph

/-! ## A. Tests on admissible triples -/

variable {N : Finset (Fin 3 → ℤ)}

/-- The triple `(a, b, c)` passes the tests `D₀`, `D₁`, `D₂` on its first, first two and three
vectors: each test `d` and its image under the triple are neighbours together. -/
def PassesTests (N : Finset (Fin 3 → ℤ)) (D₀ : List ℤ) (D₁ : List (ℤ × ℤ))
    (D₂ : List (Fin 3 → ℤ)) (a b c : Fin 3 → ℤ) : Prop :=
  (∀ k ∈ D₀, k • a ∈ N ↔ ![k, 0, 0] ∈ N) ∧
    (∀ p ∈ D₁, p.1 • a + p.2 • b ∈ N ↔ ![p.1, p.2, 0] ∈ N) ∧
    ∀ d ∈ D₂, d 0 • a + d 1 • b + d 2 • c ∈ N ↔ d ∈ N

instance (N : Finset (Fin 3 → ℤ)) (D₀ : List ℤ) (D₁ : List (ℤ × ℤ)) (D₂ : List (Fin 3 → ℤ))
    (a b c : Fin 3 → ℤ) : Decidable (PassesTests N D₀ D₁ D₂ a b c) := by
  unfold PassesTests
  infer_instance

/-- The admissible triples are the triples of `S`, if every triple of `S` is admissible and only
the triples of `S` pass the tests. -/
lemma admissible_iff_of_tests (hN : ∀ j, (Pi.single j 1 : Fin 3 → ℤ) ∈ N)
    {S : Finset (Fin 3 → Fin 3 → ℤ)} (D₀ : List ℤ) (D₁ : List (ℤ × ℤ))
    (D₂ : List (Fin 3 → ℤ)) (hS : ∀ v ∈ S, Admissible N v)
    (hD : ∀ a ∈ N, ∀ b ∈ N, ∀ c ∈ N, PassesTests N D₀ D₁ D₂ a b c → ![a, b, c] ∈ S)
    (v : Fin 3 → Fin 3 → ℤ) : Admissible N v ↔ v ∈ S := by
  refine ⟨fun hv => ?_, hS v⟩
  have h := fun d => hv.act_mem_iff hN d
  simp only [act_apply, Fin.sum_univ_three] at h
  have hv3 : v = ![v 0, v 1, v 2] := by ext j : 1; fin_cases j <;> rfl
  rw [hv3]
  exact hD _ (hv.mem 0) _ (hv.mem 1) _ (hv.mem 2)
    ⟨fun k _ => by simpa using h ![k, 0, 0], fun p _ => by simpa using h ![p.1, p.2, 0],
      fun d _ => h d⟩

/-- The order of the point group is the number of admissible triples, once they are known. -/
lemma card_pointGroup_ofBonds (bonds : List (Bond (Fin 3 → ℤ) Unit))
    (hN : ∀ j, (Pi.single j 1 : Fin 3 → ℤ) ∈ bondNeighbors bonds)
    {S : Finset (Fin 3 → Fin 3 → ℤ)} (h : ∀ v, Admissible (bondNeighbors bonds) v ↔ v ∈ S) :
    Nat.card (ofBonds bonds).pointGroup = S.card := by
  rw [card_pointGroup hN (bonded_ofBonds_unit bonds),
    Nat.card_congr (Equiv.subtypeEquivRight h)]
  simp

end PeriodicGraph

open PeriodicGraph

/-! ## B. The admissible triples -/

/-- The images of the basis vectors under the eight point operations of the primitive orthorhombic
lattice, the sign changes of the three basis vectors. -/
def orthorhombicPointTriples : Finset (Fin 3 → Fin 3 → ℤ) :=
  {![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-1, 0, 0], ![0, -1, 0], ![0, 0, -1]],
    ![![-1, 0, 0], ![0, -1, 0], ![0, 0, 1]], ![![-1, 0, 0], ![0, 1, 0], ![0, 0, -1]],
    ![![-1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![1, 0, 0], ![0, -1, 0], ![0, 0, -1]],
    ![![1, 0, 0], ![0, -1, 0], ![0, 0, 1]], ![![1, 0, 0], ![0, 1, 0], ![0, 0, -1]]}

/-- The point operations of the primitive orthorhombic lattice are the eight of
`orthorhombicPointTriples`. -/
lemma orthorhombic_admissible_iff (v : Fin 3 → Fin 3 → ℤ) :
    Admissible (bondNeighbors orthorhombicBonds) v ↔ v ∈ orthorhombicPointTriples :=
  admissible_iff_of_tests (fun j => by fin_cases j <;> decide) [2] [(-1, -1), (-1, 1)]
    [![-1, 0, -1], ![-1, 0, 1]] (by decide +kernel) (by decide +kernel) v

/-- The images of the basis vectors under the eight point operations of the base-centred
orthorhombic lattice, in the basis `baseCentredVectors a b c`. -/
def baseCentredOrthorhombicPointTriples : Finset (Fin 3 → Fin 3 → ℤ) :=
  {![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-1, 0, 0], ![0, -1, 0], ![0, 0, -1]],
    ![![-1, 0, 0], ![0, -1, 0], ![0, 0, 1]], ![![0, -1, 0], ![-1, 0, 0], ![0, 0, -1]],
    ![![0, -1, 0], ![-1, 0, 0], ![0, 0, 1]], ![![0, 1, 0], ![1, 0, 0], ![0, 0, -1]],
    ![![0, 1, 0], ![1, 0, 0], ![0, 0, 1]], ![![1, 0, 0], ![0, 1, 0], ![0, 0, -1]]}

/-- The point operations of the base-centred orthorhombic lattice are the eight of
`baseCentredOrthorhombicPointTriples`. -/
lemma baseCentredOrthorhombic_admissible_iff (v : Fin 3 → Fin 3 → ℤ) :
    Admissible (bondNeighbors baseCentredOrthorhombicBonds) v ↔
      v ∈ baseCentredOrthorhombicPointTriples :=
  admissible_iff_of_tests (fun j => by fin_cases j <;> decide) [] [(-2, -1), (-1, -2), (-1, -1)]
    [![-1, -1, -1], ![-2, -2, 1], ![-2, -2, -1]] (by decide +kernel) (by decide +kernel) v

/-- The images of the basis vectors under the eight point operations of the body-centred
orthorhombic lattice, in the basis `bccVectors a b c`. -/
def bodyCentredOrthorhombicPointTriples : Finset (Fin 3 → Fin 3 → ℤ) :=
  {![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-1, -1, -1], ![0, 0, 1], ![0, 1, 0]],
    ![![-1, 0, 0], ![0, -1, 0], ![0, 0, -1]], ![![0, -1, 0], ![-1, 0, 0], ![1, 1, 1]],
    ![![0, 0, -1], ![1, 1, 1], ![-1, 0, 0]], ![![0, 0, 1], ![-1, -1, -1], ![1, 0, 0]],
    ![![0, 1, 0], ![1, 0, 0], ![-1, -1, -1]], ![![1, 1, 1], ![0, 0, -1], ![0, -1, 0]]}

/-- The point operations of the body-centred orthorhombic lattice are the eight of
`bodyCentredOrthorhombicPointTriples`. -/
lemma bodyCentredOrthorhombic_admissible_iff (v : Fin 3 → Fin 3 → ℤ) :
    Admissible (bondNeighbors bodyCentredOrthorhombicBonds) v ↔
      v ∈ bodyCentredOrthorhombicPointTriples :=
  admissible_iff_of_tests (fun j => by fin_cases j <;> decide) [2] [(-1, -1), (-2, -2), (0, -2)]
    [![0, -2, -2], ![-1, -1, -1]] (by decide +kernel) (by decide +kernel) v

/-- The images of the basis vectors under the eight point operations of the face-centred
orthorhombic lattice, in the basis `fccVectors a b c`. -/
def faceCentredOrthorhombicPointTriples : Finset (Fin 3 → Fin 3 → ℤ) :=
  {![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-1, 0, 0], ![-1, 0, 1], ![-1, 1, 0]],
    ![![-1, 0, 0], ![0, -1, 0], ![0, 0, -1]], ![![0, -1, 1], ![-1, 0, 1], ![0, 0, 1]],
    ![![0, -1, 1], ![0, -1, 0], ![1, -1, 0]], ![![0, 1, -1], ![0, 1, 0], ![-1, 1, 0]],
    ![![0, 1, -1], ![1, 0, -1], ![0, 0, -1]], ![![1, 0, 0], ![1, 0, -1], ![1, -1, 0]]}

/-- The point operations of the face-centred orthorhombic lattice are the eight of
`faceCentredOrthorhombicPointTriples`. -/
lemma faceCentredOrthorhombic_admissible_iff (v : Fin 3 → Fin 3 → ℤ) :
    Admissible (bondNeighbors faceCentredOrthorhombicBonds) v ↔
      v ∈ faceCentredOrthorhombicPointTriples :=
  admissible_iff_of_tests (fun j => by fin_cases j <;> decide) []
    [(-1, 1), (-2, 1), (-1, -1), (-1, 2)] [![-1, 1, 2], ![0, -1, 1]] (by decide +kernel)
    (by decide +kernel) v

/-! ## C. The orders -/

/-- **The point group of the primitive orthorhombic lattice has order `8`.** -/
lemma orthorhombic_card_pointGroup : Nat.card orthorhombicGraph.pointGroup = 8 :=
  (card_pointGroup_ofBonds orthorhombicBonds (fun j => by fin_cases j <;> decide)
    orthorhombic_admissible_iff).trans (by decide)

/-- **The point group of the base-centred orthorhombic lattice has order `8`.** -/
lemma baseCentredOrthorhombic_card_pointGroup :
    Nat.card baseCentredOrthorhombicGraph.pointGroup = 8 :=
  (card_pointGroup_ofBonds baseCentredOrthorhombicBonds (fun j => by fin_cases j <;> decide)
    baseCentredOrthorhombic_admissible_iff).trans (by decide)

/-- **The point group of the body-centred orthorhombic lattice has order `8`.** -/
lemma bodyCentredOrthorhombic_card_pointGroup :
    Nat.card bodyCentredOrthorhombicGraph.pointGroup = 8 :=
  (card_pointGroup_ofBonds bodyCentredOrthorhombicBonds (fun j => by fin_cases j <;> decide)
    bodyCentredOrthorhombic_admissible_iff).trans (by decide)

/-- **The point group of the face-centred orthorhombic lattice has order `8`.** -/
lemma faceCentredOrthorhombic_card_pointGroup :
    Nat.card faceCentredOrthorhombicGraph.pointGroup = 8 :=
  (card_pointGroup_ofBonds faceCentredOrthorhombicBonds (fun j => by fin_cases j <;> decide)
    faceCentredOrthorhombic_admissible_iff).trans (by decide)

end CondensedMatter.Crystal
