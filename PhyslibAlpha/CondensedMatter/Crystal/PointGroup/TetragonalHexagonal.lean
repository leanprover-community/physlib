/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Cubic
public import PhyslibAlpha.CondensedMatter.Crystal.Examples.TetragonalHexagonal

/-!

# The point groups of the tetragonal and hexagonal lattices

The point groups of the primitive and body-centred tetragonal lattices have order sixteen, and
the point group of the primitive hexagonal lattice has order twenty-four.

## i. Overview

The orders are counted as for the cubic lattices, by `PeriodicGraph.card_pointGroup` and the
reflection of admissibility into a Boolean test on lists of triples of integers. They are those of
the holohedries `4/mmm` and `6/mmm`. With the bonds of the first shell only, the primitive
tetragonal graph is the simple cubic graph, and its point group has order `48`.

The exponent of each group is computed in the same way: an element of the point stabilizer is
determined by the images of the three basis vectors, so it is enough to check its powers on the
basis, for each admissible triple, which is again a Boolean test on the list of admissible
triples. Every element of the primitive tetragonal point group satisfies `A ^ 4 = 1`, and every
element of the hexagonal point group satisfies `A ^ 6 = 1`. So the primitive tetragonal group has
no rotation of order three, and the hexagonal group none of order four.

## ii. Key results

- `tetragonal_card_pointGroup`, `bodyCentredTetragonal_card_pointGroup` : order `16`.
- `hexagonal_card_pointGroup` : order `24`.
- `tetragonal_pow_four` : `A ^ 4 = 1` on the point stabilizer.
- `hexagonal_pow_six` : `A ^ 6 = 1` on the point stabilizer.

## iii. Table of contents

- A. Powers from admissible triples
- B. The orders
- C. The exponents

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

namespace PeriodicGraph

/-! ## A. Powers from admissible triples -/

lemma toAdd_pow_apply {G : Type*} [AddCommGroup G] (A : Multiplicative (AddAut G)) (n : ℕ)
    (x : G) : (Multiplicative.toAdd (A ^ n) : AddAut G) x =
      (Multiplicative.toAdd A : AddAut G)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Function.iterate_succ_apply, ← ih]
    rfl

/-- The powers of the map determined by a tuple of columns, in components. -/
lemma toVec3_act_iterate (v : Fin 3 → Fin 3 → ℤ) (n : ℕ) (d : Fin 3 → ℤ) :
    toVec3 ((act v)^[n] d) =
      (act3 (toVec3 (v 0)) (toVec3 (v 1)) (toVec3 (v 2)))^[n] (toVec3 d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, toVec3_act]

/-- The three basis vectors, as triples. -/
def basis3 : List Vec3 := [(1, 0, 0), (0, 1, 0), (0, 0, 1)]

lemma toVec3_single_mem_basis3 (j : Fin 3) : toVec3 (Pi.single j 1) ∈ basis3 := by
  fin_cases j <;> decide

/-- Whether the `n`-th power of every admissible triple of the neighbour list `l` fixes the
three basis vectors. -/
def powFixesBasisB (l : List Vec3) (n : ℕ) : Bool :=
  (admissibleTriples l).all fun t => basis3.all fun e => beq3 ((act3 t.1 t.2.1 t.2.2)^[n] e) e

/-- If the Boolean test passes, the `n`-th power of every admissible tuple fixes the basis. -/
lemma iterate_act_single_eq_of_powFixesBasisB {N : Finset (Fin 3 → ℤ)} {l : List Vec3}
    (hl : ∀ t, t ∈ l ↔ ofVec3 t ∈ N) {n : ℕ} (h : powFixesBasisB l n = true)
    {v : Fin 3 → Fin 3 → ℤ} (hv : Admissible N v) (j : Fin 3) :
    (act v)^[n] (Pi.single j 1) = Pi.single j 1 := by
  have ht : (toVec3 (v 0), toVec3 (v 1), toVec3 (v 2)) ∈ admissibleTriples l := by
    rw [mem_admissibleTriples hl]
    simp only [ofVec3_toVec3]
    rw [vec3_eq]
    exact hv
  simp only [powFixesBasisB, List.all_eq_true, beq3_iff] at h
  exact toVec3_injective
    ((toVec3_act_iterate v n _).trans (h _ ht _ (toVec3_single_mem_basis3 j)))

variable {N : Finset (Fin 3 → ℤ)} (hN : ∀ j, (Pi.single j 1 : Fin 3 → ℤ) ∈ N)
  {g : PeriodicGraph (Crystal.ofUnitCell (Fin 3 → ℤ) Unit)}
  (hg : ∀ d, g.Bonded () () d ↔ d ∈ N)
include hN hg

/-- If the `n`-th power of every admissible triple fixes the basis, then every element of the
point stabilizer satisfies `A ^ n = 1`. -/
lemma pow_eq_one_of_admissible (n : ℕ)
    (h : ∀ v, Admissible N v → ∀ j, (act v)^[n] (Pi.single j 1) = Pi.single j 1)
    (A : Multiplicative (AddAut (Fin 3 → ℤ))) (hA : A ∈ g.pointStabilizer) : A ^ n = 1 := by
  set v := fun j => (Multiplicative.toAdd A : AddAut (Fin 3 → ℤ)) (Pi.single j 1)
  have hv : Admissible N v := (pointStabilizerEquiv hN hg ⟨A, hA⟩).2
  have hact : ⇑(Multiplicative.toAdd A : AddAut (Fin 3 → ℤ)) = act v :=
    funext (apply_eq_act _)
  have hpow : ∀ d, (act v)^[n] d = d := by
    have hlin : (act v)^[n] = ⇑(act v ^ n) := (Module.End.coe_pow (act v) n).symm
    intro d
    rw [hlin, ← Finset.univ_sum_single d, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (d j) : Fin 3 → ℤ) = d j • Pi.single j 1 by
      ext k; simp [Pi.single_apply], map_zsmul, ← hlin, h v hv j]
  refine Multiplicative.toAdd.injective (AddEquiv.ext fun d => ?_)
  rw [toAdd_pow_apply, hact, hpow]
  rfl

end PeriodicGraph

/-! ## B. The orders

The neighbour lists are written out with the neighbours that are not basis vectors first, so
that the Boolean test fails early on most candidate tuples.
-/

/-- The ten neighbours of the primitive tetragonal lattice. -/
def tetragonalNeighbors : List PeriodicGraph.Vec3 :=
  [(1, 1, 0), (1, -1, 0), (-1, -1, 0), (-1, 1, 0),
    (1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 0, 0), (0, -1, 0), (0, 0, -1)]

/-- **The point group of the primitive tetragonal lattice has order `16`.** -/
lemma tetragonal_card_pointGroup : Nat.card tetragonalGraph.pointGroup = 16 := by
  refine (PeriodicGraph.card_pointGroup (N := PeriodicGraph.bondNeighbors tetragonalBonds) ?_
    (PeriodicGraph.bonded_ofBonds_unit tetragonalBonds)).trans ?_
  · intro j
    fin_cases j <;> decide
  · rw [PeriodicGraph.card_admissible_eq_length (PeriodicGraph.mem_iff_of_perm
      (bonds := tetragonalBonds) (l := tetragonalNeighbors) (by decide +kernel)) (by decide)]
    decide +kernel

/-- The sixteen neighbours of the body-centred tetragonal lattice. -/
def bodyCentredTetragonalNeighbors : List PeriodicGraph.Vec3 :=
  [(1, 1, 1), (0, 1, 1), (1, 0, 1), (1, 1, 2), (-1, 1, 0),
    (-1, -1, -1), (0, -1, -1), (-1, 0, -1), (-1, -1, -2), (1, -1, 0),
    (1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 0, 0), (0, -1, 0), (0, 0, -1)]

/-- **The point group of the body-centred tetragonal lattice has order `16`.** -/
lemma bodyCentredTetragonal_card_pointGroup :
    Nat.card bodyCentredTetragonalGraph.pointGroup = 16 := by
  refine (PeriodicGraph.card_pointGroup
    (N := PeriodicGraph.bondNeighbors bodyCentredTetragonalBonds) ?_
    (PeriodicGraph.bonded_ofBonds_unit bodyCentredTetragonalBonds)).trans ?_
  · intro j
    fin_cases j <;> decide
  · rw [PeriodicGraph.card_admissible_eq_length (PeriodicGraph.mem_iff_of_perm
      (bonds := bodyCentredTetragonalBonds) (l := bodyCentredTetragonalNeighbors)
      (by decide +kernel)) (by decide)]
    decide +kernel

/-- The eight neighbours of the primitive hexagonal lattice. -/
def hexagonalNeighbors : List PeriodicGraph.Vec3 :=
  [(1, 1, 0), (-1, -1, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 0, 0), (0, -1, 0), (0, 0, -1)]

/-- **The point group of the primitive hexagonal lattice has order `24`.** -/
lemma hexagonal_card_pointGroup : Nat.card hexagonalGraph.pointGroup = 24 := by
  refine (PeriodicGraph.card_pointGroup (N := PeriodicGraph.bondNeighbors hexagonalBonds) ?_
    (PeriodicGraph.bonded_ofBonds_unit hexagonalBonds)).trans ?_
  · intro j
    fin_cases j <;> decide
  · rw [PeriodicGraph.card_admissible_eq_length (PeriodicGraph.mem_iff_of_perm
      (bonds := hexagonalBonds) (l := hexagonalNeighbors) (by decide +kernel)) (by decide)]
    decide +kernel

/-- The six neighbours of the first shell, `±x, ±y, ±z`. -/
def firstShellNeighbors : List PeriodicGraph.Vec3 :=
  [(1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 0, 0), (0, -1, 0), (0, 0, -1)]

/-- With the bonds of the first shell only, `±x, ±y, ±z`, a tetragonal lattice has the point
group of the simple cubic lattice, of order `48`. -/
lemma tetragonal_firstShell_card_pointGroup :
    Nat.card (PeriodicGraph.ofBonds (G := Fin 3 → ℤ) (F := Unit)
      [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩]).pointGroup = 48 := by
  refine (PeriodicGraph.card_pointGroup (N := PeriodicGraph.bondNeighbors
    [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩]) ?_
    (PeriodicGraph.bonded_ofBonds_unit _)).trans ?_
  · intro j
    fin_cases j <;> decide
  · rw [PeriodicGraph.card_admissible_eq_length (PeriodicGraph.mem_iff_of_perm
      (bonds := [⟨(), (), ![1, 0, 0]⟩, ⟨(), (), ![0, 1, 0]⟩, ⟨(), (), ![0, 0, 1]⟩])
      (l := firstShellNeighbors) (by decide +kernel)) (by decide)]
    decide +kernel

/-! ## C. The exponents -/

/-- Every element of the point group of the primitive tetragonal lattice satisfies `A ^ 4 = 1`. -/
lemma tetragonal_pow_four (A : Multiplicative (AddAut (Fin 3 → ℤ)))
    (hA : A ∈ tetragonalGraph.pointStabilizer) : A ^ 4 = 1 :=
  PeriodicGraph.pow_eq_one_of_admissible (N := PeriodicGraph.bondNeighbors tetragonalBonds)
    (fun j => by fin_cases j <;> decide) (PeriodicGraph.bonded_ofBonds_unit tetragonalBonds) 4
    (fun _ hv => PeriodicGraph.iterate_act_single_eq_of_powFixesBasisB
      (PeriodicGraph.mem_iff_of_perm (bonds := tetragonalBonds) (l := tetragonalNeighbors)
        (by decide +kernel)) (n := 4) (by decide +kernel) hv) A hA

/-- Every element of the point group of the primitive hexagonal lattice satisfies `A ^ 6 = 1`. -/
lemma hexagonal_pow_six (A : Multiplicative (AddAut (Fin 3 → ℤ)))
    (hA : A ∈ hexagonalGraph.pointStabilizer) : A ^ 6 = 1 :=
  PeriodicGraph.pow_eq_one_of_admissible (N := PeriodicGraph.bondNeighbors hexagonalBonds)
    (fun j => by fin_cases j <;> decide) (PeriodicGraph.bonded_ofBonds_unit hexagonalBonds) 6
    (fun _ hv => PeriodicGraph.iterate_act_single_eq_of_powFixesBasisB
      (PeriodicGraph.mem_iff_of_perm (bonds := hexagonalBonds) (l := hexagonalNeighbors)
        (by decide +kernel)) (n := 6) (by decide +kernel) hv) A hA

end CondensedMatter.Crystal
