/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.PointOperations
public import Mathlib.Algebra.Ring.Int.Units

/-!
# The hypercubic lattice

The simplest crystal: one site per cell of `ℤᵈ`, bonded to its nearest neighbors.

## i. Overview

The hypercubic lattice has a single site in each cell of `ℤᵈ`. Each site is bonded to the two
neighboring sites along every coordinate axis. For `d = 1` this is the infinite chain, for `d = 2`
the square lattice and for `d = 3` the simple cubic lattice.

A symmetry of the lattice keeps the bonds exactly when it maps the `2 d` neighbors of a site to the
neighbors of its image. Its shifts are translations and always do. The rotations and reflections
that remain are those whose lattice automorphism permutes the unit steps `±eⱼ`.

## ii. Key results

- `Crystal.hypercubic` : the crystal with one site per cell of `ℤᵈ`.
- `Crystal.hypercubicGraph` : its nearest-neighbor bonds.
- `Crystal.hypercubicGraph_adj` : two sites are bonded when their cells differ by a unit step.
- `Crystal.mem_spaceGroup_hypercubic_iff` : a symmetry is in the space group exactly when its
  lattice automorphism permutes the unit steps.

## iii. Table of contents

- A. The hypercubic lattice
- B. Neighbors
- C. The space group

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

/-! ## A. The hypercubic lattice -/

/-- The `2 d` unit steps `±eⱼ` of the lattice `ℤᵈ`. -/
def unitSteps (d : ℕ) : Set (Fin d → ℤ) :=
  Set.range fun p : Fin d × ℤˣ => Pi.single p.1 (p.2 : ℤ)

/-- A vector is a unit step when it or its negative is some `eⱼ`. -/
lemma mem_unitSteps_iff {d : ℕ} {v : Fin d → ℤ} :
    v ∈ unitSteps d ↔ ∃ j : Fin d, v = Pi.single j 1 ∨ -v = Pi.single j 1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨j, ε⟩, rfl⟩
    rcases Int.units_eq_one_or ε with rfl | rfl <;> exact ⟨j, by simp [Pi.single_neg]⟩
  · rintro ⟨j, h | h⟩
    exacts [⟨(j, 1), by simp [h]⟩, ⟨(j, -1), by simp [← h, Pi.single_neg]⟩]

/-- One site per cell of `ℤᵈ`. -/
abbrev hypercubic (d : ℕ) := Crystal.ofUnitCell (Fin d → ℤ) Unit

/-- The bonds of the hypercubic lattice: one for each coordinate direction. -/
def hypercubicBonds (d : ℕ) : Finset (Bond (hypercubic d)) :=
  Finset.univ.image fun j : Fin d => ⟨(), (), Pi.single j 1⟩

/-- Each site is bonded to its neighbor one cell further along every coordinate axis. -/
def hypercubicGraph (d : ℕ) : PeriodicGraph (hypercubic d) :=
  PeriodicGraph.ofBonds (hypercubicBonds d)

/-! ## B. Neighbors -/

/-- Two sites of the hypercubic lattice are bonded when their cells differ by a unit step. -/
lemma hypercubicGraph_adj (d : ℕ) (x y : (hypercubic d).Site) :
    (hypercubicGraph d).toSimpleGraph.Adj x y ↔ y.cell - x.cell ∈ unitSteps d := by
  simp only [hypercubicGraph, PeriodicGraph.adj_ofBonds, hypercubicBonds, Finset.mem_image,
    Finset.mem_univ, true_and, exists_exists_eq_and, Bond.Links, mem_unitSteps_iff,
    sub_eq_iff_eq_add', neg_sub]
  exact and_iff_right_of_imp (by rintro ⟨j, h | h⟩ rfl <;> simpa using congrFun h j)

/-! ## C. The space group -/

/-- A lattice automorphism preserves the bonds of the hypercubic lattice exactly when it permutes
the unit steps `±eⱼ`. -/
lemma linear_mem_spaceGroup_iff (d : ℕ) (A : (Fin d → ℤ) ≃+ (Fin d → ℤ)) :
    Symmetry.linear (hypercubic d) (Multiplicative.ofAdd A, 1) ∈
        (hypercubicGraph d).spaceGroup ↔ ∀ v, A v ∈ unitSteps d ↔ v ∈ unitSteps d := by
  rw [PeriodicGraph.mem_spaceGroup_iff]
  have e : ∀ x : (hypercubic d).Site,
      Symmetry.linear (hypercubic d) (Multiplicative.ofAdd A, 1) x = ⟨A x.cell, x.label⟩ :=
    fun x => rfl
  simp only [e, hypercubicGraph_adj, ← map_sub]
  refine ⟨fun h v => ?_, fun h x y => h _⟩
  simpa using h ⟨0, ()⟩ ⟨v, ()⟩

/-- Every shift of the hypercubic lattice is a translation, so it preserves the bonds. -/
lemma shift_mem_spaceGroup (d : ℕ) (c : Multiplicative (Unit → Fin d → ℤ)) :
    Symmetry.shift (hypercubic d) c ∈ (hypercubicGraph d).spaceGroup := by
  rw [show c = Multiplicative.ofAdd fun _ => Multiplicative.toAdd c () from rfl,
    Symmetry.shift_const]
  exact (hypercubicGraph d).translations_le_spaceGroup ⟨_, rfl⟩

/-- **The space group of the hypercubic lattice: a symmetry of the crystal preserves the bonds
exactly when its lattice automorphism permutes the `2 d` unit steps.** Its shifts are translations
and are always allowed, so the space group consists of the translations together with the signed
permutations of the coordinates. -/
lemma mem_spaceGroup_hypercubic_iff (d : ℕ) (φ : Symmetry (hypercubic d)) :
    φ ∈ (hypercubicGraph d).spaceGroup ↔ ∀ v, φ.lattice v ∈ unitSteps d ↔ v ∈ unitSteps d := by
  obtain ⟨c, σ, h⟩ := Symmetry.exists_eq_shift_mul_linear φ
  rw [Subsingleton.elim σ 1] at h
  rw [← linear_mem_spaceGroup_iff]
  conv_lhs => rw [h]
  exact Subgroup.mul_mem_cancel_left _ (shift_mem_spaceGroup d c)

end Physlib.CondensedMatter.Crystal
