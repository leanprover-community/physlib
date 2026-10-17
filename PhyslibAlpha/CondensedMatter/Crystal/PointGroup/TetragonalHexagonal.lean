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

The orders are counted as for the cubic lattices, by `PeriodicGraph.card_pointGroup`. They are
those of the holohedries `4/mmm` and `6/mmm`. With the bonds of the first shell only, the
primitive tetragonal graph is the simple cubic graph, and its point group has order `48`.

The exponent of each group is computed in the same way: an element of the point stabilizer is
determined by the images of the three basis vectors, so it is enough to check its powers on the
basis, for each admissible triple. Every element of the primitive tetragonal point group
satisfies `A ^ 4 = 1`, and every element of the hexagonal point group satisfies `A ^ 6 = 1`. So
the primitive tetragonal group has no rotation of order three, and the hexagonal group none of
order four.

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

/-! ## B. The orders -/

/-- **The point group of the primitive tetragonal lattice has order `16`.** -/
lemma tetragonal_card_pointGroup : Nat.card tetragonalGraph.pointGroup = 16 := by
  refine (PeriodicGraph.card_pointGroup (N := PeriodicGraph.bondNeighbors tetragonalBonds) ?_
    (PeriodicGraph.bonded_ofBonds_unit tetragonalBonds)).trans ?_
  · intro j
    fin_cases j <;> decide
  · rw [Nat.card_congr (PeriodicGraph.admissibleEquiv _), Nat.card_eq_fintype_card]
    decide +kernel

/-- The admissible triples of the body-centred tetragonal graph whose first vector is `a`. Each
is checked on its own: one kernel computation over all `16 ^ 3` triples does not fit in memory. -/
private abbrev bctFiber (a : ↥(PeriodicGraph.bondNeighbors bodyCentredTetragonalBonds)) : ℕ :=
  Fintype.card {u : Fin 2 → ↥(PeriodicGraph.bondNeighbors bodyCentredTetragonalBonds) //
    PeriodicGraph.Admissible (PeriodicGraph.bondNeighbors bodyCentredTetragonalBonds) fun j =>
      (Fin.cons (α := fun _ => ↥(PeriodicGraph.bondNeighbors bodyCentredTetragonalBonds)) a u j :
        Fin 3 → ℤ)}

private lemma bctFiber_0 : bctFiber ⟨![1, 0, 0], by decide⟩ = 2 := by decide +kernel
private lemma bctFiber_1 : bctFiber ⟨![0, 1, 0], by decide⟩ = 2 := by decide +kernel
private lemma bctFiber_2 : bctFiber ⟨![0, 0, 1], by decide⟩ = 2 := by decide +kernel
private lemma bctFiber_3 : bctFiber ⟨![1, 1, 1], by decide⟩ = 2 := by decide +kernel
private lemma bctFiber_4 : bctFiber ⟨![0, 1, 1], by decide⟩ = 0 := by decide +kernel
private lemma bctFiber_5 : bctFiber ⟨![1, 0, 1], by decide⟩ = 0 := by decide +kernel
private lemma bctFiber_6 : bctFiber ⟨![1, 1, 2], by decide⟩ = 0 := by decide +kernel
private lemma bctFiber_7 : bctFiber ⟨![-1, 1, 0], by decide⟩ = 0 := by decide +kernel
private lemma bctFiber_8 : bctFiber ⟨![-1, 0, 0], by decide⟩ = 2 := by decide +kernel
private lemma bctFiber_9 : bctFiber ⟨![0, -1, 0], by decide⟩ = 2 := by decide +kernel
private lemma bctFiber_10 : bctFiber ⟨![0, 0, -1], by decide⟩ = 2 := by decide +kernel
private lemma bctFiber_11 : bctFiber ⟨![-1, -1, -1], by decide⟩ = 2 := by decide +kernel
private lemma bctFiber_12 : bctFiber ⟨![0, -1, -1], by decide⟩ = 0 := by decide +kernel
private lemma bctFiber_13 : bctFiber ⟨![-1, 0, -1], by decide⟩ = 0 := by decide +kernel
private lemma bctFiber_14 : bctFiber ⟨![-1, -1, -2], by decide⟩ = 0 := by decide +kernel
private lemma bctFiber_15 : bctFiber ⟨![1, -1, 0], by decide⟩ = 0 := by decide +kernel

/-- **The point group of the body-centred tetragonal lattice has order `16`.** -/
lemma bodyCentredTetragonal_card_pointGroup :
    Nat.card bodyCentredTetragonalGraph.pointGroup = 16 := by
  refine (PeriodicGraph.card_pointGroup
    (N := PeriodicGraph.bondNeighbors bodyCentredTetragonalBonds) ?_
    (PeriodicGraph.bonded_ofBonds_unit bodyCentredTetragonalBonds)).trans ?_
  · intro j
    fin_cases j <;> decide
  rw [Nat.card_congr (PeriodicGraph.admissibleEquiv _), Nat.card_eq_fintype_card,
    ← Fintype.card_congr ((Fin.consEquiv _).subtypeEquiv fun _ => Iff.rfl),
    Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have hN : PeriodicGraph.bondNeighbors bodyCentredTetragonalBonds =
      {![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1], ![0, 1, 1], ![1, 0, 1], ![1, 1, 2],
        ![-1, 1, 0], ![-1, 0, 0], ![0, -1, 0], ![0, 0, -1], ![-1, -1, -1], ![0, -1, -1],
        ![-1, 0, -1], ![-1, -1, -2], ![1, -1, 0]} := by
    decide
  have key : ∀ a, bctFiber a = if (a : Fin 3 → ℤ) ∈ ({![1, 0, 0], ![0, 1, 0], ![0, 0, 1],
      ![1, 1, 1], ![-1, 0, 0], ![0, -1, 0], ![0, 0, -1], ![-1, -1, -1]} : Finset (Fin 3 → ℤ))
      then 2 else 0 := by
    rintro ⟨d, hd⟩
    show _ = if d ∈ _ then 2 else 0
    have hd' := hN ▸ hd
    fin_cases hd'
    exacts [bctFiber_0.trans rfl, bctFiber_1.trans rfl, bctFiber_2.trans rfl, bctFiber_3.trans rfl,
      bctFiber_4.trans rfl, bctFiber_5.trans rfl, bctFiber_6.trans rfl, bctFiber_7.trans rfl,
      bctFiber_8.trans rfl, bctFiber_9.trans rfl, bctFiber_10.trans rfl, bctFiber_11.trans rfl,
      bctFiber_12.trans rfl, bctFiber_13.trans rfl, bctFiber_14.trans rfl, bctFiber_15.trans rfl]
  calc _ = ∑ a, bctFiber a := Finset.sum_congr rfl fun a _ => by
          simp only [bctFiber, Fintype.card_subtype, Finset.card_filter]; rfl
    _ = 16 := by
      simp only [key]
      rw [Finset.sum_coe_sort (PeriodicGraph.bondNeighbors bodyCentredTetragonalBonds)
        (fun d => if d ∈ _ then 2 else 0), hN]
      decide

/-- **The point group of the primitive hexagonal lattice has order `24`.** -/
lemma hexagonal_card_pointGroup : Nat.card hexagonalGraph.pointGroup = 24 := by
  refine (PeriodicGraph.card_pointGroup (N := PeriodicGraph.bondNeighbors hexagonalBonds) ?_
    (PeriodicGraph.bonded_ofBonds_unit hexagonalBonds)).trans ?_
  · intro j
    fin_cases j <;> decide
  · rw [Nat.card_congr (PeriodicGraph.admissibleEquiv _), Nat.card_eq_fintype_card]
    decide +kernel

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
  · rw [Nat.card_congr (PeriodicGraph.admissibleEquiv _), Nat.card_eq_fintype_card]
    decide +kernel

/-! ## C. The exponents -/

/-- Every element of the point group of the primitive tetragonal lattice satisfies `A ^ 4 = 1`. -/
lemma tetragonal_pow_four (A : Multiplicative (AddAut (Fin 3 → ℤ)))
    (hA : A ∈ tetragonalGraph.pointStabilizer) : A ^ 4 = 1 := by
  refine PeriodicGraph.pow_eq_one_of_admissible (N := PeriodicGraph.bondNeighbors tetragonalBonds)
    (fun j => by fin_cases j <;> decide) (PeriodicGraph.bonded_ofBonds_unit tetragonalBonds) 4
    (fun v hv => ?_) A hA
  obtain ⟨w, rfl⟩ : ∃ w : Fin 3 → ↥(PeriodicGraph.bondNeighbors tetragonalBonds),
      v = fun j => (w j : Fin 3 → ℤ) := ⟨fun j => ⟨v j, hv.mem j⟩, rfl⟩
  revert w
  decide +kernel

/-- Every element of the point group of the primitive hexagonal lattice satisfies `A ^ 6 = 1`. -/
lemma hexagonal_pow_six (A : Multiplicative (AddAut (Fin 3 → ℤ)))
    (hA : A ∈ hexagonalGraph.pointStabilizer) : A ^ 6 = 1 := by
  refine PeriodicGraph.pow_eq_one_of_admissible (N := PeriodicGraph.bondNeighbors hexagonalBonds)
    (fun j => by fin_cases j <;> decide) (PeriodicGraph.bonded_ofBonds_unit hexagonalBonds) 6
    (fun v hv => ?_) A hA
  obtain ⟨w, rfl⟩ : ∃ w : Fin 3 → ↥(PeriodicGraph.bondNeighbors hexagonalBonds),
      v = fun j => (w j : Fin 3 → ℤ) := ⟨fun j => ⟨v j, hv.mem j⟩, rfl⟩
  revert w
  decide +kernel

end CondensedMatter.Crystal
