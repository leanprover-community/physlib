/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Basic
public import PhyslibAlpha.CondensedMatter.Crystal.BrillouinCoordinates
public import PhyslibAlpha.CondensedMatter.Crystal.Examples.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!

# The point group of the hypercubic lattice in every dimension

The point group of the hypercubic lattice in `d` dimensions consists of the signed permutations
of the axes and has order `2 ^ d * d !`.

## i. Overview

The nearest neighbours of a site of the hypercubic lattice `ℤ^d` are the displacements `±e_j`,
which are the integer vectors whose coordinates have absolute values summing to one. A lattice
automorphism preserves the set of these displacements exactly when it maps each basis vector to
`±e_k` for a distinct axis `k`: it is a permutation of the axes together with a choice of sign
for each axis. All of these signed permutations preserve the bonds. The point group is therefore
the hyperoctahedral group, the symmetry group of the `d`-dimensional cube, which has `2 ^ d`
sign choices and `d !` permutations. For `d = 2` it is the dihedral group of order eight and for
`d = 3` the octahedral group of order forty-eight.

## ii. Key results

- `signedPerm` : the lattice automorphism given by a permutation of the axes and signs.
- `mem_pointStabilizer_hypercubic_iff` : a lattice automorphism preserves the bonds of the
  hypercubic lattice exactly when it is a signed permutation.
- `card_pointGroup_hypercubic` : the point group has order `2 ^ d * d !`.

## iii. Table of contents

- A. Bonds of the hypercubic lattice
- B. Signed permutations
- C. The point group

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

open PeriodicGraph

variable {d : ℕ}

/-! ## A. Bonds of the hypercubic lattice -/

/-- The sum of the absolute values of the coordinates. -/
def l1 (r : Fin d → ℤ) : ℤ := ∑ i, |r i|

lemma l1_neg (r : Fin d → ℤ) : l1 (-r) = l1 r := by simp [l1]

lemma l1_single (j : Fin d) : l1 (Pi.single j (1 : ℤ) : Fin d → ℤ) = 1 := by
  rw [l1, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The bonded displacements of the hypercubic lattice are the vectors `±e_j`. -/
lemma hypercubic_bonded_iff_exists (r : Fin d → ℤ) :
    (hypercubicGraph d).Bonded () () r ↔ ∃ j, r = Pi.single j 1 ∨ r = -Pi.single j 1 := by
  change (⟨0, ()⟩ ≠ (⟨r, ()⟩ : CellSite (Fin d → ℤ) Unit) ∧ ∃ b ∈ hypercubicBonds d,
    b.Links ⟨0, ()⟩ ⟨r, ()⟩ ∨ b.Links ⟨r, ()⟩ ⟨0, ()⟩) ↔ _
  simp only [hypercubicBonds, List.mem_ofFn, Bond.Links, true_and, ne_eq, CellSite.mk.injEq,
    and_true, zero_add]
  constructor
  · rintro ⟨-, _, ⟨j, rfl⟩, h | h⟩
    · exact ⟨j, Or.inl h⟩
    · exact ⟨j, Or.inr (eq_neg_of_add_eq_zero_left h.symm)⟩
  · rintro ⟨j, h | h⟩
    · refine ⟨?_, _, ⟨j, rfl⟩, Or.inl h⟩
      intro h0
      have := congrFun (h0.trans h) j
      simp at this
    · refine ⟨?_, _, ⟨j, rfl⟩, Or.inr ?_⟩
      · intro h0
        have := congrFun (h0.trans h) j
        simp at this
      · rw [h]; simp

/-- **Two sites of the hypercubic lattice are bonded exactly when their cells differ by a vector
whose coordinates have absolute values summing to one.** -/
lemma hypercubic_bonded_iff (r : Fin d → ℤ) :
    (hypercubicGraph d).Bonded () () r ↔ l1 r = 1 := by
  rw [hypercubic_bonded_iff_exists]
  constructor
  · rintro ⟨j, h | h⟩ <;> subst h <;> simp [l1_neg, l1_single]
  · intro h
    have hnn : ∀ i, 0 ≤ |r i| := fun i => abs_nonneg _
    obtain ⟨j, hj⟩ : ∃ j, r j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      simp [l1, hcon] at h
    have hle : |r j| ≤ 1 := h ▸ Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
    have hj1 : |r j| = 1 := le_antisymm hle (Int.one_le_abs hj)
    have hrest : ∀ i, i ≠ j → r i = 0 := by
      intro i hij
      have h2 : ∑ i' ∈ Finset.univ.erase j, |r i'| = 0 := by
        have := Finset.add_sum_erase Finset.univ (fun i' => |r i'|) (Finset.mem_univ j)
        unfold l1 at h
        linarith
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i' _ => hnn i')).1 h2 i
        (Finset.mem_erase.2 ⟨hij, Finset.mem_univ _⟩)
      exact abs_eq_zero.1 this
    refine ⟨j, ?_⟩
    rcases abs_eq (zero_le_one) |>.1 hj1 with h1 | h1
    · left; ext i; by_cases hi : i = j
      · subst hi; simp [h1]
      · simp [hrest i hi, hi]
    · right; ext i; by_cases hi : i = j
      · subst hi; simp [h1]
      · simp [hrest i hi, hi]

/-! ## B. Signed permutations -/

/-- The sign `+1` for `true` and `-1` for `false`. -/
def signOf (b : Bool) : ℤ := if b then 1 else -1

lemma signOf_mul_self (b : Bool) : signOf b * signOf b = 1 := by cases b <;> simp [signOf]

lemma abs_signOf (b : Bool) : |signOf b| = 1 := by cases b <;> simp [signOf]

lemma signOf_ne_zero (b : Bool) : signOf b ≠ 0 := by cases b <;> simp [signOf]

lemma signOf_injective : Function.Injective signOf := by
  intro a b h; cases a <;> cases b <;> simp_all [signOf]

/-- The lattice automorphism that permutes the axes by `π` and multiplies the `i`-th coordinate
by the sign `ε i`. -/
def signedPerm (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) : (Fin d → ℤ) ≃+ (Fin d → ℤ) where
  toFun r i := signOf (ε i) * r (π.symm i)
  invFun r i := signOf (ε (π i)) * r (π i)
  left_inv r := by
    funext j
    simp only [Equiv.symm_apply_apply]
    rw [← mul_assoc, signOf_mul_self, one_mul]
  right_inv r := by
    funext j
    simp only [Equiv.apply_symm_apply]
    rw [← mul_assoc, signOf_mul_self, one_mul]
  map_add' a b := by
    funext i
    simp [mul_add]

lemma signedPerm_apply (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (r : Fin d → ℤ) (i : Fin d) :
    signedPerm π ε r i = signOf (ε i) * r (π.symm i) := rfl

/-- A signed permutation preserves the sum of the absolute values of the coordinates. -/
lemma l1_signedPerm (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (r : Fin d → ℤ) :
    l1 (signedPerm π ε r) = l1 r := by
  unfold l1
  simp only [signedPerm_apply, abs_mul, abs_signOf, one_mul]
  exact Equiv.sum_comp π.symm (fun i => |r i|)

lemma signedPerm_single (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (j : Fin d) :
    signedPerm π ε (Pi.single j 1) = Pi.single (π j) (signOf (ε (π j))) := by
  funext i
  by_cases hi : i = π j
  · subst hi; simp [signedPerm_apply]
  · have : π.symm i ≠ j := fun h => hi (by rw [← h]; simp)
    simp [signedPerm_apply, hi, this]

lemma signedPerm_injective :
    Function.Injective fun p : Equiv.Perm (Fin d) × (Fin d → Bool) => signedPerm p.1 p.2 := by
  rintro ⟨π, ε⟩ ⟨π', ε'⟩ h
  have h1 : ∀ j, (Pi.single (π j) (signOf (ε (π j))) : Fin d → ℤ) =
      Pi.single (π' j) (signOf (ε' (π' j))) := fun j => by
    rw [← signedPerm_single, ← signedPerm_single]
    exact congrArg (fun A : (Fin d → ℤ) ≃+ (Fin d → ℤ) => A (Pi.single j 1)) h
  have hπ : ∀ j, π j = π' j := by
    intro j
    have := congrFun (h1 j) (π j)
    by_contra hne
    simp [hne, signOf_ne_zero] at this
  have hπe : π = π' := Equiv.ext hπ
  subst hπe
  refine Prod.ext rfl (funext fun i => ?_)
  obtain ⟨j, rfl⟩ := π.surjective i
  have := congrFun (h1 j) (π j)
  simp only [Pi.single_eq_same] at this
  exact signOf_injective this

/-! ## C. The point group -/

/-- **A signed permutation preserves the bonds of the hypercubic lattice.** -/
lemma signedPerm_mem_pointStabilizer (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) :
    Multiplicative.ofAdd (signedPerm π ε) ∈ (hypercubicGraph d).pointStabilizer := by
  intro r
  change (hypercubicGraph d).Bonded () () (signedPerm π ε r) ↔ _
  rw [hypercubic_bonded_iff, hypercubic_bonded_iff, l1_signedPerm]

/-- **The lattice automorphisms preserving the bonds of the hypercubic lattice are exactly the
signed permutations.** -/
lemma mem_pointStabilizer_hypercubic_iff (A : Multiplicative (AddAut (Fin d → ℤ))) :
    A ∈ (hypercubicGraph d).pointStabilizer ↔
      ∃ (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool), Multiplicative.toAdd A = signedPerm π ε := by
  constructor
  · intro hA
    have hbond : ∀ j, ∃ (k : Fin d) (b : Bool),
        (Multiplicative.toAdd A : AddAut (Fin d → ℤ)) (Pi.single j 1) = Pi.single k (signOf b) := by
      intro j
      have h1 : (hypercubicGraph d).Bonded () ()
          ((Multiplicative.toAdd A : AddAut (Fin d → ℤ)) (Pi.single j 1)) :=
        (hA _).2 ((hypercubic_bonded_iff_exists _).2 ⟨j, Or.inl rfl⟩)
      obtain ⟨k, h | h⟩ := (hypercubic_bonded_iff_exists _).1 h1
      · exact ⟨k, true, by simpa [signOf] using h⟩
      · refine ⟨k, false, ?_⟩
        rw [h]
        ext i; by_cases hi : i = k <;> simp [signOf, hi]
    choose f ε' hf using hbond
    have hinj : Function.Injective f := by
      intro j j' hjj
      have e1 := hf j
      have e2 := hf j'
      rw [← hjj] at e2
      have : (Multiplicative.toAdd A : AddAut (Fin d → ℤ))
          (signOf (ε' j') • Pi.single j 1 : Fin d → ℤ) =
          (Multiplicative.toAdd A : AddAut (Fin d → ℤ)) (signOf (ε' j) • Pi.single j' 1) := by
        rw [map_zsmul, map_zsmul, e1, e2]
        ext i; by_cases hi : i = f j <;> simp [hi]; ring
      have h3 := congrFun ((Multiplicative.toAdd A : AddAut (Fin d → ℤ)).injective this) j
      by_contra hne
      simp [hne, signOf_ne_zero] at h3
    let π : Equiv.Perm (Fin d) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
    refine ⟨π, fun i => ε' (π.symm i), ?_⟩
    refine AddEquiv.ext fun r => funext fun i => ?_
    rw [apply_eq_sum_single, Finset.sum_eq_single (π.symm i), signedPerm_apply]
    · have : f (π.symm i) = i := π.apply_symm_apply i
      rw [hf, this]
      simp [mul_comm]
    · intro j _ hj
      have : f j ≠ i := fun h => hj (by rw [← h]; exact (π.symm_apply_apply j).symm)
      rw [hf]
      simp [this]
    · exact fun h => absurd (Finset.mem_univ _) h
  · rintro ⟨π, ε, h⟩
    rw [show A = Multiplicative.ofAdd (signedPerm π ε) from by rw [← h]; rfl]
    exact signedPerm_mem_pointStabilizer π ε

/-- **The point group of the hypercubic lattice is the group of signed permutations of the
axes**: it is in bijection with the pairs of a permutation and a choice of signs. -/
noncomputable def pointStabilizerEquivSignedPerm :
    (Equiv.Perm (Fin d) × (Fin d → Bool)) ≃ (hypercubicGraph d).pointStabilizer :=
  Equiv.ofBijective (fun p => ⟨Multiplicative.ofAdd (signedPerm p.1 p.2),
    signedPerm_mem_pointStabilizer p.1 p.2⟩)
    ⟨fun p q h => signedPerm_injective (congrArg (fun x => Multiplicative.toAdd x.1) h),
      fun ⟨A, hA⟩ => by
        obtain ⟨π, ε, h⟩ := (mem_pointStabilizer_hypercubic_iff A).1 hA
        exact ⟨(π, ε), Subtype.ext (by simp [← h])⟩⟩

/-- **The point group of the hypercubic lattice in `d` dimensions has order `2 ^ d * d !`.** -/
lemma card_pointGroup_hypercubic (d : ℕ) :
    Nat.card (hypercubicGraph d).pointGroup = 2 ^ d * d.factorial := by
  rw [Nat.card_congr (pointGroupEquiv (hypercubicGraph d)).toEquiv,
    ← Nat.card_congr (pointStabilizerEquivSignedPerm (d := d)), Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_perm, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  ring

end CondensedMatter.Crystal
