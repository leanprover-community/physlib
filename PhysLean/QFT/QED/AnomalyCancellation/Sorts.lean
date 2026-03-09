/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.QED.AnomalyCancellation.Permutations
public import Mathlib.Data.Fin.Tuple.Sort
/-!
# Sort for Pure U(1) charges

We define the sort function for Pure U(1) charges, and prove some basic properties.

-/

@[expose] public section

open Nat
open Finset

namespace PureU1

variable {n : ℕ}

/-- A charge is sorted if for all `i ≤ j`, then `S i ≤ S j`. -/
@[simp]
def Sorted {n : ℕ} (S : (PureU1 n).Charges) : Prop :=
  ∀ i j (_ : i ≤ j), S i ≤ S j

/-- Given a charge assignment `S`, the corresponding sorted charge assignment. -/
@[simp]
def sort {n : ℕ} (S : (PureU1 n).Charges) : (PureU1 n).Charges :=
  ((FamilyPermutations n).rep (Tuple.sort S).symm S)

lemma sort_sorted {n : ℕ} (S : (PureU1 n).Charges) : Sorted (sort S) := by
  simp only [Sorted, PureU1_numberCharges, sort, FamilyPermutations, PermGroup, permCharges,
    MonoidHom.coe_mk, OneHom.coe_mk, chargeMap_apply]
  intro i j hij
  exact Tuple.monotone_sort S hij

lemma sort_perm {n : ℕ} (S : (PureU1 n).Charges) (M :(FamilyPermutations n).group) :
    sort ((FamilyPermutations n).rep M S) = sort S :=
  @Tuple.comp_perm_comp_sort_eq_comp_sort n ℚ _ S M⁻¹

lemma sort_apply {n : ℕ} (S : (PureU1 n).Charges) (j : Fin n) :
    sort S j = S ((Tuple.sort S) j) := by
  rfl

lemma sort_zero {n : ℕ} (S : (PureU1 n).Charges) (hS : sort S = 0) : S = 0 := by
  funext i
  have hj : ∀ j, sort S j = 0 := by
    rw [hS]
    intro j
    rfl
  have hi := hj ((Tuple.sort S).invFun i)
  rw [sort_apply] at hi
  simp only [PureU1_numberCharges, Equiv.invFun_as_coe, Equiv.apply_symm_apply] at hi
  rw [hi]
  rfl

lemma sort_projection {n : ℕ} (S : (PureU1 n).Charges) : sort (sort S) = sort S :=
  sort_perm S (Tuple.sort S).symm

/-- The sort function acting on `LinSols`. -/
def sortAFL {n : ℕ} (S : (PureU1 n).LinSols) : (PureU1 n).LinSols :=
  ((FamilyPermutations n).linSolRep (Tuple.sort S.val).symm S)

lemma sortAFL_val {n : ℕ} (S : (PureU1 n).LinSols) : (sortAFL S).val = sort S.val := by
  rfl

lemma sortAFL_zero {n : ℕ} (S : (PureU1 n).LinSols) (hS : sortAFL S = 0) : S = 0 := by
  apply ACCSystemLinear.LinSols.ext
  have h1 : sort S.val = 0 := by
    rw [← sortAFL_val]
    rw [hS]
    rfl
  exact sort_zero S.val h1

end PureU1
