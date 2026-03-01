/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.QED.AnomalyCancellation.Basic
import PhysLean.QFT.AnomalyCancellation.GroupActions
/-!
# Permutations of Pure U(1) ACC

We define the permutation group action on the charges of the Pure U(1) ACC system.
We further define the action on the ACC System.

-/

open Nat
open Finset

namespace PureU1

/-- The permutation group of the n-fermions. -/
@[simp]
def PermGroup (n : ℕ) := Equiv.Perm (Fin n)

/-- The type `PermGroup n` inherits the instance of a group from `Equiv.Perm`. -/
instance {n : ℕ} : Group (PermGroup n) := Equiv.Perm.permGroup

section Charges

/-- The image of an element of `permGroup` under the representation on charges. -/
@[simps!]
def chargeMap {n : ℕ} (f : PermGroup n) :
    (PureU1 n).Charges →ₗ[ℚ] (PureU1 n).Charges where
  toFun S := S ∘ f.toFun
  map_add' _ _ := rfl
  map_smul' _ _:= rfl

/-- The representation of `permGroup` acting on the vector space of charges. -/
@[simp]
def permCharges {n : ℕ} : Representation ℚ (PermGroup n) (PureU1 n).Charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g := by rfl
  map_one' := by rfl

lemma accGrav_invariant {n : ℕ} (f : (PermGroup n)) (S : (PureU1 n).Charges) :
    PureU1.accGrav n (permCharges f S) = accGrav n S := by
  simp only [accGrav, PermGroup, permCharges, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, chargeMap_apply]
  apply (Equiv.Perm.sum_comp _ _ _ ?_)
  simp

open BigOperators
lemma accCube_invariant {n : ℕ} (f : (PermGroup n)) (S : (PureU1 n).Charges) :
    accCube n (permCharges f S) = accCube n S := by
  rw [accCube_explicit, accCube_explicit]
  change ∑ i : Fin n, ((((fun a => a^3) ∘ S) (f.symm i))) = _
  apply (Equiv.Perm.sum_comp _ _ _ ?_)
  simp

end Charges

/-- The permutations acting on the ACC system. -/
@[simp]
def FamilyPermutations (n : ℕ) : ACCSystemGroupAction (PureU1 n) where
  group := PermGroup n
  groupInst := inferInstance
  rep := permCharges
  linearInvariant := by
    intro i
    simp only [PureU1_numberLinear] at i
    match i with
    | 0 => exact accGrav_invariant
  quadInvariant := by
    intro i
    simp only [PureU1_numberQuadratic] at i
    exact Fin.elim0 i
  cubicInvariant := accCube_invariant

lemma FamilyPermutations_charges_apply (S : (PureU1 n).Charges)
    (i : Fin n) (f : (FamilyPermutations n).group) :
    ((FamilyPermutations n).rep f S) i = S (f.invFun i) := by
  rfl

lemma FamilyPermutations_anomalyFreeLinear_apply (S : (PureU1 n).LinSols)
    (i : Fin n) (f : (FamilyPermutations n).group) :
    ((FamilyPermutations n).linSolRep f S).val i = S.val (f.invFun i) := by
  rfl

/-- A permutation of fermions which takes one ordered subset into another. -/
noncomputable def permOfInjection (f g : Fin m ↪ Fin n) : (FamilyPermutations n).group :=
  Equiv.extendSubtype (g.toEquivRange.symm.trans f.toEquivRange)

section permTwo

variable {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j')

/-- Given two distinct elements, an embedding of `Fin 2` into `Fin n`. -/
def permTwoInj : Fin 2 ↪ Fin n where
  toFun s := match s with
    | 0 => i
    | 1 => j
  inj' s1 s2 := by
    aesop

lemma permTwoInj_fst : i ∈ Set.range ⇑(permTwoInj hij) := by
  simp only [Set.mem_range]
  use 0
  rfl

lemma permTwoInj_fst_apply :
    (Function.Embedding.toEquivRange (permTwoInj hij)).symm ⟨i, permTwoInj_fst hij⟩ = 0 := by
  exact (Equiv.symm_apply_eq (Function.Embedding.toEquivRange (permTwoInj hij))).mpr rfl

lemma permTwoInj_snd : j ∈ Set.range ⇑(permTwoInj hij) := by
  simp only [Set.mem_range]
  use 1
  rfl

lemma permTwoInj_snd_apply :
    (Function.Embedding.toEquivRange (permTwoInj hij)).symm
    ⟨j, permTwoInj_snd hij⟩ = 1 := by
  exact (Equiv.symm_apply_eq (Function.Embedding.toEquivRange (permTwoInj hij))).mpr rfl

/-- A permutation which swaps `i` with `i'` and `j` with `j'`. -/
noncomputable def permTwo : (FamilyPermutations n).group :=
  permOfInjection (permTwoInj hij) (permTwoInj hij')

lemma permTwo_fst : (permTwo hij hij').toFun i' = i := by
  rw [permTwo, permOfInjection]
  have ht := Equiv.extendSubtype_apply_of_mem
    ((permTwoInj hij').toEquivRange.symm.trans
    (permTwoInj hij).toEquivRange) i' (permTwoInj_fst hij')
  simp only [Equiv.trans_apply, Function.Embedding.toEquivRange_apply] at ht
  simp only [Equiv.toFun_as_coe, ht, permTwoInj_fst_apply, Fin.isValue]
  rfl

lemma permTwo_snd : (permTwo hij hij').toFun j' = j := by
  rw [permTwo, permOfInjection]
  have ht := Equiv.extendSubtype_apply_of_mem
    ((permTwoInj hij').toEquivRange.symm.trans
    (permTwoInj hij).toEquivRange) j' (permTwoInj_snd hij')
  simp only [Equiv.trans_apply, Function.Embedding.toEquivRange_apply] at ht
  simp only [Equiv.toFun_as_coe, ht, permTwoInj_snd_apply, Fin.isValue]
  rfl

end permTwo

section permThree

variable {i j k i' j' k' : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hij' : i' ≠ j')
  (hjk' : j' ≠ k') (hik' : i' ≠ k')

/-- Given three distinct elements an embedding of `Fin 3` into `Fin n`. -/
def permThreeInj : Fin 3 ↪ Fin n where
  toFun s := match s with
    | 0 => i
    | 1 => j
    | 2 => k
  inj' s1 s2 := by
    aesop

lemma permThreeInj_fst : i ∈ Set.range ⇑(permThreeInj hij hjk hik) := by
  simp only [Set.mem_range]
  use 0
  rfl

lemma permThreeInj_fst_apply :
    (Function.Embedding.toEquivRange (permThreeInj hij hjk hik)).symm
    ⟨i, permThreeInj_fst hij hjk hik⟩ = 0 := by
  exact (Equiv.symm_apply_eq (Function.Embedding.toEquivRange (permThreeInj hij hjk hik))).mpr rfl

lemma permThreeInj_snd : j ∈ Set.range ⇑(permThreeInj hij hjk hik) := by
  simp only [Set.mem_range]
  use 1
  rfl

lemma permThreeInj_snd_apply :
    (Function.Embedding.toEquivRange (permThreeInj hij hjk hik)).symm
    ⟨j, permThreeInj_snd hij hjk hik⟩ = 1 := by
  exact (Equiv.symm_apply_eq (Function.Embedding.toEquivRange (permThreeInj hij hjk hik))).mpr rfl

lemma permThreeInj_thd : k ∈ Set.range ⇑(permThreeInj hij hjk hik) := by
  simp only [Set.mem_range]
  use 2
  rfl

lemma permThreeInj_thd_apply :
    (Function.Embedding.toEquivRange (permThreeInj hij hjk hik)).symm
    ⟨k, permThreeInj_thd hij hjk hik⟩ = 2 := by
  exact (Equiv.symm_apply_eq (Function.Embedding.toEquivRange (permThreeInj hij hjk hik))).mpr rfl

/-- A permutation which swaps three distinct elements with another three. -/
noncomputable def permThree : (FamilyPermutations n).group :=
  permOfInjection (permThreeInj hij hjk hik) (permThreeInj hij' hjk' hik')

lemma permThree_fst : (permThree hij hjk hik hij' hjk' hik').toFun i' = i := by
  rw [permThree, permOfInjection]
  have ht := Equiv.extendSubtype_apply_of_mem
    ((permThreeInj hij' hjk' hik').toEquivRange.symm.trans
    (permThreeInj hij hjk hik).toEquivRange) i' (permThreeInj_fst hij' hjk' hik')
  simp only [Equiv.trans_apply, Function.Embedding.toEquivRange_apply] at ht
  simp only [Equiv.toFun_as_coe, ht, permThreeInj_fst_apply, Fin.isValue]
  rfl

lemma permThree_snd : (permThree hij hjk hik hij' hjk' hik').toFun j' = j := by
  rw [permThree, permOfInjection]
  have ht := Equiv.extendSubtype_apply_of_mem
    ((permThreeInj hij' hjk' hik').toEquivRange.symm.trans
    (permThreeInj hij hjk hik).toEquivRange) j' (permThreeInj_snd hij' hjk' hik')
  simp only [Equiv.trans_apply, Function.Embedding.toEquivRange_apply] at ht
  simp only [Equiv.toFun_as_coe, ht, permThreeInj_snd_apply, Fin.isValue]
  rfl

lemma permThree_thd : (permThree hij hjk hik hij' hjk' hik').toFun k' = k := by
  rw [permThree, permOfInjection]
  have ht := Equiv.extendSubtype_apply_of_mem
    ((permThreeInj hij' hjk' hik').toEquivRange.symm.trans
    (permThreeInj hij hjk hik).toEquivRange) k' (permThreeInj_thd hij' hjk' hik')
  simp only [Equiv.trans_apply, Function.Embedding.toEquivRange_apply] at ht
  simp only [Equiv.toFun_as_coe, ht, permThreeInj_thd_apply, Fin.isValue]
  rfl

end permThree

lemma Prop_two (P : ℚ × ℚ → Prop) {S : (PureU1 n).LinSols}
    {a b : Fin n} (hab : a ≠ b)
    (h : ∀ (f : (FamilyPermutations n).group),
    P ((((FamilyPermutations n).linSolRep f S).val a),
      (((FamilyPermutations n).linSolRep f S).val b))) : ∀ (i j : Fin n) (_ : i ≠ j),
    P (S.val i, S.val j) := by
  intro i j hij
  have h1 := h (permTwo hij hab).symm
  rw [FamilyPermutations_anomalyFreeLinear_apply, FamilyPermutations_anomalyFreeLinear_apply] at h1
  simp only [Equiv.invFun_as_coe, Equiv.symm_symm] at h1
  change P
    (S.val ((permTwo hij hab).toFun a),
    S.val ((permTwo hij hab).toFun b)) at h1
  erw [permTwo_fst,permTwo_snd] at h1
  exact h1

lemma Prop_three (P : ℚ × ℚ × ℚ → Prop) {S : (PureU1 n).LinSols}
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : ∀ (f : (FamilyPermutations n).group),
    P ((((FamilyPermutations n).linSolRep f S).val a),
      ((((FamilyPermutations n).linSolRep f S).val b),
      (((FamilyPermutations n).linSolRep f S).val c)))) : ∀ (i j k : Fin n)
      (_ : i ≠ j) (_ : j ≠ k) (_ : i ≠ k), P (S.val i, (S.val j, S.val k)) := by
  intro i j k hij hjk hik
  have h1 := h (permThree hij hjk hik hab hbc hac).symm
  rw [FamilyPermutations_anomalyFreeLinear_apply, FamilyPermutations_anomalyFreeLinear_apply,
    FamilyPermutations_anomalyFreeLinear_apply] at h1
  simp only [Equiv.invFun_as_coe, Equiv.symm_symm] at h1
  change P
    (S.val ((permThree hij hjk hik hab hbc hac).toFun a),
    S.val ((permThree hij hjk hik hab hbc hac).toFun b),
    S.val ((permThree hij hjk hik hab hbc hac).toFun c)) at h1
  erw [permThree_fst,permThree_snd, permThree_thd] at h1
  exact h1

end PureU1
