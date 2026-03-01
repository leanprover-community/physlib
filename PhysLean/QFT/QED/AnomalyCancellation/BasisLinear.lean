/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.QED.AnomalyCancellation.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
/-!
# Basis of `LinSols`

We give a basis of vector space `LinSols`, and find the rank thereof.

-/

namespace PureU1

open BigOperators Module

variable {n : ℕ}
namespace BasisLinear

/-- The basis elements as charges, defined to have a `1` in the `j`th position and a `-1` in the
last position. -/
@[simp]
def asCharges (j : Fin n) : (PureU1 n.succ).Charges :=
  (fun i =>
    if i = j.castSucc then 1
    else if i = Fin.last n then
        - 1
      else 0)

lemma asCharges_eq_castSucc (j : Fin n) :
    asCharges j (Fin.castSucc j) = 1 := by
  simp [asCharges]

lemma asCharges_ne_castSucc {k j : Fin n} (h : k ≠ j) :
    asCharges k (Fin.castSucc j) = 0 := by
  simp only [asCharges, Nat.succ_eq_add_one, PureU1_numberCharges, Fin.castSucc_inj]
  split
  · rename_i h1
    exact False.elim (h (id (Eq.symm h1)))
  · split
    · rename_i h1 h2
      rw [Fin.ext_iff] at h1 h2
      simp only [Fin.val_castSucc, Fin.val_last] at h1 h2
      have hj : j.val < n := by
        exact j.prop
      simp_all
    · rfl

/-- The basis elements as `LinSols`. -/
@[simps!]
def asLinSols (j : Fin n) : (PureU1 n.succ).LinSols :=
  ⟨asCharges j, by
    intro i
    simp only [Nat.succ_eq_add_one, PureU1_numberLinear] at i
    match i with
    | 0 =>
    simp only [Fin.isValue, PureU1_linearACCs, accGrav,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [Fin.sum_univ_castSucc]
    rw [Finset.sum_eq_single j]
    · simp only [asCharges, PureU1_numberCharges, ↓reduceIte]
      have hn : ¬ (Fin.last n = Fin.castSucc j) := Fin.ne_of_gt j.prop
      split
      · rename_i ht
        exact (hn ht).elim
      · with_unfolding_all rfl
    · intro k _ hkj
      exact asCharges_ne_castSucc hkj.symm
    · intro hk
      simp at hk⟩

lemma sum_of_vectors {n : ℕ} (f : Fin k → (PureU1 n).LinSols) (j : Fin n) :
    (∑ i : Fin k, (f i)).1 j = (∑ i : Fin k, (f i).1 j) :=
  sum_of_anomaly_free_linear (fun i => f i) j

TODO "6VZO6" "The definition of `coordinateMap` here may be improved by replacing
  `Finsupp.equivFunOnFinite` with `Finsupp.linearEquivFunOnFinite`. Investigate this."
/-- The coordinate map for the basis. -/
noncomputable
def coordinateMap : (PureU1 n.succ).LinSols ≃ₗ[ℚ] Fin n →₀ ℚ where
  toFun S := Finsupp.equivFunOnFinite.invFun (S.1 ∘ Fin.castSucc)
  map_add' S T := Finsupp.ext (congrFun rfl)
  map_smul' a S := Finsupp.ext (congrFun rfl)
  invFun f := ∑ i : Fin n, f i • asLinSols i
  left_inv S := by
    simp only [Nat.succ_eq_add_one, PureU1_numberCharges, Equiv.invFun_as_coe,
      Finsupp.equivFunOnFinite_symm_apply_apply, Function.comp_apply]
    apply pureU1_anomalyFree_ext
    intro j
    rw [sum_of_vectors]
    simp only [HSMul.hSMul, SMul.smul, PureU1_numberCharges,
      asLinSols_val]
    rw [Finset.sum_eq_single j]
    · simp only [asCharges, PureU1_numberCharges, ↓reduceIte, mul_one]
    · intro k _ hkj
      rw [asCharges_ne_castSucc hkj]
      exact Rat.mul_zero (S.val k.castSucc)
    · simp
  right_inv f := by
    simp only [PureU1_numberCharges, Equiv.invFun_as_coe]
    ext
    rename_i j
    simp only [Nat.succ_eq_add_one, Finsupp.equivFunOnFinite_symm_apply_apply, Function.comp_apply]
    rw [sum_of_vectors]
    simp only [HSMul.hSMul, SMul.smul, PureU1_numberCharges,
      asLinSols_val]
    rw [Finset.sum_eq_single j]
    · simp only [asCharges, PureU1_numberCharges, ↓reduceIte, mul_one]
    · intro k _ hkj
      rw [asCharges_ne_castSucc hkj]
      exact Rat.mul_zero (f k)
    · simp

/-- The basis of `LinSols`. -/
noncomputable
def asBasis : Basis (Fin n) ℚ ((PureU1 n.succ).LinSols) where
  repr := coordinateMap

/-- The module over `ℚ` defined by linear solutions to the pure `U(1)` ACCs is finite. -/
instance : Module.Finite ℚ ((PureU1 n.succ).LinSols) :=
  Module.Finite.of_basis asBasis

/-- The module of solutions to the linear pure-U(1) acc has rank equal to `n`. -/
lemma finrank_AnomalyFreeLinear :
    Module.finrank ℚ (((PureU1 n.succ).LinSols)) = n := by
  have h := Module.mk_finrank_eq_card_basis (@asBasis n)
  simp only [Nat.succ_eq_add_one, Module.finrank_eq_rank, Cardinal.mk_fintype,
    Fintype.card_fin] at h
  exact Module.finrank_eq_of_rank_eq h

end BasisLinear

end PureU1
