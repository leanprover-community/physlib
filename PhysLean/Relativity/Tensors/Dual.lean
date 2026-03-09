/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.MetricTensor
/-!

# Dual tensors

-/

@[expose] public section

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C G : Type} [Group G] {S : TensorSpecies k C G}

namespace Tensor

/-- The linear map taking a tensor based on the color `S.τ c` to a tensor
  based on the color `c`, defined by contraction with the metric tensor. -/
noncomputable def fromDualMap {c : C} : S.Tensor ![S.τ c] →ₗ[k] S.Tensor ![c] where
  toFun t := permT id (by simp; rfl)
    (contrT 1 1 2 (by simp; rfl) (prodT (metricTensor c) t))
  map_add' t1 t2 := by
    simp
  map_smul' r t := by
    simp

lemma fromDualMap_apply {c : C} (t : S.Tensor ![S.τ c]) :
    fromDualMap t = permT id (by simp; rfl)
      (contrT 1 1 2 (by simp; rfl) (prodT (metricTensor c) t)) := by
  rfl

/-- The linear map taking a tensor based on the color `c` to a tensor
  based on the color `S.τ c`, defined by contraction with the metric tensor. -/
noncomputable def toDualMap {c : C} : S.Tensor ![c] →ₗ[k] S.Tensor ![S.τ c] where
  toFun t := permT id (by
    simp; rfl) (contrT 1 1 2 (by
    change _ ∧ S.τ (S.τ c) = c
    simp) (prodT (metricTensor (S.τ c)) t))
  map_add' t1 t2 := by
    simp
  map_smul' r t := by
    simp

lemma toDualMap_apply {c : C} (t : S.Tensor ![c]) :
    toDualMap t = permT id (by
      simp; rfl) (contrT 1 1 2 (by
      change _ ∧ S.τ (S.τ c) = c
      simp) (prodT (metricTensor (S.τ c)) t)) := by
  rfl

@[simp]
lemma toDualMap_fromDualMap {c : C} (t : S.Tensor ![S.τ c]) :
    toDualMap (fromDualMap t) = t := by
  rw [toDualMap_apply, fromDualMap_apply, prodT_permT_right, prodT_contrT_snd]
  rw [contrT_permT, contrT_permT]
  rw [contrT_comm, permT_permT, permT_permT]
  conv_lhs =>
    enter [2, 2]
    change contrT 1 1 2 _ _
    enter [2]
    change contrT 3 1 2 _ _
  conv_lhs =>
    enter [2, 2, 2, 2];
    rw [prodT_assoc']
    enter [2]
    rw [prodT_swap]
  conv_lhs =>
    enter [2, 2, 2]
    rw [contrT_permT]
    enter [2]
    rw [contrT_permT]
    enter [2]
    rw [contrT_congr (finSumFinEquiv (m := 1) (n := 4) (Sum.inr 1))
      (finSumFinEquiv (m := 1) (n := 4) (Sum.inr 2)) _ (by rfl) (by rfl)]
    enter [2]
    rw (transparency := .instances) [contrT_prodT_snd 1 2 (by change _ ∧ S.τ (S.τ c) = c; simp)]
    rw [contrT_dual_metricTensor_metricTensor]
    rw [prodT_permT_right, prodT_swap]
    simp only [prodRightMap_id, permT_permT, CompTriple.comp_eq]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [permT_permT]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [permT_permT]
  conv_lhs =>
    enter [2, 2, 2]
    rw [permT_permT]
  conv_lhs =>
    enter [2, 2]
    rw (transparency := .instances) [contrT_permT]
  conv_lhs =>
    enter [2, 2, 2]
    rw [contrT_congr 1 2 _ (by rfl) (by rfl)]
    enter [2]
    rw [contrT_unitTensor_dual_single]
  simp only [permT_permT, CompTriple.comp_eq]
  rw (transparency := .instances) [permT_permT]
  apply permT_congr_eq_id
  ext i
  fin_cases i
  simp

lemma fromDualMap_eq_permT_toDualMap {c : C} (t : S.Tensor ![S.τ c]) :
    fromDualMap t = permT id (by simp) (toDualMap t) := by
  rw [fromDualMap_apply, toDualMap_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, permT_permT, CompTriple.comp_eq]
  rw [metricTensor_congr (by simp : c = S.τ (S.τ c))]
  rw [prodT_permT_left, contrT_permT]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, permT_permT, CompTriple.comp_eq]
  apply permT_congr
  · ext i
    fin_cases i
    rfl
  · rfl

lemma toDualMap_eq_permT_fromDualMap {c : C} (t : S.Tensor ![c]) :
    toDualMap t = (fromDualMap (permT id (by simp) t)) := by
  rw [fromDualMap_eq_permT_toDualMap]
  rw [toDualMap_apply, toDualMap_apply]
  conv_rhs =>
    enter [2, 2]
    rw [prodT_permT_right]
    rw [metricTensor_congr (by simp : S.τ (S.τ (S.τ c)) = S.τ c)]
    rw [prodT_permT_left]
    rw [contrT_permT, contrT_permT]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, permT_permT, CompTriple.comp_eq,
    τ_τ_apply, PermCond.on_id, Matrix.cons_val_fin_one, implies_true]
  apply permT_congr
  · ext i
    fin_cases i
    rfl
  · rfl

@[simp]
lemma fromDualMap_toDualMap {c : C} (t : S.Tensor ![c]) :
    fromDualMap (toDualMap t) = t := by
  rw [fromDualMap_eq_permT_toDualMap]
  conv_lhs =>
    enter [2, 2]
    rw [toDualMap_eq_permT_fromDualMap]
  simp

/-- The linear equivalence between `S.Tensor ![c]` and
  `S.Tensor ![S.τ c]` formed by contracting with metric tensors. -/
noncomputable def toDual {c : C} : S.Tensor ![c] ≃ₗ[k] S.Tensor ![S.τ c] :=
  LinearEquiv.mk toDualMap fromDualMap.toFun
    (fun x => by simp) (fun x => by simp)

lemma toDual_equivariant {c : C} (g : G) (t : S.Tensor ![c]) :
    toDual (g • t) = g • toDual t := by
  simp [toDual, toDualMap]
  conv_lhs => rw [← metricTensor_invariant g]
  rw [prodT_equivariant, contrT_equivariant, permT_equivariant]

end Tensor

open Tensor
@[simp]
lemma repDim_τ {c : C} [StrongRankCondition k] :
    S.repDim (S.τ c) = S.repDim c := by
  trans Module.finrank k (S.Tensor ![S.τ c])
  · rw [finrank_tensor_eq]
    simp
  rw [toDual.symm.finrank_eq]
  rw [finrank_tensor_eq]
  simp

end TensorSpecies
