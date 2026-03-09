/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.UnitTensor
/-!

# The metric tensors

-/

@[expose] public section

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C G : Type} [Group G] {S : TensorSpecies k C G}

open Tensor

/-- The metric tensor associated with a color `c`. -/
noncomputable def metricTensor (c : C) : S.Tensor ![c, c] :=
  fromConstPair (S.metric.app (Discrete.mk c))

lemma metricTensor_congr {c c1 : C} (h : c = c1) :
    S.metricTensor c = permT id (by simp [h]) (metricTensor c1) := by
  subst h
  simp

@[simp]
lemma metricTensor_invariant {c : C} (g : G) :
    g • S.metricTensor c = metricTensor c := by
  rw [metricTensor, actionT_fromConstPair]

lemma permT_fromPairTContr_metric_metric {c : C} :
    permT ![1, 0] (And.intro (by decide) (fun i => by fin_cases i <;> rfl))
    (fromPairTContr ((S.metric.app (Discrete.mk c)).hom (1 : k))
    ((S.metric.app (Discrete.mk (S.τ c))).hom (1 : k))) =
    (unitTensor c) := by
  rw [fromPairTContr, ← fromPairT_comm]
  change _ = fromPairT ((S.unit.app (Discrete.mk c)).hom (1 : k))
  rw [← S.contr_metric]
  rfl

lemma fromPairTContr_metric_metric_eq_permT_unit {c : C} :
    fromPairTContr ((S.metric.app (Discrete.mk c)).hom (1 : k))
    ((S.metric.app (Discrete.mk (S.τ c))).hom (1 : k)) =
    permT ![1, 0] (And.intro (by decide) (fun i => by fin_cases i <;> rfl))
    (unitTensor c) := by
  rw [← permT_fromPairTContr_metric_metric]
  rw [permT_permT]
  symm
  apply permT_congr_eq_id
  decide

/-- The contraction of the metric tensor with its dual gives the unit tensor.
  This is the de-categorification of `S.contr_metric`. -/
@[simp]
lemma contrT_metricTensor_metricTensor {c : C} :
    contrT 2 1 2 (by simp; rfl) (prodT (metricTensor c) (metricTensor (S.τ c))) =
      permT ![1, 0] (And.intro (by decide) (fun i => by fin_cases i <;> rfl))
      (unitTensor (S := S) c) := by
  rw [metricTensor, metricTensor, fromConstPair, fromConstPair]
  rw [fromPairT_contr_fromPairT_eq_fromPairTContr]
  erw [fromPairTContr_metric_metric_eq_permT_unit]
  rw [permT_permT]
  rfl

lemma contrT_metricTensor_metricTensor_eq_dual_unit {c : C} :
    contrT 2 1 2 (by simp; rfl) (prodT (metricTensor c) (metricTensor (S.τ c))) =
      permT ![0, 1] (And.intro (by decide) (fun i => by
        fin_cases i
        · change S.τ (S.τ c) = c
          simp
        · rfl))
      (unitTensor (S := S) (S.τ c)) := by
  rw [contrT_metricTensor_metricTensor]
  rw [unitTensor_eq_permT_dual]
  rw [permT_permT]
  apply permT_congr
  · decide
  · rfl

@[simp]
lemma contrT_dual_metricTensor_metricTensor {c : C} :
    contrT 2 1 2 (by change _ ∧ S.τ (S.τ c) = c; simp)
      (prodT (metricTensor (S.τ c)) (metricTensor c)) =
      permT id (by simp; exact ⟨rfl,rfl⟩) (unitTensor (S := S) c) := by
  have hm := S.metricTensor_congr (by simp : c = S.τ (S.τ c))
  rw [hm]
  rw [prodT_permT_right, contrT_permT]
  conv_lhs =>
    enter [2]
    change contrT 2 1 2 _ _
    rw [contrT_metricTensor_metricTensor]
  simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue]
  conv_rhs => rw [unitTensor_eq_permT_dual]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, permT_permT, CompTriple.comp_eq]
  rw (transparency := .instances) [permT_permT]
  apply permT_congr
  · ext i
    fin_cases i <;> rfl
  · rfl

end TensorSpecies
