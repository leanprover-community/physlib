/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.LorentzCovariance
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Pre
/-!
# Lorentz invariants among two four-vector indices

Up to scale, the metric is the only Lorentz invariant of two four-vector indices.

## i. Overview

A rank-two tensor `T^{μν}` has a single Lorentz invariant up to scale, its contraction with the
metric: nothing else ties two indices, the Levi-Civita symbol needing four. For an equivariant
map `f : ℂT(fun _ : Fin 2 => .up) →ₗ[ℂ] B`, `IsLorentzCovariant 2`, every Lorentz invariant in the
range of `f` is a multiple of `f metric`, the image of the metric `η` (A), and modulo a
Lorentz-stable submodule `S` the invariants of `LinearMap.range f ⊔ S` reduce to the line through
it (C). For a given `f` the image may be zero.

The invariants of the range of `f` are the images of invariant tensors, so it is enough that an
invariant tensor is a multiple of the metric (B). Relabelled to `ℂT[.up, .up]` such a tensor is
`fromPairT` of an element of `ComplexVector ⊗ ComplexVector`, and the invariants of that tensor
product are the line through the metric, `Lorentz.ComplexVector.invariants_tprod_eq_span_metricVal`.

## ii. Key results

- `Lorentz.RankTwo.metric` : the metric `η` with the colours of `IsLorentzCovariant 2`.
- `Lorentz.RankTwo.exists_eq_smul_metric_of_invariant` : an invariant tensor is a multiple of
  the metric.
- `Lorentz.RankTwo.exists_smul_map_metric_of_invariant` : an invariant in the range of `f` is a
  multiple of `f metric`.
- `Lorentz.RankTwo.reducesInvariantsTo_span_metric` : the same modulo a stable submodule.

## iii. Table of contents

- A. The metric
- B. The invariant tensors
- C. The invariants of an equivariant map

## iv. References

* None.

-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants TensorSpecies Tensor complexLorentzTensor

namespace RankTwo

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-!

## A. The metric

-/

/-- The metric `η` on two contravariant indices, with its colours relabelled from
  `![.up, .up]` to `fun _ => .up`. -/
noncomputable def metric : ℂT(fun _ : Fin 2 => Color.up) :=
  permT id (show IsReindexing ![Color.up, Color.up] (fun _ : Fin 2 => Color.up) id from
    ⟨Function.bijective_id, fun i => by fin_cases i <;> rfl⟩) η

/-- The metric is Lorentz invariant. -/
lemma metric_invariant (g : SL(2,ℂ)) : g • metric = metric := by
  rw [metric, ← permT_equivariant, actionT_contrMetric]

/-- The coefficient tensor of the metric is the Minkowski metric. -/
lemma coeffEquiv_symm_minkowskiMatrixZ :
    (coeffEquiv 2).symm (fun d => ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ)) = metric := by
  rw [metric, contrMetric_eq_basis]
  simp only [map_sub, permT_basis]
  rw [coeffEquiv_symm_apply, sum_pi_fin_two]
  simp [Fintype.sum_sum_type, Fin.sum_univ_three, minkowskiMatrixZ, sub_eq_add_neg]
  rw [← add_assoc, ← add_assoc]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ (congrArg Neg.neg ?_))
    (congrArg Neg.neg ?_)) (congrArg Neg.neg ?_) <;>
    exact congrArg _ (funext fun i => by fin_cases i <;> rfl)

/-- `ofComponents T` sends the metric to the contraction `η_{μν} T^{μν}`. -/
lemma ofComponents_metric (T : (Fin 2 → Fin 1 ⊕ Fin 3) → B) :
    ofComponents T metric
      = ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ) • T d := by
  rw [← coeffEquiv_symm_minkowskiMatrixZ, ofComponents_coeffEquiv_symm]

/-!

## B. The invariant tensors

-/

/-- Relabelling the colours `fun _ => .up` of two indices as `![.up, .up]`. -/
lemma isReindexing_up_up :
    IsReindexing (fun _ : Fin 2 => Color.up) ![Color.up, Color.up] id :=
  ⟨Function.bijective_id, fun i => by fin_cases i <;> rfl⟩

/-- Relabelling the colours `![.up, .up]` of two indices as `fun _ => .up`. -/
lemma isReindexing_up_up' :
    IsReindexing ![Color.up, Color.up] (fun _ : Fin 2 => Color.up) id :=
  ⟨Function.bijective_id, fun i => by fin_cases i <;> rfl⟩

/-- The invariant tensors with two four-vector indices are the multiples of the metric.
  Relabelled to `ℂT[.up, .up]` such a tensor comes from `ComplexVector ⊗ ComplexVector`, whose
  invariants are the line through the metric. -/
lemma exists_eq_smul_metric_of_invariant (t : ℂT(fun _ : Fin 2 => Color.up))
    (ht : ∀ g : SL(2,ℂ), g • t = t) : ∃ a : ℂ, t = a • metric := by
  obtain ⟨a, ha⟩ := Tensor.exists_eq_smul_fromPairT_of_invariant (S := complexLorentzTensor)
    (c1 := .up) (c2 := .up) ComplexVector.invariants_tprod_eq_span_metricVal
    (t := permT id isReindexing_up_up t) fun g => by rw [← permT_equivariant, ht]
  have hback : permT id isReindexing_up_up' (permT id isReindexing_up_up t) = t :=
    (permT_permT _ _ t).trans (permT_congr_eq_id _ _ _ rfl)
  refine ⟨a, ?_⟩
  rw [← hback, ha, map_smul, metric, contrMetric, metricTensor, fromConstPair]
  congr 3
  exact ComplexVector.metric_apply_one.symm

/-!

## C. The invariants of an equivariant map

-/

variable {f : ℂT(fun _ : Fin 2 => Color.up) →ₗ[ℂ] B}

/-- The invariants of the range of `f` reduce to the line through the image `f metric` of the
  metric. A Lorentz invariant of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is
  a multiple of `f metric` plus an element of `S`. -/
lemma reducesInvariantsTo_span_metric (hf : IsLorentzCovariant 2 B repLorentz f) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f)
      (ℂ ∙ f metric) := by
  have h := hf.reducesInvariantsTo_map (complexLorentzTensor.isAdjointClosed _) (ℂ ∙ metric)
    fun t ht => by
      obtain ⟨a, rfl⟩ := exists_eq_smul_metric_of_invariant t ht
      exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
  rwa [Submodule.map_span, Set.image_singleton] at h

/-- Every Lorentz invariant of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is a
  multiple of the image `f metric` of the metric plus an element of `S`. -/
lemma exists_smul_map_metric_add_of_invariant (hf : IsLorentzCovariant 2 B repLorentz f)
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ LinearMap.range f ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • f metric + y := by
  obtain ⟨z, hz, y, hy, rfl⟩ := Submodule.mem_sup.1
    (reducesInvariantsTo_span_metric hf S hS x hx hinv)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨a, y, hy, rfl⟩

/-- Every Lorentz invariant in the range of `f` is a multiple of the image `f metric` of the
  metric. -/
lemma exists_smul_map_metric_of_invariant (hf : IsLorentzCovariant 2 B repLorentz f) {x : B}
    (hx : x ∈ LinearMap.range f) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • f metric := by
  obtain ⟨a, y, hy, rfl⟩ := exists_smul_map_metric_add_of_invariant hf ⊥
    (fun _ _ hy => by rw [(Submodule.mem_bot ℂ).1 hy, map_zero]; exact Submodule.zero_mem _)
    (Submodule.mem_sup_left hx) hinv
  rw [(Submodule.mem_bot ℂ).1 hy, add_zero]
  exact ⟨a, rfl⟩

end RankTwo

end Lorentz
