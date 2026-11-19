/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Vector.Invariants.Basic
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Pre
/-!
# Lorentz invariants among two four-vector indices

Up to scale, the metric is the only Lorentz invariant of two four-vector indices.

## i. Overview

A rank-two tensor `T^{μν}` has a single Lorentz invariant up to scale, its contraction with the
metric: nothing else ties two indices, the Levi-Civita symbol needing four. The invariant tensors
with two four-vector indices are the line through the metric `η` (A, B). Relabelled to
`ℂT[.up, .up]` such a tensor is `fromPairT` of an element of `ComplexVector ⊗ ComplexVector`, and
the invariants of that tensor product are the line through the metric,
`Lorentz.ComplexVector.invariants_tprod_eq_span_metricVal`.

For an equivariant map `f : ℂT(fun _ : Fin 2 => .up) →ₗ[ℂ] B`, the
invariants of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, therefore reduce to the
line through `f metric` (C). For a given `f` the image may be zero.

## ii. Key results

- `Lorentz.RankTwo.metric` : the metric `η` with the colours `fun _ : Fin 2 => .up`.
- `Lorentz.ComplexVector.invariants_tensorPower_two_eq_span` : the invariant tensors are the line
  through the metric.
- `Lorentz.ComplexVector.reducesInvariantsTo_span_metric` : the invariants of the range of `f`,
  modulo a stable submodule, reduce to the line through `f metric`.

## iii. Table of contents

- A. The metric
- B. The invariant tensors
- C. The invariants of an equivariant map

## iv. References

* None.

-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants TensorSpecies complexLorentzTensor
open TensorSpecies.Tensor hiding ofComponents

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
    ofComponents (S := complexLorentzTensor) (c := fun _ : Fin 2 => .up) T metric
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

/-- The invariant tensors with two four-vector indices are the line through the metric.
  Relabelled to `ℂT[.up, .up]` such a tensor comes from `ComplexVector ⊗ ComplexVector`, whose
  invariants are the line through the metric. -/
lemma _root_.Lorentz.ComplexVector.invariants_tensorPower_two_eq_span :
    (complexLorentzTensor.tensorRep (fun _ : Fin 2 => Color.up)).invariants = ℂ ∙ metric := by
  refine Representation.invariants_eq_span_singleton metric_invariant fun t ht => ?_
  obtain ⟨a, ha⟩ := Representation.exists_eq_smul_of_invariants_eq_span
    (invariants_tensorRep_pair_eq_span (S := complexLorentzTensor) (c1 := .up) (c2 := .up)
      ComplexVector.invariants_tprod_eq_span_metricVal) (x := permT id isReindexing_up_up t)
    fun g => by rw [tensorRep_apply, ← permT_equivariant, show g • t = t from ht g]
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
lemma _root_.Lorentz.ComplexVector.reducesInvariantsTo_span_metric
    (hf : complexLorentzTensor.IsEquivariant (fun _ : Fin 2 => .up) repLorentz f) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f)
      (ℂ ∙ f metric) := by
  have h := TensorSpecies.IsEquivariant.reducesInvariantsTo_span hf
    (complexLorentzTensor.hasReynolds _) ComplexVector.invariants_tensorPower_two_eq_span
  rwa [Set.image_singleton] at h

end RankTwo

end Lorentz
