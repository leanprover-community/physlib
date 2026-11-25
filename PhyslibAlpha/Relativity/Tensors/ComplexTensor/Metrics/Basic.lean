/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Basic
public import PhyslibAlpha.Relativity.Fermions.Weyl.Metric
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Pre
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Vector.InvariantCoeff
/-!
# The metrics are the unique invariant tensors with two indices of one colour

Up to scale, the metric of a colour is the only invariant tensor with two indices of that colour.

## i. Overview

A tensor with two indices of colour `k` is `fromPairT` of an element of the tensor square of the
representation of that colour. The invariants of that tensor square are the line through the
metric, for the four-vectors, the covectors and each of the four Weyl representations, so the
invariant tensors of `ℂT[k, k]` are the line through `metricTensor k` (A). For an equivariant map
`f` out of `ℂT[k, k]`, every Lorentz invariant of the range of `f` is a multiple of
`f (metricTensor k)`, modulo a Lorentz-stable submodule, the shape of a mass term (B).

The colours `fun _ : Fin 2 => .up` of two four-vector indices are a reindexing of `![.up, .up]`,
so the invariant tensors with these colours are the line through the reindexed metric
`RankTwo.metric`, whose components are the Minkowski metric (C).

## ii. Key results

- `complexLorentzTensor.invariants_pair_eq_span_metricTensor` : the invariant tensors with two
  indices of one colour are the line through the metric.
- `Lorentz.invariantReductionToMetricTensor` : the invariants of the range of an equivariant map
  reduce to the image of the metric.
- `complexLorentzTensor.invariants_up_pow_two_eq_span_metric` : the same for the colours
  `fun _ : Fin 2 => .up`.
- `Lorentz.ComplexVector.reducesInvariantsTo_span_metric` : the invariants of an equivariant map
  out of these tensors reduce to the image of the metric.

## iii. Table of contents

- A. The invariant tensors with two indices of one colour
- B. The reduction to the metric
- C. Two four-vector indices with constant colours
  - C.1. The metric with constant colours
  - C.2. The invariant tensors
  - C.3. The invariants of an equivariant map

## iv. References

The uniqueness of the metric of each representation is in
`PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Pre` and
`PhyslibAlpha.Relativity.Fermions.Weyl.Metric`.

-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants TensorSpecies complexLorentzTensor
open TensorSpecies.Tensor

/-!

## A. The invariant tensors with two indices of one colour

-/

/-- The invariant tensors with two indices of one colour are the line through the metric of that
  colour. A tensor with two indices comes from the tensor square of the representation of the
  colour, whose invariants are the line through the metric. -/
lemma _root_.complexLorentzTensor.invariants_pair_eq_span_metricTensor
    (k : complexLorentzTensor.Color) :
    (complexLorentzTensor.tensorRep ![k, k]).invariants = ℂ ∙ metricTensor k := by
  cases k
  · rw [invariants_tensorRep_pair_eq_span (S := complexLorentzTensor) (c1 := .upL) (c2 := .upL)
      Fermion.LeftHandedWeyl.invariants_tprod_eq_span_metricVal]
    exact congrArg (ℂ ∙ fromPairT ·) Fermion.LeftHandedWeyl.metric_apply_one.symm
  · rw [invariants_tensorRep_pair_eq_span (S := complexLorentzTensor) (c1 := .downL)
      (c2 := .downL) Fermion.DualLeftHandedWeyl.invariants_tprod_eq_span_metricVal]
    exact congrArg (ℂ ∙ fromPairT ·) Fermion.DualLeftHandedWeyl.metric_apply_one.symm
  · rw [invariants_tensorRep_pair_eq_span (S := complexLorentzTensor) (c1 := .upR) (c2 := .upR)
      Fermion.RightHandedWeyl.invariants_tprod_eq_span_metricVal]
    exact congrArg (ℂ ∙ fromPairT ·) Fermion.RightHandedWeyl.metric_apply_one.symm
  · rw [invariants_tensorRep_pair_eq_span (S := complexLorentzTensor) (c1 := .downR)
      (c2 := .downR) Fermion.DualRightHandedWeyl.invariants_tprod_eq_span_metricVal]
    exact congrArg (ℂ ∙ fromPairT ·) Fermion.DualRightHandedWeyl.metric_apply_one.symm
  · rw [invariants_tensorRep_pair_eq_span (S := complexLorentzTensor) (c1 := .up) (c2 := .up)
      ComplexVector.invariants_tprod_eq_span_metricVal]
    exact congrArg (ℂ ∙ fromPairT ·) ComplexVector.metric_apply_one.symm
  · rw [invariants_tensorRep_pair_eq_span (S := complexLorentzTensor) (c1 := .down)
      (c2 := .down) ComplexCoVector.invariants_tprod_eq_span_metricVal]
    exact congrArg (ℂ ∙ fromPairT ·) ComplexCoVector.metric_apply_one.symm

/-!

## B. The reduction to the metric

-/

/-- For an equivariant map `f` out of `ℂT[k, k]`, the Lorentz invariants of the range of `f`
  reduce to the span of the image `f (metricTensor k)` of the metric. -/
noncomputable def invariantReductionToMetricTensor {k : complexLorentzTensor.Color} {B : Type*}
    [AddCommGroup B] [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}
    {f : ℂT[k, k] →ₗ[ℂ] B} (hf : complexLorentzTensor.IsEquivariant ![k, k] repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  hf.invariantReductionToSpan (complexLorentzTensor.hasReynolds _)
    (invariants_pair_eq_span_metricTensor k)

/-!

## C. Two four-vector indices with constant colours

-/

namespace RankTwo

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-!

### C.1. The metric with constant colours

-/

/-- Relabelling the colours `![.up, .up]` of two indices as `fun _ => .up`. -/
lemma isReindexing_up_up :
    IsReindexing ![Color.up, Color.up] (fun _ : Fin 2 => Color.up) id :=
  ⟨Function.bijective_id, fun i => by fin_cases i <;> rfl⟩

/-- The metric `η` on two contravariant indices, with its colours relabelled from
  `![.up, .up]` to `fun _ => .up`. -/
noncomputable def metric : ℂT(fun _ : Fin 2 => Color.up) :=
  permT id isReindexing_up_up η

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

/-- `liftComponents T` sends the metric to the contraction `η_{μν} T^{μν}`. -/
lemma liftComponents_metric (T : (Fin 2 → Fin 1 ⊕ Fin 3) → B) :
    liftComponents T metric
      = ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ) • T d := by
  rw [← coeffEquiv_symm_minkowskiMatrixZ, liftComponents_coeffEquiv_symm]

/-!

### C.2. The invariant tensors

-/

/-- The invariant tensors with two four-vector indices of constant colours are the line through
  the metric, the reindexing of the line through `η`. -/
lemma _root_.complexLorentzTensor.invariants_up_pow_two_eq_span_metric :
    (complexLorentzTensor.tensorRep (fun _ : Fin 2 => Color.up)).invariants = ℂ ∙ metric := by
  rw [invariants_tensorRep_eq_span_of_permT isReindexing_up_up
    (invariants_pair_eq_span_metricTensor .up), Set.image_singleton]
  rfl

/-!

### C.3. The invariants of an equivariant map

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
    (complexLorentzTensor.hasReynolds _) invariants_up_pow_two_eq_span_metric
  rwa [Set.image_singleton] at h

end RankTwo

end Lorentz
