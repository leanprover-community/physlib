/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Channel.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Channels are contractions

Unital positive linear maps are contractions with respect to the order-unit norm and are
therefore continuous.

## i. Overview

An observable lies between the positive and negative multiples of the certain outcome set by
its order-unit norm. A channel preserves both inequalities and the certain outcome, so the
same bound holds for its image.

## ii. Key results

- `Channel.norm_apply_le`: Channels are contractions.
- `Channel.continuous`: Channels are continuous.
- `Channel.toContinuousLinearMap`: Channels as continuous linear maps.

## iii. Table of contents

- A. Contractivity and continuity

## iv. References

-/

@[expose] public section

open ProbabilisticTheory

/-! ## A. Contractivity and continuity -/

namespace Channel

variable {P Q : ProbabilisticTheory}

/-- Unital positive linear maps are contractions for the order-unit norm. -/
lemma orderUnitNorm_apply_le (T : Channel P Q) (x : P.Observables) :
    orderUnitNorm (T x) ≤ orderUnitNorm x := by
  apply orderUnitNorm_le
  refine ⟨orderUnitNorm_nonneg x, ?_, ?_⟩
  · simpa using OrderHomClass.mono T (neg_orderUnitNorm_smul_one_le x)
  · simpa using OrderHomClass.mono T (le_orderUnitNorm_smul_one x)

/-- Unital positive linear maps are contractions for the norm. -/
lemma norm_apply_le (T : Channel P Q) (x : P.Observables) : ‖T x‖ ≤ ‖x‖ :=
  T.orderUnitNorm_apply_le x

/-- Unital positive linear maps are continuous. -/
@[continuity, fun_prop]
lemma continuous (T : Channel P Q) : Continuous T :=
  AddMonoidHomClass.continuous_of_bound T 1 (by simpa using T.norm_apply_le)

/-- A unital positive linear map regarded as a continuous linear map. -/
noncomputable def toContinuousLinearMap (T : Channel P Q) : P.Observables →L[ℝ] Q.Observables :=
  ⟨T.toLinearMap, T.continuous⟩

@[simp] lemma toContinuousLinearMap_apply (T : Channel P Q) (x : P.Observables) :
    T.toContinuousLinearMap x = T x := rfl

end Channel
