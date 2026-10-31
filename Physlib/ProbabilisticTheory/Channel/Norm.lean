/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Separation

/-!
# Channels are contractions

Unital positive linear maps are contractions with respect to the order-unit norm and are
therefore continuous.

## i. Overview

The norm bound follows from the characterization of the order-unit norm in terms of states.
Every state on the codomain pulls back along a channel to a state on the domain, so evaluating
the image of an observable cannot exceed its original norm.

## ii. Key results

- `UnitalPositiveLinearMap.norm_apply_le`: Channels are contractions.
- `UnitalPositiveLinearMap.continuous`: Channels are continuous.
- `UnitalPositiveLinearMap.toContinuousLinearMap`: Channels as continuous linear maps.

## iii. Table of contents

- A. Contractivity and continuity

## iv. References

-/

@[expose] public section

open ProbabilisticTheory ArchimedeanOrderUnitSpace
open scoped ArchimedeanOrderUnitSpace

/-! ## A. Contractivity and continuity -/

namespace UnitalPositiveLinearMap

variable {E F : Type*} [ArchimedeanOrderUnitSpace E] [ArchimedeanOrderUnitSpace F]

/-- Unital positive linear maps are contractions for the order-unit norm. -/
lemma orderUnitNorm_apply_le (T : E →ₚ₁[ℝ] F) (x : E) :
    orderUnitNorm (T x) ≤ orderUnitNorm x := by
  rcases subsingleton_or_nontrivial F with h | h
  · rw [Subsingleton.elim (T x) 0, orderUnitNorm_zero]
    exact orderUnitNorm_nonneg x
  · refine (orderUnitNorm_le_iff_forall_abs_apply_le _ _).2 ?_
    intro ω
    exact abs_apply_le_orderUnitNorm (comap T ω) x

/-- Unital positive linear maps are contractions for the norm. -/
lemma norm_apply_le (T : E →ₚ₁[ℝ] F) (x : E) : ‖T x‖ ≤ ‖x‖ :=
  T.orderUnitNorm_apply_le x

/-- Unital positive linear maps are continuous. -/
@[continuity, fun_prop]
lemma continuous (T : E →ₚ₁[ℝ] F) : Continuous T :=
  AddMonoidHomClass.continuous_of_bound T 1 (by simpa using T.norm_apply_le)

/-- A unital positive linear map regarded as a continuous linear map. -/
noncomputable def toContinuousLinearMap (T : E →ₚ₁[ℝ] F) : E →L[ℝ] F :=
  ⟨T.toLinearMap, T.continuous⟩

@[simp] lemma toContinuousLinearMap_apply (T : E →ₚ₁[ℝ] F) (x : E) :
    T.toContinuousLinearMap x = T x := rfl

end UnitalPositiveLinearMap
