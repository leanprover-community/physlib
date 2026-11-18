/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Order.Filter.IndicatorFunction
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Indicators of disjoint unions

The indicator of a disjoint union is the sum of the indicators of its parts.

## i. Overview

At each point at most one set of a disjoint family contains the point. The indicators of the
sets therefore sum to the indicator of their union. For nonnegative values the partial sums
increase to this indicator.

## ii. Key results

- `Set.hasSum_indicator_iUnion` : indicators of disjoint sets sum to the indicator of the union.
- `Set.isLUB_sum_indicator_iUnion` : nonnegative partial sums increase to the union indicator.

## iii. Table of contents

- A. Disjoint unions

## iv. References

-/

@[expose] public section

namespace Set

variable {α : Type*} {s : ℕ → Set α}

/-! ## A. Disjoint unions -/

/-- The indicators of disjoint sets sum to the indicator of their union. -/
lemma hasSum_indicator_iUnion {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (hd : Pairwise (Function.onFun Disjoint s)) (f : α → M) (x : α) :
    HasSum (fun n ↦ (s n).indicator f x) ((⋃ n, s n).indicator f x) := by
  simpa only [HasSum, SummationFilter.unconditional_filter,
    ← Finset.indicator_biUnion_apply _ _ (hd.set_pairwise _)] using
    (tendsto_indicator_biUnion_finset s f x).mono_right (pure_le_nhds _)

/-- For nonnegative values the partial sums of indicators of disjoint sets increase to the
indicator of their union. -/
lemma isLUB_sum_indicator_iUnion {f : α → ℝ} (hf : 0 ≤ f)
    (hd : Pairwise (Function.onFun Disjoint s)) (x : α) :
    IsLUB (range fun N ↦ ∑ n ∈ Finset.range N, (s n).indicator f x)
      ((⋃ n, s n).indicator f x) :=
  isLUB_of_tendsto_atTop
    ((Finset.sum_mono_set_of_nonneg fun _ ↦ Set.indicator_nonneg (fun y _ ↦ hf y) x).comp
      Finset.range_mono)
    (hasSum_indicator_iUnion hd f x).tendsto_sum_nat

end Set
