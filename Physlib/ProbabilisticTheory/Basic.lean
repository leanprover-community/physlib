/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Basic.Real.Basic

/-!
# Probabilistic theories

A probabilistic theory is described by its ordered real observables and a certain outcome.

## i. Overview

The observables of a physical system form an ordered real vector space. Positive observables are
those whose measured values are never negative. The certain outcome `1` bounds every observable
up to a multiple and sets the scale of the theory. The order is Archimedean, so no observable is
infinitesimally positive and the certain outcome defines a genuine norm.

## ii. Key results

- `ProbabilisticTheory` : ordered real observables with a certain outcome and an Archimedean
  order.

## iii. Table of contents

- A. Observable space and certain outcome

## iv. References

-/

@[expose] public section

/-! ## A. Observable space and certain outcome -/

/-- An ordered real observable space with a certain outcome and no infinitesimal observables. -/
structure ProbabilisticTheory where
  /-- The real observables. -/
  Observables : Type*
  /-- Observables can be added and subtracted. -/
  [addCommGroup : AddCommGroup Observables]
  /-- The order saying which observables are positive. -/
  [partialOrder : PartialOrder Observables]
  /-- Observables can be scaled by real numbers. -/
  [module : Module ℝ Observables]
  /-- Adding an observable preserves the order. -/
  [isOrderedAddMonoid : IsOrderedAddMonoid Observables]
  /-- Scaling by a nonnegative real preserves the order. -/
  [posSMulMono : PosSMulMono ℝ Observables]
  /-- The certain outcome. -/
  [one : One Observables]
  /-- The certain outcome is nonnegative. -/
  one_nonneg' : 0 ≤ (1 : Observables)
  /-- Every observable is bounded above by a natural multiple of the certain outcome. -/
  exists_nsmul_one_le' : ∀ B : Observables, ∃ n : ℕ, B ≤ n • (1 : Observables)
  /-- An observable below every positive multiple of the certain outcome is nonpositive. -/
  le_zero_of_forall_pos_smul_one_le' : ∀ A : Observables,
    (∀ ε : ℝ, 0 < ε → A ≤ ε • (1 : Observables)) → A ≤ 0

attribute [instance] ProbabilisticTheory.addCommGroup ProbabilisticTheory.partialOrder
  ProbabilisticTheory.module ProbabilisticTheory.isOrderedAddMonoid
  ProbabilisticTheory.posSMulMono ProbabilisticTheory.one
