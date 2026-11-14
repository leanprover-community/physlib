/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Weight.Basic
public import Physlib.ProbabilisticTheory.State.Basic

/-!
# States as weights

Restriction of a state to positive observables gives a finite normalized weight.

## i. Overview

State values are nonnegative on the positive cone. Reading them as extended nonnegative
reals produces a weight with value one on the certain outcome.

## ii. Key results

- `ProbabilisticTheory.State.toWeight` : the weight induced by a state.
- `ProbabilisticTheory.State.toWeight_isState` : finiteness and normalization.

## iii. Table of contents

- A. From a state to a weight

## iv. References

-/

@[expose] public section

open ProbabilisticTheory
open scoped ENNReal

namespace ProbabilisticTheory.State

variable {P : ProbabilisticTheory}

/-!

## A. From a state to a weight

-/

/-- The weight induced by a state: `ENNReal.ofReal` applied to the state's values on the positive
cone, where they are automatically nonnegative. -/
noncomputable def toWeight (s : P.State) : Weight P where
  toFun A := ENNReal.ofReal (s (A : P.Observables))
  map_add' A B := by
    simp [ENNReal.ofReal_add (map_nonneg s A.2) (map_nonneg s B.2)]
  map_smul' c A := by
    simp [ENNReal.smul_def, ENNReal.ofReal_mul c.coe_nonneg]

@[simp]
lemma toWeight_apply (s : P.State) (A : PosCone P) :
    s.toWeight A = ENNReal.ofReal (s (A : P.Observables)) :=
  rfl

/-- The weight induced by a state agrees with the state itself on the positive cone. -/
lemma toReal_toWeight_apply (s : P.State) (A : PosCone P) :
    (s.toWeight A).toReal = s (A : P.Observables) := by
  rw [toWeight_apply, ENNReal.toReal_ofReal (map_nonneg s A.2)]

/-- The weight induced by a state is finite and normalized. -/
lemma toWeight_isState (s : P.State) : s.toWeight.IsState where
  finite _ := ENNReal.ofReal_ne_top
  normalized := by simp

end ProbabilisticTheory.State
