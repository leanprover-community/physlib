/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Weight.Extension
public import Physlib.ProbabilisticTheory.State.Weight

/-!
# States from normalized weights

Finite normalized weights correspond exactly to states.

## i. Overview

A finite normalized weight extends linearly to a state. Restriction to positive observables
recovers the original weight, giving an equivalence.

## ii. Key results

- `Weight.IsState.toState` : extend a finite normalized weight to a state.
- `Weight.stateEquiv` : the correspondence with states.

## iii. Table of contents

- A. From a normalized weight to a state
- B. The equivalence

## iv. References

-/

@[expose] public section

open ProbabilisticTheory
open scoped ENNReal

namespace Weight

variable {P : ProbabilisticTheory} {w : Weight P}

/-!

## A. From a normalized weight to a state

-/

/-- A finite normalized weight extends to a state. -/
noncomputable def IsState.toState (hw : w.IsState) : P.State :=
  .ofLinearMap hw.finite.toLinearMap
    (fun A hA => (hw.finite.toLinearMap_coe ⟨A, hA⟩).symm ▸ ENNReal.toReal_nonneg)
    ((hw.finite.toLinearMap_coe 1).trans (by simp [hw.normalized]))

/-- The extended state agrees with the weight on positive observables. -/
@[simp]
lemma IsState.toState_apply (hw : w.IsState) (A : PosCone P) : hw.toState A = (w A).toReal :=
  hw.finite.toLinearMap_coe A

/-!

## B. The equivalence

-/

/-- Finite normalized weights correspond exactly to states. -/
noncomputable def stateEquiv : {w : Weight P // w.IsState} ≃ P.State where
  toFun w := w.2.toState
  invFun s := ⟨s.toWeight, s.toWeight_isState⟩
  left_inv w := by
    ext A
    simp [w.2.finite A]
  right_inv s := DFunLike.ext _ _ fun A => by
    obtain ⟨P, Q, rfl⟩ := PosCone.exists_sub A
    simp only [map_sub, IsState.toState_apply, State.toReal_toWeight_apply]

end Weight
