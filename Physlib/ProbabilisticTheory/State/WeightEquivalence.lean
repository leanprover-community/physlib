/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Weight.Extension
public import Physlib.ProbabilisticTheory.State.Basic

/-!
# Equivalence between states and finite normalized weights

## i. Overview

A state is, on its own terms, a normalized positive linear functional — `𝓢[ℝ, E]`, already fully
built in `State/Basic.lean`. It is not *defined* as a weight; the two are independent notions, and
the correspondence between them is a genuine theorem.

## ii. Key results

- `Weight.stateEquiv` : finite normalized weights correspond exactly to states.

## iii. Table of contents

- A. From a normalized weight to a state
- B. From a state to a weight
- C. The equivalence

-/

@[expose] public section

open scoped ENNReal

variable {E : Type*} [OrderUnitSpace E]

namespace Weight

variable {w : Weight E}

/-!

## A. From a normalized weight to a state

-/

namespace IsState

/-- A finite normalized weight extends to a state. -/
noncomputable def toState (hw : w.IsState) : 𝓢[ℝ, E] :=
  UnitalPositiveLinearMap.ofLinearMap (hw.finite.toLinearMap)
    (fun A hA => by
      rw [Weight.IsFinite.toLinearMap_apply, hw.finite.toFun_of_nonneg ⟨A, hA⟩]
      exact ENNReal.toReal_nonneg)
    ((hw.finite.toFun_of_nonneg 1).trans (by simp [hw.normalized]))

end IsState

end Weight

namespace UnitalPositiveLinearMap

/-!

## B. From a state to a weight

-/

/-- The weight induced by a state: `ENNReal.ofReal` applied to the state's values on the positive
cone, where they are automatically nonnegative. -/
noncomputable def toWeight (s : 𝓢[ℝ, E]) : Weight E where
  toFun A := ENNReal.ofReal (s (A : E))
  map_add' A B := (congrArg ENNReal.ofReal (map_add s (A : E) B)).trans
    (ENNReal.ofReal_add (map_nonneg s A.2) (map_nonneg s B.2))
  map_smul' c A := by
    show ENNReal.ofReal (s ((c : ℝ) • (A : E))) = c • ENNReal.ofReal (s (A : E))
    rw [map_smul, smul_eq_mul, ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ENNReal.smul_def, smul_eq_mul]

@[simp]
lemma toWeight_apply (s : 𝓢[ℝ, E]) (A : PosCone E) : s.toWeight A = ENNReal.ofReal (s (A : E)) :=
  rfl

/-- The weight induced by a state agrees with the state itself on the positive cone. -/
lemma toReal_toWeight_apply (s : 𝓢[ℝ, E]) (A : PosCone E) :
    (s.toWeight A).toReal = s (A : E) := by
  rw [toWeight_apply, ENNReal.toReal_ofReal (map_nonneg s A.2)]

/-- The weight induced by a state is finite and normalized. -/
lemma toWeight_isState (s : 𝓢[ℝ, E]) : s.toWeight.IsState where
  finite _ := ENNReal.ofReal_ne_top
  normalized := by simp

end UnitalPositiveLinearMap

namespace Weight

/-!

## C. The equivalence

-/

/-- Finite normalized weights correspond exactly to states. -/
noncomputable def stateEquiv : {w : Weight E // w.IsState} ≃ 𝓢[ℝ, E] where
  toFun w := w.2.toState
  invFun s := ⟨s.toWeight, s.toWeight_isState⟩
  left_inv := by
    rintro ⟨w, hw⟩
    refine Subtype.ext (Weight.ext fun A => ?_)
    change ENNReal.ofReal (IsFinite.toFun w (A : E)) = w A
    rw [IsFinite.toFun_of_nonneg hw.finite A, ENNReal.ofReal_toReal (hw.finite A)]
  right_inv s := by
    ext A
    obtain ⟨r, hr⟩ := OrderUnitSpace.exists_real_shift_nonneg A
    show IsFinite.toFun s.toWeight A = s A
    rw [s.toWeight_isState.finite.toFun_eq A hr, IsFinite.rawValue]
    simp only [UnitalPositiveLinearMap.toReal_toWeight_apply, PosCone.coe_one, _root_.map_add,
      _root_.map_smul, smul_eq_mul, _root_.map_one]
    ring

end Weight
