/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.State.WeightEquivalence

/-!

# Tracial states and weights

Tracial weights and tracial states.

## i. Overview

A state `ω` is tracial when `ω (a⋆ a) = ω (a a⋆)`. For a complex-linear functional this is
equivalent to `f (a b) = f (b a)`. A finite tracial weight gives a tracial state.

## ii. Key results

- `UnitalPositiveLinearMap.IsTracial` : tracial states.
- `Weight.IsTracial` : tracial weights.

## iii. Table of contents

- A. Tracial weights
- B. Tracial states

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. Tracial weights -/

namespace Weight

variable {A : Type*} [OrderUnitSpace A] [Mul A] [Star A]

/-- A weight is tracial when its finite positive-linear extensions assign equal values to `x† x`
and `x x†`. -/
def IsTracial (w : Weight A) : Prop :=
  ∀ (hw : w.IsFinite) (x : A),
    hw.toPositiveLinearMap (star x * x) = hw.toPositiveLinearMap (x * star x)

namespace IsTracial

variable {w : Weight A}

/-- A finite tracial weight's real positive-linear extension has equal values on `x† x` and
`x x†`. -/
lemma toPositiveLinearMap_star_mul_self (ht : w.IsTracial) (hw : w.IsFinite) (x : A) :
    hw.toPositiveLinearMap (star x * x) = hw.toPositiveLinearMap (x * star x) :=
  ht hw x

end IsTracial

end Weight

/-! ## B. Tracial states -/

namespace UnitalPositiveLinearMap

variable {A : Type*} [OrderUnitSpace A] [Mul A] [Star A]

/-- A state is tracial when it assigns equal values to `x† x` and `x x†`. -/
def IsTracial (s : 𝓢[ℝ, A]) : Prop := ∀ x : A, s (star x * x) = s (x * star x)

end UnitalPositiveLinearMap

namespace Weight.IsState

variable {A : Type*} [OrderUnitSpace A] [Mul A] [Star A] {w : Weight A}

/-- The state of a tracial weight assigns equal values to `x†x` and `xx†`. -/
lemma isTracial (hw : w.IsState) (ht : w.IsTracial) :
    ∀ x : A, hw.toState (star x * x) = hw.toState (x * star x) :=
  fun x => ht.toPositiveLinearMap_star_mul_self hw.finite x

end Weight.IsState

end ProbabilisticTheory
