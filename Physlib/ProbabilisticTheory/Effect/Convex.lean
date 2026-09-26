/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.UnitInterval
public import Physlib.ProbabilisticTheory.Effect.Basic

/-!
# Convexity and mixtures of effects

## i. Overview

The effect interval `[0, 1]` is convex: randomizing between two effects with some probability
gives back an effect. Physically, flipping a biased coin to decide which of two measurements to
actually run is itself a legitimate measurement.

## ii. Key results

- `Effect.convex` : the effect interval is convex.
- `Effect.mix` : randomize between two effects with a given probability.

## iii. Table of contents

- A. Convexity and mixtures of effects

-/

@[expose] public section

variable {E : Type*} [OrderUnitSpace E]

namespace Effect

/-!

## A. Convexity and mixtures of effects

-/

/-- The effect interval is convex. -/
lemma convex : Convex ℝ (Effect E : Set E) := convex_Icc 0 1

/-- Randomize between two effects with probability `t` of testing the first. -/
def mix (e f : Effect E) (t : unitInterval) : Effect E :=
  ⟨(t : ℝ) • (e : E) + (1 - (t : ℝ)) • (f : E),
    convex e.2 f.2 t.2.1 (sub_nonneg.mpr t.2.2) (by ring)⟩

/-- Evaluation of a mixture is the pointwise convex combination. -/
@[simp]
lemma coe_mix (e f : Effect E) (t : unitInterval) :
    ((mix e f t : Effect E) : E) = (t : ℝ) • (e : E) + (1 - (t : ℝ)) • (f : E) := rfl

end Effect
