/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Separation

/-!
# Effects tested by states

State evaluations distinguish effects and recover their distance.

## i. Overview

The distance between two effects is the largest difference in the probabilities predicted by
a state. Effects with equal probabilities in every state are equal.

## ii. Key results

- `Effect.dist_eq_sSup_abs_apply` : recover effect distance from state evaluations.
- `Effect.ext_of_forall_apply_eq` : states distinguish effects.

## iii. Table of contents

- A. States separate effects

## iv. References

-/

@[expose] public section

open ProbabilisticTheory
open scoped Effect

namespace ProbabilisticTheory.Effect

variable {P : ProbabilisticTheory}

open State

/-!

## A. States separate effects

-/

/-- The distance between two effects is the supremum of the difference in their evaluations over
all states. -/
lemma dist_eq_sSup_abs_apply [Nontrivial P.Observables] (e f : P.Effect) :
    Dist.dist e f = sSup (Set.range fun ω : P.State => |ω e - ω f|) := by
  rw [dist_eq_orderUnitNorm, ← sSup_abs_apply_eq_orderUnitNorm]
  simp_rw [map_sub]

/-- An effect is determined by its values under all states. -/
lemma ext_of_forall_apply_eq {e f : P.Effect}
    (h : ∀ ω : P.State, ω e = ω f) : e = f :=
  Subtype.ext (State.ext_of_forall_apply_eq h)

/-- Evaluation by states is injective on effects. -/
lemma injective_apply_state :
    Function.Injective (fun (e : P.Effect) (ω : P.State) => ω e) :=
  fun _ _ h => ext_of_forall_apply_eq (congrFun h)

end ProbabilisticTheory.Effect
