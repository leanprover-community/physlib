/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Effect.Basic

/-!
# Orthogonal effects

Effects: the order interval `[0, 1]` of an ordered space, modelling yes/no measurement outcomes.

## i. Overview

Two effects are orthogonal when their sum is still an effect, that is, still bounded by the order
unit. Their partial sum is then again an effect.

## ii. Key results

- `Effect.Orthogonal` : two effects whose sum is bounded by the order unit.
- `Effect.addOfOrthogonal` : the partial sum of two orthogonal effects.

## iii. Table of contents

- A. Orthogonal effects

## iv. References

- G. Ludwig, *Foundations of Quantum Mechanics I*, Springer, 1983.
  <https://link.springer.com/book/10.1007/978-3-642-86751-4>

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. Orthogonal effects

-/

namespace Effect

variable {E : Type*} [OrderUnitSpace E]

/-- Two effects are orthogonal when their sum is still bounded by the order unit. -/
def Orthogonal (e f : Effect E) : Prop := (e : E) + (f : E) ≤ 1

/-- The partial sum of two orthogonal effects. -/
def addOfOrthogonal (e f : Effect E) (h : Orthogonal e f) : Effect E :=
  ⟨(e : E) + (f : E), add_nonneg e.2.1 f.2.1, h⟩

/-- The underlying observable of an orthogonal effect sum is the ordinary sum. -/
@[simp]
lemma coe_addOfOrthogonal (e f : Effect E) (h : Orthogonal e f) :
    (addOfOrthogonal e f h : E) = (e : E) + (f : E) := rfl

end Effect

end ProbabilisticTheory
