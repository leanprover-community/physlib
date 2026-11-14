/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Channel.Basic

/-!
# States

## i. Overview

A state assigns each observable its expectation value. It is a channel into the real numbers:
positive (`0 ≤ A ⟹ 0 ≤ ω A`) and normalized so the certain outcome reads `ω 1 = 1`. In quantum
mechanics, `ω A = tr(ρA)` for a density matrix `ρ`.

## ii. Key results

- `ProbabilisticTheory.State` : normalized real expectation functionals on observables.
- `ProbabilisticTheory.State.comap` : pull back a state by evaluating observables through a
  channel.

## iii. Table of contents

- A. States
- B. Transporting states along channels

## iv. References

-/

@[expose] public section

/-!

## A. States

-/

/-- States assign normalized real expectation values to observables. -/
abbrev ProbabilisticTheory.State (P : ProbabilisticTheory) := Channel P .real

namespace ProbabilisticTheory.State

variable {P Q : ProbabilisticTheory}

-- Keep ℝ explicit in state evaluation and projections so tactics index their types consistently.
instance : FunLike P.State P.Observables ℝ :=
  inferInstanceAs (FunLike (Channel P .real) P.Observables ℝ)

/-- The real positive functional underlying a state. -/
abbrev toPositiveLinearMap (ω : P.State) : P.Observables →ₚ[ℝ] ℝ :=
  Channel.toPositiveLinearMap ω

/-- The real linear functional underlying a state. -/
abbrev toLinearMap (ω : P.State) : P.Observables →ₗ[ℝ] ℝ :=
  ω.toPositiveLinearMap.toLinearMap

@[simp]
lemma toPositiveLinearMap_apply (ω : P.State) (A : P.Observables) :
    ω.toPositiveLinearMap A = ω A := rfl

/-!

## B. Transporting states along channels

-/

/-- Pull back a state by applying the channel before evaluating each observable. -/
def comap (ω : Q.State) (f : Channel P Q) : P.State := ω.comp f

@[simp]
lemma comap_apply (ω : Q.State) (f : Channel P Q) (x : P.Observables) :
    ω.comap f x = ω (f x) := rfl

end ProbabilisticTheory.State
