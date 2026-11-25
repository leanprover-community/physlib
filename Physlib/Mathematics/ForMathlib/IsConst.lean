/-
Copyright (c) 2026 Physlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Mathlib.Logic.Function.Const
/-!
# The value of a constant function

Extract the common value of a constant function on a nonempty domain.

## i. Overview

A proof `h : f.IsConst` identifies the outputs of `f` at any two inputs. If the domain is
nonempty, `h.value` names their common value without requiring the caller to supply an input.

## ii. Key results

- `Function.IsConst.apply_eq_value`: at every input `x`, `f x = h.value`.

## iii. Table of contents

- A. The common value

## iv. References

`Mathlib.Logic.Function.Const` defines `Function.IsConst`.
-/

@[expose] public noncomputable section

namespace Function.IsConst

/-!
## A. The common value
-/

variable {α β : Sort*} [Nonempty α] {f : α → β} (h : f.IsConst)

/-- The common value of a constant function on a nonempty domain. -/
def value : β :=
  (isConst_iff_exists_forall_eq_of_nonempty_domain.mp h).choose

/-- A constant function takes its common value at every input. -/
lemma apply_eq_value : ∀ x, f x = h.value :=
  (isConst_iff_exists_forall_eq_of_nonempty_domain.mp h).choose_spec

end Function.IsConst
