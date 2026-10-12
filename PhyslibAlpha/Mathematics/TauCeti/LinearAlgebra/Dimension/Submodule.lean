/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Intersections of submodules by dimension

A dimension-counting criterion for nontrivial submodule intersection.

## i. Overview

A dimension-counting criterion for nontrivial submodule intersection.

## ii. Key results

This file proves the statement described in the overview.

## iii. Table of contents

- A. Development

## iv. References

* Standard material; the statements and proofs are original to this formalization.
-/

public section

/-! ## A. Development -/

open Module (finrank)

namespace Submodule

variable {𝕜 E : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Two subspaces whose dimensions sum to more than the dimension of the ambient
space have nontrivial intersection. -/
lemma inf_ne_bot_of_finrank_lt [FiniteDimensional 𝕜 E] {V W : Submodule 𝕜 E}
    (h : finrank 𝕜 E < finrank 𝕜 V + finrank 𝕜 W) : V ⊓ W ≠ ⊥ := fun hbot =>
  absurd (Submodule.finrank_add_finrank_le_of_disjoint (disjoint_iff.mpr hbot))
    (by omega)

end Submodule

end
