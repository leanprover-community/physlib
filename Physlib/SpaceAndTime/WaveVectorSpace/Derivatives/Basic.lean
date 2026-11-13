/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.SpaceAndTime.WaveVectorSpace.Basic
/-!

# Derivatives on `WaveVectorSpace`

## i. Overview

## ii. Key results

## iii. Table of contents

## iv. References

-/
@[expose] public section

namespace WaveVectorSpace

variable {d : ℕ}

/-!
## A. Derivatives of functions on `WaveVectorSpace d`
-/

/-- Given a function `f : WaveVectorSpace d → M`,
`∂[i] f` is its derivative in the direction of the `i`ᵗʰ basis vector. -/
noncomputable def deriv {M : Type*} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (i : Fin d) (f : WaveVectorSpace d → M) (k : WaveVectorSpace d) : M :=
  fderiv ℝ f k (basis i)

@[inherit_doc deriv]
notation "∂[" i "]" => deriv i

lemma deriv_eq {M : Type*} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (i : Fin d) (f : WaveVectorSpace d → M) (k : WaveVectorSpace d) :
    ∂[i] f k = fderiv ℝ f k (basis i) :=
  rfl

end WaveVectorSpace
