/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Particles.SuperSymmetry.N1.Basic
public import Physlib.Mathematics.Calculus.Wirtinger.Coordinate

/-!

# SUSY N=1 superpotential data

The superpotential of the N=1 chiral sector, and its gradient as a chiral tensor.

## i. Overview

A superpotential on a domain `D` of configurations is a function `W` that is holomorphic on `D`.
Its gradient `∂_I W` is the covector of colour `chiralDown` whose components are the holomorphic
Wirtinger derivatives of `W`. The conjugates `W̄` and `∂̄_J̄ W̄` are `star W` and
`conjChiralCovector` of the gradient.

## ii. Key results

- `SUSY.N1.SuperpotentialData` : a superpotential, holomorphic on a domain.
- `SUSY.N1.SuperpotentialData.dW` : its gradient, a `chiralDown` covector.
- `SUSY.N1.SuperpotentialData.repr_dW` : the components of the gradient are `∂_I W`.

## iii. Table of contents

- A. The superpotential data
- B. The gradient

## iv. References

* None.
-/

@[expose] public section
noncomputable section

namespace SUSY.N1

open TensorSpecies TensorSpecies.Tensor ChiralColor Physlib.Wirtinger

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-!
## A. The superpotential data

-/

/-- A superpotential on the domain `D`: a function `W` of the chiral configuration, holomorphic on
`D`. -/
structure SuperpotentialData (ι : Type) [Fintype ι] [DecidableEq ι]
    (D : Set (ChiralScalarConfiguration ι)) where
  /-- The superpotential `W`. -/
  W : ChiralScalarConfiguration ι → ℂ
  /-- `W` is holomorphic on `D`. -/
  holomorphic : ∀ u ∈ D, DifferentiableAt ℂ W u

namespace SuperpotentialData

variable {D : Set (ChiralScalarConfiguration ι)}

/-!
## B. The gradient

-/

/-- The gradient `∂_I W` of the superpotential, a covector of colour `chiralDown`. -/
def dW (sp : SuperpotentialData ι D) (u : ChiralScalarConfiguration ι) :
    (chiralTensor (ι := ι)).Tensor ![chiralDown] :=
  ofComponents ![chiralDown] (fun φ => dWirtingerCoord sp.W (φ 0) u)

/-- The `I`-th component of the gradient is `∂_I W`. -/
lemma repr_dW (sp : SuperpotentialData ι D) (u : ChiralScalarConfiguration ι) (I : ι) :
    (basis (S := (chiralTensor (ι := ι)).toTensorSpecies) ![chiralDown]).repr (sp.dW u) ![I] =
      dWirtingerCoord sp.W I u := by
  rw [← componentMap_eq_repr, dW, componentMap_ofComponents]
  rfl

end SuperpotentialData

end SUSY.N1
