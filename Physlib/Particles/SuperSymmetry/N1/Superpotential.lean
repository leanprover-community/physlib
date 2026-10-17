/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Particles.SuperSymmetry.N1.Basic
public import Physlib.Mathematics.Calculus.Wirtinger.Coordinate

/-!

# SUSY N=1 superpotential

The superpotential of the N=1 chiral sector, and its gradient as a chiral tensor.

## i. Overview

A superpotential on a domain `D` of configurations is a function `W` that is holomorphic on `D`.
It coerces to that function, so `W u` is its value at `u`.
Its gradient `∂_I W` is the covector of colour `chiralDown` whose components are the holomorphic
Wirtinger derivatives of `W`. The conjugates `W̄` and `∂̄_J̄ W̄` are `star W` and
`conjChiralCovector` of the gradient.

## ii. Key results

- `SUSY.N1.Superpotential` : a superpotential, holomorphic on a domain.
- `SUSY.N1.Superpotential.dW` : its gradient, a `chiralDown` covector.
- `SUSY.N1.Superpotential.repr_dW` : the components of the gradient are `∂_I W`.

## iii. Table of contents

- A. The superpotential
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
## A. The superpotential

-/

/-- A superpotential on the domain `D`: a function `W` of the chiral configuration, holomorphic on
`D`. -/
structure Superpotential (ι : Type) [Fintype ι] [DecidableEq ι]
    (D : Set (ChiralScalarConfiguration ι)) where
  /-- The superpotential `W`. -/
  W : ChiralScalarConfiguration ι → ℂ
  /-- `W` is holomorphic on `D`. -/
  holomorphic : ∀ u ∈ D, DifferentiableAt ℂ W u

namespace Superpotential

variable {D : Set (ChiralScalarConfiguration ι)}

attribute [coe] Superpotential.W

/-- A superpotential is applied as the function `W`. -/
instance : CoeFun (Superpotential ι D) (fun _ => ChiralScalarConfiguration ι → ℂ) := ⟨W⟩

/-!
## B. The gradient

-/

/-- The gradient `∂_I W` of the superpotential, a covector of colour `chiralDown`. -/
def dW (W : Superpotential ι D) (u : ChiralScalarConfiguration ι) :
    (chiralTensor (ι := ι)).Tensor ![chiralDown] :=
  ofComponents ![chiralDown] (fun φ => dWirtingerCoord W (φ 0) u)

/-- The `I`-th component of the gradient is `∂_I W`. -/
lemma repr_dW (W : Superpotential ι D) (u : ChiralScalarConfiguration ι) (I : ι) :
    (basis (S := (chiralTensor (ι := ι)).toTensorSpecies) ![chiralDown]).repr (W.dW u) ![I] =
      dWirtingerCoord W I u := by
  rw [← componentMap_eq_repr, dW, componentMap_ofComponents]
  rfl

end Superpotential

end SUSY.N1
