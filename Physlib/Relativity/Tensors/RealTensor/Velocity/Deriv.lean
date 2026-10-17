/-
Copyright (c) 2026 Scott Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Hughes
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Velocity.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivatives of Lorentz velocities

Derivatives of unit four-velocity curves are Minkowski orthogonal to their values.

## i. Overview

Differentiating the normalization of a curve in `Lorentz.Velocity` gives orthogonality
of its value and derivative. The derivative is taken in the ambient Lorentz vector space.
When the parameter is proper time, this is orthogonality of four-velocity and four-acceleration.

## ii. Key results

- `Lorentz.Velocity.minkowskiProduct_eq_zero_of_hasDerivAt`: the derivative of a curve of
  unit four-velocities is Minkowski orthogonal to its value.

## iii. Table of contents

- A. Derivative orthogonality

## iv. References

The proof uses the bilinear derivative rule from `Mathlib.Analysis.Calculus.Deriv.Mul`.
-/

@[expose] public section

namespace Lorentz.Velocity

open scoped Lorentz.Vector

/-! ## A. Derivative orthogonality -/

/-- The derivative of a curve of unit future-directed four-velocities is Minkowski
orthogonal to its value. -/
lemma minkowskiProduct_eq_zero_of_hasDerivAt {d : ℕ} {u : ℝ → Velocity d}
    {a : Vector d} {t : ℝ} (hu : HasDerivAt (fun s => (u s).1) a t) :
    ⟪(u t).1, a⟫ₘ = 0 := by
  have hprod := Vector.minkowskiProduct.hasDerivAt_of_bilinear
    (fun _ => hu) (fun _ => hu)
  have hconst : HasDerivAt (fun s : ℝ => ⟪(u s).1, (u s).1⟫ₘ) 0 t := by
    simpa only [Velocity.minkowskiProduct_self_eq_one] using hasDerivAt_const t (1 : ℝ)
  have hzero := hprod.unique hconst
  rw [Vector.minkowskiProduct_symm a (u t).1] at hzero
  linarith

end Lorentz.Velocity
