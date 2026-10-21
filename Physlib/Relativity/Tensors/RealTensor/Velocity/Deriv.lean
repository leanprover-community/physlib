/-
Copyright (c) 2026 Scott Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Hughes
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Velocity.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivatives of Lorentz velocities

Derivatives of unit four-velocity curves and the spatial-part constructor.

## i. Overview

Differentiating the normalization of a curve in `Lorentz.Velocity` gives orthogonality
of its value and derivative. The spatial-part constructor has an explicit derivative,
obtained from the squared Euclidean norm and the square-root chain rule. Derivatives are
taken in the ambient Lorentz vector space. For a worldline's four-velocity parametrized
by proper time, the derivative is four-acceleration.

## ii. Key results

- `Lorentz.Velocity.minkowskiProduct_eq_zero_of_hasDerivAt`: the derivative of a curve of
  unit four-velocities is Minkowski orthogonal to its value.
- `Lorentz.Velocity.hasDerivAt_ofSpatialPart`: the ambient derivative of the unit
  four-velocity determined by a differentiable spatial-part curve.

## iii. Table of contents

- A. Derivative orthogonality
- B. Derivative of the spatial-part constructor

## iv. References

The proofs use the bilinear derivative rule from `Mathlib.Analysis.Calculus.Deriv.Mul`
and the squared-norm derivative from `Mathlib.Analysis.InnerProductSpace.Calculus`.
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

/-! ## B. Derivative of the spatial-part constructor -/

/-- The ambient derivative of the unit future-directed four-velocity determined by
a differentiable spatial-part curve. -/
lemma hasDerivAt_ofSpatialPart {d : ℕ} {p : ℝ → EuclideanSpace ℝ (Fin d)}
    {p' : EuclideanSpace ℝ (Fin d)} {t : ℝ} (hp : HasDerivAt p p' t) :
    HasDerivAt (fun s => (ofSpatialPart (p s)).1)
      (Vector.ofTemporalComponent (inner ℝ (p t) p' / Real.sqrt (1 + ‖p t‖ ^ 2)) +
        Vector.ofSpatialComponent p') t := by
  have htime : HasDerivAt (fun s => Real.sqrt (1 + ‖p s‖ ^ 2))
      (inner ℝ (p t) p' / Real.sqrt (1 + ‖p t‖ ^ 2)) t := by
    have hnorm : HasDerivAt (fun s => 1 + ‖p s‖ ^ 2) (2 * inner ℝ (p t) p') t := by
      convert! HasDerivAt.add (hasDerivAt_const t (1 : ℝ)) hp.norm_sq using 1
      simp only [zero_add]
    have h := HasDerivAt.sqrt hnorm (by positivity)
    have hne : Real.sqrt (1 + ‖p t‖ ^ 2) ≠ 0 := by positivity
    convert h using 1
    field_simp [hne]
  have h := HasDerivAt.add
    ((Vector.ofTemporalComponent (d := d)).hasFDerivAt.comp_hasDerivAt t htime)
    ((Vector.ofSpatialComponent (d := d)).hasFDerivAt.comp_hasDerivAt t hp)
  convert h using 1
  funext s μ
  rcases μ with j | j
  · fin_cases j
    simp [ofSpatialPart, Vector.ofTemporalComponent, Vector.ofSpatialComponent,
      Vector.basis_apply, Vector.apply_sum]
  · simp [ofSpatialPart, Vector.ofTemporalComponent, Vector.ofSpatialComponent,
      Vector.basis_apply, Vector.apply_sum]

end Lorentz.Velocity
