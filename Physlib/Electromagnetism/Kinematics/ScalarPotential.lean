/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Kinematics.VectorPotential
/-!

# The Scalar Potential

## i. Overview

The electromagnetic potential is given by
`A = (1/c φ, \vec A)`
where `φ` is the scalar potential and `\vec A` is the vector potential.

In this module we define the scalar potential, and prove lemmas about it.

Since `A` is relativistic it is a function of `SpaceTime d`, whilst
the scalar potential is non-relativistic and is therefore a function of `Time` and `Space d`.

## ii. Key results

- `ElectromagneticPotential.scalarPotential` : The scalar potential from an
  electromagnetic potential.

## iii. Table of contents

- A. Definition of the Scalar Potential
- B. Relation to constructors
- C. Smoothness of the Scalar Potential
- D. Differentiability of the Scalar Potential

## iv. References

* None.
-/

@[expose] public section
namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. Definition of the Scalar Potential

-/

/-- The scalar potential from the electromagnetic potential. -/
noncomputable def scalarPotential {d} (c : SpeedOfLight := 1) (A : ElectromagneticPotential d) :
    Time → Space d → ℝ := timeSlice c <|
  fun x => c * A x (Sum.inl 0)

/-!

## B. Relation to constructors

-/

@[simp]
lemma ofScalarPotential_scalarPotential {d} (c : SpeedOfLight)
    (φ : Time → Space d → ℝ) : (ofScalarPotential c φ).scalarPotential c = φ := by
  simp only [scalarPotential, ofScalarPotential, Fin.isValue]
  field_simp
  simp

@[simp]
lemma ofStaticScalarPotential_scalarPotential {d} (c : SpeedOfLight)
    (φ : Space d → ℝ) : (ofStaticScalarPotential c φ).scalarPotential c = fun _ => φ := by
  simp [ofStaticScalarPotential]

@[simp]
lemma ofVectorPotential_scalarPotential {d} (c : SpeedOfLight)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    (ofVectorPotential c A).scalarPotential = 0 := by
  simp only [scalarPotential, SpeedOfLight.val_one, ofVectorPotential, Fin.isValue, mul_zero]
  rfl

@[simp]
lemma ofStaticVectorPotential_scalarPotential {d} (c : SpeedOfLight)
    (A : Space d → EuclideanSpace ℝ (Fin d)) :
    (ofStaticVectorPotential c A).scalarPotential = 0 := by
  simp [ofStaticVectorPotential]

@[simp]
lemma ofPotentials_scalarPotential {d} (c : SpeedOfLight) (φ : Time → Space d → ℝ)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    (ofPotentials c φ A).scalarPotential c = φ := by
  simp only [scalarPotential, ofPotentials, Fin.isValue]
  field_simp
  simp

@[simp]
lemma ofStaticPotentials_scalarPotential {d} (c : SpeedOfLight) (φ : Space d → ℝ)
    (A : Space d → EuclideanSpace ℝ (Fin d)) :
    (ofStaticPotentials c φ A).scalarPotential c = fun _ => φ := by
  simp [ofStaticPotentials_eq_ofPotentials]

open MeasureTheory Matrix Space InnerProductSpace Time in
lemma ofElectromagneticField_scalarPotential (c : SpeedOfLight)
    (E : Time → Space → EuclideanSpace ℝ (Fin 3))
    (B : Time → Space → EuclideanSpace ℝ (Fin 3)) :
    (ofElectromagneticField c E B).scalarPotential c = fun t x =>
    - ∫ u in (0 : ℝ)..1, ⟪E t (u • x), basis.repr x⟫_ℝ ∂(volume) := by
  simp [ofElectromagneticField]

open MeasureTheory Matrix Space InnerProductSpace Time in
lemma ofElectromagneticField_scalarPotential_eq_add_vectorPotential (c : SpeedOfLight)
    (E : Time → Space → EuclideanSpace ℝ (Fin 3))
    (B : Time → Space → EuclideanSpace ℝ (Fin 3)) (hb : ContDiff ℝ 1 ↿B) :
    (ofElectromagneticField c E B).scalarPotential c = fun t x =>
    - ∫ u in (0 : ℝ)..1, ⟪E t (u • x) +
    ∂ₜ ((ofElectromagneticField c E B).vectorPotential c ·
      (u • x)) t, basis.repr x⟫_ℝ ∂(volume) := by
  simp [ofElectromagneticField_scalarPotential, inner_add_left]
  ext t x
  simp only [neg_inj]
  congr
  ext u
  simp [time_deriv_vectorPotential_inner_radial_eq_zero_ofElectromagneticField (B := B) hb]

/-!

## C. Smoothness of the Scalar Potential

We prove various lemmas about the smoothness of the scalar potential.

-/

@[fun_prop]
lemma scalarPotential_contDiff {n} {d} (c : SpeedOfLight) (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) : ContDiff ℝ n ↿(A.scalarPotential c) := by
  simp [scalarPotential]
  apply timeSlice_contDiff
  have h1 : ∀ i, ContDiff ℝ n (fun x => A x i) := by
    rw [SpaceTime.contDiff_vector]
    exact hA
  apply ContDiff.mul
  · fun_prop
  exact h1 (Sum.inl 0)

open ContDiff

@[fun_prop]
lemma scalarPotential_contDiff_space_of_smooth {n : ℕ} {d} (c : SpeedOfLight)
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (t : Time) : ContDiff ℝ n (A.scalarPotential c t) := by
  have hA : ContDiff ℝ n A := hA.of_le (ENat.LEInfty.out)
  fun_prop

/-!

## d. Differentiability of the Scalar Potential

We prove various lemmas about the differentiability of the scalar potential.

-/

@[fun_prop]
lemma scalarPotential_differentiable {d} (c : SpeedOfLight) (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) : Differentiable ℝ ↿(A.scalarPotential c) := by
  simp [scalarPotential]
  apply timeSlice_differentiable
  have h1 : ∀ i, Differentiable ℝ (fun x => A x i) := by
    rw [SpaceTime.differentiable_vector]
    exact hA
  apply Differentiable.mul
  · fun_prop
  exact h1 (Sum.inl 0)

end ElectromagneticPotential

end Electromagnetism
