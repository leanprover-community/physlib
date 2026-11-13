/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.Core
public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.CircularMotion

/-!
# Uniform rotations in the complex plane
Rotation preserves Euclidean distances and gives the orbital derivatives.

## i. Overview

Positions are complex numbers and time is real. Multiplying by the angular speed
and imaginary unit gives tangent velocity.

## ii. Key results

- `hasDerivAt_rotatingVelocity` gives the main result of this module.

## iii. Table of contents

- A. Rotation, derivatives, and periodicity

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace ClassicalMechanics.LagrangeThreeBody

/-!
## A. Rotation, derivatives, and periodicity
-/

/-- Counterclockwise rotation by a real angle, in radians. -/
def rotate (θ : ℝ) (z : ℂ) : ℂ :=
  ⟨Real.cos θ * z.re - Real.sin θ * z.im,
   Real.sin θ * z.re + Real.cos θ * z.im⟩

/-- Complex multiplier representing a plane rotation. -/
def rotor (θ : ℝ) : ℂ := ⟨Real.cos θ, Real.sin θ⟩

/-- Velocity of a rotating point when its current position is `z`. -/
def tangent (ω : ℝ) (z : ℂ) : ℂ := ((ω : ℂ) * Complex.I) * z

/-- Velocity along a rotating trajectory. -/
def rotateVelocity (ω θ : ℝ) (z : ℂ) : ℂ := tangent ω (rotate θ z)

/-- The signed area of the parallelogram spanned by two plane vectors. -/
def cross (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

lemma rotate_eq_mul (θ : ℝ) (z : ℂ) : rotate θ z = rotor θ * z := by
  apply Complex.ext
  · simp [rotate, rotor, Complex.mul_re]
  · simp [rotate, rotor, Complex.mul_im]
    ring

@[simp] lemma rotate_zero_angle (z : ℂ) : rotate 0 z = z := by
  apply Complex.ext <;> simp [rotate]

@[simp] lemma rotate_zero_vector (θ : ℝ) : rotate θ 0 = 0 := by
  simp [rotate_eq_mul]

lemma rotate_add (θ : ℝ) (z w : ℂ) :
    rotate θ (z + w) = rotate θ z + rotate θ w := by
  simp only [rotate_eq_mul, mul_add]

lemma rotate_sub (θ : ℝ) (z w : ℂ) :
    rotate θ (z - w) = rotate θ z - rotate θ w := by
  simp only [rotate_eq_mul, mul_sub]

lemma rotate_smul (θ a : ℝ) (z : ℂ) : rotate θ (a • z) = a • rotate θ z := by
  simp only [rotate_eq_mul, Complex.real_smul]
  ring

lemma rotate_add_angles (θ ψ : ℝ) (z : ℂ) :
    rotate (θ + ψ) z = rotate θ (rotate ψ z) := by
  apply Complex.ext <;>
    simp [rotate, Real.sin_add, Real.cos_add] <;> ring

lemma rotate_neg_cancel (θ : ℝ) (z : ℂ) : rotate (-θ) (rotate θ z) = z := by
  rw [← rotate_add_angles, neg_add_cancel, rotate_zero_angle]

lemma rotate_injective (θ : ℝ) : Function.Injective (rotate θ) := by
  intro z w h
  have h' := congrArg (rotate (-θ)) h
  simpa only [rotate_neg_cancel] using h'

lemma rotate_norm_sq (θ : ℝ) (z : ℂ) : ‖rotate θ z‖ ^ 2 = ‖z‖ ^ 2 := by
  have h := rotation_squared_length θ z.re z.im 1
  simp only [xCoordinate, yCoordinate, mul_one] at h
  rw [Complex.sq_norm, Complex.sq_norm]
  simpa only [Complex.normSq_apply, rotate, pow_two] using h

@[simp] lemma norm_rotate (θ : ℝ) (z : ℂ) : ‖rotate θ z‖ = ‖z‖ := by
  have hs := rotate_norm_sq θ z
  have h₁ := norm_nonneg (rotate θ z)
  have h₂ := norm_nonneg z
  nlinarith

lemma rotate_pair_distance (θ : ℝ) (z w : ℂ) :
    ‖rotate θ z - rotate θ w‖ = ‖z - w‖ := by
  rw [← rotate_sub, norm_rotate]

lemma equidistant_rotate {ι : Type*} (q : ι → ℂ) (ℓ θ : ℝ)
    (hq : ∀ i j, i ≠ j → ‖q i - q j‖ = ℓ) :
    ∀ i j, i ≠ j → ‖rotate θ (q i) - rotate θ (q j)‖ = ℓ := by
  intro i j hij
  rw [rotate_pair_distance]
  exact hq i j hij

lemma firstMoment_rotate {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (q : ι → ℂ) (θ : ℝ) :
    firstMoment m (fun i => rotate θ (q i)) = rotate θ (firstMoment m q) := by
  simp only [firstMoment, rotate_eq_mul, Complex.real_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma firstMoment_tangent {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (q : ι → ℂ) (ω : ℝ) :
    firstMoment m (fun i => tangent ω (q i)) = tangent ω (firstMoment m q) := by
  simp only [firstMoment, tangent, Complex.real_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Assemble two real derivative certificates into a complex one. -/
lemma hasDerivAt_mk {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => (⟨f s, g s⟩ : ℂ)) (⟨f', g'⟩ : ℂ) t := by
  have hd := hf.ofReal_comp.add (hg.ofReal_comp.mul_const Complex.I)
  change HasDerivAt (fun s => (f s : ℂ) + (g s : ℂ) * Complex.I)
    ((f' : ℂ) + (g' : ℂ) * Complex.I) t at hd
  simpa only [← Complex.mk_eq_add_mul_I] using hd

lemma coordinateVelocity_eq_tangent (ω t : ℝ) (z : ℂ) :
    (⟨xVelocity ω z.re z.im t, yVelocity ω z.re z.im t⟩ : ℂ) =
      rotateVelocity ω (ω * t) z := by
  apply Complex.ext <;>
    simp [rotateVelocity, tangent, rotate, xVelocity, yVelocity,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- Actual first derivative; no equation of motion is assumed. -/
lemma hasDerivAt_rotating (ω : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun s => rotate (ω * s) z) (rotateVelocity ω (ω * t) z) t := by
  have h := hasDerivAt_mk (hasDerivAt_xCoordinate ω z.re z.im t)
    (hasDerivAt_yCoordinate ω z.re z.im t)
  rw [coordinateVelocity_eq_tangent] at h
  simpa only [rotate, xCoordinate, yCoordinate] using h

/-- Actual second derivative, first expressed as the derivative of the velocity. -/
lemma hasDerivAt_rotatingVelocity (ω : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun s => rotateVelocity ω (ω * s) z)
      (-(ω ^ 2) • rotate (ω * t) z) t := by
  have h := (hasDerivAt_rotating ω z t).const_mul ((ω : ℂ) * Complex.I)
  have ha : ((ω : ℂ) * Complex.I) * rotateVelocity ω (ω * t) z =
      -(ω ^ 2) • rotate (ω * t) z := by
    simp only [rotateVelocity, tangent, Complex.real_smul, Complex.ofReal_neg,
      Complex.ofReal_pow]
    linear_combination (((ω : ℂ) ^ 2) * rotate (ω * t) z) * Complex.I_sq
  rw [ha] at h
  exact h

lemma norm_tangent (ω : ℝ) (z : ℂ) : ‖tangent ω z‖ = |ω| * ‖z‖ := by
  simp [tangent, Complex.norm_real, Real.norm_eq_abs]

lemma norm_rotateVelocity (ω θ : ℝ) (z : ℂ) :
    ‖rotateVelocity ω θ z‖ = |ω| * ‖z‖ := by
  rw [rotateVelocity, norm_tangent, norm_rotate]

lemma cross_tangent (ω : ℝ) (z : ℂ) : cross z (tangent ω z) = ω * ‖z‖ ^ 2 := by
  simp [cross, tangent, Complex.mul_re, Complex.mul_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring

lemma cross_rotate (θ : ℝ) (z w : ℂ) :
    cross (rotate θ z) (rotate θ w) = cross z w := by
  calc
    cross (rotate θ z) (rotate θ w) =
        cross z w * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by
      simp only [cross, rotate]
      ring
    _ = cross z w := by rw [Real.sin_sq_add_cos_sq, mul_one]

lemma rotate_two_pi (θ : ℝ) (z : ℂ) : rotate (θ + 2 * Real.pi) z = rotate θ z := by
  apply Complex.ext <;> simp [rotate, Real.sin_add, Real.cos_add]

lemma angular_advance (ω t : ℝ) (hω : ω ≠ 0) :
    ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by
  field_simp [hω]

lemma rotate_periodic (ω : ℝ) (hω : ω ≠ 0) (z : ℂ) :
    Function.Periodic (fun t => rotate (ω * t) z) (2 * Real.pi / ω) := by
  intro t
  dsimp only
  rw [angular_advance ω t hω, rotate_two_pi]

lemma rotateVelocity_periodic (ω : ℝ) (hω : ω ≠ 0) (z : ℂ) :
    Function.Periodic (fun t => rotateVelocity ω (ω * t) z)
      (2 * Real.pi / ω) := by
  intro t
  change tangent ω (rotate (ω * (t + 2 * Real.pi / ω)) z) =
    tangent ω (rotate (ω * t) z)
  rw [angular_advance ω t hω, rotate_two_pi]

end ClassicalMechanics.LagrangeThreeBody
