/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Geometry.Sphere.Profile
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fourier transform of the sphere measure

Archimedes' formula computes the exact sine multiplier of the sphere measure.

## i. Overview

Archimedes' formula computes the exact sine multiplier of the sphere measure.

## ii. Key results

* `integral_exp_symm`.
* `sphere_fourier_axis`: The Fourier transform of the sphere measure along an axis.
* `sphere_fourier`.

## iii. Table of contents

- A. Fourier transform of the sphere measure

## iv. References

* Bär, [Green-hyperbolic operators on globally hyperbolic
  spacetimes](https://arxiv.org/abs/1310.0738).

## A. Fourier transform of the sphere measure
-/

@[expose] public section

noncomputable section

namespace Sphere3

open MeasureTheory
open scoped Pointwise FourierTransform SchwartzMap

lemma integral_exp_symm (a R : ℝ) (ha : a ≠ 0) :
    ∫ z in (-R)..R, Complex.exp (Complex.I * (a * z)) = 2 * Real.sin (a * R) / a := by
  have hc : Complex.I * (a : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ha)
  have h1 := integral_exp_mul_complex (a := -R) (b := R) hc
  have h2 : ∀ z : ℝ, Complex.exp (Complex.I * (a * z)) = Complex.exp ((Complex.I * a) * z) :=
    fun z => by congr 1; ring
  simp_rw [h2]
  rw [h1]
  have h3 : Complex.exp (Complex.I * (a : ℂ) * (R : ℂ)) -
      Complex.exp (Complex.I * (a : ℂ) * ((-R : ℝ) : ℂ)) =
      2 * Complex.I * Complex.sin ((a : ℂ) * R) := by
    rw [Complex.sin]
    push_cast
    have e1 : Complex.I * (a : ℂ) * -(R : ℂ) = -(Complex.I * (a : ℂ) * (R : ℂ)) := by ring
    have e2 : -((a : ℂ) * R) * Complex.I = -(Complex.I * (a : ℂ) * R) := by ring
    have e3 : (a : ℂ) * R * Complex.I = Complex.I * (a : ℂ) * R := by ring
    rw [e1, e2, e3]
    linear_combination (Complex.exp (Complex.I * a * R) - Complex.exp (-(Complex.I * a * R))) *
      Complex.I_sq
  rw [h3]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have h5 : Complex.sin ((a : ℂ) * R) = ((Real.sin (a * R) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sin]
  rw [h5]
  field_simp

/-- The Fourier transform of the sphere measure along an axis. -/
lemma sphere_fourier_axis (i : Fin 3) {a R : ℝ} (ha : a ≠ 0) (hR : 0 < R) :
    ∫ n : Sph, Complex.exp (Complex.I * (a * (R * n.1 i))) ∂sphereMeasure =
      (4 * Real.pi * Real.sin (a * R) / (a * R) : ℝ) := by
  have h := sphereProfile_eq i (h := fun z : ℝ => Complex.exp (Complex.I * (a * z)))
    (by fun_prop) hR
  simp only [sphereProfile] at h
  rw [show (fun n : Sph => Complex.exp (Complex.I * (a * (R * n.1 i)))) =
    fun n : Sph => Complex.exp (Complex.I * ((a : ℂ) * ((R * n.1 i : ℝ) : ℂ))) by
      funext n; push_cast; rfl]
  rw [h, integral_exp_symm a R ha]
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  rw [Complex.real_smul]
  push_cast
  field_simp
  ring


lemma sphere_fourier (k : Space 3) (hk : k ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∫ n : Sph, Complex.exp (Complex.I * ((R * inner ℝ k n.1 : ℝ) : ℂ)) ∂sphereMeasure =
      (4 * Real.pi * Real.sin (R * ‖k‖) / (R * ‖k‖) : ℝ) := by
  have ha : ‖k‖ ≠ 0 := norm_ne_zero_iff.mpr hk
  set a := ‖k‖ with ha_def
  let w : Space 3 := a • Space.basis (0 : Fin 3)
  have hw : ‖k‖ = ‖w‖ := by
    simp [w, norm_smul, ha_def]
  let U : Space 3 ≃ₗᵢ[ℝ] Space 3 := Submodule.reflection (ℝ ∙ (k - w))ᗮ
  have hUk : U k = w := Submodule.reflection_sub hw
  have hinner : ∀ n : Sph, inner ℝ k n.1 = a * (U n.1) 0 := by
    intro n
    have h1 := U.inner_map_map k n.1
    rw [hUk] at h1
    rw [← h1]
    simp [w, inner_smul_left, Space.basis_inner]
  have hcongr : ∀ n : Sph, Complex.exp (Complex.I * ((R * inner ℝ k n.1 : ℝ) : ℂ)) =
      (fun m : Sph => Complex.exp (Complex.I * ((a : ℂ) * (R * m.1 0 : ℝ)))) (sphereEquiv U n) := by
    intro n
    simp only [hinner, sphereEquiv_coe]
    push_cast
    ring_nf
  simp_rw [hcongr]
  have key := (sphereEquiv_measurePreserving U).integral_comp'
    (f := (sphereEquiv U).toMeasurableEquiv)
    (fun m : Sph => Complex.exp (Complex.I * ((a : ℂ) * (R * m.1 0 : ℝ))))
  refine Eq.trans key ?_
  have h0 := sphere_fourier_axis (0 : Fin 3) (a := a) (R := R) ha hR
  rw [show a * R = R * a by ring] at h0
  simpa using h0

end Sphere3
