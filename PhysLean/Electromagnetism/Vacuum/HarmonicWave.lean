/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Vacuum.IsPlaneWave
/-!

# Harmonic Wave in Vacuum

## i. Overview

In this module we define the electromagnetic potential for a monochromatic harmonic wave
travelling in the x-direction in free space, and prove various properties about it,
including that it satisfies Maxwell's equations in free space, that it is a plane wave.

We work here in a general dimension `d` so we use the magnetic field is the
form of a matrix rather than a vector.

## ii. Key results

- `harmonicWaveX` : Definition of the electromagnetic
  potential for a harmonic wave travelling in the x-direction.
- `harmonicWaveX_isExtrema` : The harmonic wave satisfies Maxwell's equations in free space.
- `harmonicWaveX_isPlaneWave` : The harmonic wave is a plane wave.
- `harmonicWaveX_polarization_ellipse` : The polarization ellipse equation for the harmonic wave.

## iii. Table of contents

- A. The electromagnetic potential for a harmonic wave
  - A.1. Differentiability of the electromagnetic potential
  - A.2. Smoothness of the electromagnetic potential
- B. The scalar potential
- C. The vector potential
  - C.1. Components of the vector potential
  - C.2. Space derivatives of the vector potential
- D. The electric field
  - D.1. Components of the electric field
  - D.2. Spatial derivatives of the electric field
  - D.3. Time derivatives of the electric field
  - D.4. Divergence of the electric field
- E. The magnetic field matrix for a harmonic wave
  - E.1. Components of the magnetic field matrix
  - E.2. Space derivatives of the magnetic field matrix
- F. Maxwell's equations for a harmonic wave
- G. The harmonic wave is a plane wave
- H. Polarization ellipse of the harmonic wave

## iv. References

-/
namespace Electromagnetism

open Space Module
open Time
open ClassicalMechanics

variable (OM : OpticalMedium)
open Matrix
open Real
namespace ElectromagneticPotential
open InnerProductSpace

/-!

## A. The electromagnetic potential for a harmonic wave

-/

/-- The electromagnetic potential for a Harmonic wave travelling in the `x`-direction
  with wave number `k`. -/
noncomputable def harmonicWaveX (𝓕 : FreeSpace) (k : ℝ) (E₀ : Fin d → ℝ)
  (φ : Fin d → ℝ) : ElectromagneticPotential d.succ := fun x μ =>
  match μ with
  | Sum.inl 0 => 0
  | Sum.inr 0 => 0
  | Sum.inr ⟨Nat.succ i, h⟩ => -E₀ ⟨i, Nat.succ_lt_succ_iff.mp h⟩ * 1 / (𝓕.c * k) *
      Real.sin (k * (𝓕.c * x.time 𝓕.c - x.space 0) + φ ⟨i, Nat.succ_lt_succ_iff.mp h⟩)

/-!

### A.1. Differentiability of the electromagnetic potential

-/

lemma harmonicWaveX_differentiable {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) :
    Differentiable ℝ (harmonicWaveX 𝓕 k E₀ φ) := by
  rw [← Lorentz.Vector.differentiable_apply]
  intro μ
  match μ with
  | Sum.inl 0 => simp [harmonicWaveX]
  | Sum.inr ⟨0, h⟩ => simp [harmonicWaveX]
  | Sum.inr ⟨Nat.succ i, h⟩ =>
    simp [harmonicWaveX]
    apply Differentiable.const_mul
    fun_prop

/-!

### A.2. Smoothness of the electromagnetic potential

-/

lemma harmonicWaveX_contDiff {d} (n : WithTop ℕ∞) (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) :
    ContDiff ℝ n (harmonicWaveX 𝓕 k E₀ φ) := by
  rw [← Lorentz.Vector.contDiff_apply]
  intro μ
  match μ with
  | Sum.inl 0 => simp [harmonicWaveX]; fun_prop
  | Sum.inr ⟨0, h⟩ => simp [harmonicWaveX]; fun_prop
  | Sum.inr ⟨Nat.succ i, h⟩ =>
    simp [harmonicWaveX]
    apply ContDiff.mul
    · fun_prop
    · fun_prop

/-!

## B. The scalar potential

The scalar potential of the harmonic wave is zero.

-/

@[simp]
lemma harmonicWaveX_scalarPotential_eq_zero {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) :
    (harmonicWaveX 𝓕 k E₀ φ).scalarPotential 𝓕.c = 0 := by
  ext x
  simp [harmonicWaveX, scalarPotential]
  rfl

/-!

## C. The vector potential

-/

/-!

### C.1. Components of the vector potential

-/

@[simp]
lemma harmonicWaveX_vectorPotential_zero_eq_zero {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) :
    (harmonicWaveX 𝓕 k E₀ φ).vectorPotential 𝓕.c t x 0 = 0 := by
  simp [harmonicWaveX, vectorPotential, SpaceTime.timeSlice]
  rfl

lemma harmonicWaveX_vectorPotential_succ {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (i : Fin d) :
    (harmonicWaveX 𝓕 k E₀ φ).vectorPotential 𝓕.c t x i.succ =
    - E₀ i * 1 / (𝓕.c * k) * Real.sin (k * (t.val * 𝓕.c - x 0) + φ i) := by
  simp [harmonicWaveX, vectorPotential, SpaceTime.timeSlice, Fin.succ]
  left
  ring_nf

lemma harmonicWaveX_vectorPotential_succ' {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (i : ℕ)
    (hi : i.succ < d.succ) :
    (harmonicWaveX 𝓕 k E₀ φ).vectorPotential 𝓕.c t x ⟨i.succ, hi⟩ =
    - E₀ ⟨i, by grind⟩ * 1 / (𝓕.c * k) * Real.sin (k * (t.val * 𝓕.c - x 0) + φ ⟨i, by grind⟩) := by
  simp [harmonicWaveX, vectorPotential, SpaceTime.timeSlice]
  left
  ring_nf

/-!

### C.2. Space derivatives of the vector potential

-/

open Space
@[simp]
lemma harmonicWaveX_vectorPotential_space_deriv_succ {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (j : Fin d)
    (i : Fin d.succ) :
    Space.deriv j.succ (fun x => vectorPotential 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x i) x
    = 0 := by
  match i with
  | 0 => simp
  | ⟨Nat.succ i, hi⟩ =>
    simp [harmonicWaveX_vectorPotential_succ']
    rw [Space.deriv_eq]
    rw [fderiv_const_mul (by fun_prop)]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, mul_eq_zero,
      div_eq_zero_iff, neg_eq_zero, SpeedOfLight.val_ne_zero, false_or]
    rw [fderiv_sin (by fun_prop)]
    simp only [fderiv_add_const, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
      mul_eq_zero]
    right
    right
    rw [fderiv_const_mul (by fun_prop)]
    rw [fderiv_const_sub]
    simp only [smul_neg, ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul, neg_eq_zero, mul_eq_zero]
    rw [← Space.deriv_eq]
    rw [Space.deriv_component]
    simp

open Space
@[simp]
lemma harmonicWaveX_vectorPotential_succ_space_deriv_zero {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (i : Fin d) :
    Space.deriv 0 (fun x => vectorPotential 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x i.succ) x
    = E₀ i / 𝓕.c.val * Real.cos (𝓕.c.val * k * t.val - k * x 0 + φ i) := by
  simp [harmonicWaveX_vectorPotential_succ]
  rw [Space.deriv_eq_fderiv_basis]
  rw [fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [fderiv_sin (by fun_prop)]
  simp only [fderiv_add_const, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul (by fun_prop)]
  rw [fderiv_const_sub]
  simp only [smul_neg, ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, mul_neg]
  rw [← Space.deriv_eq_fderiv_basis]
  rw [Space.deriv_component]
  simp only [↓reduceIte, mul_one]
  field_simp

/-!

## D. The electric field

-/

/-!

### D.1. Components of the electric field

-/
lemma harmonicWaveX_electricField_zero {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) :
    (harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x 0 = 0 := by
  simp [ElectromagneticPotential.electricField]
  rw [← Time.deriv_euclid]
  simp only [harmonicWaveX_vectorPotential_zero_eq_zero, Time.deriv_const]
  refine vectorPotential_differentiable_time (harmonicWaveX 𝓕 k E₀ φ) ?_ x
  exact harmonicWaveX_differentiable 𝓕 k E₀ φ

lemma harmonicWaveX_electricField_succ {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (i : Fin d) :
    (harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x i.succ =
    E₀ i * Real.cos (k * 𝓕.c * t.val - k * x 0 + φ i) := by
  simp [ElectromagneticPotential.electricField]
  rw [← Time.deriv_euclid]
  simp [harmonicWaveX_vectorPotential_succ]
  rw [Time.deriv_eq]
  rw [fderiv_const_mul]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [fderiv_sin (by fun_prop)]
  rw [fderiv_add_const]
  rw [fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [fderiv_sub_const]
  rw [fderiv_mul_const (by fun_prop)]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, Time.fderiv_val, smul_eq_mul, mul_one]
  field_simp
  · fun_prop
  · refine vectorPotential_differentiable_time (harmonicWaveX 𝓕 k E₀ φ) ?_ x
    exact harmonicWaveX_differentiable 𝓕 k E₀ φ

/-!

### D.2. Spatial derivatives of the electric field

-/

lemma harmonicWaveX_electricField_space_deriv_same {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (i : Fin d.succ) :
    Space.deriv i (fun x => electricField 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x i) x
    = 0 := by
  match i with
  | 0 => simp [harmonicWaveX_electricField_zero]
  | ⟨Nat.succ i, hi⟩ =>
    rw [← Fin.succ_mk _ _ (by grind)]
    conv_lhs =>
      enter [2, x]
      rw [harmonicWaveX_electricField_succ _ _ hk]
    rw [Space.deriv_eq]
    rw [fderiv_const_mul (by fun_prop)]
    simp only [Nat.succ_eq_add_one, Fin.succ_mk, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul, mul_eq_zero]
    rw [fderiv_cos (by fun_prop)]
    simp only [fderiv_add_const, neg_smul, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, neg_eq_zero, mul_eq_zero]
    right
    right
    rw [fderiv_const_sub]
    simp only [ContinuousLinearMap.neg_apply, neg_eq_zero]
    rw [fderiv_const_mul (by fun_prop)]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, mul_eq_zero]
    rw [← Space.deriv_eq]
    rw [Space.deriv_component]
    simp

/-!

### D.3. Time derivatives of the electric field

-/

lemma harmonicWaveX_electricField_succ_time_deriv {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (i : Fin d) :
    Time.deriv (fun t => electricField 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x i.succ) t
    = - k * 𝓕.c * E₀ i * Real.sin (k * 𝓕.c * t.val - k * x 0 + φ i) := by
  conv_lhs =>
    enter [1, t]
    rw [harmonicWaveX_electricField_succ _ _ hk]
  rw [Time.deriv_eq]
  rw [fderiv_const_mul (by fun_prop)]
  simp only [Nat.succ_eq_add_one, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
    neg_mul]
  rw [fderiv_cos (by fun_prop)]
  simp only [fderiv_add_const, neg_smul, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, mul_neg, neg_inj]
  rw [fderiv_sub_const]
  rw [fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, Time.fderiv_val, smul_eq_mul, mul_one]
  ring

/-!

### D.4. Divergence of the electric field

-/

@[simp]
lemma harmonicWaveX_div_electricField_eq_zero {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) :
    Space.div (fun x => electricField 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x) x = 0 := by
  simp [Space.div]
  apply Finset.sum_eq_zero
  intro i _
  exact harmonicWaveX_electricField_space_deriv_same 𝓕 k hk E₀ φ t x i

/-!

## E. The magnetic field matrix for a harmonic wave
-/

/-!

### E.1. Components of the magnetic field matrix

-/

@[simp]
lemma harmonicWaveX_magneticFieldMatrix_succ_succ {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ)
    (i j : Fin d) :
    (harmonicWaveX 𝓕 k E₀ φ).magneticFieldMatrix 𝓕.c t x (i.succ, j.succ) = 0 := by
  rw [magneticFieldMatrix_eq_vectorPotential]
  simp only [Nat.succ_eq_add_one, harmonicWaveX_vectorPotential_space_deriv_succ, sub_self]
  exact harmonicWaveX_differentiable 𝓕 k E₀ φ

lemma harmonicWaveX_magneticFieldMatrix_zero_succ {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ)
    (i : Fin d) :
    (harmonicWaveX 𝓕 k E₀ φ).magneticFieldMatrix 𝓕.c t x (0, i.succ) =
    (- E₀ i / 𝓕.c.val) * cos (𝓕.c.val * k * t.val - k * x 0 + φ i) := by
  rw [magneticFieldMatrix_eq_vectorPotential]
  simp only [Nat.succ_eq_add_one, harmonicWaveX_vectorPotential_zero_eq_zero, Space.deriv_const,
    zero_sub]
  rw [harmonicWaveX_vectorPotential_succ_space_deriv_zero]
  simp only [Nat.succ_eq_add_one]
  ring
  grind
  exact harmonicWaveX_differentiable 𝓕 k E₀ φ

lemma harmonicWaveX_magneticFieldMatrix_succ_zero {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ)
    (i : Fin d) :
    (harmonicWaveX 𝓕 k E₀ φ).magneticFieldMatrix 𝓕.c t x (i.succ, 0) =
    (E₀ i / 𝓕.c.val) * cos (𝓕.c.val * k * t.val - k * x 0 + φ i) := by
  rw [magneticFieldMatrix_eq_vectorPotential]
  simp only [Nat.succ_eq_add_one, harmonicWaveX_vectorPotential_zero_eq_zero, Space.deriv_const,
    sub_zero]
  rw [harmonicWaveX_vectorPotential_succ_space_deriv_zero]
  simp only [ne_eq]
  grind
  exact harmonicWaveX_differentiable 𝓕 k E₀ φ

/-!

### E.2. Space derivatives of the magnetic field matrix

-/

lemma harmonicWaveX_magneticFieldMatrix_space_deriv_succ {d} (𝓕 : FreeSpace) (k : ℝ)
    (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ)
    (i j : Fin d.succ) (l : Fin d) :
    Space.deriv l.succ (fun x => magneticFieldMatrix 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x (i, j)) x
    = 0 := by
  match i, j with
  | 0, 0 => simp
  | ⟨Nat.succ i, hi⟩, ⟨Nat.succ j, hj⟩ =>
    conv_lhs =>
      enter [2, x]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_magneticFieldMatrix_succ_succ _ _]
    simp
  | 0, ⟨Nat.succ j, hj⟩ =>
    conv_lhs =>
      enter [2, x]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_magneticFieldMatrix_zero_succ _ k hk]
    have h1 (i : Fin d) : Space.deriv l.succ
        (fun x => - E₀ i / 𝓕.c.val * cos (𝓕.c.val * k * t.val - k * x 0 + φ i)) x
        = 0 := by
      rw [Space.deriv_eq]
      rw [fderiv_const_mul]
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, mul_eq_zero,
        div_eq_zero_iff, neg_eq_zero, SpeedOfLight.val_ne_zero, or_false]
      rw [fderiv_cos (by fun_prop)]
      simp only [fderiv_add_const, neg_smul, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, neg_eq_zero, mul_eq_zero]
      right
      right
      rw [fderiv_const_sub]
      simp only [ContinuousLinearMap.neg_apply, neg_eq_zero]
      rw [fderiv_const_mul (by fun_prop)]
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, mul_eq_zero]
      rw [← Space.deriv_eq]
      rw [Space.deriv_component]
      simp only [Fin.succ_ne_zero, ↓reduceIte, or_true]
      fun_prop
    rw [← h1 ⟨j, by grind⟩]

  | ⟨Nat.succ j, hj⟩, 0 =>
    conv_lhs =>
      enter [2, x]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_magneticFieldMatrix_succ_zero _ k hk]
    have h1 (i : Fin d) : Space.deriv l.succ
        (fun x => E₀ i / 𝓕.c.val * cos (𝓕.c.val * k * t.val - k * x 0 + φ i)) x
        = 0 := by
      rw [Space.deriv_eq]
      rw [fderiv_const_mul]
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, mul_eq_zero,
        div_eq_zero_iff, SpeedOfLight.val_ne_zero, or_false]
      rw [fderiv_cos (by fun_prop)]
      simp only [fderiv_add_const, neg_smul, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, neg_eq_zero, mul_eq_zero]
      right
      right
      rw [fderiv_const_sub]
      simp only [ContinuousLinearMap.neg_apply, neg_eq_zero]
      rw [fderiv_const_mul (by fun_prop)]
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, mul_eq_zero]
      rw [← Space.deriv_eq]
      rw [Space.deriv_component]
      simp only [Fin.succ_ne_zero, ↓reduceIte, or_true]
      fun_prop
    rw [← h1 ⟨j, by grind⟩]

lemma harmonicWaveX_magneticFieldMatrix_zero_succ_space_deriv_zero {d} (𝓕 : FreeSpace) (k : ℝ)
    (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ)
    (i : Fin d) :
    Space.deriv 0 (fun x => magneticFieldMatrix 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x (0, i.succ)) x
    = -E₀ i * k / 𝓕.c.val * sin (𝓕.c.val * k * t.val - k * x 0 + φ i) := by
  conv_lhs =>
    enter [2, x]
    rw [harmonicWaveX_magneticFieldMatrix_zero_succ _ k hk]
  rw [Space.deriv_eq]
  rw [fderiv_const_mul]
  simp only [Nat.succ_eq_add_one, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
    neg_mul]
  rw [fderiv_cos (by fun_prop)]
  simp only [fderiv_add_const, neg_smul, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, mul_neg]
  rw [fderiv_const_sub]
  simp only [ContinuousLinearMap.neg_apply, mul_neg, neg_neg]
  rw [fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [← Space.deriv_eq]
  rw [Space.deriv_component]
  simp only [↓reduceIte, mul_one]
  ring
  fun_prop

/-!

## F. Maxwell's equations for a harmonic wave

-/

lemma harmonicWaveX_isExtrema {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) :
    IsExtrema 𝓕 (harmonicWaveX 𝓕 k E₀ φ) 0 := by
  rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix]
  intro t x
  apply And.intro
  /- Gauss's law -/
  · simp
    rw [harmonicWaveX_div_electricField_eq_zero 𝓕 k hk E₀ φ t x]
  /- Ampère's law -/
  · intro i
    rw [Fin.sum_univ_succ]
    conv_rhs =>
      enter [1, 2, 2, i]
      rw [harmonicWaveX_magneticFieldMatrix_space_deriv_succ _ _ hk]
    simp
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simp
      rw [← Time.deriv_euclid]
      conv_lhs =>
        enter [1, t]
        rw [harmonicWaveX_electricField_zero 𝓕 k E₀]
      simp only [Time.deriv_const]
      refine electricField_differentiable_time ?_ x
      exact harmonicWaveX_contDiff 2 𝓕 k E₀ φ
    rw [harmonicWaveX_magneticFieldMatrix_zero_succ_space_deriv_zero _ k hk]
    rw [← Time.deriv_euclid]
    rw [harmonicWaveX_electricField_succ_time_deriv _ _ hk]
    field_simp
    simp [𝓕.c_sq]
    field_simp
    ring_nf
    left
    trivial
    apply electricField_differentiable_time
    exact harmonicWaveX_contDiff 2 𝓕 k E₀ φ
  · apply harmonicWaveX_contDiff
  · change ContDiff ℝ _ (fun _ => 0)
    fun_prop

/-!

## G. The harmonic wave is a plane wave

-/

lemma harmonicWaveX_isPlaneWave {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) :
    IsPlaneWave 𝓕 (harmonicWaveX 𝓕 k E₀ φ) ⟨Space.basis 0, by simp⟩ := by
  apply And.intro
  · use fun u => WithLp.toLp 2 fun i =>
      match i with
      | 0 => 0
      | ⟨Nat.succ i, h⟩ => E₀ ⟨i, by grind⟩ * cos (-k * u + φ ⟨i, by grind⟩)
    ext t x i
    match i with
    | 0 =>
      simp [harmonicWaveX_electricField_zero, planeWave]
      rfl
    | ⟨Nat.succ i, h⟩ =>
      simp only [Nat.succ_eq_add_one, neg_mul]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_electricField_succ _ _ hk]
      simp [planeWave]
      left
      congr
      ring
  · use fun u ij =>
      match ij with
      | (0, 0) => 0
      | (0, ⟨Nat.succ j, hj⟩) =>
        (- E₀ ⟨j, by grind⟩ / 𝓕.c.val) * cos (-k * u + φ ⟨j, by grind⟩)
      | (⟨Nat.succ i, hi⟩, 0) =>
        (E₀ ⟨i, by grind⟩ / 𝓕.c.val) * cos (-k * u + φ ⟨i, by grind⟩)
      | (⟨Nat.succ i, hi⟩, ⟨Nat.succ j, hj⟩) => 0
    intro t x
    ext ij
    match ij with
    | (0, 0) =>
      simp only [Nat.succ_eq_add_one, magneticFieldMatrix_diag_eq_zero, inner_basis, neg_mul]
      rfl
    | (⟨0, h0⟩, ⟨Nat.succ j, hj⟩) =>
      simp only [Nat.succ_eq_add_one, Fin.zero_eta, inner_basis, neg_mul]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_magneticFieldMatrix_zero_succ _ k hk]
      simp only [Nat.succ_eq_add_one, mul_eq_mul_left_iff, div_eq_zero_iff, neg_eq_zero,
        SpeedOfLight.val_ne_zero, or_false]
      left
      congr
      ring
    | (⟨Nat.succ i, hi⟩, ⟨0, h0⟩) =>
      simp only [Nat.succ_eq_add_one, Fin.zero_eta, inner_basis, neg_mul]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_magneticFieldMatrix_succ_zero _ k hk]
      simp only [Nat.succ_eq_add_one, mul_eq_mul_left_iff, div_eq_zero_iff,
        SpeedOfLight.val_ne_zero, or_false]
      left
      congr
      ring
    | (⟨Nat.succ i, hi⟩, ⟨Nat.succ j, hj⟩) =>
      simp only [Nat.succ_eq_add_one]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_magneticFieldMatrix_succ_succ _ _]

/-!

## H. Polarization ellipse of the harmonic wave

-/

open Real in
lemma harmonicWaveX_polarization_ellipse {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (hi : ∀ i, E₀ i ≠ 0) :
    2 * d * ∑ i : Fin d, ((harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x i.succ / E₀ i) ^ 2 -
    2 * ∑ i, ∑ j, ((harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x i.succ / E₀ i) *
      ((harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x j.succ / E₀ j) *
      Real.cos (φ j - φ i) =
    ∑ i, ∑ j, Real.sin (φ j - φ i) ^ 2 := by
  have h1 (i : Fin d) : (harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x i.succ / E₀ i
    = Real.cos (k * 𝓕.c * t.val - k * x 0 + φ i) := by
    rw [harmonicWaveX_electricField_succ 𝓕 k hk E₀ φ t x i]
    specialize hi i
    field_simp
  conv_lhs =>
    enter [1, 2, 2, i]
    rw [h1]
  conv_lhs =>
    enter [2, 2, 2, i, 2, j]
    rw [h1, h1]
  let τ := k * 𝓕.c * t.val - k * x 0
  have hij (i j : Fin d) :
      cos (τ + φ i) ^ 2 + cos (τ + φ j) ^ 2
      - 2 * cos (τ + φ i) * cos (τ + φ j) * cos (φ j - φ i) = sin (φ j - φ i) ^ 2 := by
    calc _
      _ = cos (τ + φ i) ^ 2 * (sin (φ j) ^ 2 + cos (φ j) ^ 2) + cos (τ + φ j) ^ 2
        * (sin (φ i) ^ 2 + cos (φ i) ^ 2)
        - 2 * cos (τ + φ i) * cos (τ + φ j) * cos (φ j - φ i) := by simp
      _ = (cos (τ) * sin (φ j - φ i)) ^ 2 + (sin (τ) * sin (φ j - φ i)) ^ 2 := by
        have h1 : cos (τ + φ i) * sin (φ j) - cos (τ + φ j) * sin (φ i) =
            cos τ * sin (φ j - φ i) := by
          field_simp
          symm
          rw [cos_add, cos_add, sin_sub]
          ring
        have h2 : cos (τ + φ i) * cos (φ j) - cos (τ + φ j) * cos (φ i) =
            sin τ * sin (φ j - φ i) := by
          field_simp
          conv_lhs => enter [1]; rw [cos_add]
          conv_lhs => enter [2]; rw [cos_add]
          conv_rhs => enter [2]; rw [sin_sub]
          ring
        rw [← h1, ← h2]
        rw [cos_sub]
        ring
      _ = sin (φ j - φ i) ^ 2 * (cos (τ) ^ 2 + sin (τ) ^ 2) := by ring
      _ = sin (φ j - φ i) ^ 2 := by simp
  symm
  calc _
    _ = ∑ (i : Fin d), ∑ (j : Fin d), (cos (τ + φ i) ^ 2 + cos (τ + φ j) ^ 2
        - 2 * cos (τ + φ i) * cos (τ + φ j) * cos (φ j - φ i)) := by
      simp [← hij]
    _ = 2 * ∑ (i : Fin d), ∑ (j : Fin d), cos (τ + φ j) ^ 2
        - 2 * ∑ (i : Fin d), ∑ (j : Fin d), cos (τ + φ i) * cos (τ + φ j) * cos (φ j - φ i) := by
      rw [two_mul]
      conv_rhs =>
        enter [1, 1]
        rw [Finset.sum_comm]
      rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr
      funext i
      rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr
      funext j
      ring
    _ = 2 * d * ∑ (j : Fin d), cos (τ + φ j) ^ 2
        - 2 * ∑ (i : Fin d), ∑ (j : Fin d), cos (τ + φ i) * cos (τ + φ j) * cos (φ j - φ i) := by
      rw [Finset.sum_const, Finset.card_fin]
      ring

end ElectromagneticPotential

end Electromagnetism
