/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith
-/
import PhysLean.ClassicalMechanics.WaveEquation.Basic
import PhysLean.Electromagnetism.Dynamics.IsExtrema
/-!

# Electromagnetic wave equation

## i. Overview

In this module we define a proposition `IsPlaneWave` on electromagnetic potentials
which is true if the potential corresponds to a plane wave.
From this we derive various properties of plane waves including
the orthogonality of the electric field, magnetic field and direction of propagation,
in general dimensions.

## ii. Key results

- `IsPlaneWave` : The proposition defining plane waves.
- `IsPlaneWave.electricFunction` : The electric function corresponding to a plane wave.
- `IsPlaneWave.magneticFunction` : The magnetic function corresponding to a plane wave.
- `IsPlaneWave.magneticFieldMatrix_eq_propogator_cross_electricField` :
    The magnetic field expressed in terms of the electric field and direction of propagation.
- `IsPlaneWave.electricField_eq_propogator_cross_magneticFieldMatrix` :
    The electric field expressed in terms of the magnetic field and direction of propagation.

## iii. Table of contents

- A. The property of being a plane wave
  - A.1. The electric and magnetic functions from a plane wave
    - A.1.1. Electric function and magnetic function in terms of E and B fields
    - A.1.2. Uniqueness of the electric function
    - A.1.3. Uniqueness of the magnetic function
  - A.2. Differentiability conditions
  - A.3. Time derivative of electric and magnetic fields of a plane wave
  - A.4. Space derivative of electric and magnetic fields of a plane wave
  - A.5. Space derivative in terms of time derivative
- B. The magnetic field in terms of the electric field
  - B.1. Time derivative of the magnetic field in terms of electric field
  - B.2. Space derivative of the magnetic field in terms of electric field
  - B.3. Magnetic field equal propogator cross electric field up to constant
- C. The electric field in terms of the magnetic field
  - C.1. The time derivative of the electric field in terms of magnetic field
  - C.2. The space derivative of the electric field in terms of magnetic field
  - C.3. Electric field equal propogator cross magnetic field up to constant

## iv. References

-/

namespace Electromagnetism

open Space Module
open Time
open ClassicalMechanics

open Matrix
/-!

## A. The property of being a plane wave
-/
namespace ElectromagneticPotential
open InnerProductSpace

/-- The proposition on a electromagnetic potential which is true if
  it corresponds to a plane wave. -/
def IsPlaneWave {d : ℕ} (𝓕 : FreeSpace)
    (A : ElectromagneticPotential d) (s : Direction d) : Prop :=
  (∃ E₀, A.electricField 𝓕.c = planeWave E₀ 𝓕.c s) ∧
  (∃ (B₀ : ℝ → Fin d × Fin d → ℝ), ∀ t x, A.magneticFieldMatrix 𝓕.c t x =
    B₀ (⟪x, s.unit⟫_ℝ - 𝓕.c * t))
namespace IsPlaneWave
/-!

### A.1. The electric and magnetic functions from a plane wave
-/

/-- The corresponding electric field function from `ℝ` to `EuclideanSpace ℝ (Fin d)`
  of a plane wave. -/
noncomputable def electricFunction {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d}
    (hA : IsPlaneWave 𝓕 A s) : ℝ → EuclideanSpace ℝ (Fin d) :=
  Classical.choose hA.1

lemma electricField_eq_electricFunction {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d}
    (P : IsPlaneWave 𝓕 A s) (t : Time) (x : Space d) :
    A.electricField 𝓕.c t x =
    P.electricFunction (⟪x, s.unit⟫_ℝ - 𝓕.c * t) := by
  rw [Classical.choose_spec P.1]
  rfl

/-- The corresponding magnetic field function from `ℝ` to
  `Fin d × Fin d → ℝ` of a plane wave. -/
noncomputable def magneticFunction {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d}
    (hA : IsPlaneWave 𝓕 A s) : ℝ → Fin d × Fin d → ℝ :=
  Classical.choose hA.2

lemma magneticFieldMatrix_eq_magneticFunction {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d} {s : Direction d}
    (P : IsPlaneWave 𝓕 A s) (t : Time) (x : Space d) :
    A.magneticFieldMatrix 𝓕.c t x =
    P.magneticFunction (⟪x, s.unit⟫_ℝ - 𝓕.c * t) := by
  rw [Classical.choose_spec P.2 t x]
  rfl

/-!

#### A.1.1. Electric function and magnetic function in terms of E and B fields

-/

lemma electricFunction_eq_electricField {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) :
    P.electricFunction = fun u =>
    A.electricField 𝓕.c ⟨(- u)/𝓕.c.1⟩ (0 : Space d) := by
  funext u
  rw [P.electricField_eq_electricFunction]
  congr
  simp only [inner_zero_left, zero_sub]
  field_simp

lemma magneticFunction_eq_magneticFieldMatrix {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) :
    P.magneticFunction = fun u =>
    A.magneticFieldMatrix 𝓕.c ⟨(- u)/𝓕.c.1⟩ (0 : Space d) := by
  funext u
  rw [P.magneticFieldMatrix_eq_magneticFunction]
  congr
  simp only [inner_zero_left, zero_sub]
  field_simp

/-!

#### A.1.2. Uniqueness of the electric function

-/

lemma electricFunction_unique {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d}
    (P : IsPlaneWave 𝓕 A s) (E1 : ℝ → EuclideanSpace ℝ (Fin d))
    (hE₁ : A.electricField 𝓕.c = planeWave E1 𝓕.c s) :
    E1 = P.electricFunction := by
  funext x
  obtain ⟨t, rfl⟩ : ∃ t, x = ⟪0, s.unit⟫_ℝ - 𝓕.c * t := by use (- x/𝓕.c); field_simp; simp
  trans A.electricField 𝓕.c t (0 : Space d)
  · rw [hE₁]
    rfl
  · rw [P.electricField_eq_electricFunction]

/-!

#### A.1.3. Uniqueness of the magnetic function

-/

lemma magneticFunction_unique {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d}
    (P : IsPlaneWave 𝓕 A s)
    (B1 : ℝ → Fin d × Fin d → ℝ)
    (hB₁ : ∀ t x, A.magneticFieldMatrix 𝓕.c t x =
      B1 (⟪x, s.unit⟫_ℝ - 𝓕.c * t)) :
    B1 = P.magneticFunction := by
  funext x
  obtain ⟨t, rfl⟩ : ∃ t, x = ⟪0, s.unit⟫_ℝ - 𝓕.c * t := by use (- x/𝓕.c); field_simp; simp
  trans A.magneticFieldMatrix 𝓕.c t (0 : Space d)
  · rw [hB₁]
  · rw [P.magneticFieldMatrix_eq_magneticFunction]

/-!

### A.2. Differentiability conditions

-/

lemma electricFunction_differentiable {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ P.electricFunction := by
  rw [electricFunction_eq_electricField]
  change Differentiable ℝ (↿(electricField 𝓕.c A) ∘ fun u => ({ val := -u / 𝓕.c.val }, 0))
  apply Differentiable.comp
  · exact electricField_differentiable hA
  · refine Differentiable.prodMk ?_ ?_
    · change Differentiable ℝ (Time.toRealCLE.symm ∘ fun u => -u / 𝓕.c.val)
      apply Differentiable.comp
      · fun_prop
      · fun_prop
    · fun_prop

lemma magneticFunction_differentiable {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A)
    (ij : Fin d × Fin d) :
    Differentiable ℝ (fun u => P.magneticFunction u ij) := by
  rw [magneticFunction_eq_magneticFieldMatrix]
  simp only
  change Differentiable ℝ (↿(fun t x => A.magneticFieldMatrix 𝓕.c t x ij) ∘
    fun u => ({ val := -u / 𝓕.c.val }, 0))
  apply Differentiable.comp
  · exact magneticFieldMatrix_differentiable A hA ij
  · refine Differentiable.prodMk ?_ ?_
    · change Differentiable ℝ (Time.toRealCLE.symm ∘ fun u => -u / 𝓕.c.val)
      apply Differentiable.comp
      · fun_prop
      · fun_prop
    · fun_prop

/-!

### A.3. Time derivative of electric and magnetic fields of a plane wave

-/

lemma electricField_time_deriv {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) (t : Time)
    (x : Space d) :
    ∂ₜ (A.electricField 𝓕.c · x) t = - 𝓕.c.val •
    fderiv ℝ P.electricFunction (⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) 1 := by
  conv_lhs =>
    enter [1, t]
    rw [P.electricField_eq_electricFunction]
  rw [Time.deriv_eq]
  rw [fderiv_comp']
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv, one_smul,
    neg_smul]
  rw [fderiv_fun_sub]
  simp only [fderiv_fun_const, Pi.zero_apply, zero_sub, ContinuousLinearMap.neg_apply, neg_smul,
    neg_inj]
  rw [fderiv_const_mul]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, Time.fderiv_val, smul_eq_mul, mul_one]
  · fun_prop
  · fun_prop
  · fun_prop
  · apply Differentiable.differentiableAt
    exact IsPlaneWave.electricFunction_differentiable P hA
  · fun_prop

lemma magneticFieldMatrix_time_deriv {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) (t : Time)
    (x : Space d) (i j : Fin d) :
    ∂ₜ (A.magneticFieldMatrix 𝓕.c · x (i, j)) t = - 𝓕.c.val •
    fderiv ℝ (fun u => P.magneticFunction u (i, j)) (⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) 1 := by
  conv_lhs =>
    enter [1, t]
    rw [P.magneticFieldMatrix_eq_magneticFunction]
  rw [Time.deriv_eq]
  change fderiv ℝ ((fun u => P.magneticFunction u (i, j)) ∘
    fun t => ⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) t 1 = _
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul,
    one_mul, neg_mul]
  rw [fderiv_fun_sub]
  simp only [fderiv_fun_const, Pi.zero_apply, zero_sub, ContinuousLinearMap.neg_apply, neg_mul,
    neg_inj, mul_eq_mul_right_iff]
  rw [fderiv_const_mul]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, Time.fderiv_val, smul_eq_mul, mul_one,
    true_or]
  · fun_prop
  · fun_prop
  · fun_prop
  · apply Differentiable.differentiableAt
    exact magneticFunction_differentiable P hA (i, j)
  · fun_prop

/-!

### A.4. Space derivative of electric and magnetic fields of a plane wave

-/

lemma electricField_space_deriv {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) (t : Time)
    (x : Space d) (i : Fin d) :
    ∂[i] (A.electricField 𝓕.c t ·) x = s.unit i •
    fderiv ℝ P.electricFunction (⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) 1 := by
  conv_lhs =>
    enter [2, t]
    rw [P.electricField_eq_electricFunction]
  rw [Space.deriv_eq_fderiv_basis]
  rw [fderiv_comp']
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv, one_smul]
  rw [fderiv_fun_sub]
  simp only [fderiv_fun_const, Pi.zero_apply, sub_zero]
  rw [← Space.deriv_eq_fderiv_basis]
  simp only [deriv_inner_left]
  · fun_prop
  · fun_prop
  · apply Differentiable.differentiableAt
    exact IsPlaneWave.electricFunction_differentiable P hA
  · fun_prop

lemma magneticFieldMatrix_space_deriv {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) (t : Time)
    (x : Space d) (i j : Fin d) (k : Fin d) :
    ∂[k] (A.magneticFieldMatrix 𝓕.c t · (i, j)) x = s.unit k •
    fderiv ℝ (fun u => P.magneticFunction u (i, j))
      (⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) 1 := by
  conv_lhs =>
    enter [2, t]
    rw [P.magneticFieldMatrix_eq_magneticFunction]
  rw [Space.deriv_eq_fderiv_basis]
  change fderiv ℝ ((fun u => P.magneticFunction u (i, j)) ∘
    fun x => ⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) x _ = _
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul,
    one_mul, mul_eq_mul_right_iff]
  rw [fderiv_fun_sub]
  simp only [fderiv_fun_const, Pi.zero_apply, sub_zero]
  rw [← Space.deriv_eq_fderiv_basis]
  simp only [deriv_inner_left, true_or]
  · fun_prop
  · fun_prop
  · apply Differentiable.differentiableAt
    exact magneticFunction_differentiable P hA (i, j)
  · fun_prop

/-!

### A.5. Space derivative in terms of time derivative
-/

lemma electricField_space_deriv_eq_time_deriv {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) (t : Time)
    (x : Space d) (i : Fin d) (k : Fin d) :
    ∂[k] (A.electricField 𝓕.c t · i) x = - (s.unit k / 𝓕.c.val) •
    ∂ₜ (A.electricField 𝓕.c · x i) t := by
  rw [Space.deriv_euclid]
  rw [IsPlaneWave.electricField_space_deriv P hA t x k]
  rw [Time.deriv_euclid]
  rw [IsPlaneWave.electricField_time_deriv P hA t x]
  simp only [fderiv_eq_smul_deriv, one_smul, PiLp.smul_apply, smul_eq_mul, neg_mul, mul_neg,
    neg_neg]
  field_simp
  · exact electricField_differentiable_time hA x
  · exact electricField_differentiable_space hA t

lemma magneticFieldMatrix_space_deriv_eq_time_deriv {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) (t : Time)
    (x : Space d) (i j : Fin d) (k : Fin d) :
    ∂[k] (A.magneticFieldMatrix 𝓕.c t · (i, j)) x = - (s.unit k / 𝓕.c.val) •
    ∂ₜ (A.magneticFieldMatrix 𝓕.c · x (i, j)) t := by
  rw [IsPlaneWave.magneticFieldMatrix_space_deriv P hA t x i j k,
    IsPlaneWave.magneticFieldMatrix_time_deriv P hA t x i j]
  simp only [fderiv_eq_smul_deriv, smul_eq_mul, one_mul, neg_mul, mul_neg, neg_neg]
  field_simp

/-!

## B. The magnetic field in terms of the electric field

-/

/-!

### B.1. Time derivative of the magnetic field in terms of electric field

-/
open ContDiff

lemma time_deriv_magneticFieldMatrix_eq_electricField_mul_propogator {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A)
    (t : Time) (x : Space d) (i j : Fin d) :
    ∂ₜ (A.magneticFieldMatrix 𝓕.c · x (i, j)) t =
    ∂ₜ (fun t => s.unit j / 𝓕.c * A.electricField 𝓕.c t x i
    - s.unit i / 𝓕.c * A.electricField 𝓕.c t x j) t := by
  rw [time_deriv_magneticFieldMatrix]
  rw [P.electricField_space_deriv_eq_time_deriv, P.electricField_space_deriv_eq_time_deriv]
  conv_rhs =>
    rw [Time.deriv_eq]
    rw [fderiv_fun_sub (by
      apply Differentiable.differentiableAt
      apply Differentiable.const_mul
      exact electricField_apply_differentiable_time hA _ _) (by
        apply Differentiable.differentiableAt
        apply Differentiable.const_mul
        exact electricField_apply_differentiable_time hA _ _)]
    rw [fderiv_const_mul (by
        apply Differentiable.differentiableAt
        exact electricField_apply_differentiable_time hA _ _)]
    rw [fderiv_const_mul (by
        apply Differentiable.differentiableAt
        exact electricField_apply_differentiable_time hA _ _)]
  simp [← Time.deriv_eq]
  field_simp
  ring
  · exact hA
  · exact hA
  · exact hA

/-!

### B.2. Space derivative of the magnetic field in terms of electric field

-/

lemma space_deriv_magneticFieldMatrix_eq_electricField_mul_propogator {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A)
    (t : Time) (x : Space d) (i j k : Fin d) :
    ∂[k] (A.magneticFieldMatrix 𝓕.c t · (i, j)) x =
    ∂[k] (fun x => s.unit j / 𝓕.c * A.electricField 𝓕.c t x i
    - s.unit i / 𝓕.c * A.electricField 𝓕.c t x j) x := by
  rw [P.magneticFieldMatrix_space_deriv_eq_time_deriv hA]
  rw [P.time_deriv_magneticFieldMatrix_eq_electricField_mul_propogator hA]
  rw [Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sub]
  rw [fderiv_const_mul, fderiv_const_mul]
  simp [← Space.deriv_eq_fderiv_basis]
  rw [Time.deriv_eq]
  rw [fderiv_fun_sub]
  rw [fderiv_const_mul, fderiv_const_mul]
  simp [← Time.deriv_eq]
  rw [P.electricField_space_deriv_eq_time_deriv, P.electricField_space_deriv_eq_time_deriv]
  simp only [smul_eq_mul, neg_mul, mul_neg, sub_neg_eq_add]
  field_simp
  ring
  any_goals exact hA
  any_goals apply Differentiable.differentiableAt
  any_goals apply Differentiable.const_mul
  any_goals exact electricField_apply_differentiable_time hA x _
  any_goals exact electricField_apply_differentiable_space hA t _

/-!

### B.3. Magnetic field equal propogator cross electric field up to constant

-/

lemma magneticFieldMatrix_eq_propogator_cross_electricField {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) (i j : Fin d) :
    ∃ C, ∀ t x, A.magneticFieldMatrix 𝓕.c t x (i, j) =
    1/ 𝓕.c * (s.unit j * A.electricField 𝓕.c t x i -
      s.unit i * A.electricField 𝓕.c t x j) + C := by
  apply Space.equal_up_to_const_of_deriv_eq
  · exact magneticFieldMatrix_differentiable A hA (i, j)
  · apply Differentiable.const_mul
    apply Differentiable.sub
    · apply Differentiable.const_mul
      exact electricField_apply_differentiable hA
    · apply Differentiable.const_mul
      exact electricField_apply_differentiable hA
  · intro t x
    rw [P.time_deriv_magneticFieldMatrix_eq_electricField_mul_propogator hA t x i j]
    congr
    funext t
    field_simp
  · intro t x k
    rw [P.space_deriv_magneticFieldMatrix_eq_electricField_mul_propogator hA t x i j]
    congr
    funext x
    field_simp

/-!

## C. The electric field in terms of the magnetic field

-/
/-!

### C.1. The time derivative of the electric field in terms of magnetic field

-/

lemma time_deriv_electricField_eq_magneticFieldMatrix {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ ∞ A)
    (h : IsExtrema 𝓕 A 0)
    (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (A.electricField 𝓕.c · x i) t =
    ∂ₜ (fun t => 𝓕.c * ∑ j, A.magneticFieldMatrix 𝓕.c t x (i, j) * s.unit j) t := by
  rw [Time.deriv_euclid]
  rw [time_deriv_electricField_of_isExtrema hA 0 _ h t x i]
  simp only [one_div, _root_.mul_inv_rev, LorentzCurrentDensity.currentDensity_zero, Pi.zero_apply,
    PiLp.zero_apply, mul_zero, sub_zero]
  conv_lhs =>
    enter [2, 2, i];
    rw [magneticFieldMatrix_space_deriv_eq_time_deriv P (hA.of_le ENat.LEInfty.out) t x i]
  rw [Time.deriv_eq, fderiv_const_mul]
  simp [← Time.deriv_eq]
  have h1 : ∂ₜ (fun t => ∑ j, A.magneticFieldMatrix 𝓕.c t x (i, j) * s.unit j) t
    = ∑ j, ∂ₜ (A.magneticFieldMatrix 𝓕.c · x (i, j)) t * s.unit j := by
    rw [Time.deriv_eq]
    rw [fderiv_fun_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
    conv_lhs =>
      enter [2, k]
      rw [fderiv_mul_const (by
        apply Differentiable.differentiableAt
        apply magneticFieldMatrix_differentiable_time
        exact (hA.of_le ENat.LEInfty.out))]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    congr
    funext i
    ring_nf
    rfl
    · intro k _
      apply DifferentiableAt.mul_const
      apply Differentiable.differentiableAt
      apply magneticFieldMatrix_differentiable_time
      exact (hA.of_le ENat.LEInfty.out)

  rw [h1, Finset.mul_sum, Finset.mul_sum,← Finset.sum_neg_distrib]
  field_simp
  congr
  funext k
  field_simp
  simp [𝓕.c_sq]
  field_simp
  conv_lhs =>
    enter [1, 2, 1, t]
    rw [magneticFieldMatrix_antisymm]
  rw [Time.deriv_eq, fderiv_fun_neg]
  simp [← Time.deriv_eq]
  · refine DifferentiableAt.fun_sum ?_
    intro k _
    apply DifferentiableAt.mul_const
    apply Differentiable.differentiableAt
    apply magneticFieldMatrix_differentiable_time
    exact (hA.of_le ENat.LEInfty.out)
  · change ContDiff ℝ ∞ (fun _ => 0)
    fun_prop
  · exact electricField_differentiable_time (hA.of_le (ENat.LEInfty.out)) x

/-!

### C.2. The space derivative of the electric field in terms of magnetic field

-/

lemma space_deriv_electricField_eq_magneticFieldMatrix {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ ∞ A)
    (h : IsExtrema 𝓕 A 0)
    (t : Time) (x : Space d) (i k : Fin d) :
    ∂[k] (A.electricField 𝓕.c t · i) x =
    ∂[k] (fun x => 𝓕.c * ∑ j, A.magneticFieldMatrix 𝓕.c t x (i, j) * s.unit j) x := by
  have hA2 : ContDiff ℝ 2 A := hA.of_le ENat.LEInfty.out
  rw [P.electricField_space_deriv_eq_time_deriv hA2 t x i k]
  rw [P.time_deriv_electricField_eq_magneticFieldMatrix hA h t x i]
  rw [Time.deriv_eq]
  rw [fderiv_const_mul]
  rw [fderiv_fun_sum]
  simp [Finset.mul_sum, - Finset.sum_neg_distrib]
  rw [Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sum]
  simp [- Finset.sum_neg_distrib]
  congr
  funext j
  rw [fderiv_mul_const, fderiv_const_mul, fderiv_mul_const]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [← Space.deriv_eq_fderiv_basis]
  rw [P.magneticFieldMatrix_space_deriv_eq_time_deriv hA2 t x i j k]
  simp [← Time.deriv_eq]
  field_simp
  any_goals apply Differentiable.differentiableAt
  · exact fieldStrengthMatrix_differentiable_space hA2 t
  · apply Differentiable.mul_const
    exact fieldStrengthMatrix_differentiable_space hA2 t
  · exact fieldStrengthMatrix_differentiable_time hA2 x
  · intro i _
    apply Differentiable.differentiableAt
    apply Differentiable.const_mul
    apply Differentiable.mul_const
    exact fieldStrengthMatrix_differentiable_space hA2 t
  · intro i _
    apply Differentiable.differentiableAt
    apply Differentiable.mul_const
    exact fieldStrengthMatrix_differentiable_time hA2 x
  · apply Differentiable.fun_sum
    intro i _
    apply Differentiable.mul_const
    exact fieldStrengthMatrix_differentiable_time hA2 x

/-!

### C.3. Electric field equal propogator cross magnetic field up to constant

-/

lemma electricField_eq_propogator_cross_magneticFieldMatrix {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ ∞ A)
    (h : IsExtrema 𝓕 A 0) (i : Fin d) :
    ∃ C, ∀ t x, A.electricField 𝓕.c t x i =
    𝓕.c * ∑ j, A.magneticFieldMatrix 𝓕.c t x (i, j) * s.unit j + C := by
  have hA2 : ContDiff ℝ 2 A := hA.of_le ENat.LEInfty.out
  apply Space.equal_up_to_const_of_deriv_eq
  · exact electricField_apply_differentiable hA2
  · apply Differentiable.const_mul
    apply Differentiable.fun_sum
    intro j _
    apply Differentiable.mul_const
    exact magneticFieldMatrix_differentiable A hA2 (i, j)
  · intro t x
    rw [P.time_deriv_electricField_eq_magneticFieldMatrix hA _ t x i]
    congr
  · intro t x i
    rw [P.space_deriv_electricField_eq_magneticFieldMatrix hA]
    congr

end IsPlaneWave

end ElectromagneticPotential

end Electromagnetism
