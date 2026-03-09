/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Kinematics.ElectricField
/-!

# The Magnetic Field

## i. Overview

In 3-spatial dimensions from the electromagnetic potential we can define the magnetic field
` \vec B` as `(∇ × (A.vectorPotential t)) x`.
In this module we define this magnetic field from the electromagnetic potential.

In general dimensions we define the magnetic field matrix from the spatial components of the
field strength matrix. This is an antisymmetric matrix.

## ii. Key results

- `ElectromagneticPotential.magneticField` : The magnetic field from the electromagnetic potential
  in 3 spatial dimensions.
- `ElectromagneticPotential.magneticFieldMatrix` : The magnetic field matrix from the
  electromagnetic potential in general spatial dimensions.
- `ElectromagneticPotential.time_deriv_magneticFieldMatrix` : The time derivative of the magnetic
  field matrix in terms of the vector potential. (Aka Faraday's law).

## iii. Table of contents

- A. The magnetic field
  - A.1. Relation between the magnetic field and the field strength matrix
  - A.2. Divergence of the magnetic field
- B. The field strength matrix in terms of the electric and magnetic fields
- C. Magnetic field matrix
  - C.1. Antisymmetry of the magnetic field matrix
  - C.2. Magnetic field in terms of the magnetic field matrix
  - C.3. Magnetic field matrix in terms of vector potentials
  - C.4. Smoothness of the magnetic field matrix
  - C.5. Differentiablity of the magnetic field matrix
  - C.6. Spatial derivative of the magnetic field matrix
  - C.7. Temporal derivative of the magnetic field matrix
  - C.8. `curl` of the magnetic field matrix
- D. Magnetic field matrix for distributions
  - D.1. Magnetic field matrix in terms of vector potentials
  - D.2. The magnetic field matrix in terms of the field strength
  - D.3. Magnetic field matrix in 1d

## iv. References

-/

namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
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

open Space Time

/-!

## A. The magnetic field

-/

/-- The magnetic field from the electromagnetic potential. -/
noncomputable def magneticField (c : SpeedOfLight := 1) (A : ElectromagneticPotential) :
    MagneticField :=
  fun t x => (∇ × (A.vectorPotential c t)) x

lemma magneticField_eq {c : SpeedOfLight} (A : ElectromagneticPotential) :
    A.magneticField c = fun t x => (∇ × (A.vectorPotential c t)) x := rfl

/-!

### A.1. Relation between the magnetic field and the field strength matrix

-/

lemma magneticField_fst_eq_fieldStrengthMatrix {c : SpeedOfLight}
    (A : ElectromagneticPotential) (t : Time)
    (x : Space) (hA : Differentiable ℝ A) :
    A.magneticField c t x 0 =
    - A.fieldStrengthMatrix ((toTimeAndSpace c).symm (t, x)) (Sum.inr 1, Sum.inr 2) := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp only [Fin.isValue, inr_i_inr_i, neg_mul, one_mul, sub_neg_eq_add, neg_add_rev, neg_neg]
  rw [magneticField]
  simp only [curl, Fin.isValue]
  rw [neg_add_eq_sub]
  congr
  all_goals
  · rw [SpaceTime.deriv_sum_inr c _ hA]
    simp only [Fin.isValue, ContinuousLinearEquiv.apply_symm_apply]
    rw [Space.deriv_eq, Space.deriv_eq, Lorentz.Vector.fderiv_apply]
    rfl
    · refine Differentiable.comp hA ?_
      refine Differentiable.fun_comp ?_ ?_
      · exact ContinuousLinearEquiv.differentiable (toTimeAndSpace c).symm
      · fun_prop

lemma magneticField_snd_eq_fieldStrengthMatrix {c : SpeedOfLight}
    (A : ElectromagneticPotential) (t : Time)
    (x : Space) (hA : Differentiable ℝ A) :
    A.magneticField c t x 1 = A.fieldStrengthMatrix ((toTimeAndSpace c).symm (t, x))
      (Sum.inr 0, Sum.inr 2) := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp only [Fin.isValue, inr_i_inr_i, neg_mul, one_mul, sub_neg_eq_add]
  rw [magneticField]
  simp only [curl, Fin.isValue]
  rw [neg_add_eq_sub]
  congr
  all_goals
  · rw [SpaceTime.deriv_sum_inr c _ hA]
    simp only [Fin.isValue, ContinuousLinearEquiv.apply_symm_apply]
    rw [Space.deriv_eq, Space.deriv_eq, Lorentz.Vector.fderiv_apply]
    rfl
    · refine Differentiable.comp hA ?_
      refine Differentiable.fun_comp ?_ ?_
      · exact ContinuousLinearEquiv.differentiable (toTimeAndSpace c).symm
      · fun_prop

lemma magneticField_thd_eq_fieldStrengthMatrix {c : SpeedOfLight} (A : ElectromagneticPotential)
    (t : Time) (x : Space) (hA : Differentiable ℝ A) :
    A.magneticField c t x 2 =
    - A.fieldStrengthMatrix ((toTimeAndSpace c).symm (t, x)) (Sum.inr 0, Sum.inr 1) := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp only [Fin.isValue, inr_i_inr_i, neg_mul, one_mul, sub_neg_eq_add, neg_add_rev, neg_neg]
  rw [magneticField]
  simp only [curl, Fin.isValue]
  rw [neg_add_eq_sub]
  congr
  all_goals
  · rw [SpaceTime.deriv_sum_inr c _ hA]
    simp only [Fin.isValue, ContinuousLinearEquiv.apply_symm_apply]
    rw [Space.deriv_eq, Space.deriv_eq, Lorentz.Vector.fderiv_apply]
    rfl
    · refine Differentiable.comp hA ?_
      refine Differentiable.fun_comp ?_ ?_
      · exact ContinuousLinearEquiv.differentiable (toTimeAndSpace c).symm
      · fun_prop

/-!

### A.2. Divergence of the magnetic field

-/

lemma magneticField_div_eq_zero (A : ElectromagneticPotential)
    (hA : ContDiff ℝ 2 A) (t : Time) : Space.div (A.magneticField c t) = 0 := by
  rw [magneticField_eq]
  simp only
  rw [Space.div_of_curl_eq_zero]
  exact vectorPotential_contDiff_space A hA t

/-!

## B. The field strength matrix in terms of the electric and magnetic fields

-/

lemma fieldStrengthMatrix_eq_electric_magnetic {c} (A : ElectromagneticPotential) (t : Time)
    (x : Space) (hA : Differentiable ℝ A) (μ ν : Fin 1 ⊕ Fin 3) :
    A.fieldStrengthMatrix ((toTimeAndSpace c).symm (t, x)) (μ, ν) =
    match μ, ν with
    | Sum.inl 0, Sum.inl 0 => 0
    | Sum.inl 0, Sum.inr i => - A.electricField c t x i / c
    | Sum.inr i, Sum.inl 0 => A.electricField c t x i / c
    | Sum.inr i, Sum.inr j =>
    match i, j with
    | 0, 0 => 0
    | 0, 1 => - A.magneticField c t x 2
    | 0, 2 => A.magneticField c t x 1
    | 1, 0 => A.magneticField c t x 2
    | 1, 1 => 0
    | 1, 2 => - A.magneticField c t x 0
    | 2, 0 => - A.magneticField c t x 1
    | 2, 1 => A.magneticField c t x 0
    | 2, 2 => 0 := by
  match μ, ν with
  | Sum.inl 0, Sum.inl 0 => simp
  | Sum.inl 0, Sum.inr i => simp [electricField_eq_fieldStrengthMatrix A t x i hA]
  | Sum.inr i, Sum.inl 0 =>
    simp [electricField_eq_fieldStrengthMatrix A t x i hA]
    field_simp
    exact fieldStrengthMatrix_antisymm A ((toTimeAndSpace c).symm (t, x)) (Sum.inr i) (Sum.inl 0)
  | Sum.inr i, Sum.inr j =>
    match i, j with
    | 0, 0 => simp
    | 0, 1 =>
      simp [magneticField_thd_eq_fieldStrengthMatrix A t x hA]
    | 0, 2 =>
      simp [magneticField_snd_eq_fieldStrengthMatrix A t x hA]
    | 1, 0 =>
      simp [magneticField_thd_eq_fieldStrengthMatrix A t x hA]
      rw [fieldStrengthMatrix_antisymm]
    | 1, 1 => simp
    | 1, 2 =>
      simp [magneticField_fst_eq_fieldStrengthMatrix A t x hA]
    | 2, 0 =>
      simp [magneticField_snd_eq_fieldStrengthMatrix A t x hA]
      rw [fieldStrengthMatrix_antisymm]
    | 2, 1 =>
      simp [magneticField_fst_eq_fieldStrengthMatrix A t x hA]
      rw [fieldStrengthMatrix_antisymm]
    | 2, 2 => simp

lemma fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime (c : SpeedOfLight)
    (A : ElectromagneticPotential)
    (x : SpaceTime) (hA : Differentiable ℝ A) (μ ν : Fin 1 ⊕ Fin 3) :
    let tx := SpaceTime.toTimeAndSpace c x
    A.fieldStrengthMatrix x (μ, ν) =
    match μ, ν with
    | Sum.inl 0, Sum.inl 0 => 0
    | Sum.inl 0, Sum.inr i => - A.electricField c tx.1 tx.2 i / c
    | Sum.inr i, Sum.inl 0 => A.electricField c tx.1 tx.2 i / c
    | Sum.inr i, Sum.inr j =>
    match i, j with
    | 0, 0 => 0
    | 0, 1 => - A.magneticField c tx.1 tx.2 2
    | 0, 2 => A.magneticField c tx.1 tx.2 1
    | 1, 0 => A.magneticField c tx.1 tx.2 2
    | 1, 1 => 0
    | 1, 2 => - A.magneticField c tx.1 tx.2 0
    | 2, 0 => - A.magneticField c tx.1 tx.2 1
    | 2, 1 => A.magneticField c tx.1 tx.2 0
    | 2, 2 => 0 := by
  dsimp
  rw [← fieldStrengthMatrix_eq_electric_magnetic A]
  simp only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  exact hA

/-!

## C. Magnetic field matrix

-/

/-- The matrix corresponding to the magnetic field in general dimensions.
  In `3` space-dimensions this reduces to a vector. -/
noncomputable def magneticFieldMatrix (c : SpeedOfLight := 1) (A : ElectromagneticPotential d) :
    Time → Space d → (Fin d × Fin d) → ℝ := timeSlice c <| fun x ij =>
    A.fieldStrengthMatrix x (Sum.inr ij.1, Sum.inr ij.2)

lemma magneticFieldMatrix_eq {c : SpeedOfLight} (A : ElectromagneticPotential d) :
    A.magneticFieldMatrix c = fun t x ij =>
      A.fieldStrengthMatrix ((toTimeAndSpace c).symm (t, x)) (Sum.inr ij.1, Sum.inr ij.2) := rfl

lemma fieldStrengthMatrix_inr_inr_eq_magneticFieldMatrix {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (x : SpaceTime d) (i j : Fin d) :
    A.fieldStrengthMatrix x (Sum.inr i, Sum.inr j) =
    A.magneticFieldMatrix c (x.time c) x.space (i, j) := by
  rw [magneticFieldMatrix_eq]
  simp

/-!

### C.1. Antisymmetry of the magnetic field matrix

-/

lemma magneticFieldMatrix_antisymm {c : SpeedOfLight}
    (A : ElectromagneticPotential d) (t : Time)
    (x : Space d) (i j : Fin d) :
    A.magneticFieldMatrix c t x (i, j) = - A.magneticFieldMatrix c t x (j, i) := by
  rw [magneticFieldMatrix_eq]
  exact fieldStrengthMatrix_antisymm A ((toTimeAndSpace c).symm (t, x)) (Sum.inr i) (Sum.inr j)

@[simp]
lemma magneticFieldMatrix_diag_eq_zero {c : SpeedOfLight}
    (A : ElectromagneticPotential d) (t : Time)
    (x : Space d) (i : Fin d) :
    A.magneticFieldMatrix c t x (i, i) = 0 := by
  rw [magneticFieldMatrix_eq]
  exact fieldStrengthMatrix_diag_eq_zero A ((toTimeAndSpace c).symm (t, x)) (Sum.inr i)

/-!

### C.2. Magnetic field in terms of the magnetic field matrix

-/

lemma magneticField_eq_magneticFieldMatrix {c : SpeedOfLight} (A : ElectromagneticPotential)
    (hA : Differentiable ℝ A) :
    A.magneticField c = fun t x => WithLp.toLp 2 fun i =>
      match i with
      | 0 => - A.magneticFieldMatrix c t x (1, 2)
      | 1 => A.magneticFieldMatrix c t x (0, 2)
      | 2 => - A.magneticFieldMatrix c t x (0, 1) := by
  rw [magneticFieldMatrix_eq]
  ext t x i
  fin_cases i
  · simp [magneticField_fst_eq_fieldStrengthMatrix A t x hA]
  · simp [magneticField_snd_eq_fieldStrengthMatrix A t x hA]
  · simp [magneticField_thd_eq_fieldStrengthMatrix A t x hA]

lemma magneticField_curl_eq_magneticFieldMatrix{c : SpeedOfLight} (A : ElectromagneticPotential)
    (hA : ContDiff ℝ 2 A) (t : Time) :
    (∇ × A.magneticField c t) x i = ∑ j, Space.deriv j (A.magneticFieldMatrix c t · (j, i)) x:= by
  rw [magneticField_eq_magneticFieldMatrix A (hA.differentiable (by simp))]
  simp only [curl, Fin.isValue]
  fin_cases i
  · simp only [Fin.isValue, deriv_eq_fderiv_basis, fderiv_fun_neg, ContinuousLinearMap.neg_apply,
    Fin.zero_eta, Fin.sum_univ_three, magneticFieldMatrix_diag_eq_zero, fderiv_fun_const,
    Pi.zero_apply, ContinuousLinearMap.zero_apply, zero_add]
    conv_lhs =>
      enter [2, 1, 2, x]
      rw [magneticFieldMatrix_antisymm]
    conv_lhs =>
      enter [1, 1, 1, 2, x]
      rw [magneticFieldMatrix_antisymm]
    simp
  · simp only [Fin.isValue, deriv_eq_fderiv_basis, fderiv_fun_neg, ContinuousLinearMap.neg_apply,
    sub_neg_eq_add, Fin.mk_one, Fin.sum_univ_three, magneticFieldMatrix_diag_eq_zero,
    fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply, add_zero]
    conv_lhs =>
      enter [1, 1, 1, 2, x]
      rw [magneticFieldMatrix_antisymm]
    simp only [Fin.isValue, fderiv_fun_neg, ContinuousLinearMap.neg_apply, neg_neg]
    ring
  · simp only [Fin.isValue, deriv_eq_fderiv_basis, fderiv_fun_neg, ContinuousLinearMap.neg_apply,
    sub_neg_eq_add, Fin.reduceFinMk, Fin.sum_univ_three, magneticFieldMatrix_diag_eq_zero,
    fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply, add_zero]

/-!

### C.3. Magnetic field matrix in terms of vector potentials

-/

lemma magneticFieldMatrix_eq_vectorPotential {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (t : Time) (x : Space d) (i j : Fin d) :
    A.magneticFieldMatrix c t x (i, j) = Space.deriv j (A.vectorPotential c t · i) x -
    Space.deriv i (A.vectorPotential c t · j) x := by
  rw [magneticFieldMatrix_eq]
  simp only
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp only [inr_i_inr_i, neg_mul, one_mul, sub_neg_eq_add]
  rw [SpaceTime.deriv_sum_inr c _ hA, SpaceTime.deriv_sum_inr c _ hA]
  simp [vectorPotential]
  rw [add_comm]
  congr
  all_goals
  · rw [← Space.deriv_lorentz_vector]
    rfl
    apply Differentiable.comp
    · exact hA
    · apply Differentiable.fun_comp
      · exact ContinuousLinearEquiv.differentiable (toTimeAndSpace c).symm
      · fun_prop

/-!

### C.4. Smoothness of the magnetic field matrix

-/

lemma magneticFieldMatrix_contDiff {n} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ (n + 1) A) (ij) :
    ContDiff ℝ n ↿(fun t x => A.magneticFieldMatrix c t x ij) := by
  simp [magneticFieldMatrix_eq]
  change ContDiff ℝ n ((A.fieldStrengthMatrix · (Sum.inr ij.1, Sum.inr ij.2)) ∘
    (toTimeAndSpace c).symm)
  refine ContDiff.comp ?_ ?_
  · exact fieldStrengthMatrix_contDiff (hA)
  · exact ContinuousLinearEquiv.contDiff (toTimeAndSpace c).symm

lemma magneticFieldMatrix_space_contDiff {n} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ (n + 1) A) (t : Time) (ij) :
    ContDiff ℝ n (fun x => A.magneticFieldMatrix c t x ij) := by
  change ContDiff ℝ n (↿(fun t x => A.magneticFieldMatrix c t x ij) ∘ fun x => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact magneticFieldMatrix_contDiff A hA ij
  · fun_prop

lemma magneticFieldMatrix_time_contDiff {n} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ (n + 1) A) (x : Space d) (ij) :
    ContDiff ℝ n (fun t => A.magneticFieldMatrix c t x ij) := by
  change ContDiff ℝ n (↿(fun t x => A.magneticFieldMatrix c t x ij) ∘ fun t => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact magneticFieldMatrix_contDiff A hA ij
  · fun_prop

/-!

### C.5. Differentiablity of the magnetic field matrix

-/

lemma magneticFieldMatrix_differentiable {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (ij) : Differentiable ℝ ↿(fun t x => A.magneticFieldMatrix c t x ij) := by
  simp [magneticFieldMatrix_eq]
  change Differentiable ℝ ((A.fieldStrengthMatrix · (Sum.inr ij.1, Sum.inr ij.2)) ∘
    (toTimeAndSpace c).symm)
  refine Differentiable.comp ?_ ?_
  · exact fieldStrengthMatrix_differentiable (hA)
  · exact ContinuousLinearEquiv.differentiable (toTimeAndSpace c).symm

lemma magneticFieldMatrix_differentiable_space {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (t : Time) (ij) :
    Differentiable ℝ (fun x => A.magneticFieldMatrix c t x ij) := by
  change Differentiable ℝ (↿(fun t x => A.magneticFieldMatrix c t x ij) ∘ fun x => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact magneticFieldMatrix_differentiable A hA ij
  · fun_prop

lemma magneticFieldMatrix_differentiable_time {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (x : Space d) (ij) :
    Differentiable ℝ (fun t => A.magneticFieldMatrix c t x ij) := by
  change Differentiable ℝ (↿(fun t x => A.magneticFieldMatrix c t x ij) ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact magneticFieldMatrix_differentiable A hA ij
  · fun_prop

/-!

### C.6. Spatial derivative of the magnetic field matrix

-/

lemma magneticFieldMatrix_space_deriv_eq {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) (i j k : Fin d) :
    ∂[k] (A.magneticFieldMatrix c t · (i, j)) x =
    ∂[i] (A.magneticFieldMatrix c t · (k, j)) x
    - ∂[j] (A.magneticFieldMatrix c t · (k, i)) x := by
  conv_lhs =>
    enter [2, x]
    rw [magneticFieldMatrix_eq_vectorPotential A (hA.differentiable (by simp)) t x i j]
  conv_rhs =>
    enter [1, 2, x]
    rw [magneticFieldMatrix_eq_vectorPotential A (hA.differentiable (by simp)) t x]
  conv_rhs =>
    enter [2, 2, x]
    rw [magneticFieldMatrix_eq_vectorPotential A (hA.differentiable (by simp)) t x]
  conv_lhs =>
    rw [Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sub]
  simp [← Space.deriv_eq_fderiv_basis]
  conv_rhs =>
    rw [Space.deriv_eq_fderiv_basis]
    enter [2]
    rw [Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sub, fderiv_fun_sub]
  simp [← Space.deriv_eq_fderiv_basis]
  conv_lhs =>
    rw [Space.deriv_commute _ (vectorPotential_apply_contDiff_space _ hA _ _)]
    enter [2]
    rw [Space.deriv_commute _ ((vectorPotential_apply_contDiff_space _ hA _ _))]
  conv_rhs =>
    enter [1, 1]
    rw [Space.deriv_commute _ ((vectorPotential_apply_contDiff_space _ hA _ _))]
  ring
  all_goals
  · apply Differentiable.differentiableAt
    apply Space.deriv_differentiable
    apply vectorPotential_apply_contDiff_space _ hA

/-!

### C.7. Temporal derivative of the magnetic field matrix

-/

lemma time_deriv_magneticFieldMatrix {d : ℕ} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) (i j : Fin d) :
    ∂ₜ (A.magneticFieldMatrix c · x (i, j)) t =
    ∂[i] (A.electricField c t · j) x - ∂[j] (A.electricField c t · i) x := by
  calc _
    _ = ∂ₜ (fun t => ∂[j] (fun x => A.vectorPotential c t x i) x) t
        - ∂ₜ (fun t => ∂[i] (fun x => A.vectorPotential c t x j) x) t := by
      conv_lhs =>
        enter [1, t]
        rw [magneticFieldMatrix_eq_vectorPotential _ (hA.differentiable (by simp))]
      rw [Time.deriv, fderiv_fun_sub]
      rfl
      all_goals
      · apply Differentiable.differentiableAt
        apply Space.space_deriv_differentiable_time
        apply vectorPotential_comp_contDiff _ hA
    _ = ∂[j] (fun x => ∂ₜ (fun t => A.vectorPotential c t x i) t) x
        - ∂[i] (fun x => ∂ₜ (fun t => A.vectorPotential c t x j) t) x := by
      rw [Space.time_deriv_comm_space_deriv _]
      rw [Space.time_deriv_comm_space_deriv _]
      all_goals
      · apply vectorPotential_comp_contDiff _ hA
    _ = ∂[i] (A.electricField c t · j) x - ∂[j] (A.electricField c t · i) x := by
      conv_lhs =>
        enter [1, 2, x]
        rw [time_deriv_comp_vectorPotential_eq_electricField (hA.differentiable (by simp))]
      conv_lhs =>
        enter [2, 2, x]
        rw [time_deriv_comp_vectorPotential_eq_electricField (hA.differentiable (by simp))]
      rw [Space.deriv_eq_fderiv_basis, fderiv_fun_sub
        (by apply (electricField_apply_differentiable_space hA _ _).neg.differentiableAt)
        (by
          apply Differentiable.differentiableAt
          apply Space.deriv_differentiable
          exact scalarPotential_contDiff_space c A hA t), fderiv_fun_neg]
      conv_lhs =>
        enter [2]
        rw [Space.deriv_eq_fderiv_basis, fderiv_fun_sub
        (by apply (electricField_apply_differentiable_space hA _ _).neg.differentiableAt)
        (by
          apply Differentiable.differentiableAt
          apply Space.deriv_differentiable
          exact scalarPotential_contDiff_space c A hA t), fderiv_fun_neg]
      conv_lhs =>
        enter [1]
        simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, ContinuousLinearMap.neg_apply]
        enter [2]
        rw [← Space.deriv_eq_fderiv_basis, Space.deriv_commute _
          (scalarPotential_contDiff_space c A hA t)]
      simp [← Space.deriv_eq_fderiv_basis]
      ring

lemma time_deriv_time_deriv_magneticFieldMatrix {d : ℕ} {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 3 A) (t : Time) (x : Space d) (i j : Fin d) :
    ∂ₜ (∂ₜ (A.magneticFieldMatrix c · x (i, j))) t =
    ∂[i] (fun x => ∂ₜ (fun t => A.electricField c t x) t j) x -
    ∂[j] (fun x => ∂ₜ (fun t => A.electricField c t x) t i) x := by
  conv_lhs =>
    enter [1, t]
    rw [time_deriv_magneticFieldMatrix A (hA.of_le (right_eq_inf.mp rfl)) t x i j]
  rw [Time.deriv, fderiv_fun_sub]
  simp [← Time.deriv_eq]
  rw [Space.time_deriv_comm_space_deriv _]
  rw [Space.time_deriv_comm_space_deriv _]
  congr
  · funext x
    rw [Time.deriv_euclid]
    apply electricField_differentiable_time (hA.of_le (right_eq_inf.mp rfl))
  · funext x
    rw [Time.deriv_euclid]
    apply electricField_differentiable_time (hA.of_le (right_eq_inf.mp rfl))
  · apply electricField_apply_contDiff hA
  · apply electricField_apply_contDiff hA
  · apply Differentiable.differentiableAt
    apply Space.space_deriv_differentiable_time
    apply electricField_apply_contDiff hA
  · apply Differentiable.differentiableAt
    apply Space.space_deriv_differentiable_time
    apply electricField_apply_contDiff hA

/-!

### C.8. `curl` of the magnetic field matrix

-/

lemma curl_magneticFieldMatrix_eq_electricField_fieldStrengthMatrix {d : ℕ} {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) (i : Fin d) :
    ∑ j, Space.deriv j (A.magneticFieldMatrix c t · (j, i)) x =
    (1/c^2) * ∂ₜ (fun t => A.electricField c t x) t i +
    (∑ (μ : (Fin 1 ⊕ Fin d)), (∂_ μ (A.fieldStrengthMatrix · (μ, Sum.inr i))
    ((toTimeAndSpace c).symm (t, x)))) := by
  trans (1/c^2) * ∂ₜ (fun t => A.electricField c t x) t i +
    (- (1/c^2) * ∂ₜ (fun t => A.electricField c t x) t i +
    ∑ j, Space.deriv j (A.magneticFieldMatrix c t · (j, i)) x)
  · ring
  congr 1
  rw [Fintype.sum_sum_type]
  congr
  · simp
    rw [time_deriv_electricField_eq_fieldStrengthMatrix hA t x i]
    field_simp
  · funext j
    rw [SpaceTime.deriv_sum_inr c]
    simp
    rfl
    · apply fieldStrengthMatrix_differentiable hA

end ElectromagneticPotential

/-!

## D. Magnetic field matrix for distributions

-/

namespace DistElectromagneticPotential
open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix SchwartzMap Lorentz
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-- The magnetic field matrix of an electromagnetic potential which is a distribution. -/
noncomputable def magneticFieldMatrix {d} (c : SpeedOfLight) :
    DistElectromagneticPotential d →ₗ[ℝ]
    (Time × Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d) ⊗[ℝ] EuclideanSpace ℝ (Fin d)) where
  toFun A :=
    ⟨TensorProduct.map (Lorentz.Vector.spatialCLM d).toLinearMap
      (Lorentz.Vector.spatialCLM d).toLinearMap, by continuity⟩ ∘L
    distTimeSlice c A.fieldStrength
  map_add' A1 A2 := by
    ext ε
    simp
  map_smul' r A := by
    ext ε
    simp

/-!

### D.1. Magnetic field matrix in terms of vector potentials

-/

lemma magneticFieldMatrix_eq_vectorPotential {c : SpeedOfLight}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(Time × Space d, ℝ)) :
    A.magneticFieldMatrix c ε = ∑ i, ∑ j,
    (Space.distSpaceDeriv j (A.vectorPotential c) ε i -
      Space.distSpaceDeriv i (A.vectorPotential c) ε j) •
    EuclideanSpace.basisFun (Fin d) ℝ i ⊗ₜ[ℝ] EuclideanSpace.basisFun (Fin d) ℝ j := by
  simp only [magneticFieldMatrix, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.coe_mk', Function.comp_apply, distTimeSlice_apply, fieldStrength_eq_basis,
    Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, inl_0_inl_0, one_mul, inr_i_inr_i, neg_mul, sub_neg_eq_add, sub_self,
    zero_smul, zero_add, map_add, map_sum, map_smul, map_tmul, ContinuousLinearMap.coe_coe,
    Lorentz.Vector.spatialCLM_basis_sum_inl, Lorentz.Vector.spatialCLM_basis_sum_inr,
    EuclideanSpace.basisFun_apply, zero_tmul, smul_zero, Finset.sum_const_zero, tmul_zero]
  simp [← distTimeSlice_apply, distTimeSlice_distDeriv_inr, vectorPotential,
  Space.distSpaceDeriv_apply_CLM, Lorentz.Vector.spatialCLM, neg_add_eq_sub]

lemma magneticFieldMatrix_basis_repr_eq_vector_potential {c : SpeedOfLight}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(Time × Space d, ℝ)) (i j : Fin d) :
    ((PiLp.basisFun 2 ℝ (Fin d)).tensorProduct (PiLp.basisFun 2 ℝ (Fin d))).repr
        (A.magneticFieldMatrix c ε) (i, j) =
      Space.distSpaceDeriv j (A.vectorPotential c) ε i -
      Space.distSpaceDeriv i (A.vectorPotential c) ε j := by
  rw [magneticFieldMatrix_eq_vectorPotential]
  simp

lemma magneticFieldMatrix_distSpaceDeriv_basis_repr_eq_vector_potential {c : SpeedOfLight}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(Time × Space d, ℝ)) (i j k : Fin d) :
    ((PiLp.basisFun 2 ℝ (Fin d)).tensorProduct (PiLp.basisFun 2 ℝ (Fin d))).repr
    (Space.distSpaceDeriv k (A.magneticFieldMatrix c) ε) (i, j) =
    Space.distSpaceDeriv k (Space.distSpaceDeriv j (A.vectorPotential c)) ε i -
    Space.distSpaceDeriv k (Space.distSpaceDeriv i (A.vectorPotential c)) ε j := by
  simp [Space.distSpaceDeriv_apply', magneticFieldMatrix_basis_repr_eq_vector_potential]
  ring

/-!

### D.2. The magnetic field matrix in terms of the field strength

-/

lemma magneticFieldMatrix_basis_repr_eq_fieldStrength {c : SpeedOfLight}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(Time × Space d, ℝ)) (i j : Fin d) :
    ((PiLp.basisFun 2 ℝ (Fin d)).tensorProduct (PiLp.basisFun 2 ℝ (Fin d))).repr
        (A.magneticFieldMatrix c ε) (i, j) =
      (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr
        (distTimeSlice c A.fieldStrength ε) (Sum.inr i, Sum.inr j) := by
  simp only [magneticFieldMatrix_eq_vectorPotential, EuclideanSpace.basisFun_apply, map_sum,
    map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
    Basis.tensorProduct_repr_tmul_apply, PiLp.basisFun_repr, EuclideanSpace.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero, distTimeSlice_apply,
    fieldStrength_basis_repr_eq_single, inr_i_inr_i, neg_mul, one_mul, sub_neg_eq_add]
  simp only [vectorPotential, Vector.spatialCLM, LinearMap.coe_mk, AddHom.coe_mk,
    Space.distSpaceDeriv_apply_CLM, ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_mk',
    Function.comp_apply, ← distTimeSlice_apply, distTimeSlice_distDeriv_inr]
  ring

/-!

### D.3. Magnetic field matrix in 1d

-/

@[simp]
lemma magneticFieldMatrix_one_dim_eq_zero {c : SpeedOfLight}
    (A : DistElectromagneticPotential 1) :
    A.magneticFieldMatrix c = 0 := by
  ext ε
  rw [magneticFieldMatrix_eq_vectorPotential]
  simp

/-!

### D.4. Magnetic field matrix of scalar potentials

-/

@[simp]
lemma ofScalarPotential_magneticFieldMatrix {c : SpeedOfLight}
    (V : (Time × Space d) →d[ℝ] ℝ)  :
    (ofScalarPotential c V).magneticFieldMatrix c = 0 := by
  ext ε
  rw [magneticFieldMatrix_eq_vectorPotential]
  simp

end DistElectromagneticPotential
end Electromagnetism
