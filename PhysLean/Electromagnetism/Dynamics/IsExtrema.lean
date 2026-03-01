/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Dynamics.Lagrangian
/-!

# Extrema of the Lagrangian density

## i. Overview

In this module we define what it means for an electromagnetic potential
to be an extremum of the Lagrangian density in presence of a Lorentz current density.

This is equivalent to the electromagnetic potential satisfying
Maxwell's equations with sources, i.e. Gauss's law and Ampère's law.

## ii. Key results

- `IsExtrema` : The condition on an electromagnetic potential to be an extrema of the lagrangian.
- `isExtrema_iff_gauss_ampere_magneticFieldMatrix` : The electromagnetic potential is an extrema
  of the lagrangian if and only if Gauss's law and Ampère's law hold
  (in terms of the magnetic field matrix).
- `time_deriv_time_deriv_magneticFieldMatrix_of_isExtrema` : A wave-like equation for the
  magnetic field matrix from the extrema condition.
- `time_deriv_time_deriv_electricField_of_isExtrema` : A wave-like equation for the
  electric field from the extrema condition.

## iii. Table of contents

- A. The condition for an extrema of the Lagrangian density
  - A.1. Extrema condition in terms of the field strength matrix
  - A.2. Extrema condition in terms of tensors
  - A.3. Equivariance of the extrema condition
- B. Gauss's law and Ampère's law and the extrema condition
- C. Time derivatives from the extrema condition
- D. Second time derivatives from the extrema condition
  - D.1. Second time derivatives of the magnetic field from the extrema condition
  - D.2. Second time derivatives of the electric field from the extrema condition
- E. Is Extema condition in the distributional case
  - E.1. IsExtrema and Gauss's law and Ampère's law
  - E.2. IsExtrema in terms of Vector Potentials
  - E.3. The exterma condition in terms of tensors
  - E.4. The invariance of the exterma condition under Lorentz transformations

## iv. References

-/
namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor ContDiff

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
open InnerProductSpace
open Lorentz.Vector
open Time Space
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. The condition for an extrema of the Lagrangian density

-/

/-- The condition on an electromagnetic potential to be an extrema of the lagrangian. -/
def IsExtrema {d} (𝓕 : FreeSpace) (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) : Prop :=
  gradLagrangian 𝓕 A J = 0

lemma isExtrema_iff_gradLagrangian {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔ A.gradLagrangian 𝓕 J = 0 := by rfl

/-!

### A.1. Extrema condition in terms of the field strength matrix

-/

lemma isExtrema_iff_fieldStrengthMatrix {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J) :
    IsExtrema 𝓕 A J ↔
    ∀ x, ∀ ν, ∑ μ, ∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x = 𝓕.μ₀ * J x ν := by
  rw [isExtrema_iff_gradLagrangian, gradLagrangian_eq_sum_fieldStrengthMatrix A hA J hJ, funext_iff]
  conv_lhs =>
    enter [x, 1, 2, ν]
    rw [smul_smul]
  conv_lhs =>
    enter [x]
    simp only [one_div, Pi.zero_apply]
    rw [Lorentz.Vector.sum_basis_eq_zero_iff]
  apply Iff.intro
  · intro h x ν
    specialize h x ν
    simp at h
    have h' : η ν ν ≠ 0 := η_diag_ne_zero
    simp_all
    linear_combination (norm := field_simp) 𝓕.μ₀ * h
    ring
  · intro h x ν
    specialize h x ν
    simp only [mul_eq_zero]
    right
    linear_combination (norm := field_simp) 𝓕.μ₀⁻¹ * h
    ring

/-!

### A.2. Extrema condition in terms of tensors

The electromagnetic potential is an exterma of the lagrangian if and only if

$$\frac{1}{\mu_0} \partial_\mu F^{\mu \nu} - J^{\nu} = 0.$$

-/

lemma isExtrema_iff_tensors {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J) :
    IsExtrema 𝓕 A J ↔ ∀ x,
    {((1/ 𝓕.μ₀ : ℝ) • tensorDeriv A.toFieldStrength x | κ κ ν') + - (J x | ν')}ᵀ = 0 := by
  apply Iff.intro
  · intro h
    simp only [IsExtrema] at h
    intro x
    have h1 : ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
        (permT id (PermCond.auto) {((1/ 𝓕.μ₀ : ℝ) • tensorDeriv A.toFieldStrength x | κ κ ν') +
        - (J x | ν')}ᵀ)) = 0 := by
      funext ν
      have h2 : gradLagrangian 𝓕 A J x ν = 0 := by simp [h]
      rw [gradLagrangian_eq_tensor A hA J hJ] at h2
      simp only [Nat.reduceSucc, Nat.reduceAdd, Fin.isValue, one_div, map_smul, map_neg, map_add,
        permT_permT, CompTriple.comp_eq, apply_add, apply_smul, Lorentz.Vector.neg_apply,
        mul_eq_zero] at h2
      have hn : η ν ν ≠ 0 := η_diag_ne_zero
      simp_all only [Fin.isValue, false_or, ne_eq, Nat.reduceSucc, Nat.reduceAdd, one_div, map_smul,
        map_neg, map_add, permT_permT, CompTriple.comp_eq, apply_add, apply_smul,
        Lorentz.Vector.neg_apply, Lorentz.Vector.zero_apply]
    generalize {((1/ 𝓕.μ₀ : ℝ) • tensorDeriv A.toFieldStrength x | κ κ ν') +
        - (J x | ν')}ᵀ = V at *
    simp only [Nat.reduceSucc, Nat.reduceAdd, Fin.isValue, EmbeddingLike.map_eq_zero_iff] at h1
    rw [permT_eq_zero_iff] at h1
    exact h1
  · intro h
    simp only [IsExtrema]
    funext x
    funext ν
    rw [gradLagrangian_eq_tensor A hA J hJ, h]
    simp only [map_zero, Lorentz.Vector.zero_apply, mul_zero, Pi.zero_apply]

/-!

### A.3. Equivariance of the extrema condition

If `A` is an extrema of the lagrangian with current density `J`, then the Lorentz transformation
`Λ • A (Λ⁻¹ • x)` is an extrema of the lagrangian with current density `Λ • J (Λ⁻¹ • x)`.

Combined with `time_deriv_time_deriv_electricField_of_isExtrema`, this shows that
the speed with which an electromagnetic wave propagates is invariant under Lorentz transformations.

-/

lemma isExtrema_lorentzGroup_apply_iff {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J)
    (Λ : LorentzGroup d) :
    IsExtrema 𝓕 (fun x => Λ • A (Λ⁻¹ • x)) (fun x => Λ • J (Λ⁻¹ • x)) ↔
    IsExtrema 𝓕 A J := by
  rw [isExtrema_iff_tensors]
  conv_lhs =>
    enter [x, 1, 1, 2, 2, 2]
    change tensorDeriv (fun x => toFieldStrength (fun x => Λ • A (Λ⁻¹ • x)) x) x
    enter [1,x]
    rw [toFieldStrength_equivariant _ _ (hA.differentiable (by simp))]
  conv_lhs =>
    enter [x]
    rw [tensorDeriv_equivariant _ _ _ (by
      apply toFieldStrength_differentiable
      exact hA.of_le ENat.LEInfty.out)]
    rw [smul_comm]
    rw [Tensorial.toTensor_smul, Tensorial.toTensor_smul]
    simp only [Nat.reduceAdd, Nat.reduceSucc, Fin.isValue, one_div, map_smul, actionT_smul,
      contrT_equivariant, map_neg, permT_equivariant]
    rw [smul_comm, ← Tensor.actionT_neg, ← Tensor.actionT_add]
  apply Iff.intro
  · intro h
    rw [isExtrema_iff_tensors A hA J hJ]
    intro x
    apply MulAction.injective Λ
    simp only [Nat.reduceAdd, Nat.reduceSucc, Fin.isValue, one_div, map_smul, map_neg,
      _root_.smul_add, actionT_smul, _root_.smul_neg, _root_.smul_zero]
    simpa using h (Λ • x)
  · intro h x
    rw [isExtrema_iff_tensors A hA J hJ] at h
    specialize h (Λ⁻¹ • x)
    simp at h
    rw [h]
    simp
  · change ContDiff ℝ ∞ (actionCLM Λ ∘ A ∘ actionCLM Λ⁻¹)
    apply ContDiff.comp
    · exact ContinuousLinearMap.contDiff (actionCLM Λ)
    · apply ContDiff.comp
      · exact hA
      · exact ContinuousLinearMap.contDiff (actionCLM Λ⁻¹)
  · change ContDiff ℝ ∞ (actionCLM Λ ∘ J ∘ actionCLM Λ⁻¹)
    apply ContDiff.comp
    · exact ContinuousLinearMap.contDiff (actionCLM Λ)
    · apply ContDiff.comp
      · exact hJ
      · exact ContinuousLinearMap.contDiff (actionCLM Λ⁻¹)

/-!

## B. Gauss's law and Ampère's law and the extrema condition

-/

lemma isExtrema_iff_gauss_ampere_magneticFieldMatrix {d} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
    IsExtrema 𝓕 A J ↔ ∀ t, ∀ x, (∇ ⬝ (A.electricField 𝓕.c t)) x = J.chargeDensity 𝓕.c t x / 𝓕.ε₀
    ∧ ∀ i, 𝓕.μ₀ * 𝓕.ε₀ * ∂ₜ (fun t => A.electricField 𝓕.c t x) t i =
    ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c t · (j, i)) x - 𝓕.μ₀ * J.currentDensity 𝓕.c t x i := by
  rw [isExtrema_iff_gradLagrangian]
  rw [funext_iff]
  conv_lhs =>
    enter [x]
    rw [gradLagrangian_eq_electricField_magneticField (𝓕 := 𝓕) A hA J hJ]
    simp only [Pi.zero_apply]
    rw [Lorentz.Vector.sum_inl_inr_basis_eq_zero_iff]
  simp only [forall_and]
  apply and_congr
  · apply Iff.intro
    · intro h t x
      specialize h ((toTimeAndSpace 𝓕.c).symm (t, x))
      simp at h
      linear_combination (norm := simp) (𝓕.μ₀ * 𝓕.c) * h
      field_simp
      simp only [FreeSpace.c_sq, one_div, mul_inv_rev, mul_zero]
      field_simp
      ring
    · intro h x
      specialize h (x.time 𝓕.c) x.space
      linear_combination (norm := simp) (𝓕.μ₀⁻¹ * 𝓕.c⁻¹) * h
      field_simp
      simp only [FreeSpace.c_sq, one_div, mul_inv_rev, mul_zero]
      field_simp
      ring
  · apply Iff.intro
    · intro h t x i
      specialize h ((toTimeAndSpace 𝓕.c).symm (t, x)) i
      simp at h
      linear_combination (norm := simp) (𝓕.μ₀) * h
      field_simp
      simp
    · intro h x i
      specialize h (x.time 𝓕.c) x.space i
      linear_combination (norm := simp) (𝓕.μ₀⁻¹) * h
      field_simp
      simp

/-!

## C. Time derivatives from the extrema condition

-/

lemma time_deriv_electricField_of_isExtrema {A : ElectromagneticPotential d}
    {𝓕 : FreeSpace}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J)
    (h : IsExtrema 𝓕 A J) (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (A.electricField 𝓕.c · x) t i =
      1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c t · (j, i)) x -
      (1/ 𝓕.ε₀) * J.currentDensity 𝓕.c t x i := by
  rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ] at h
  linear_combination (norm := simp) (𝓕.μ₀ * 𝓕.ε₀)⁻¹ * ((h t x).2 i)
  field_simp
  ring

/-!

## D. Second time derivatives from the extrema condition

-/

/-!

### D.1. Second time derivatives of the magnetic field from the extrema condition

We show that the magnetic field matrix $B_{ij}$ satisfies the following wave-like equation

$$\frac{\partial^2 B_{ij}}{\partial t^2} = c^2 \sum_k \frac{\partial^2 B_{ij}}{\partial x_k^2} +
  \frac{1}{\epsilon_0} \left(\frac{\partial J_i}{\partial x_j} -
  \frac{\partial J_j}{\partial x_i} \right).$$
When the free current density is zero, this reduces to the wave equation.
-/

lemma time_deriv_time_deriv_magneticFieldMatrix_of_isExtrema {A : ElectromagneticPotential d}
    {𝓕 : FreeSpace}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) (h : IsExtrema 𝓕 A J)
    (t : Time) (x : Space d) (i j : Fin d) :
    ∂ₜ (∂ₜ (A.magneticFieldMatrix 𝓕.c · x (i, j))) t =
    𝓕.c ^ 2 * ∑ k, ∂[k] (∂[k] (A.magneticFieldMatrix 𝓕.c t · (i, j))) x +
    𝓕.ε₀⁻¹ * (∂[j] (J.currentDensity 𝓕.c t · i) x - ∂[i] (J.currentDensity 𝓕.c t · j) x) := by
  rw [time_deriv_time_deriv_magneticFieldMatrix A (hA.of_le (ENat.LEInfty.out))]
  conv_lhs =>
    enter [2, 2, x]
    rw [time_deriv_electricField_of_isExtrema hA J hJ h]
  conv_lhs =>
    enter [1, 2, x]
    rw [time_deriv_electricField_of_isExtrema hA J hJ h]
  rw [Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sub (by
        apply Differentiable.const_mul
        apply Differentiable.fun_sum
        intro i _
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)))
          ((LorentzCurrentDensity.currentDensity_apply_differentiable_space
          (hJ.differentiable (by simp)) _ _).const_mul _).differentiableAt,
    fderiv_const_mul (by
        apply Differentiable.fun_sum
        intro i _
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl))),
    fderiv_const_mul (by
        apply (LorentzCurrentDensity.currentDensity_apply_differentiable_space
        (hJ.differentiable (by simp)) _ _).differentiableAt),
    fderiv_fun_sum fun i _ => by
        apply Differentiable.differentiableAt
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl))]
  conv_lhs =>
    enter [2]
    rw [Space.deriv_eq_fderiv_basis]
    rw [fderiv_fun_sub (by
        apply Differentiable.const_mul
        apply Differentiable.fun_sum
        intro i _
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)))
          ((LorentzCurrentDensity.currentDensity_apply_differentiable_space
          (hJ.differentiable (by simp)) _ _).const_mul _).differentiableAt,
    fderiv_const_mul (by
        apply Differentiable.fun_sum
        intro i _
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl))),
    fderiv_const_mul (by
        apply (LorentzCurrentDensity.currentDensity_apply_differentiable_space
        (hJ.differentiable (by simp)) _ _).differentiableAt),
    fderiv_fun_sum fun i _ => by
        apply Differentiable.differentiableAt
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl))]
  simp [← Space.deriv_eq_fderiv_basis, FreeSpace.c_sq]
  field_simp
  conv_rhs =>
    enter [1, 2, k, 2, x]
    rw [magneticFieldMatrix_space_deriv_eq A (hA.of_le (right_eq_inf.mp rfl))]
  conv_rhs =>
    enter [1, 2, k]
    rw [Space.deriv_eq_fderiv_basis]
    rw [fderiv_fun_sub (by
      apply Space.deriv_differentiable
      apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)))
      (by
      apply Space.deriv_differentiable
      apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)))]
    simp [← Space.deriv_eq_fderiv_basis]
    rw [Space.deriv_commute _ (by
      apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)))]
    enter [2]
    rw [Space.deriv_commute _ (by
      apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)))]
  simp only [Finset.sum_sub_distrib]
  ring

/-!

### D.2. Second time derivatives of the electric field from the extrema condition

We show that the electric field $E_i$ satisfies the following wave-like equation:

$$\frac{\partial^2 E_{i}}{\partial t^2} = c^2 \sum_k \frac{\partial^2 E_{i}}{\partial x_k^2} -
  \frac{c ^ 2}{\epsilon_0} \frac{\partial \rho}{\partial x_i} -
  c ^ 2 μ_0 \frac{\partial J_i}{\partial t}.$$

When the free current density and charge density are zero, this reduces to the wave equation.

-/

lemma time_deriv_time_deriv_electricField_of_isExtrema {A : ElectromagneticPotential d}
    {𝓕 : FreeSpace}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) (h : IsExtrema 𝓕 A J)
    (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (∂ₜ (A.electricField 𝓕.c · x i)) t =
      𝓕.c ^ 2 * ∑ j, (∂[j] (∂[j] (A.electricField 𝓕.c t · i)) x) -
      𝓕.c ^ 2 / 𝓕.ε₀ * ∂[i] (J.chargeDensity 𝓕.c t ·) x -
      𝓕.c ^ 2 * 𝓕.μ₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
  calc _
    _= ∂ₜ (fun t =>
      1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, Space.deriv j (fun x => magneticFieldMatrix 𝓕.c A t x (j, i)) x -
      1 / 𝓕.ε₀ * LorentzCurrentDensity.currentDensity 𝓕.c J t x i) t := by
        conv_lhs =>
          enter [1]
          change fun t => ∂ₜ (A.electricField 𝓕.c · x i) t
          enter [t]
          rw [Time.deriv_euclid (electricField_differentiable_time
            (hA.of_le (right_eq_inf.mp rfl)) _),
            time_deriv_electricField_of_isExtrema hA J hJ h]
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∂ₜ (fun t => ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c t · (j, i)) x) t -
      1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
      rw [Time.deriv_eq]
      rw [fderiv_fun_sub]
      simp only [one_div, mul_inv_rev, ContinuousLinearMap.coe_sub', Pi.sub_apply]
      rw [fderiv_const_mul (by
        apply Differentiable.fun_sum
        intro j _
        apply Space.space_deriv_differentiable_time
        apply magneticFieldMatrix_contDiff
        apply hA.of_le (right_eq_inf.mp rfl))]
      rw [fderiv_const_mul (by
        apply Differentiable.differentiableAt
        apply LorentzCurrentDensity.currentDensity_apply_differentiable_time
        exact hJ.differentiable (by simp))]
      simp [Time.deriv_eq]
      · apply Differentiable.const_mul
        apply Differentiable.fun_sum
        intro j _
        apply Space.space_deriv_differentiable_time
        apply magneticFieldMatrix_contDiff
        apply hA.of_le (right_eq_inf.mp rfl)
      · apply DifferentiableAt.const_mul
        apply Differentiable.differentiableAt
        apply LorentzCurrentDensity.currentDensity_apply_differentiable_time
        exact hJ.differentiable (by simp)
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ((∑ j, ∂ₜ (fun t => ∂[j] (A.magneticFieldMatrix 𝓕.c t · (j, i)) x)) t) -
      1 / 𝓕.ε₀ * (∂ₜ (J.currentDensity 𝓕.c · x i) t) := by
      congr
      rw [Time.deriv_eq]
      rw [fderiv_fun_sum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
      rfl
      intro i _
      apply Differentiable.differentiableAt
      apply Space.space_deriv_differentiable_time
      apply magneticFieldMatrix_contDiff
      apply hA.of_le (right_eq_inf.mp rfl)
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * (∑ j, ∂[j] (fun x => ∂ₜ (A.magneticFieldMatrix 𝓕.c · x (j, i)) t)) x -
        1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
      congr
      simp only [Finset.sum_apply]
      congr
      funext k
      rw [Space.time_deriv_comm_space_deriv]
      apply magneticFieldMatrix_contDiff
      apply hA.of_le (right_eq_inf.mp rfl)
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) *(∑ j, ∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x -
        ∂[i] (A.electricField 𝓕.c t · j) x)) x -
        1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        congr
        simp only [Finset.sum_apply]
        congr
        funext k
        congr
        funext x
        rw [time_deriv_magneticFieldMatrix _ (hA.of_le (ENat.LEInfty.out))]
    _ = (1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x) x -
          ∂[j] (fun x => ∂[i] (A.electricField 𝓕.c t · j) x) x)) -
          1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        congr
        simp only [Finset.sum_apply]
        congr
        funext j
        rw [Space.deriv_eq_fderiv_basis]
        rw [fderiv_fun_sub]
        simp [← Space.deriv_eq_fderiv_basis]
        all_goals
        · apply Differentiable.differentiableAt
          apply Space.deriv_differentiable
          apply electricField_apply_contDiff_space
          apply hA.of_le
          exact right_eq_inf.mp rfl
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x) x) -
          1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[i] (A.electricField 𝓕.c t · j) x) x) -
          1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by simp [mul_sub]
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x) x) -
        1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[i] (fun x => ∂[j] (A.electricField 𝓕.c t · j) x) x) -
        1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        congr
        funext j
        rw [Space.deriv_commute _ (by
          apply electricField_apply_contDiff_space
          apply hA.of_le
          exact right_eq_inf.mp rfl), Space.deriv_eq_fderiv_basis]
      _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x) x) -
          1 / (𝓕.μ₀ * 𝓕.ε₀) * (∂[i] (fun x => ∑ j, ∂[j] (A.electricField 𝓕.c t · j) x) x) -
          1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        congr
        rw [Space.deriv_eq_fderiv_basis]
        rw [fderiv_fun_sum]
        simp [← Space.deriv_eq_fderiv_basis]
        intro i _
        apply Differentiable.differentiableAt
        apply Space.deriv_differentiable
        apply electricField_apply_contDiff_space
        apply hA.of_le
        exact right_eq_inf.mp rfl
      _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x) x) -
          1 / (𝓕.μ₀ * 𝓕.ε₀) * (∂[i] (fun x => (∇ ⬝ (A.electricField 𝓕.c t)) x) x) -
          1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        rfl
      _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (∂[j] (A.electricField 𝓕.c t · i)) x) -
          1 / (𝓕.μ₀ * 𝓕.ε₀ ^ 2) * ∂[i] (J.chargeDensity 𝓕.c t ·) x -
          1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        congr 2
        rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix] at h

        conv_lhs =>
          enter [2, 2, x]
          rw [(h t x).1]
        trans 1 / (𝓕.μ₀ * 𝓕.ε₀) * Space.deriv i
            (fun x => (1/ 𝓕.ε₀) * LorentzCurrentDensity.chargeDensity 𝓕.c J t x) x
        · congr
          funext x
          ring
        · rw [Space.deriv_eq_fderiv_basis]
          rw [fderiv_const_mul]
          simp [← Space.deriv_eq_fderiv_basis]
          field_simp
          apply Differentiable.differentiableAt
          apply LorentzCurrentDensity.chargeDensity_differentiable_space
          exact hJ.differentiable (by simp)
        · exact hA
        · exact hJ
      _ = 𝓕.c ^ 2 * ∑ j, (∂[j] (∂[j] (A.electricField 𝓕.c t · i)) x) -
            𝓕.c ^ 2 / 𝓕.ε₀ * ∂[i] (J.chargeDensity 𝓕.c t ·) x -
            𝓕.c ^ 2 * 𝓕.μ₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
          simp [FreeSpace.c_sq]
          field_simp

end ElectromagneticPotential

/-!

## E. Is Extema condition in the distributional case

The above results looked at the extrema condition for electromagnetic potentials that are
functions. We now look at the case where the electromagnetic potential is a distribution.

-/

namespace DistElectromagneticPotential

/-- The proposition on an electromagnetic potential, corresponding to the statement that
  it is an extrema of the lagrangian. -/
def IsExtrema {d} (𝓕 : FreeSpace)
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) : Prop := A.gradLagrangian 𝓕 J = 0

lemma isExtrema_iff_gradLagrangian {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔ A.gradLagrangian 𝓕 J = 0 := by rfl

lemma isExtrema_iff_components {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔ (∀ ε, A.gradLagrangian 𝓕 J ε (Sum.inl 0) = 0)
    ∧ (∀ ε i, A.gradLagrangian 𝓕 J ε (Sum.inr i) = 0) := by
  apply Iff.intro
  · intro h
    rw [isExtrema_iff_gradLagrangian] at h
    simp [h]
  · intro h
    rw [isExtrema_iff_gradLagrangian]
    ext ε
    funext i
    match i with
    | Sum.inl 0 => exact h.1 ε
    | Sum.inr j => exact h.2 ε j
/-!

### E.1. IsExtrema and Gauss's law and Ampère's law

We show that `A` is an extrema of the lagrangian if and only if Gauss's law and Ampère's law hold.
In other words,

$$\nabla \cdot \mathbf{E} = \frac{\rho}{\varepsilon_0}$$
and
$$\mu_0 \varepsilon_0 \frac{\partial \mathbf{E}_i}{\partial t} -
  \sum_j \partial_j \mathbf{B}_{j i} + \mu_0 \mathbf{J}_i = 0.$$
Here $\mathbf{B}$ is the magnetic field matrix.

-/
open Space
lemma isExtrema_iff_space_time {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔
      (∀ ε, distSpaceDiv (A.electricField 𝓕.c) ε = (1/𝓕.ε₀) * (J.chargeDensity 𝓕.c) ε) ∧
      (∀ ε i, 𝓕.μ₀ * 𝓕.ε₀ * (Space.distTimeDeriv (A.electricField 𝓕.c)) ε i -
      ∑ j, ((PiLp.basisFun 2 ℝ (Fin d)).tensorProduct (PiLp.basisFun 2 ℝ (Fin d))).repr
        ((Space.distSpaceDeriv j (A.magneticFieldMatrix 𝓕.c)) ε) (j, i) +
      𝓕.μ₀ * J.currentDensity 𝓕.c ε i = 0) := by
  rw [isExtrema_iff_components]
  refine and_congr ?_ ?_
  · simp [gradLagrangian_sum_inl_0]
    field_simp
    simp [𝓕.c_sq]
    field_simp
    simp [sub_eq_zero]
    apply Iff.intro
    · intro h ε
      convert h (SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℝ) ℝ
        (SpaceTime.toTimeAndSpace 𝓕.c (d := d)) ε) using 1
      · simp [SpaceTime.distTimeSlice_symm_apply]
        ring_nf
        congr
        ext x
        simp
      · simp [SpaceTime.distTimeSlice_symm_apply]
        congr
        ext x
        simp
    · intro h ε
      convert h (SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℝ) ℝ
        (SpaceTime.toTimeAndSpace 𝓕.c (d := d)).symm ε) using 1
      · simp [SpaceTime.distTimeSlice_symm_apply]
        ring_nf
  · apply Iff.intro
    · intro h ε i
      specialize h (SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℝ) ℝ
        (SpaceTime.toTimeAndSpace 𝓕.c (d := d)) ε) i
      linear_combination (norm := field_simp) (𝓕.μ₀) * h
      simp [gradLagrangian_sum_inr_i, SpaceTime.distTimeSlice_symm_apply]
      have hx : (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (SpaceTime.toTimeAndSpace 𝓕.c).symm)
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (SpaceTime.toTimeAndSpace 𝓕.c)) ε)
          = ε := by
        ext i
        simp
      simp [hx, 𝓕.c_sq]
      field_simp
      ring
    · intro h ε i
      specialize h (SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℝ) ℝ
        (SpaceTime.toTimeAndSpace 𝓕.c (d := d)).symm ε) i
      linear_combination (norm := field_simp) (𝓕.μ₀⁻¹) * h
      simp [gradLagrangian_sum_inr_i, SpaceTime.distTimeSlice_symm_apply, 𝓕.c_sq]
      field_simp
      ring

/-!

### E.2. IsExtrema in terms of Vector Potentials

We show that `A` is an extrema of the lagrangian if and only if Gauss's law and Ampère's law hold.
In other words,

$$\nabla \cdot \mathbf{E} = \frac{\rho}{\varepsilon_0}$$
and
$$\mu_0 \varepsilon_0 \frac{\partial \mathbf{E}_i}{\partial t} -
  \sum_j -(\partial_j \partial_j \vec A_i - \partial_j \partial_i \vec A_j) +
  \mu_0 \mathbf{J}_i = 0.$$

-/

lemma isExtrema_iff_vectorPotential {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔
      (∀ ε, distSpaceDiv (A.electricField 𝓕.c) ε = (1/𝓕.ε₀) * (J.chargeDensity 𝓕.c) ε) ∧
      (∀ ε i, 𝓕.μ₀ * 𝓕.ε₀ * distTimeDeriv (A.electricField 𝓕.c) ε i -
      (∑ x, -(distSpaceDeriv x (distSpaceDeriv x (A.vectorPotential 𝓕.c)) ε i
        - distSpaceDeriv x (distSpaceDeriv i (A.vectorPotential 𝓕.c)) ε x)) +
      𝓕.μ₀ * J.currentDensity 𝓕.c ε i = 0) := by
  rw [isExtrema_iff_space_time]
  refine and_congr (by rfl) ?_
  suffices ∀ ε i, ∑ x, -(distSpaceDeriv x (distSpaceDeriv x (A.vectorPotential 𝓕.c)) ε i
        - distSpaceDeriv x (distSpaceDeriv i (A.vectorPotential 𝓕.c)) ε x) =
        ∑ j, ((PiLp.basisFun 2 ℝ (Fin d)).tensorProduct (PiLp.basisFun 2 ℝ (Fin d))).repr
          ((Space.distSpaceDeriv j (A.magneticFieldMatrix 𝓕.c)) ε) (j, i) by
    conv_lhs => enter [2, 2]; rw [← this]
  intro ε i
  congr
  funext j
  rw [magneticFieldMatrix_distSpaceDeriv_basis_repr_eq_vector_potential]
  ring

/-!

### E.3. The exterma condition in terms of tensors

We show that `A` is an extrema of the lagrangian if and only if the equation
$$\frac{1}{\mu_0} \partial_\kappa F^{\kappa \nu'} - J^{\nu'} = 0,$$
holds.

-/
open SpaceTime minkowskiMatrix
lemma isExterma_iff_tensor {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔ ∀ ε,
    {((1/ 𝓕.μ₀ : ℝ) • distTensorDeriv A.fieldStrength ε | κ κ ν') + - (J ε | ν')}ᵀ = 0 := by
  apply Iff.intro
  · intro h
    simp only [IsExtrema] at h
    intro x
    have h1 : ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
        (permT id (PermCond.auto) {((1/ 𝓕.μ₀ : ℝ) • distTensorDeriv A.fieldStrength x | κ κ ν') +
        - (J x | ν')}ᵀ)) = 0 := by
      funext ν
      have h2 : gradLagrangian 𝓕 A J x ν = 0 := by simp [h]
      rw [gradLagrangian_eq_tensor A J] at h2
      simp at h2
      have hn : minkowskiMatrix ν ν ≠ 0 := minkowskiMatrix.η_diag_ne_zero
      simp_all
    rw [EmbeddingLike.map_eq_zero_iff, permT_eq_zero_iff] at h1
    exact h1
  · intro h
    simp only [IsExtrema]
    ext x
    funext ν
    rw [gradLagrangian_eq_tensor A J, h]
    simp

/-!

### E.4. The invariance of the exterma condition under Lorentz transformations

We show that the Exterma condition is invariant under Lorentz transformations.
This implies that if an electromagnetic potential is an extrema in one inertial frame,
it is also an extrema in any other inertial frame.
In otherwords that the Maxwell's equations are Lorentz invariant.
A natural consequence of this is that the speed of light is the same in all inertial frames.

-/

lemma isExterma_equivariant {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) (Λ : LorentzGroup d) :
    IsExtrema 𝓕 (Λ • A) (Λ • J) ↔ IsExtrema 𝓕 A J := by
  rw [isExterma_iff_tensor]
  conv_lhs =>
    enter [x, 1, 1, 2, 2, 2]
    rw [fieldStrength_equivariant, distTensorDeriv_equivariant]
    rw [lorentzGroup_smul_dist_apply]
  conv_lhs =>
    enter [x]
    rw [smul_comm]
    rw [Tensorial.toTensor_smul, lorentzGroup_smul_dist_apply, Tensorial.toTensor_smul]
    simp only [Nat.reduceAdd, Nat.reduceSucc, Fin.isValue, one_div, map_smul, actionT_smul,
      contrT_equivariant, map_neg, permT_equivariant]
    rw [smul_comm, ← Tensor.actionT_neg, ← Tensor.actionT_add]
  apply Iff.intro
  · intro h
    rw [isExterma_iff_tensor A J]
    intro x
    apply MulAction.injective Λ
    simp only [Nat.reduceAdd, Nat.reduceSucc, Fin.isValue, one_div, map_smul, map_neg,
      _root_.smul_add, actionT_smul, _root_.smul_neg, _root_.smul_zero]
    simpa [schwartzAction_mul_apply] using h (schwartzAction Λ x)
  · intro h x
    rw [isExterma_iff_tensor A J] at h
    specialize h (schwartzAction Λ⁻¹ x)
    simp at h
    rw [h]
    simp

end DistElectromagneticPotential
end Electromagnetism
