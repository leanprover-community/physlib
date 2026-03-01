/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Kinematics.MagneticField
import PhysLean.Electromagnetism.Dynamics.Basic
/-!

# The kinetic term

## i. Overview

The kinetic term of the electromagnetic field is `- 1/(4 μ₀) F_μν F^μν`.
We define this, show it is invariant under Lorentz transformations,
and show properties of its variational gradient.

In particular the variational gradient `gradKineticTerm` of the kinetic term
is directly related to Gauss's law and the Ampere law.

In this implementation we have set `μ₀ = 1`. It is a TODO to introduce this constant.

## ii. Key results

- `ElectromagneticPotential.kineticTerm` is the kinetic term of an electromagnetic potential.
- `ElectromagneticPotential.kineticTerm_equivariant` shows that the kinetic term is
  Lorentz invariant.
- `ElectromagneticPotential.gradKineticTerm` is the variational gradient of the kinetic term.
- `ElectromagneticPotential.gradKineticTerm_eq_electric_magnetic` gives a first expression for the
  variational gradient in terms of the electric and magnetic fields.
- `DistElectromagneticPotential.gradKineticTerm` is the variational gradient of the kinetic term
  for distributional electromagnetic potentials.

## iii. Table of contents

- A. The kinetic term
  - A.1. Lorentz invariance of the kinetic term
  - A.2. Kinetic term simplified expressions
  - A.3. The kinetic term in terms of the electric and magnetic fields
  - A.4. The kinetic term in terms of the electric and magnetic matrix
  - A.5. The kinetic term for constant fields
  - A.6. Smoothness of the kinetic term
  - A.7. The kinetic term shifted by time mul a constant
- B. Variational gradient of the kinetic term
  - B.1. Variational gradient in terms of fderiv
  - B.2. Writing the variational gradient as a sums over double derivatives of the potential
  - B.3. Variational gradient as a sums over fieldStrengthMatrix
  - B.4. Variational gradient in terms of the Gauss's and Ampère laws
  - B.5. Linearity properties of the variational gradient
  - B.6. HasVarGradientAt for the variational gradient
  - B.7. Gradient of the kinetic term in terms of the tensor derivative
- C. The gradient of the kinetic term for distributions
  - C.1. The gradient of the kinetic term as a tensor

## iv. References

- https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html

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
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. The kinetic term

The kinetic term is `- 1/(4 μ₀) F_μν F^μν`. We define this and show that it is
Lorentz invariant.

-/

/-- The kinetic energy from an electromagnetic potential. -/
noncomputable def kineticTerm {d} (𝓕 : FreeSpace) (A : ElectromagneticPotential d) :
    SpaceTime d → ℝ := fun x =>
  - 1/(4 * 𝓕.μ₀) * {η' d | μ μ' ⊗ η' d | ν ν' ⊗
    A.toFieldStrength x | μ ν ⊗ A.toFieldStrength x | μ' ν'}ᵀ.toField

/-!

### A.1. Lorentz invariance of the kinetic term

We show that the kinetic energy is Lorentz invariant.

-/

lemma kineticTerm_equivariant {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (Λ : LorentzGroup d)
    (hf : Differentiable ℝ A) (x : SpaceTime d) :
    kineticTerm 𝓕 (fun x => Λ • A (Λ⁻¹ • x)) x = kineticTerm 𝓕 A (Λ⁻¹ • x) := by
  rw [kineticTerm, kineticTerm]
  conv_lhs =>
    enter [2]
    rw [toFieldStrength_equivariant A Λ hf, Tensorial.toTensor_smul]
    rw [← actionT_coMetric Λ, Tensorial.toTensor_smul]
    simp only [prodT_equivariant, contrT_equivariant, toField_equivariant]

/-!

### A.2. Kinetic term simplified expressions

-/

lemma kineticTerm_eq_sum {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    A.kineticTerm 𝓕 x =
    - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν, ∑ μ', ∑ ν', η μ μ' * η ν ν' *
      (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x) (μ, ν)
      * (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr
        (A.toFieldStrength x) (μ', ν') := by
  rw [kineticTerm]
  rw [toField_eq_repr]
  rw [contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [2, 2, μ]
    rw [contrT_basis_repr_apply_eq_fin]
    enter [2, ν]
    rw [prodT_basis_repr_apply]
    enter [1]
    rw [contrT_basis_repr_apply_eq_fin]
    enter [2, μ']
    rw [contrT_basis_repr_apply_eq_fin]
    enter [2, ν']
    rw [prodT_basis_repr_apply]
    enter [1]
    rw [prodT_basis_repr_apply]
    enter [1]
    erw [coMetric_repr_apply_eq_minkowskiMatrix]
    change η (finSumFinEquiv.symm μ') (finSumFinEquiv.symm μ)
  conv_lhs =>
    enter [2, 2, μ, 2, ν, 1, 2, μ', 2, ν', 1, 2]
    erw [coMetric_repr_apply_eq_minkowskiMatrix]
    change η (finSumFinEquiv.symm ν') (finSumFinEquiv.symm ν)
  conv_lhs =>
    enter [2, 2, μ, 2, ν, 1, 2, μ', 2, ν', 2]
    rw [toFieldStrength_tensor_basis_eq_basis]
    change ((Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x))
      (finSumFinEquiv.symm μ', finSumFinEquiv.symm ν')
  conv_lhs =>
    enter [2, 2, μ, 2, ν, 2]
    rw [toFieldStrength_tensor_basis_eq_basis]
    change ((Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x))
      (finSumFinEquiv.symm μ, finSumFinEquiv.symm ν)
  rw [← finSumFinEquiv.sum_comp]
  conv_lhs =>
    enter [2, 2, μ]
    rw [← finSumFinEquiv.sum_comp]
    enter [2, ν]
    rw [← finSumFinEquiv.sum_comp]
    rw [Finset.sum_mul]
    enter [2, μ']
    rw [← finSumFinEquiv.sum_comp]
    rw [Finset.sum_mul]
    enter [2, ν']
    simp
  conv_lhs => enter [2, 2, μ]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, 2, μ', 2, ν]; rw [Finset.sum_comm]
  conv_lhs => enter [2, 2, μ']; rw [Finset.sum_comm]
  rfl

lemma kineticTerm_eq_sum_fieldStrengthMatrix {d} {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (x : SpaceTime d) : A.kineticTerm 𝓕 x =
    - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν, ∑ μ', ∑ ν', η μ μ' * η ν ν' *
      A.fieldStrengthMatrix x (μ, ν) * A.fieldStrengthMatrix x (μ', ν') := by
  rw [kineticTerm_eq_sum]

lemma kineticTerm_eq_sum_fieldStrengthMatrix_sq {d} {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (x : SpaceTime d) : A.kineticTerm 𝓕 x =
    - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν, η μ μ * η ν ν * ‖A.fieldStrengthMatrix x (μ, ν)‖ ^ 2 := by
  rw [kineticTerm_eq_sum_fieldStrengthMatrix]
  congr
  funext μ
  congr
  funext ν
  rw [Finset.sum_eq_single μ]
  · rw [Finset.sum_eq_single ν]
    · simp
      ring
    · intro b _ hb
      nth_rewrite 2 [minkowskiMatrix.off_diag_zero]
      simp only [mul_zero, zero_mul]
      exact id (Ne.symm hb)
    · simp
  · intro b _ hb
    rw [Finset.sum_eq_zero]
    intro ν' _
    rw [minkowskiMatrix.off_diag_zero]
    simp only [zero_mul]
    exact id (Ne.symm hb)
  · simp

lemma kineticTerm_eq_sum_potential {d} {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (x : SpaceTime d) :
    A.kineticTerm 𝓕 x = - 1 / (2 * 𝓕.μ₀) * ∑ μ, ∑ ν,
        (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) := by
  calc _
    _ = - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν, ∑ μ', ∑ ν', η μ μ' * η ν ν' *
      (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ)
      * (η μ' μ' * ∂_ μ' A x ν' - η ν' ν' * ∂_ ν' A x μ') := by
      rw [kineticTerm_eq_sum]
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      apply Finset.sum_congr rfl (fun μ' _ => ?_)
      apply Finset.sum_congr rfl (fun ν' _ => ?_)
      rw [toFieldStrength_basis_repr_apply_eq_single, toFieldStrength_basis_repr_apply_eq_single]
    _ = - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν, ∑ μ', η μ μ' * η ν ν *
        (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ)
        * (η μ' μ' * ∂_ μ' A x ν - η ν ν * ∂_ ν A x μ') := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      apply Finset.sum_congr rfl (fun μ' _ => ?_)
      rw [Finset.sum_eq_single ν]
      · intro b _ hb
        nth_rewrite 2 [minkowskiMatrix.off_diag_zero]
        simp only [mul_zero, zero_mul]
        exact id (Ne.symm hb)
      · simp
    _ = - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν, η μ μ * η ν ν *
        (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ)
        * (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ) := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      rw [Finset.sum_eq_single μ]
      · intro b _ hb
        rw [minkowskiMatrix.off_diag_zero]
        simp only [zero_mul]
        exact id (Ne.symm hb)
      · simp
    _ = - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν,
        ((η μ μ) ^ 2 * η ν ν * ∂_ μ A x ν - (η ν ν) ^ 2 * η μ μ * ∂_ ν A x μ)
        * (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ) := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    _ = - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν,
        (η ν ν * ∂_ μ A x ν - η μ μ * ∂_ ν A x μ)
        * (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ) := by simp
    _ = - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν,
        ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - (η ν ν) ^ 2 * ∂_ μ A x ν * ∂_ ν A x μ) + (-
        (η μ μ) ^ 2 * ∂_ ν A x μ * ∂_ μ A x ν + η μ μ * η ν ν * (∂_ ν A x μ)^2)) := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    _ = - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν,
        ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) +
        (- ∂_ ν A x μ * ∂_ μ A x ν + η μ μ * η ν ν * (∂_ ν A x μ)^2)) := by simp
    _ = - 1 / (4 * 𝓕.μ₀) * ∑ μ, ∑ ν,
        ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) +
        (- ∂_ μ A x ν * ∂_ ν A x μ + η ν ν * η μ μ * (∂_ μ A x ν)^2)) := by
      congr 1
      conv_lhs =>
        enter [2, μ];
        rw [Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib]
      conv_lhs => enter [2]; rw [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      conv_lhs =>
        enter [2, μ];
        rw [← Finset.sum_add_distrib]
    _ = - 1 / (4 * 𝓕.μ₀) * ∑ μ, ∑ ν,
        (2 * (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ)) := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    _ = - 1 / (2 * 𝓕.μ₀) * ∑ μ, ∑ ν,
        (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) := by
      conv_lhs =>
        enter [2, 2, μ]
        rw [← Finset.mul_sum]
      rw [← Finset.mul_sum]
      ring

/-!

### A.3. The kinetic term in terms of the electric and magnetic fields

-/
open InnerProductSpace

lemma kineticTerm_eq_electric_magnetic {𝓕 : FreeSpace} (A : ElectromagneticPotential) (t : Time)
    (x : Space) (hA : Differentiable ℝ A) :
    A.kineticTerm 𝓕 ((toTimeAndSpace 𝓕.c).symm (t, x)) =
    1/2 * (𝓕.ε₀ * ‖A.electricField 𝓕.c t x‖ ^ 2 - (1 / 𝓕.μ₀) * ‖A.magneticField 𝓕.c t x‖ ^ 2) := by
  rw [kineticTerm_eq_sum]
  simp only [one_div]
  conv_lhs =>
    enter [2, 2, μ, 2, ν, 2, μ', 2, ν']
    rw [fieldStrengthMatrix_eq_electric_magnetic A t x hA,
      fieldStrengthMatrix_eq_electric_magnetic A t x hA]
  simp [Fintype.sum_sum_type, Fin.sum_univ_three]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]
  field_simp
  simp only [Fin.isValue, FreeSpace.c_sq, one_div, mul_inv_rev]
  field_simp
  ring

lemma kineticTerm_eq_electric_magnetic' {𝓕 : FreeSpace} {A : ElectromagneticPotential}
    (hA : Differentiable ℝ A) (x : SpaceTime) :
    A.kineticTerm 𝓕 x =
    1/2 * (𝓕.ε₀ * ‖A.electricField 𝓕.c (x.time 𝓕.c) x.space‖ ^ 2 -
      (1 / 𝓕.μ₀) * ‖A.magneticField 𝓕.c (x.time 𝓕.c) x.space‖ ^ 2) := by
  rw [← kineticTerm_eq_electric_magnetic _ _ _ hA]
  congr
  apply toTimeAndSpace.injective
  simp

/-!

### A.4. The kinetic term in terms of the electric and magnetic matrix

-/

lemma kineticTerm_eq_electricMatrix_magneticFieldMatrix_time_space {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (t : Time)
    (x : Space d) (hA : Differentiable ℝ A) :
    A.kineticTerm 𝓕 ((toTimeAndSpace 𝓕.c).symm (t, x)) =
    1/2 * (𝓕.ε₀ * ‖A.electricField 𝓕.c t x‖ ^ 2 -
    (1 / (2 * 𝓕.μ₀)) * ∑ i, ∑ j, ‖A.magneticFieldMatrix 𝓕.c t x (i, j)‖ ^ 2) := by
  rw [kineticTerm_eq_sum_fieldStrengthMatrix_sq]
  simp [Fintype.sum_sum_type]
  rw [Finset.sum_add_distrib]
  simp only [Fin.isValue, Finset.sum_neg_distrib]
  have h1 : ∑ i, ∑ j, magneticFieldMatrix 𝓕.c A t x (i, j) ^ 2
      = ∑ i, ∑ j, (A.fieldStrengthMatrix ((toTimeAndSpace 𝓕.c).symm (t, x)))
        (Sum.inr i, Sum.inr j) ^ 2 := by rfl
  rw [h1]
  ring_nf
  have h2 : ‖electricField 𝓕.c A t x‖ ^ 2 = 𝓕.c.val ^ 2 *
      ∑ i, |(A.fieldStrengthMatrix ((toTimeAndSpace 𝓕.c).symm (t, x)))
      (Sum.inl 0, Sum.inr i)| ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    conv_lhs =>
      enter [2, i]
      rw [electricField_eq_fieldStrengthMatrix A t x i hA]
      simp only [Fin.isValue, neg_mul, norm_neg, norm_mul, Real.norm_eq_abs, FreeSpace.c_abs]
      rw [mul_pow]
    rw [← Finset.mul_sum]
  rw [h2]
  simp only [Fin.isValue, one_div, sq_abs]
  conv_lhs =>
    enter [1, 2, 1, 2, 2, i]
    rw [fieldStrengthMatrix_antisymm]
  simp [FreeSpace.c_sq]
  field_simp
  ring

lemma kineticTerm_eq_electricMatrix_magneticFieldMatrix {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (x : SpaceTime d)
    (hA : Differentiable ℝ A) :
    A.kineticTerm 𝓕 x =
    1/2 * (𝓕.ε₀ * ‖A.electricField 𝓕.c (x.time 𝓕.c) x.space‖ ^ 2 -
    (1 / (2 * 𝓕.μ₀)) * ∑ i, ∑ j, ‖A.magneticFieldMatrix 𝓕.c (x.time 𝓕.c) x.space (i, j)‖ ^ 2) := by
  rw [← kineticTerm_eq_electricMatrix_magneticFieldMatrix_time_space A (x.time 𝓕.c)]
  simp only [toTimeAndSpace_symm_apply_time_space]
  exact hA

/-!

### A.5. The kinetic term for constant fields

-/

lemma kineticTerm_const {d} {𝓕 : FreeSpace} (A₀ : Lorentz.Vector d) :
    kineticTerm 𝓕 (fun _ : SpaceTime d => A₀) = 0 := by
  funext x
  rw [kineticTerm_eq_sum_potential]
  conv_lhs =>
    enter [2, 2, μ, 2, ν]
    repeat rw [SpaceTime.deriv_eq]
    simp
  simp

lemma kineticTerm_add_const {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (A₀ : Lorentz.Vector d) :
    kineticTerm 𝓕 (fun x => A x + A₀) = kineticTerm 𝓕 A := by
  funext x
  rw [kineticTerm_eq_sum_potential, kineticTerm_eq_sum_potential]
  congr
  funext μ
  congr
  funext ν
  congr
  all_goals
  · rw [SpaceTime.deriv_eq]
    simp
    rfl

/-!

### A.6. Smoothness of the kinetic term

-/

lemma kineticTerm_contDiff {d} {n : WithTop ℕ∞} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ (n + 1) A) :
    ContDiff ℝ n (A.kineticTerm 𝓕) := by
  change ContDiff ℝ n (fun x => A.kineticTerm 𝓕 x)
  conv =>
    enter [3, x]
    rw [kineticTerm_eq_sum_fieldStrengthMatrix]
  apply ContDiff.mul
  · fun_prop
  apply ContDiff.sum
  intro μ _
  apply ContDiff.sum
  intro ν _
  apply ContDiff.sum
  intro μ' _
  apply ContDiff.sum
  intro ν' _
  apply ContDiff.mul
  · apply ContDiff.mul
    · fun_prop
    exact fieldStrengthMatrix_contDiff hA
  exact fieldStrengthMatrix_contDiff hA

/-!

### A.7. The kinetic term shifted by time mul a constant

This result is used in finding the canonical momentum.
-/

lemma kineticTerm_add_time_mul_const {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (ha : Differentiable ℝ A)
    (c : Lorentz.Vector d) (x : SpaceTime d) :
    kineticTerm 𝓕 (fun x => A x + x (Sum.inl 0) • c) x = A.kineticTerm 𝓕 x +
        (-1 / (2 * 𝓕.μ₀) * ∑ ν, ((2 * c ν * η ν ν * ∂_ (Sum.inl 0) A x ν + η ν ν * c ν ^ 2 -
        2 * c ν * (∂_ ν A x (Sum.inl 0)))) + 1/(2 * 𝓕.μ₀) * c (Sum.inl 0) ^2) := by
  have diff_a : ∂_ (Sum.inl 0) (fun x => A x + x (Sum.inl 0) • c) =
      ∂_ (Sum.inl 0) A + (fun x => c) := by
    funext x ν
    rw [SpaceTime.deriv_eq]

    rw [fderiv_fun_add _ (by fun_prop)]
    simp only [Fin.isValue, ContinuousLinearMap.add_apply, Lorentz.Vector.apply_add, Pi.add_apply]
    congr
    rw [fderiv_smul_const (by fun_prop)]
    simp [Lorentz.Vector.coordCLM]
    exact ha.differentiableAt
  have diff_b (i : Fin d) : ∂_ (Sum.inr i) (fun x => A x + x (Sum.inl 0) • c) =
      ∂_ (Sum.inr i) A := by
    funext x ν
    rw [SpaceTime.deriv_eq]
    rw [fderiv_fun_add _ (by fun_prop)]
    simp only [Fin.isValue, ContinuousLinearMap.add_apply, Lorentz.Vector.apply_add]
    rw [fderiv_smul_const (by fun_prop)]
    simp only [Fin.isValue, ContinuousLinearMap.smulRight_apply,
      Lorentz.Vector.apply_smul]
    rw [← SpaceTime.deriv_eq]
    simp [Lorentz.Vector.coordCLM]
    exact ha.differentiableAt
  have hdiff (μ : Fin 1 ⊕ Fin d) :
      ∂_ μ (fun x => A x + x (Sum.inl 0) • c) x =
      ∂_ μ A x + if μ = Sum.inl 0 then c else 0 := by
    match μ with
    | Sum.inl 0 => simp [diff_a]
    | Sum.inr i => simp [diff_b i]
  rw [kineticTerm_eq_sum_potential]
  calc _
    _ = -1 / (2 * 𝓕.μ₀) *
    ∑ μ, ∑ ν, (η μ μ * η ν ν * (∂_ μ A x + if μ = Sum.inl 0 then c else 0) ν ^ 2 -
          (∂_ μ A x + if μ = Sum.inl 0 then c else 0) ν *
          (∂_ ν A x + if ν = Sum.inl 0 then c else 0) μ) := by
      congr
      funext μ
      congr
      funext ν
      rw [hdiff μ, hdiff ν]
    _ = -1 / (2 * 𝓕.μ₀) *
      ∑ μ, ∑ ν, (η μ μ * η ν ν * (∂_ μ A x ν + if μ = Sum.inl 0 then c ν else 0) ^ 2 -
          (∂_ μ A x ν + if μ = Sum.inl 0 then c ν else 0) *
          (∂_ ν A x μ + if ν = Sum.inl 0 then c μ else 0)) := by
      congr
      funext μ
      congr
      funext ν
      congr
      all_goals
      · simp
        split_ifs
        simp
        rfl
    _ = -1 / (2 * 𝓕.μ₀) *
      ∑ μ, ∑ ν, ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) +
          (if μ = Sum.inl 0 then c ν else 0) * (2 * η μ μ * η ν ν * ∂_ μ A x ν +
          η μ μ * η ν ν * (if μ = Sum.inl 0 then c ν else 0) -
          (∂_ ν A x μ) - (if ν = Sum.inl 0 then c μ else 0))
          - (∂_ μ A x ν) * (if ν = Sum.inl 0 then c μ else 0)) := by
      congr
      funext μ
      congr
      funext ν
      ring
    _ = -1 / (2 * 𝓕.μ₀) *
        ∑ μ, ∑ ν, ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ)) +
        -1 / (2 * 𝓕.μ₀) * ∑ μ, ∑ ν, ((if μ = Sum.inl 0 then c ν else 0) *
        (2 * η μ μ * η ν ν * ∂_ μ A x ν +
          η μ μ * η ν ν * (if μ = Sum.inl 0 then c ν else 0) -
          (∂_ ν A x μ) - (if ν = Sum.inl 0 then c μ else 0))
          - (∂_ μ A x ν) * (if ν = Sum.inl 0 then c μ else 0)) := by
      rw [← mul_add]
      rw [← Finset.sum_add_distrib]
      congr
      funext μ
      rw [← Finset.sum_add_distrib]
      congr
      ring_nf
    _ = A.kineticTerm 𝓕 x +
        -1 / (2 * 𝓕.μ₀) * ∑ μ, ∑ ν, ((if μ = Sum.inl 0 then c ν else 0) *
        (2 * η μ μ * η ν ν * ∂_ μ A x ν +
        η μ μ * η ν ν * (if μ = Sum.inl 0 then c ν else 0) -
        (∂_ ν A x μ) - (if ν = Sum.inl 0 then c μ else 0))
        - (∂_ μ A x ν) * (if ν = Sum.inl 0 then c μ else 0)) := by
      rw [kineticTerm_eq_sum_potential]
    _ = A.kineticTerm 𝓕 x +
        -1 / (2 * 𝓕.μ₀)* ∑ μ, ∑ ν, ((if μ = Sum.inl 0 then c ν else 0) *
        (2 * η μ μ * η ν ν * ∂_ μ A x ν +
        η μ μ * η ν ν * (if μ = Sum.inl 0 then c ν else 0) -
        (∂_ ν A x μ) - (if ν = Sum.inl 0 then c μ else 0))
        - (∂_ ν A x μ) * (if μ = Sum.inl 0 then c ν else 0)) := by
      congr 1
      conv_rhs =>
        enter [2, 2, μ]
        rw [Finset.sum_sub_distrib]
      conv_rhs =>
        rw [Finset.sum_sub_distrib]
        enter [2, 2]
        rw [Finset.sum_comm]
      rw [← Finset.sum_sub_distrib]
      conv_rhs =>
        enter [2, 2, μ]
        rw [← Finset.sum_sub_distrib]
    _ = A.kineticTerm 𝓕 x +
        -1 / (2 * 𝓕.μ₀) * ∑ ν, (c ν * (2 * η ν ν * ∂_ (Sum.inl 0) A x ν + η ν ν * c ν -
        (∂_ ν A x (Sum.inl 0)) - (if ν = Sum.inl 0 then c (Sum.inl 0) else 0))
        - (∂_ ν A x (Sum.inl 0)) * c ν) := by
      congr 1
      simp
    _ = A.kineticTerm 𝓕 x +
        -1 / (2 * 𝓕.μ₀) * ∑ ν, ((2 * c ν * η ν ν * ∂_ (Sum.inl 0) A x ν + η ν ν * c ν ^ 2 -
        2 * c ν * (∂_ ν A x (Sum.inl 0))) - c ν *
        (if ν = Sum.inl 0 then c (Sum.inl 0) else 0)) := by
      congr
      funext ν
      ring
    _ = A.kineticTerm 𝓕 x +
        (-1 / (2 * 𝓕.μ₀) * ∑ ν, ((2 * c ν * η ν ν * ∂_ (Sum.inl 0) A x ν + η ν ν * c ν ^ 2 -
        2 * c ν * (∂_ ν A x (Sum.inl 0)))) + 1/(2 * 𝓕.μ₀) * c (Sum.inl 0) ^2) := by
          simp only [Fin.isValue, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
            Finset.mem_univ, ↓reduceIte, one_div, add_right_inj]
          ring

/-!

## B. Variational gradient of the kinetic term

We define the variational gradient of the kinetic term, which is the left-hand side
of Gauss's law and Ampère's law in vacuum.

-/

/-- The variational gradient of the kinetic term of an electromagnetic potential. -/
noncomputable def gradKineticTerm {d} (𝓕 : FreeSpace) (A : ElectromagneticPotential d) :
    SpaceTime d → Lorentz.Vector d :=
  (δ (q':=A), ∫ x, kineticTerm 𝓕 q' x)

/-!

### B.1. Variational gradient in terms of fderiv

We give a first simplification of the variational gradient in terms of the
a complicated expression involving `fderiv`. This is not very useful in itself,
but acts as a starting point for further simplifications.

-/
lemma gradKineticTerm_eq_sum_fderiv {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) :
    let F' : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) → (SpaceTime d → ℝ) →
    SpaceTime d → Lorentz.Vector d := fun μν => (fun ψ x =>
    -(fderiv ℝ (fun x' => (fun x' => η μν.1 μν.1 * η μν.2 μν.2 * ψ x') x' * ∂_ μν.1 A x' μν.2) x)
              (Lorentz.Vector.basis μν.1) •
          Lorentz.Vector.basis μν.2 +
        -(fderiv ℝ (fun x' => ∂_ μν.1 A x' μν.2 *
          (fun x' => η μν.1 μν.1 * η μν.2 μν.2 * ψ x') x') x)
              (Lorentz.Vector.basis μν.1) • Lorentz.Vector.basis μν.2 +
      -(-(fderiv ℝ (fun x' => ψ x' * ∂_ μν.2 A x' μν.1) x) (Lorentz.Vector.basis μν.1) •
        Lorentz.Vector.basis μν.2 +
          -(fderiv ℝ (fun x' => ∂_ μν.1 A x' μν.2 * ψ x') x) (Lorentz.Vector.basis μν.2) •
          Lorentz.Vector.basis μν.1))
    A.gradKineticTerm 𝓕 = fun x => ∑ μν, F' μν (fun x' => -1/(2 * 𝓕.μ₀) * (fun _ => 1) x') x := by
  apply HasVarGradientAt.varGradient
  change HasVarGradientAt (fun A' x => ElectromagneticPotential.kineticTerm 𝓕 A' x) _ A
  conv =>
    enter [1, A', x]
    rw [kineticTerm_eq_sum_potential]
  let F : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) → (SpaceTime d → Lorentz.Vector d) →
    SpaceTime d → ℝ := fun (μ, ν) A' x =>
        (η μ μ * η ν ν * ∂_ μ A' x ν ^ 2 - ∂_ μ A' x ν * ∂_ ν A' x μ)
  let F' : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) → (SpaceTime d → ℝ) →
    SpaceTime d → Lorentz.Vector d := fun μν => (fun ψ x =>
    -(fderiv ℝ (fun x' => (fun x' => η μν.1 μν.1 * η μν.2 μν.2 * ψ x') x' * ∂_ μν.1 A x' μν.2) x)
              (Lorentz.Vector.basis μν.1) •
          Lorentz.Vector.basis μν.2 +
        -(fderiv ℝ (fun x' => ∂_ μν.1 A x' μν.2 *
          (fun x' => η μν.1 μν.1 * η μν.2 μν.2 * ψ x') x') x)
              (Lorentz.Vector.basis μν.1) • Lorentz.Vector.basis μν.2 +
      -(-(fderiv ℝ (fun x' => ψ x' * ∂_ μν.2 A x' μν.1) x) (Lorentz.Vector.basis μν.1) •
        Lorentz.Vector.basis μν.2 +
          -(fderiv ℝ (fun x' => ∂_ μν.1 A x' μν.2 * ψ x') x) (Lorentz.Vector.basis μν.2) •
            Lorentz.Vector.basis μν.1))
  have F_hasVarAdjDerivAt (μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) :
      HasVarAdjDerivAt (F μν) (F' μν) A := by
    have h1 :=
      HasVarAdjDerivAt.mul _ _ _ _ A (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
        (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
    have h1' := HasVarAdjDerivAt.const_mul _ _ A h1 (c := η μν.1 μν.1 * η μν.2 μν.2)
    have h2 :=
      HasVarAdjDerivAt.mul _ _ _ _ A (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
        (deriv_hasVarAdjDerivAt μν.2 μν.1 A hA)
    have h3 := HasVarAdjDerivAt.neg _ _ A h2
    have h4 := HasVarAdjDerivAt.add _ _ _ _ _ h1' h3
    convert h4
    simp [F]
    ring
  have F_sum_hasVarAdjDerivAt :
      HasVarAdjDerivAt (fun A' x => ∑ μ, ∑ ν, F (μ, ν) A' x) (fun ψ x => ∑ μν, F' μν ψ x) A := by
    convert HasVarAdjDerivAt.sum _ _ A (hA) (fun i => F_hasVarAdjDerivAt i)
    exact Eq.symm (Fintype.sum_prod_type fun x => F x _ _)
  have hF_mul := HasVarAdjDerivAt.const_mul _ _ A F_sum_hasVarAdjDerivAt (c := -1/(2 * 𝓕.μ₀))
  change HasVarGradientAt (fun A' x => -1 / (2 * 𝓕.μ₀) * ∑ μ, ∑ ν, F (μ, ν) A' x) _ A
  apply HasVarGradientAt.intro _ hF_mul
  rfl

/-!

### B.2. Writing the variational gradient as a sums over double derivatives of the potential

We rewrite the variational gradient as a simple double sum over
second derivatives of the potential.

-/

lemma gradKineticTerm_eq_sum_sum {d} {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (x : SpaceTime d) (ha : ContDiff ℝ ∞ A) :
    A.gradKineticTerm 𝓕 x = ∑ (ν : (Fin 1 ⊕ Fin d)), ∑ (μ : (Fin 1 ⊕ Fin d)),
        (1 / (𝓕.μ₀) * (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by
  have diff_partial (μ) :
      ∀ ν, Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [Lorentz.Vector.differentiable_apply]
    refine Differentiable.clm_apply ?_ ?_
    · refine ((contDiff_succ_iff_fderiv (n := 1)).mp ?_).2.2.differentiable
        (by simp)
      exact ContDiff.of_le ha (right_eq_inf.mp rfl)
    · fun_prop
  rw [gradKineticTerm_eq_sum_fderiv A ha]
  calc _
      _ = ∑ (μ : (Fin 1 ⊕ Fin d)), ∑ (ν : (Fin 1 ⊕ Fin d)),
      (- (fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / (2 * 𝓕.μ₀)) * ∂_ μ A x' ν) x)
        (Lorentz.Vector.basis μ) • Lorentz.Vector.basis ν +
        -(fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / (2 * 𝓕.μ₀)) * ∂_ μ A x' ν) x)
        (Lorentz.Vector.basis μ) • Lorentz.Vector.basis ν +
      -(-(fderiv ℝ (fun x' => -1 / (2 * 𝓕.μ₀) * ∂_ ν A x' μ) x) (Lorentz.Vector.basis μ)
          • Lorentz.Vector.basis ν +
      -(fderiv ℝ (fun x' => -1 / (2 * 𝓕.μ₀) * ∂_ μ A x' ν) x) (Lorentz.Vector.basis ν)
        • Lorentz.Vector.basis μ)) := by
        dsimp
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        refine Finset.sum_congr rfl (fun ν _ => ?_)
        simp only [mul_one, neg_smul, neg_add_rev, neg_neg, mul_neg]
        ring_nf
      _ = ∑ (μ : (Fin 1 ⊕ Fin d)), ∑ (ν : (Fin 1 ⊕ Fin d)),
      ((- 2 * (fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / (2 * 𝓕.μ₀)) * ∂_ μ A x' ν) x)
        (Lorentz.Vector.basis μ) +
      ((fderiv ℝ (fun x' => -1 / (2 * 𝓕.μ₀) * ∂_ ν A x' μ) x) (Lorentz.Vector.basis μ))) •
        Lorentz.Vector.basis ν +
        (fderiv ℝ (fun x' => -1 / (2 * 𝓕.μ₀) * ∂_ μ A x' ν) x) (Lorentz.Vector.basis ν) •
          Lorentz.Vector.basis μ) := by
        apply Finset.sum_congr rfl (fun μ _ => ?_)
        apply Finset.sum_congr rfl (fun ν _ => ?_)
        rw [← add_smul]
        rw [neg_add, ← add_assoc, ← neg_smul, ← add_smul]
        congr 1
        · ring_nf
        · simp [← neg_smul]
      _ = ∑ (μ : (Fin 1 ⊕ Fin d)), ∑ (ν : (Fin 1 ⊕ Fin d)),
      ((- 2 * (fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / (2 * 𝓕.μ₀)) * ∂_ μ A x' ν) x)
        (Lorentz.Vector.basis μ) +
      2 * ((fderiv ℝ (fun x' => -1 / (2 * 𝓕.μ₀) * ∂_ ν A x' μ) x) (Lorentz.Vector.basis μ)))) •
        Lorentz.Vector.basis ν := by
        conv_lhs => enter [2, μ]; rw [Finset.sum_add_distrib]
        rw [Finset.sum_add_distrib]
        conv_lhs => enter [2]; rw [Finset.sum_comm]
        rw [← Finset.sum_add_distrib]
        conv_lhs => enter [2, μ]; rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl (fun μ _ => ?_)
        apply Finset.sum_congr rfl (fun ν _ => ?_)
        rw [← add_smul]
        ring_nf
      _ = ∑ (μ : (Fin 1 ⊕ Fin d)), ∑ (ν : (Fin 1 ⊕ Fin d)),
      ((- 2 * ((η μ μ * η ν ν * -1 / (2 * 𝓕.μ₀)) * ∂_ μ (fun x' => ∂_ μ A x' ν) x) +
      2 * ((-1 / (2 * 𝓕.μ₀) * ∂_ μ (fun x' => ∂_ ν A x' μ) x)))) • Lorentz.Vector.basis ν := by
        apply Finset.sum_congr rfl (fun μ _ => ?_)
        apply Finset.sum_congr rfl (fun ν _ => ?_)
        congr
        · rw [fderiv_const_mul]
          simp [SpaceTime.deriv_eq]
          conv => enter [2, x]; rw [SpaceTime.deriv_eq]
          apply diff_partial μ ν
        · rw [fderiv_const_mul]
          simp [SpaceTime.deriv_eq]
          conv => enter [2, x]; rw [SpaceTime.deriv_eq]
          apply diff_partial ν μ
      _ = ∑ (μ : (Fin 1 ⊕ Fin d)), ∑ (ν : (Fin 1 ⊕ Fin d)),
        ((1 / (𝓕.μ₀) * (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν) := by
        apply Finset.sum_congr rfl (fun μ _ => ?_)
        apply Finset.sum_congr rfl (fun ν _ => ?_)
        ring_nf
      _ = ∑ (ν : (Fin 1 ⊕ Fin d)), ∑ (μ : (Fin 1 ⊕ Fin d)),
        (1 / (𝓕.μ₀) * (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by rw [Finset.sum_comm]

/-!

### B.3. Variational gradient as a sums over fieldStrengthMatrix

We rewrite the variational gradient as a simple double sum over the
fieldStrengthMatrix.

-/

lemma gradKineticTerm_eq_fieldStrength {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (ha : ContDiff ℝ ∞ A) :
    A.gradKineticTerm 𝓕 x = ∑ (ν : (Fin 1 ⊕ Fin d)), (1/𝓕.μ₀ * η ν ν) •
    (∑ (μ : (Fin 1 ⊕ Fin d)), (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x))
    • Lorentz.Vector.basis ν := by
  have diff_partial (μ) :
      ∀ ν, Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [Lorentz.Vector.differentiable_apply]
    refine Differentiable.clm_apply ?_ ?_
    · refine ((contDiff_succ_iff_fderiv (n := 1)).mp ?_).2.2.differentiable
        (by simp)
      exact ContDiff.of_le ha (right_eq_inf.mp rfl)
    · fun_prop
  calc _
      _ = ∑ (ν : (Fin 1 ⊕ Fin d)), ∑ (μ : (Fin 1 ⊕ Fin d)),
        (1/𝓕.μ₀ * (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by
          rw [gradKineticTerm_eq_sum_sum A x ha]
      _ = ∑ (ν : (Fin 1 ⊕ Fin d)), ∑ (μ : (Fin 1 ⊕ Fin d)),
        ((1/𝓕.μ₀ * η ν ν) * (η μ μ * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        η ν ν * ∂_ μ (fun x' => ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          apply Finset.sum_congr rfl (fun μ _ => ?_)
          congr 1
          ring_nf
          simp
      _ = ∑ (ν : (Fin 1 ⊕ Fin d)), ∑ (μ : (Fin 1 ⊕ Fin d)),
        ((1/𝓕.μ₀ * η ν ν) * (∂_ μ (fun x' => η μ μ * ∂_ μ A x' ν) x -
            ∂_ μ (fun x' => η ν ν * ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          apply Finset.sum_congr rfl (fun μ _ => ?_)
          congr
          · rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, fderiv_const_mul]
            rfl
            apply diff_partial μ ν
          · rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, fderiv_const_mul]
            rfl
            apply diff_partial ν μ
      _ = ∑ (ν : (Fin 1 ⊕ Fin d)), ∑ (μ : (Fin 1 ⊕ Fin d)),
        ((1/𝓕.μ₀ * η ν ν) * (∂_ μ (fun x' => η μ μ * ∂_ μ A x' ν -
            η ν ν * ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          apply Finset.sum_congr rfl (fun μ _ => ?_)
          congr
          rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, SpaceTime.deriv_eq, fderiv_fun_sub]
          simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply]
          · conv => enter [2, x]; rw [SpaceTime.deriv_eq]
            apply Differentiable.differentiableAt
            apply Differentiable.const_mul
            exact diff_partial μ ν
          · conv => enter [2, x]; rw [SpaceTime.deriv_eq]
            apply Differentiable.differentiableAt
            apply Differentiable.const_mul
            exact diff_partial ν μ
      _ = ∑ (ν : (Fin 1 ⊕ Fin d)), ∑ (μ : (Fin 1 ⊕ Fin d)),
        ((1/𝓕.μ₀ * η ν ν) * (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x)) •
            Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          apply Finset.sum_congr rfl (fun μ _ => ?_)
          congr
          funext x
          rw [toFieldStrength_basis_repr_apply_eq_single]
      _ = ∑ (ν : (Fin 1 ⊕ Fin d)), ((1/𝓕.μ₀ * η ν ν) *
          ∑ (μ : (Fin 1 ⊕ Fin d)), (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x))
          • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          rw [← Finset.sum_smul, Finset.mul_sum]
      _ = ∑ (ν : (Fin 1 ⊕ Fin d)), (1/𝓕.μ₀ * η ν ν) •
          (∑ (μ : (Fin 1 ⊕ Fin d)), (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x))
          • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          rw [smul_smul]

/-!

### B.4. Variational gradient in terms of the Gauss's and Ampère laws

We rewrite the variational gradient in terms of the electric and magnetic fields,
explicitly relating it to Gauss's law and Ampère's law.

-/
open Time Space

lemma gradKineticTerm_eq_electric_magnetic {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (ha : ContDiff ℝ ∞ A) :
    A.gradKineticTerm 𝓕 x =
    (1/(𝓕.μ₀ * 𝓕.c) * Space.div (A.electricField 𝓕.c (x.time 𝓕.c)) x.space) •
    Lorentz.Vector.basis (Sum.inl 0) +
    ∑ i, (𝓕.μ₀⁻¹ * (1 / 𝓕.c ^ 2 * ∂ₜ (fun t => A.electricField 𝓕.c t x.space) (x.time 𝓕.c) i-
      ∑ j, Space.deriv j (A.magneticFieldMatrix 𝓕.c (x.time 𝓕.c) · (j, i)) x.space)) •
      Lorentz.Vector.basis (Sum.inr i) := by
  have diff_partial (μ) :
      ∀ ν, Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [Lorentz.Vector.differentiable_apply]
    refine Differentiable.clm_apply ?_ ?_
    · refine ((contDiff_succ_iff_fderiv (n := 1)).mp ?_).2.2.differentiable
        (by simp)
      exact ContDiff.of_le ha (right_eq_inf.mp rfl)
    · fun_prop
  have hdiff (μ ν) : Differentiable ℝ fun x => (A.fieldStrengthMatrix x) (μ, ν) := by
    conv => enter [2, x]; rw [toFieldStrength_basis_repr_apply_eq_single,
      SpaceTime.deriv_eq, SpaceTime.deriv_eq]
    apply Differentiable.sub
    apply Differentiable.const_mul
    · exact diff_partial (μ, ν).1 (μ, ν).2
    apply Differentiable.const_mul
    · exact diff_partial (μ, ν).2 (μ, ν).1
  rw [gradKineticTerm_eq_fieldStrength A x ha]
  rw [Fintype.sum_sum_type, Fin.sum_univ_one]
  congr 1
  · rw [smul_smul]
    congr 1
    rw [div_electricField_eq_fieldStrengthMatrix]
    simp only [one_div, Fin.isValue, inl_0_inl_0, mul_one, mul_inv_rev,
      toTimeAndSpace_symm_apply_time_space]
    field_simp
    apply ha.of_le (ENat.LEInfty.out)
  · congr
    funext j
    simp only [one_div, inr_i_inr_i, mul_neg, mul_one, neg_smul]
    rw [curl_magneticFieldMatrix_eq_electricField_fieldStrengthMatrix]
    rw [smul_smul, ← neg_smul]
    congr
    simp only [one_div, toTimeAndSpace_symm_apply_time_space, sub_add_cancel_left, mul_neg]
    apply ha.of_le (ENat.LEInfty.out)

lemma gradKineticTerm_eq_electric_magnetic_three {𝓕 : FreeSpace} (A : ElectromagneticPotential)
    (x : SpaceTime) (ha : ContDiff ℝ ∞ A) :
    A.gradKineticTerm 𝓕 x =
    (1/(𝓕.μ₀ * 𝓕.c) * Space.div (A.electricField 𝓕.c (x.time 𝓕.c)) x.space) •
      Lorentz.Vector.basis (Sum.inl 0) +
    ∑ i, (𝓕.μ₀⁻¹ * (1 / 𝓕.c ^ 2 * ∂ₜ (fun t => A.electricField 𝓕.c t x.space) (x.time 𝓕.c) i-
      Space.curl (A.magneticField 𝓕.c (x.time 𝓕.c)) x.space i)) •
      Lorentz.Vector.basis (Sum.inr i) := by
  rw [gradKineticTerm_eq_electric_magnetic A x ha]
  congr
  funext i
  congr
  rw [magneticField_curl_eq_magneticFieldMatrix]
  exact ha.of_le (ENat.LEInfty.out)
/-!

### B.5. Linearity properties of the variational gradient

-/

lemma gradKineticTerm_add {d} {𝓕 : FreeSpace} (A1 A2 : ElectromagneticPotential d)
    (hA1 : ContDiff ℝ ∞ A1) (hA2 : ContDiff ℝ ∞ A2) :
    (A1 + A2).gradKineticTerm 𝓕 = A1.gradKineticTerm 𝓕 + A2.gradKineticTerm 𝓕 := by
  funext x
  rw [gradKineticTerm_eq_fieldStrength]
  simp only [Pi.add_apply]
  rw [gradKineticTerm_eq_fieldStrength, gradKineticTerm_eq_fieldStrength]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl (fun ν _ => ?_)
  rw [← smul_add, ← add_smul, ← Finset.sum_add_distrib]
  congr
  funext μ
  rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, SpaceTime.deriv_eq]
  conv_lhs =>
    enter [1, 2, x]
    rw [fieldStrengthMatrix_add _ _ _ (hA1.differentiable (by simp))
      (hA2.differentiable (by simp))]
    simp [Finsupp.coe_add, Pi.add_apply]
  rw [fderiv_fun_add]
  rfl
  · apply fieldStrengthMatrix_differentiable <| hA1.of_le (ENat.LEInfty.out)
  · apply fieldStrengthMatrix_differentiable <| hA2.of_le (ENat.LEInfty.out)
  · exact hA2
  · exact hA1
  · exact hA1.add hA2

lemma gradKineticTerm_smul {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (c : ℝ) :
    (c • A).gradKineticTerm 𝓕 = c • A.gradKineticTerm 𝓕 := by
  funext x
  rw [gradKineticTerm_eq_fieldStrength]
  simp only [Pi.smul_apply]
  rw [gradKineticTerm_eq_fieldStrength]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl (fun ν _ => ?_)
  conv_rhs => rw [smul_comm]
  congr 1
  rw [smul_smul]
  congr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun μ _ => ?_)
  conv_rhs =>
    rw [SpaceTime.deriv_eq]
    change (c • fderiv ℝ (fun x => (A.fieldStrengthMatrix x) (μ, ν)) x) (Lorentz.Vector.basis μ)
    rw [← fderiv_const_smul
      (fieldStrengthMatrix_differentiable <| hA.of_le (ENat.LEInfty.out)).differentiableAt]
    rw [← SpaceTime.deriv_eq]
  congr
  funext x
  rw [fieldStrengthMatrix_smul _ _ _]
  rfl
  · exact hA.differentiable (by simp)
  · exact hA
  · exact hA.const_smul c

/-!

### B.6. HasVarGradientAt for the variational gradient

-/

lemma kineticTerm_hasVarGradientAt {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) : HasVarGradientAt (kineticTerm 𝓕) (A.gradKineticTerm 𝓕) A := by
  rw [gradKineticTerm_eq_sum_fderiv A hA]
  change HasVarGradientAt (fun A' x => ElectromagneticPotential.kineticTerm 𝓕 A' x) _ A
  conv =>
    enter [1, A', x]
    rw [kineticTerm_eq_sum_potential]
  let F : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) → (SpaceTime d → Lorentz.Vector d) →
    SpaceTime d → ℝ := fun (μ, ν) A' x =>
        (η μ μ * η ν ν * ∂_ μ A' x ν ^ 2 - ∂_ μ A' x ν * ∂_ ν A' x μ)
  let F' : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) → (SpaceTime d → ℝ) →
    SpaceTime d → Lorentz.Vector d := fun μν => (fun ψ x =>
    -(fderiv ℝ (fun x' => (fun x' => η μν.1 μν.1 * η μν.2 μν.2 * ψ x') x' * ∂_ μν.1 A x' μν.2) x)
              (Lorentz.Vector.basis μν.1) •
          Lorentz.Vector.basis μν.2 +
        -(fderiv ℝ (fun x' => ∂_ μν.1 A x' μν.2 *
          (fun x' => η μν.1 μν.1 * η μν.2 μν.2 * ψ x') x') x)
              (Lorentz.Vector.basis μν.1) • Lorentz.Vector.basis μν.2 +
      -(-(fderiv ℝ (fun x' => ψ x' * ∂_ μν.2 A x' μν.1) x) (Lorentz.Vector.basis μν.1) •
        Lorentz.Vector.basis μν.2 +
          -(fderiv ℝ (fun x' => ∂_ μν.1 A x' μν.2 * ψ x') x) (Lorentz.Vector.basis μν.2) •
            Lorentz.Vector.basis μν.1))
  have F_hasVarAdjDerivAt (μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) :
      HasVarAdjDerivAt (F μν) (F' μν) A := by
    have h1 :=
      HasVarAdjDerivAt.mul _ _ _ _ A (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
        (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
    have h1' := HasVarAdjDerivAt.const_mul _ _ A h1 (c := η μν.1 μν.1 * η μν.2 μν.2)
    have h2 :=
      HasVarAdjDerivAt.mul _ _ _ _ A (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
        (deriv_hasVarAdjDerivAt μν.2 μν.1 A hA)
    have h3 := HasVarAdjDerivAt.neg _ _ A h2
    have h4 := HasVarAdjDerivAt.add _ _ _ _ _ h1' h3
    convert h4
    simp [F]
    ring
  have F_sum_hasVarAdjDerivAt :
      HasVarAdjDerivAt (fun A' x => ∑ μ, ∑ ν, F (μ, ν) A' x) (fun ψ x => ∑ μν, F' μν ψ x) A := by
    convert HasVarAdjDerivAt.sum _ _ A (hA) (fun i => F_hasVarAdjDerivAt i)
    exact Eq.symm (Fintype.sum_prod_type fun x => F x _ _)
  have hF_mul := HasVarAdjDerivAt.const_mul _ _ A F_sum_hasVarAdjDerivAt (c := -1/(2 * 𝓕.μ₀))
  change HasVarGradientAt (fun A' x => -1 / (2 * 𝓕.μ₀) * ∑ μ, ∑ ν, F (μ, ν) A' x) _ A
  apply HasVarGradientAt.intro _ hF_mul
  rfl

/-!

### B.7. Gradient of the kinetic term in terms of the tensor derivative

-/

lemma gradKineticTerm_eq_tensorDeriv {d} {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (x : SpaceTime d)
    (hA : ContDiff ℝ ∞ A) (ν : Fin 1 ⊕ Fin d) :
    A.gradKineticTerm 𝓕 x ν = η ν ν * ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
    (permT id (PermCond.auto) {(1/ 𝓕.μ₀ : ℝ) • tensorDeriv A.toFieldStrength x | κ κ ν'}ᵀ)) ν := by
  trans η ν ν * (Lorentz.Vector.basis.repr
    ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
    (permT id (PermCond.auto) {(1/ 𝓕.μ₀ : ℝ) • tensorDeriv A.toFieldStrength x | κ κ ν'}ᵀ))) ν
  swap
  · simp [Lorentz.Vector.basis_repr_apply]
  simp [Lorentz.Vector.basis_eq_map_tensor_basis]
  rw [permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_rhs =>
    enter [2, 2, 2, μ]
    rw [tensorDeriv_toTensor_basis_repr (by
      apply toFieldStrength_differentiable
      apply hA.of_le (ENat.LEInfty.out))]
    enter [2, x]
    rw [toFieldStrength_tensor_basis_eq_basis]
    change fieldStrengthMatrix A x _
  conv_lhs =>
    rw [gradKineticTerm_eq_fieldStrength A x hA]
    simp [Lorentz.Vector.apply_sum]
  ring_nf
  congr 1
  rw [← finSumFinEquiv.sum_comp]
  congr
  funext μ
  congr
  · apply Lorentz.CoVector.indexEquiv.symm.injective
    simp only [Nat.reduceSucc, Nat.reduceAdd, Fin.isValue, Function.comp_apply, Fin.cast_eq_self,
      Equiv.symm_apply_apply]
    simp [Lorentz.CoVector.indexEquiv]
    funext j
    fin_cases j
    simp [ComponentIdx.prodEquiv, ComponentIdx.prodIndexEquiv]
    simp [ComponentIdx.DropPairSection.ofFinEquiv, ComponentIdx.DropPairSection.ofFin]
    intro h
    change ¬ 0 = 0 at h
    simp at h
  funext x
  congr
  · apply finSumFinEquiv.injective
    simp only [Nat.reduceSucc, Nat.reduceAdd, Fin.isValue, Function.comp_apply, Fin.cast_eq_self,
      Equiv.apply_symm_apply]
    simp [ComponentIdx.prodEquiv, ComponentIdx.prodIndexEquiv]
    simp [ComponentIdx.DropPairSection.ofFinEquiv, ComponentIdx.DropPairSection.ofFin]
    intro _ h
    apply False.elim
    apply h
    decide
  · apply finSumFinEquiv.injective
    simp only [Nat.reduceSucc, Nat.reduceAdd, Fin.isValue, Function.comp_apply, Fin.cast_eq_self,
      Equiv.apply_symm_apply]
    simp [ComponentIdx.prodEquiv, ComponentIdx.prodIndexEquiv]
    simp [ComponentIdx.DropPairSection.ofFinEquiv, ComponentIdx.DropPairSection.ofFin]
    split_ifs
    · rename_i h
      suffices ¬ (finSumFinEquiv (Sum.inr 1) = (0 : Fin (1 + 1 + 1))) from False.elim (this h)
      decide
    · rename_i h h2
      suffices ¬ (finSumFinEquiv (Sum.inr 1) = (1 : Fin (1 + 1 + 1))) from False.elim (this h2)
      decide
    · rfl

end ElectromagneticPotential

/-!

## C. The gradient of the kinetic term for distributions

For distributions we define the gradient of the kinetic term directly
using `ElectromagneticPotential.gradKineticTerm_eq_sum_sum` as the defining formula.

-/

namespace DistElectromagneticPotential
open minkowskiMatrix SpaceTime SchwartzMap Lorentz
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-- The gradient of the kinetic term for an Electromagnetic potential which
  is a distribution. -/
noncomputable def gradKineticTerm {d} (𝓕 : FreeSpace) :
    DistElectromagneticPotential d →ₗ[ℝ] (SpaceTime d) →d[ℝ] Lorentz.Vector d where
  toFun A := {
    toFun ε := ∑ ν, ∑ μ,
      (1 / (𝓕.μ₀) * (η μ μ * η ν ν * distDeriv μ (distDeriv μ A) ε ν -
      distDeriv μ (distDeriv ν A) ε μ)) • Lorentz.Vector.basis ν
    map_add' ε1 ε2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      simp only [one_div, map_add, Lorentz.Vector.apply_add, ← add_smul]
      ring_nf
    map_smul' r ε := by
      simp [Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      ring_nf
    cont := by fun_prop}
  map_add' A1 A2 := by
    ext ε
    simp only [one_div, map_add, ContinuousLinearMap.add_apply, Lorentz.Vector.apply_add,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl (fun ν _ => ?_)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl (fun μ _ => ?_)
    simp only [← add_smul]
    ring_nf
  map_smul' r A := by
    ext ε
    simp only [one_div, map_smul, ContinuousLinearMap.smul_apply, Lorentz.Vector.apply_smul,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
    simp [Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl (fun ν _ => ?_)
    apply Finset.sum_congr rfl (fun μ _ => ?_)
    ring_nf

lemma gradKineticTerm_eq_sum_sum {d} {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d) (ε : 𝓢(SpaceTime d, ℝ)) :
    A.gradKineticTerm 𝓕 ε = ∑ ν, ∑ μ,
        (1 / (𝓕.μ₀) * (η μ μ * η ν ν * distDeriv μ (distDeriv μ A) ε ν -
        distDeriv μ (distDeriv ν A) ε μ)) • Lorentz.Vector.basis ν := rfl

lemma gradKineticTerm_eq_fieldStrength {d} {𝓕 : FreeSpace} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    A.gradKineticTerm 𝓕 ε = ∑ ν, (1/𝓕.μ₀ * η ν ν) •
    (∑ μ, ((Vector.basis.tensorProduct Vector.basis).repr
      (distDeriv μ (A.fieldStrength) ε) (μ, ν))) • Lorentz.Vector.basis ν := by
  rw [gradKineticTerm_eq_sum_sum A]
  apply Finset.sum_congr rfl (fun ν _ => ?_)
  rw [smul_smul, ← Finset.sum_smul, ← Finset.mul_sum, mul_assoc]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun μ _ => ?_)
  conv_rhs =>
    rw [distDeriv_apply, Distribution.fderivD_apply, map_neg]
    simp only [Finsupp.coe_neg, Pi.neg_apply, mul_neg]
    rw [fieldStrength_basis_repr_eq_single]
    simp only
    rw [SpaceTime.apply_fderiv_eq_distDeriv, SpaceTime.apply_fderiv_eq_distDeriv]
    simp
  ring_nf
  simp

lemma gradKineticTerm_sum_inl_eq {d} {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d) (ε : 𝓢(SpaceTime d, ℝ)) :
    A.gradKineticTerm 𝓕 ε (Sum.inl 0) =
    (1/(𝓕.μ₀ * 𝓕.c) * (distTimeSlice 𝓕.c).symm (Space.distSpaceDiv (A.electricField 𝓕.c)) ε) := by
  rw [gradKineticTerm_eq_fieldStrength A ε, Lorentz.Vector.apply_sum, distTimeSlice_symm_apply,
    Space.distSpaceDiv_apply_eq_sum_distSpaceDeriv, Finset.mul_sum]
  simp [Fintype.sum_sum_type, Finset.mul_sum]
  apply Finset.sum_congr rfl (fun ν _ => ?_)
  rw [← distTimeSlice_symm_apply]
  conv_rhs =>
    enter [2]
    rw [distTimeSlice_symm_apply, Space.distSpaceDeriv_apply']
    simp only [PiLp.neg_apply]
    rw [electricField_eq_fieldStrength, distTimeSlice_apply]
    simp only [Fin.isValue, neg_mul, neg_neg]
    rw [fieldStrength_antisymmetric_basis]
    rw [← distTimeSlice_apply, Space.apply_fderiv_eq_distSpaceDeriv, ← distTimeSlice_symm_apply,
      ← distTimeSlice_distDeriv_inr]
    simp
  field_simp

lemma gradKineticTerm_sum_inr_eq {d} {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d) (ε : 𝓢(SpaceTime d, ℝ)) (i : Fin d) :
    A.gradKineticTerm 𝓕 ε (Sum.inr i) =
    (𝓕.μ₀⁻¹ * (1 / 𝓕.c ^ 2 * (distTimeSlice 𝓕.c).symm
      (Space.distTimeDeriv (A.electricField 𝓕.c)) ε i -
      ∑ j, ((PiLp.basisFun 2 ℝ (Fin d)).tensorProduct (PiLp.basisFun 2 ℝ (Fin d))).repr
        ((distTimeSlice 𝓕.c).symm (Space.distSpaceDeriv j
          (A.magneticFieldMatrix 𝓕.c)) ε) (j, i))) := by
  simp [gradKineticTerm_eq_fieldStrength A ε, Lorentz.Vector.apply_sum,
    Fintype.sum_sum_type, mul_add, sub_eq_add_neg]
  congr
  · conv_rhs =>
      enter [2, 2]
      rw [distTimeSlice_symm_apply, Space.distTimeDeriv_apply']
      simp only [PiLp.neg_apply]
      rw [electricField_eq_fieldStrength, Space.apply_fderiv_eq_distTimeDeriv,
        ← distTimeSlice_symm_apply]
      simp [distTimeSlice_symm_distTimeDeriv_eq]
    field_simp
  · ext k
    conv_rhs =>
      rw [distTimeSlice_symm_apply, Space.distSpaceDeriv_apply']
      simp only [map_neg, Finsupp.coe_neg, Pi.neg_apply]
      rw [magneticFieldMatrix_basis_repr_eq_fieldStrength, Space.apply_fderiv_eq_distSpaceDeriv,
        ← distTimeSlice_symm_apply]
    simp [← distTimeSlice_distDeriv_inr]

/-!

### C.1. The gradient of the kinetic term as a tensor

-/

lemma gradKineticTerm_eq_distTensorDeriv {d} {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d) (ε : 𝓢(SpaceTime d, ℝ)) (ν : Fin 1 ⊕ Fin d) :
    A.gradKineticTerm 𝓕 ε ν = η ν ν * ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
    (permT id (PermCond.auto) {(1/ 𝓕.μ₀ : ℝ) •
    distTensorDeriv A.fieldStrength ε | κ κ ν'}ᵀ)) ν := by
  trans η ν ν * (Lorentz.Vector.basis.repr
    ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
    (permT id (PermCond.auto) {(1/ 𝓕.μ₀ : ℝ) • distTensorDeriv A.fieldStrength ε | κ κ ν'}ᵀ))) ν
  swap
  · rfl
  simp [Lorentz.Vector.basis_eq_map_tensor_basis]
  rw [permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    rw [gradKineticTerm_eq_fieldStrength A ε]
    simp [Lorentz.Vector.apply_sum]
  ring_nf
  congr 1
  rw [← finSumFinEquiv.sum_comp]
  congr
  funext μ
  rw [distTensorDeriv_toTensor_basis_repr]
  conv_rhs =>
    enter [1, 2, 2]
  trans (Tensor.basis _).repr (Tensorial.toTensor (distDeriv μ (A.fieldStrength) ε))
      (fun | 0 => finSumFinEquiv μ | 1 => finSumFinEquiv ν)
  · generalize (distDeriv μ (A.fieldStrength) ε) = t at *
    rw [Tensorial.basis_toTensor_apply]
    rw [Tensorial.basis_map_prod]
    simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
      Equiv.symm_symm]
    rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex]
    have hb : (((Lorentz.Vector.basis (d := d)).reindex
        Lorentz.Vector.indexEquiv.symm).tensorProduct
        (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
        ((Lorentz.Vector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
        (Lorentz.Vector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
      ext b
      match b with
      | ⟨i, j⟩ =>
      simp
    rw [hb]
    rw [Module.Basis.repr_reindex_apply]
    congr 1
    simp [ComponentIdx.prodEquiv,ComponentIdx.prodIndexEquiv, Vector.indexEquiv]
    apply And.intro
    · rw [@Equiv.eq_symm_apply]
      rfl
    · rw [@Equiv.eq_symm_apply]
      rfl
  apply congr
  · simp
    congr
    apply Lorentz.CoVector.indexEquiv.symm.injective
    simp only [Nat.reduceSucc, Fin.isValue, Equiv.symm_apply_apply]
    simp [Lorentz.CoVector.indexEquiv]
    funext j
    fin_cases j
    simp [ComponentIdx.prodEquiv, ComponentIdx.prodIndexEquiv]
    simp [ComponentIdx.DropPairSection.ofFinEquiv, ComponentIdx.DropPairSection.ofFin]
    intro h
    change ¬ 0 = 0 at h
    simp at h
  funext x
  fin_cases x
  · simp only [Nat.reduceSucc, Nat.reduceAdd, Fin.isValue, Function.comp_apply, Fin.cast_eq_self]
    simp [ComponentIdx.prodEquiv, ComponentIdx.prodIndexEquiv]
    simp [ComponentIdx.DropPairSection.ofFinEquiv, ComponentIdx.DropPairSection.ofFin]
    intro _ h
    apply False.elim
    apply h
    decide
  · simp only [Nat.reduceSucc, Nat.reduceAdd, Fin.isValue, Function.comp_apply, Fin.cast_eq_self]
    simp [ComponentIdx.prodEquiv, ComponentIdx.prodIndexEquiv]
    simp [ComponentIdx.DropPairSection.ofFinEquiv, ComponentIdx.DropPairSection.ofFin]
    split_ifs
    · rename_i h
      suffices ¬ (finSumFinEquiv (Sum.inr 1) = (0 : Fin (1 + 1 + 1))) from False.elim (this h)
      decide
    · rename_i h h2
      suffices ¬ (finSumFinEquiv (Sum.inr 1) = (1 : Fin (1 + 1 + 1))) from False.elim (this h2)
      decide
    · rfl

end DistElectromagneticPotential
end Electromagnetism
