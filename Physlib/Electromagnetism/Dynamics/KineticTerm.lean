/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Kinematics.MagneticField
public import Physlib.Electromagnetism.Dynamics.Basic
public import Physlib.Mathematics.VariationalCalculus.HasVarGradient
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
  - B.3. Variational gradient as sums over the components of the field strength tensor
  - B.4. Variational gradient in terms of the Gauss's and Ampère laws
  - B.5. Linearity properties of the variational gradient
  - B.6. HasVarGradientAt for the variational gradient
  - B.7. Gradient of the kinetic term in terms of the tensor derivative

## iv. References

* https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html. [ref: ucsd_ph130a_node452]
-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor ContDiff Physlib

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one
attribute [-simp] Fin.succAbove_zero

/-!

## A. The kinetic term

The kinetic term is `- 1/(4 μ₀) F_μν F^μν`. We define this and show that it is
Lorentz invariant.

-/

/-- The kinetic energy from an electromagnetic potential. -/
noncomputable def kineticTerm {d} (𝓕 : FreeSpace) (A : ElectromagneticPotential d) :
    SpaceTime d → ℝ := fun x =>
  - 1/(4 * 𝓕.μ₀) * {η' d | μ μ' ⊗ η' d | ν ν' ⊗
    A.toFieldStrength x | μ ν ⊗ A.toFieldStrength x | μ' ν'}ᵀ.toScalar

/-!

### A.1. Lorentz invariance of the kinetic term

We show that the kinetic energy is Lorentz invariant.

-/

lemma kineticTerm_equivariant {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (Λ : LorentzGroup d)
    (hf : Differentiable ℝ A) (x : SpaceTime d) :
    kineticTerm 𝓕 (Λ • A) x = kineticTerm 𝓕 A (Λ⁻¹ • x) := by
  rw [kineticTerm, kineticTerm]
  conv_lhs =>
    enter [2]
    rw [toFieldStrength_equivariant A Λ hf, Tensorial.toTensor_smul, ← actionT_coMetric Λ]
    simp only [prodT_equivariant, contrT_equivariant, toScalar_equivariant]

/-!

### A.2. Kinetic term simplified expressions

-/

lemma kineticTerm_eq_sum {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    A.kineticTerm 𝓕 x =
    - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν, ∑ μ', ∑ ν', η μ μ' * η ν ν' *
      toScalar {A.toFieldStrength x | [μ] [ν]}ᵀ * toScalar {A.toFieldStrength x | [μ'] [ν']}ᵀ := by
  rw [kineticTerm]
  rw [toScalar_eq_repr]
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
    rw [coMetric_repr_apply_eq_minkowskiMatrix]
    change η μ' μ
  conv_lhs =>
    enter [2, 2, μ, 2, ν, 1, 2, μ', 2, ν', 1, 2]
    rw [coMetric_repr_apply_eq_minkowskiMatrix]
    change η (ν') (ν)
  conv_lhs =>
    enter [2, 2, μ, 2, ν, 1, 2, μ', 2, ν', 2]
    rw [toFieldStrength_tensor_basis_repr_eq_eval]
  conv_lhs =>
    enter [2, 2, μ, 2, ν, 2]
    rw [toFieldStrength_tensor_basis_repr_eq_eval]
  conv_lhs =>
    enter [2, 2, μ]
    enter [2, ν]
    rw [Finset.sum_mul]
    enter [2, μ']
    rw [Finset.sum_mul]
    enter [2, ν']
  conv_lhs => enter [2, 2, μ]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, 2, μ', 2, ν]; rw [Finset.sum_comm]
  conv_lhs => enter [2, 2, μ']; rw [Finset.sum_comm]
  rfl

lemma kineticTerm_eq_sum_sq {d} {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (x : SpaceTime d) : A.kineticTerm 𝓕 x =
    - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν, η μ μ * η ν ν * ‖toScalar {A.toFieldStrength x | [μ] [ν]}ᵀ‖ ^ 2 := by
  rw [kineticTerm_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_eq_single μ (fun b _ hb => by simp [minkowskiMatrix.off_diag_zero hb.symm])
      (by simp),
    Finset.sum_eq_single ν (fun b _ hb => by simp [minkowskiMatrix.off_diag_zero hb.symm])
      (by simp)]
  simp [← pow_two, mul_assoc]

lemma kineticTerm_eq_sum_potential {d} {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (x : SpaceTime d) :
    A.kineticTerm 𝓕 x = - 1 / (2 * 𝓕.μ₀) * ∑ μ, ∑ ν,
        (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) := by
  calc _
    _ = - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν, η μ μ * η ν ν *
        (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ)
        * (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ) := by
      rw [kineticTerm_eq_sum]
      congr 1
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      rw [Finset.sum_eq_single μ (fun b _ hb => by simp [minkowskiMatrix.off_diag_zero hb.symm])
          (by simp),
        Finset.sum_eq_single ν (fun b _ hb => by simp [minkowskiMatrix.off_diag_zero hb.symm])
          (by simp),
        toFieldStrength_eval_apply_eq_single]
    _ = - 1/(4 * 𝓕.μ₀) * ∑ μ, ∑ ν,
        ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) +
        (η ν ν * η μ μ * (∂_ ν A x μ) ^ 2 - ∂_ ν A x μ * ∂_ μ A x ν)) := by
      congr 1
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      linear_combination (η μ μ * η ν ν * ∂_ μ A x ν ^ 2 -
          2 * η ν ν * η ν ν * ∂_ μ A x ν * ∂_ ν A x μ) *
          minkowskiMatrix.η_apply_mul_η_apply_diag μ +
        (η μ μ * η ν ν * ∂_ ν A x μ ^ 2 - 2 * ∂_ μ A x ν * ∂_ ν A x μ) *
          minkowskiMatrix.η_apply_mul_η_apply_diag ν
    _ = - 1 / (2 * 𝓕.μ₀) * ∑ μ, ∑ ν,
        (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) := by
      simp only [Finset.sum_add_distrib]
      conv_lhs =>
        enter [2, 2]
        rw [Finset.sum_comm]
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
    rw [toFieldStrength_eval_eq_electric_magnetic A t x hA,
      toFieldStrength_eval_eq_electric_magnetic A t x hA]
  simp [Fintype.sum_sum_type, Fin.sum_univ_three, EuclideanSpace.norm_sq_eq]
  field_simp
  rw [FreeSpace.c_sq]
  field_simp
  ring

lemma kineticTerm_eq_electric_magnetic' {𝓕 : FreeSpace} {A : ElectromagneticPotential}
    (hA : Differentiable ℝ A) (x : SpaceTime) :
    A.kineticTerm 𝓕 x =
    1/2 * (𝓕.ε₀ * ‖A.electricField 𝓕.c (x.time 𝓕.c) x.space‖ ^ 2 -
      (1 / 𝓕.μ₀) * ‖A.magneticField 𝓕.c (x.time 𝓕.c) x.space‖ ^ 2) := by
  rw [← kineticTerm_eq_electric_magnetic _ _ _ hA, toTimeAndSpace_symm_apply_time_space]

/-!

### A.4. The kinetic term in terms of the electric and magnetic matrix

-/

lemma kineticTerm_eq_electricMatrix_magneticFieldMatrix_time_space {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (t : Time)
    (x : Space d) (hA : Differentiable ℝ A) :
    A.kineticTerm 𝓕 ((toTimeAndSpace 𝓕.c).symm (t, x)) =
    1/2 * (𝓕.ε₀ * ‖A.electricField 𝓕.c t x‖ ^ 2 -
    (1 / (2 * 𝓕.μ₀)) * ∑ i, ∑ j, ‖A.magneticFieldMatrix 𝓕.c t x (i, j)‖ ^ 2) := by
  rw [kineticTerm_eq_sum_sq]
  simp [Fintype.sum_sum_type]
  rw [Finset.sum_add_distrib]
  simp only [Fin.isValue, Finset.sum_neg_distrib]
  have h1 : ∑ i, ∑ j, magneticFieldMatrix 𝓕.c A t x (i, j) ^ 2
      = ∑ i, ∑ j, toScalar {A.toFieldStrength ((toTimeAndSpace 𝓕.c).symm (t, x)) |
        [Sum.inr i] [Sum.inr j]}ᵀ ^ 2 := by rfl
  rw [h1]
  ring_nf
  have h2 : ‖electricField 𝓕.c A t x‖ ^ 2 = 𝓕.c.val ^ 2 *
      ∑ i, |toScalar {A.toFieldStrength ((toTimeAndSpace 𝓕.c).symm (t, x)) |
      [Sum.inl 0] [Sum.inr i]}ᵀ| ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    conv_lhs =>
      enter [2, i]
      rw [electricField_eq_toFieldStrength_eval A t x i hA]
      simp only [Fin.isValue, neg_mul, norm_neg, norm_mul, Real.norm_eq_abs, FreeSpace.c_abs]
      rw [mul_pow]
    rw [← Finset.mul_sum]
  rw [h2]
  simp only [Fin.isValue, one_div, sq_abs]
  conv_lhs =>
    enter [1, 2, 1, 2, 2, i]
    rw [toFieldStrength_eval_antisymm]
  simp [FreeSpace.c_sq, toFieldStrength_eval_diag_eq_zero]
  field_simp
  ring

lemma kineticTerm_eq_electricMatrix_magneticFieldMatrix {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (x : SpaceTime d)
    (hA : Differentiable ℝ A) :
    A.kineticTerm 𝓕 x =
    1/2 * (𝓕.ε₀ * ‖A.electricField 𝓕.c (x.time 𝓕.c) x.space‖ ^ 2 -
    (1 / (2 * 𝓕.μ₀)) * ∑ i, ∑ j, ‖A.magneticFieldMatrix 𝓕.c (x.time 𝓕.c) x.space (i, j)‖ ^ 2) := by
  rw [← kineticTerm_eq_electricMatrix_magneticFieldMatrix_time_space A (x.time 𝓕.c) x.space hA,
    toTimeAndSpace_symm_apply_time_space]

/-!

### A.5. The kinetic term for constant fields

-/

lemma kineticTerm_const {d} {𝓕 : FreeSpace} (A₀ : Lorentz.Vector d) :
    kineticTerm 𝓕 ⟨fun _ : SpaceTime d => A₀⟩ = 0 := by
  funext x
  simp [kineticTerm_eq_sum_potential, SpaceTime.deriv_eq]

lemma kineticTerm_add_const {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (A₀ : Lorentz.Vector d) :
    kineticTerm 𝓕 ⟨fun x => A x + A₀⟩ = kineticTerm 𝓕 A := by
  funext x
  simp [kineticTerm_eq_sum_potential, SpaceTime.deriv_eq]

/-!

### A.6. Smoothness of the kinetic term

-/

lemma kineticTerm_contDiff {d} {n : WithTop ℕ∞} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ (n + 1) A) :
    ContDiff ℝ n (A.kineticTerm 𝓕) := by
  rw [funext fun x => kineticTerm_eq_sum (𝓕 := 𝓕) A x]
  have h (μ ν) : ContDiff ℝ n (fun x => toScalar {A.toFieldStrength x | [μ] [ν]}ᵀ) :=
    toFieldStrength_eval_contDiff hA
  fun_prop

/-!

### A.7. The kinetic term shifted by time mul a constant

This result is used in finding the canonical momentum.
-/

lemma kineticTerm_add_time_mul_const {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (ha : Differentiable ℝ A)
    (c : Lorentz.Vector d) (x : SpaceTime d) :
    kineticTerm 𝓕 ⟨fun x => A x + x (Sum.inl 0) • c⟩ x = A.kineticTerm 𝓕 x +
        (-1 / (2 * 𝓕.μ₀) * ∑ ν, ((2 * c ν * η ν ν * ∂_ (Sum.inl 0) A x ν + η ν ν * c ν ^ 2 -
        2 * c ν * (∂_ ν A x (Sum.inl 0)))) + 1/(2 * 𝓕.μ₀) * c (Sum.inl 0) ^2) := by
  have diff_a : ∂_ (Sum.inl 0) (fun x => A x + x (Sum.inl 0) • c) =
      ∂_ (Sum.inl 0) A + (fun x => c) := by
    funext x ν
    rw [SpaceTime.deriv_eq, fderiv_fun_add ha.differentiableAt (by fun_prop),
      fderiv_smul_const (by fun_prop)]
    simp [Lorentz.Vector.coordCLM, SpaceTime.deriv_eq]
  have diff_b (i : Fin d) : ∂_ (Sum.inr i) (fun x => A x + x (Sum.inl 0) • c) =
      ∂_ (Sum.inr i) A := by
    funext x ν
    rw [SpaceTime.deriv_eq, fderiv_fun_add ha.differentiableAt (by fun_prop),
      fderiv_smul_const (by fun_prop)]
    simp [Lorentz.Vector.coordCLM, SpaceTime.deriv_eq]
  have hdiff (μ ν : Fin 1 ⊕ Fin d) :
      ∂_ μ (fun x => A x + x (Sum.inl 0) • c) x ν =
      ∂_ μ A x ν + if μ = Sum.inl 0 then c ν else 0 := by
    match μ with
    | Sum.inl 0 => simp [diff_a]
    | Sum.inr i => simp [diff_b i]
  rw [kineticTerm_eq_sum_potential, kineticTerm_eq_sum_potential]
  simp only [hdiff]
  have key (μ ν : Fin 1 ⊕ Fin d) :
      η μ μ * η ν ν * (∂_ μ A x ν + if μ = Sum.inl 0 then c ν else 0) ^ 2 -
        (∂_ μ A x ν + if μ = Sum.inl 0 then c ν else 0) *
          (∂_ ν A x μ + if ν = Sum.inl 0 then c μ else 0) =
      (η μ μ * η ν ν * ∂_ μ A x ν ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) +
        ((if μ = Sum.inl 0 then 2 * (c ν * η μ μ * η ν ν * ∂_ μ A x ν) +
            η μ μ * η ν ν * c ν ^ 2 - c ν * ∂_ ν A x μ else 0) -
          (if ν = Sum.inl 0 then c μ * ∂_ μ A x ν else 0) -
          (if μ = Sum.inl 0 then c ν else 0) * (if ν = Sum.inl 0 then c μ else 0)) := by
    split_ifs <;> ring
  simp only [key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_ite, ite_mul,
    mul_zero, zero_mul, inl_0_inl_0, one_mul, mul_one, two_mul, add_mul, mul_add]
  ring

/-!

## B. Variational gradient of the kinetic term

We define the variational gradient of the kinetic term, which is the left-hand side
of Gauss's law and Ampère's law in vacuum.

-/

/-- The variational gradient of the kinetic term of an electromagnetic potential. -/
noncomputable def gradKineticTerm {d} (𝓕 : FreeSpace) (A : ElectromagneticPotential d) :
    SpaceTime d → Lorentz.Vector d :=
  (δ (q':=A), ∫ x, kineticTerm 𝓕 ⟨q'⟩ x)

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
  change HasVarGradientAt (fun A' x => ElectromagneticPotential.kineticTerm 𝓕 ⟨A'⟩ x) _ A
  conv =>
    enter [1, A', x]
    rw [kineticTerm_eq_sum_potential]
  let F : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) → (SpaceTime d → Lorentz.Vector d) →
    SpaceTime d → ℝ := fun (μ, ν) A' x =>
        (η μ μ * η ν ν * ∂_ μ A' x ν ^ 2 - ∂_ μ A' x ν * ∂_ ν A' x μ)
  have F_h (μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) :=
    HasVarAdjDerivAt.congr (G := F μν)
      (HasVarAdjDerivAt.add _ _ _ _ _
        (HasVarAdjDerivAt.const_mul _ _ A
          (HasVarAdjDerivAt.mul _ _ _ _ A (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
            (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)) (c := η μν.1 μν.1 * η μν.2 μν.2))
        (HasVarAdjDerivAt.neg _ _ A
          (HasVarAdjDerivAt.mul _ _ _ _ A (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
            (deriv_hasVarAdjDerivAt μν.2 μν.1 A hA))))
      (fun φ _ => funext fun x => by
        simp [F]
        ring)
  have hF_mul := HasVarAdjDerivAt.const_mul _ _ A
    (HasVarAdjDerivAt.congr (G := fun A' x => ∑ μ, ∑ ν, F (μ, ν) A' x)
      (HasVarAdjDerivAt.sum _ _ A hA F_h)
      (fun φ _ => funext fun x => Fintype.sum_prod_type fun μν => F μν φ x))
    (c := -1/(2 * 𝓕.μ₀))
  change HasVarGradientAt (fun A' x => -1 / (2 * 𝓕.μ₀) * ∑ μ, ∑ ν, F (μ, ν) A' x) _ A
  exact HasVarGradientAt.intro _ hF_mul rfl

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
        refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
        simp only [mul_one, neg_smul, neg_add_rev, neg_neg, mul_neg]
        ring_nf
      _ = ∑ (μ : (Fin 1 ⊕ Fin d)), ∑ (ν : (Fin 1 ⊕ Fin d)),
      ((- 2 * (fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / (2 * 𝓕.μ₀)) * ∂_ μ A x' ν) x)
        (Lorentz.Vector.basis μ) +
      ((fderiv ℝ (fun x' => -1 / (2 * 𝓕.μ₀) * ∂_ ν A x' μ) x) (Lorentz.Vector.basis μ))) •
        Lorentz.Vector.basis ν +
        (fderiv ℝ (fun x' => -1 / (2 * 𝓕.μ₀) * ∂_ μ A x' ν) x) (Lorentz.Vector.basis ν) •
          Lorentz.Vector.basis μ) := by
        refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
        module
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
        refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
        rw [← add_smul]
        ring_nf
      _ = ∑ (ν : (Fin 1 ⊕ Fin d)), ∑ (μ : (Fin 1 ⊕ Fin d)),
        (1 / (𝓕.μ₀) * (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
        rw [fderiv_const_mul (by fun_prop), fderiv_const_mul (by fun_prop)]
        simp [SpaceTime.deriv_eq]
        ring_nf

/-!

### B.3. Variational gradient as sums over the components of the field strength tensor

We rewrite the variational gradient as a simple double sum over the
components of the field strength tensor.

-/

lemma gradKineticTerm_eq_fieldStrength {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (ha : ContDiff ℝ ∞ A) :
    A.gradKineticTerm 𝓕 x = ∑ (ν : (Fin 1 ⊕ Fin d)), (1/𝓕.μ₀ * η ν ν) •
    (∑ (μ : (Fin 1 ⊕ Fin d)), (∂_ μ (fun x => toScalar {A.toFieldStrength x | [μ] [ν]}ᵀ) x))
    • Lorentz.Vector.basis ν := by
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
      ((1/𝓕.μ₀ * η ν ν) * (∂_ μ (fun x => toScalar {A.toFieldStrength x | [μ] [ν]}ᵀ) x)) •
          Lorentz.Vector.basis ν := by
        refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
        congr 2
        conv_rhs =>
          simp only [toFieldStrength_eval_apply_eq_single]
          rw [SpaceTime.deriv_eq, fderiv_fun_sub (by fun_prop) (by fun_prop),
            fderiv_const_mul (by fun_prop), fderiv_const_mul (by fun_prop)]
        simp [SpaceTime.deriv_eq]
    _ = ∑ (ν : (Fin 1 ⊕ Fin d)), (1/𝓕.μ₀ * η ν ν) •
        (∑ (μ : (Fin 1 ⊕ Fin d)), (∂_ μ (fun x => toScalar {A.toFieldStrength x | [μ] [ν]}ᵀ) x))
        • Lorentz.Vector.basis ν := by
        apply Finset.sum_congr rfl (fun ν _ => ?_)
        rw [← Finset.sum_smul, ← Finset.mul_sum, ← smul_smul]

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
  rw [gradKineticTerm_eq_fieldStrength A x ha, Fintype.sum_sum_type, Fin.sum_univ_one]
  congr 1
  · rw [smul_smul]
    congr 1
    rw [div_electricField_eq_toFieldStrength_eval]
    simp only [one_div, Fin.isValue, inl_0_inl_0, mul_one, mul_inv_rev,
      toTimeAndSpace_symm_apply_time_space]
    field_simp
    apply ha.of_le (ENat.LEInfty.out)
  · congr
    funext j
    simp only [one_div, inr_i_inr_i, mul_neg, mul_one, neg_smul]
    rw [curl_magneticFieldMatrix_eq_electricField_toFieldStrength_eval, smul_smul, ← neg_smul]
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
  simp only [magneticField_curl_eq_magneticFieldMatrix A (ha.of_le ENat.LEInfty.out)]
/-!

### B.5. Linearity properties of the variational gradient

-/

lemma gradKineticTerm_add {d} {𝓕 : FreeSpace} (A1 A2 : ElectromagneticPotential d)
    (hA1 : ContDiff ℝ ∞ A1) (hA2 : ContDiff ℝ ∞ A2) :
    (A1 + A2).gradKineticTerm 𝓕 = A1.gradKineticTerm 𝓕 + A2.gradKineticTerm 𝓕 := by
  funext x
  rw [gradKineticTerm_eq_fieldStrength (A1 + A2) x (hA1.add hA2)]
  simp only [Pi.add_apply]
  rw [gradKineticTerm_eq_fieldStrength A1 x hA1, gradKineticTerm_eq_fieldStrength A2 x hA2,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl (fun ν _ => ?_)
  rw [← smul_add, ← add_smul, ← Finset.sum_add_distrib]
  congr
  funext μ
  rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, SpaceTime.deriv_eq]
  conv_lhs =>
    enter [1, 2, x]
    rw [toFieldStrength_eval_add _ _ _ (hA1.differentiable (by simp))
      (hA2.differentiable (by simp))]
  rw [fderiv_fun_add
    (toFieldStrength_eval_differentiable (hA1.of_le ENat.LEInfty.out)).differentiableAt
    (toFieldStrength_eval_differentiable (hA2.of_le ENat.LEInfty.out)).differentiableAt]
  rfl

lemma gradKineticTerm_smul {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (c : ℝ) :
    (c • A).gradKineticTerm 𝓕 = c • A.gradKineticTerm 𝓕 := by
  funext x
  rw [gradKineticTerm_eq_fieldStrength (c • A) x (hA.const_smul c)]
  simp only [Pi.smul_apply]
  rw [gradKineticTerm_eq_fieldStrength A x hA, Finset.smul_sum]
  apply Finset.sum_congr rfl (fun ν _ => ?_)
  conv_rhs => rw [smul_comm]
  congr 1
  rw [smul_smul]
  congr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun μ _ => ?_)
  conv_rhs =>
    rw [SpaceTime.deriv_eq]
    change (c • fderiv ℝ (fun x => toScalar {A.toFieldStrength x | [μ] [ν]}ᵀ) x)
      (Lorentz.Vector.basis μ)
    rw [← fderiv_const_smul
      (toFieldStrength_eval_differentiable <| hA.of_le (ENat.LEInfty.out)).differentiableAt,
      ← SpaceTime.deriv_eq]
  congr
  funext x
  rw [toFieldStrength_eval_smul _ _ _ (hA.differentiable (by simp))]
  rfl

/-!

### B.6. HasVarGradientAt for the variational gradient

-/

lemma kineticTerm_hasVarGradientAt {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) :
    HasVarGradientAt (fun A => kineticTerm 𝓕 ⟨A⟩) (A.gradKineticTerm 𝓕) A := by
  rw [gradKineticTerm_eq_sum_fderiv A hA]
  change HasVarGradientAt (fun A' x => ElectromagneticPotential.kineticTerm 𝓕 ⟨A'⟩ x) _ A
  conv =>
    enter [1, A', x]
    rw [kineticTerm_eq_sum_potential]
  let F : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) → (SpaceTime d → Lorentz.Vector d) →
    SpaceTime d → ℝ := fun (μ, ν) A' x =>
        (η μ μ * η ν ν * ∂_ μ A' x ν ^ 2 - ∂_ μ A' x ν * ∂_ ν A' x μ)
  have F_h (μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) :=
    HasVarAdjDerivAt.congr (G := F μν)
      (HasVarAdjDerivAt.add _ _ _ _ _
        (HasVarAdjDerivAt.const_mul _ _ A
          (HasVarAdjDerivAt.mul _ _ _ _ A (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
            (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)) (c := η μν.1 μν.1 * η μν.2 μν.2))
        (HasVarAdjDerivAt.neg _ _ A
          (HasVarAdjDerivAt.mul _ _ _ _ A (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
            (deriv_hasVarAdjDerivAt μν.2 μν.1 A hA))))
      (fun φ _ => funext fun x => by
        simp [F]
        ring)
  have hF_mul := HasVarAdjDerivAt.const_mul _ _ A
    (HasVarAdjDerivAt.congr (G := fun A' x => ∑ μ, ∑ ν, F (μ, ν) A' x)
      (HasVarAdjDerivAt.sum _ _ A hA F_h)
      (fun φ _ => funext fun x => Fintype.sum_prod_type fun μν => F μν φ x))
    (c := -1/(2 * 𝓕.μ₀))
  change HasVarGradientAt (fun A' x => -1 / (2 * 𝓕.μ₀) * ∑ μ, ∑ ν, F (μ, ν) A' x) _ A
  exact HasVarGradientAt.intro _ hF_mul rfl

/-!

### B.7. Gradient of the kinetic term in terms of the tensor derivative

-/

attribute [-simp] Nat.reduceAdd Nat.reduceSucc Fin.isValue in
lemma gradKineticTerm_eq_tensorDeriv {d} {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (x : SpaceTime d)
    (hA : ContDiff ℝ ∞ A) (ν : Fin 1 ⊕ Fin d) :
    A.gradKineticTerm 𝓕 x ν = η ν ν * ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
    (permT id (IsReindexing.auto) {(1/ 𝓕.μ₀ : ℝ) •
      tensorDeriv A.toFieldStrength x | κ κ ν'}ᵀ)) ν := by
  trans η ν ν * (Lorentz.Vector.basis.repr
    ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
    (permT id (IsReindexing.auto) {(1/ 𝓕.μ₀ : ℝ) • tensorDeriv A.toFieldStrength x | κ κ ν'}ᵀ))) ν
  swap
  · simp [Lorentz.Vector.basis_repr_apply]
  simp [Lorentz.Vector.basis_eq_map_tensor_basis]
  rw [permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_rhs =>
    enter [2, 2, 2, μ]
    rw [tensorDeriv_toTensor_basis_repr (by fun_prop)]
    enter [2, x]
    rw [toFieldStrength_tensor_basis_repr_eq_eval]
  conv_lhs =>
    rw [gradKineticTerm_eq_fieldStrength A x hA]
    simp [Lorentz.Vector.apply_sum]
  ring_nf
  rfl

end ElectromagneticPotential

end Electromagnetism
