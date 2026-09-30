/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Dynamics.Lagrangian
/-!

# The Hamiltonian in electromagnetism

## i. Overview

In this module we define the canonical momentum and the Hamiltonian for the
electromagnetic field in presence of a current density. We prove properties of these
quantities, and express the Hamiltonian in terms of the electric and magnetic fields
in the case of three spatial dimensions.

## ii. Key results

- `canonicalMomentum` : The canonical momentum for the electromagnetic field in presence of a
  Lorentz current density.
- `hamiltonian` : The Hamiltonian for the electromagnetic field in presence of a
  Lorentz current density.
- `hamiltonian_eq_electricField_magneticField` : The Hamiltonian expressed
  in terms of the electric and magnetic fields.

## iii. Table of contents

- A. The canonical momentum
  - A.1. The canonical momentum in terms of the kinetic term
  - A.2. The canonical momentum in terms of the field strength tensor
  - A.3. The canonical momentum in terms of the electric field
- B. The Hamiltonian
  - B.1. The hamiltonian in terms of the vector potential
  - B.2. The hamiltonian in terms of the electric and magnetic fields

## iv. References

* https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html. [ref: ucsd_ph130a_node452]
* https://ph.qmul.ac.uk/sites/default/files/EMT10new.pdf. [ref: qmul_emt10_notes]
-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
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

attribute [-simp] Fin.succAbove_zero
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. The canonical momentum

We define the canonical momentum for the lagrangian
`L(A, ∂ A)` as gradient of `v ↦ L(A + t v, ∂ (A + t v)) - t * L(A + v, ∂(A + v))` at `v = 0`
This is equivalent to `∂ L/∂ (∂_0 A)`.

-/

/-- The canonical momentum associated with the lagrangian of an electromagnetic potential
  and a Lorentz current density. -/
noncomputable def canonicalMomentum (𝓕 : FreeSpace) (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) :
    SpaceTime d → Lorentz.Vector d := fun x =>
  gradient (fun (v : Lorentz.Vector d) =>
    lagrangian 𝓕 ⟨fun x => A x + x (Sum.inl 0) • v⟩ J x) 0
  - x (Sum.inl 0) • gradient (fun (v : Lorentz.Vector d) =>
    lagrangian 𝓕 ⟨fun x => A x + v⟩ J x) 0

/-!

### A.1. The canonical momentum in terms of the kinetic term

-/
lemma canonicalMomentum_eq_gradient_kineticTerm {d}
    {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (J : LorentzCurrentDensity d) :
    A.canonicalMomentum 𝓕 J = fun x =>
    gradient (fun (v : Lorentz.Vector d) =>
    kineticTerm 𝓕 ⟨fun x => A x + x (Sum.inl 0) • v⟩ x) 0:= by
  funext x
  apply ext_inner_right (𝕜 := ℝ)
  intro v
  rw [gradient, canonicalMomentum]
  simp only [Fin.isValue, toDual_symm_apply]
  rw [inner_sub_left, inner_smul_left]
  simp [gradient]
  conv_lhs =>
    enter [2]
    simp [lagrangian_add_const]
  have hx : DifferentiableAt ℝ (fun v => kineticTerm 𝓕 ⟨fun x => A x + x (Sum.inl 0) • v⟩ x) 0 := by
    simp only [kineticTerm_add_time_mul_const _ (hA.differentiable (by simp))]
    fun_prop
  conv_lhs =>
    enter [1]
    simp only [lagrangian, Fin.isValue, map_add, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_fun_sub hx (by simp [freeCurrentPotential]; fun_prop)]
    simp only [Fin.isValue, freeCurrentPotential, map_add, map_smul, _root_.add_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, fderiv_const_add,
      FunLike.coe_sub, Pi.sub_apply]
    rw [fderiv_const_mul (by fun_prop)]
  simp only [Fin.isValue, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
  simp

/-!

### A.2. The canonical momentum in terms of the field strength tensor

-/

lemma canonicalMomentum_eq {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (J : LorentzCurrentDensity d) :
    A.canonicalMomentum 𝓕 J = fun x => fun μ =>
      (1/𝓕.μ₀) * η μ μ • toScalar {A.toFieldStrength x | [μ] [Sum.inl 0]}ᵀ := by
  rw [canonicalMomentum_eq_gradient_kineticTerm A hA J]
  funext x
  apply ext_inner_right (𝕜 := ℝ)
  intro v
  simp [gradient]
  conv_rhs => rw [Lorentz.Vector.inner_eq_sum]
  simp only [toFieldStrength_eval_apply_eq_single]
  conv_lhs =>
    enter [1, 2, v]
    rw [kineticTerm_add_time_mul_const _ (hA.differentiable (by simp))]
  simp (disch := fun_prop) only [Fin.isValue, Finset.sum_sub_distrib, one_div,
    fderiv_const_add, fderiv_fun_add, fderiv_const_mul, fderiv_fun_sub, fderiv_fun_sum,
    fderiv_mul_const, fderiv_fun_pow]
  simp [Lorentz.Vector.coordCLM]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  congr
  ext μ
  linear_combination (-(v μ * 𝓕.μ₀⁻¹ * ∂_ μ A x (Sum.inl 0))) *
    minkowskiMatrix.η_apply_mul_η_apply_diag μ

/-!

### A.3. The canonical momentum in terms of the electric field

-/

lemma canonicalMomentum_eq_electricField {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (J : LorentzCurrentDensity d) :
    A.canonicalMomentum 𝓕 J = fun x => fun μ =>
      match μ with
      | Sum.inl 0 => 0
      | Sum.inr i => - (1/(𝓕.μ₀ * 𝓕.c)) * A.electricField 𝓕.c (x.time 𝓕.c) x.space i := by
  rw [canonicalMomentum_eq A hA J]
  funext x μ
  match μ with
  | Sum.inl 0 => simp [toFieldStrength_eval_diag_eq_zero]
  | Sum.inr i =>
  simp only [one_div, inr_i_inr_i, Fin.isValue, smul_eq_mul, neg_mul, one_mul, mul_neg, mul_inv_rev,
    neg_inj]
  rw [electricField_eq_toFieldStrength_eval (hA := hA.differentiable (by simp))]
  simp only [Fin.isValue, toTimeAndSpace_symm_apply_time_space, neg_mul, mul_neg]
  field_simp
  exact toFieldStrength_eval_antisymm A x (Sum.inr i) (Sum.inl 0)
/-!

## B. The Hamiltonian

-/

/-- The Hamiltonian associated with an electromagnetic potential
  and a Lorentz current density. -/
noncomputable def hamiltonian (𝓕 : FreeSpace) (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (x : SpaceTime d) : ℝ :=
    ∑ μ, A.canonicalMomentum 𝓕 J x μ * ∂_ (Sum.inl 0) A x μ - lagrangian 𝓕 A J x

/-!

### B.1. The hamiltonian in terms of the vector potential
-/

open Time

lemma hamiltonian_eq_electricField_vectorPotential {d} {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (hA : ContDiff ℝ 2 A)
    (J : LorentzCurrentDensity d) (x : SpaceTime d) :
    A.hamiltonian 𝓕 J x =
      - (1/ 𝓕.c.val^2 * 𝓕.μ₀⁻¹) * ∑ i, A.electricField 𝓕.c (x.time 𝓕.c) x.space i *
      (∂ₜ (A.vectorPotential 𝓕.c · x.space) (x.time 𝓕.c) i) - lagrangian 𝓕 A J x := by
  rw [hamiltonian]
  congr 1
  simp [Fintype.sum_sum_type, canonicalMomentum_eq_electricField A hA J]
  rw [Finset.mul_sum]
  congr
  funext i
  rw [SpaceTime.deriv_sum_inl 𝓕.c]
  rw [← Time.deriv_euclid]
  simp [vectorPotential, timeSlice]
  ring_nf
  congr
  rw [← Time.deriv_lorentzVector]
  rfl
  · exact (hA.differentiable (by simp)).comp (by fun_prop)
  · exact vectorPotential_differentiable_time A (hA.differentiable (by simp)) x.space
  · exact hA.differentiable (by simp)

lemma hamiltonian_eq_electricField_scalarPotential {d} {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (hA : ContDiff ℝ 2 A)
    (J : LorentzCurrentDensity d) (x : SpaceTime d) :
    A.hamiltonian 𝓕 J x =
      (1/ 𝓕.c.val^2 * 𝓕.μ₀⁻¹) * (‖A.electricField 𝓕.c (x.time 𝓕.c) x.space‖ ^ 2
      + ⟪A.electricField 𝓕.c (x.time 𝓕.c) x.space,
        Space.grad (A.scalarPotential 𝓕.c (x.time 𝓕.c) ·) x.space⟫_ℝ)
        - lagrangian 𝓕 A J x := by
  rw [hamiltonian_eq_electricField_vectorPotential A hA J x]
  congr 1
  conv_lhs =>
    enter [2, 2, i]
    rw [time_deriv_vectorPotential_eq_electricField]
  simp [mul_sub, Finset.sum_sub_distrib]
  rw [EuclideanSpace.norm_sq_eq]
  ring_nf
  congr 1
  · simp
  congr
  funext i
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-!

### B.2. The hamiltonian in terms of the electric and magnetic fields

-/

lemma hamiltonian_eq_electricField_magneticField (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (J : LorentzCurrentDensity d) (x : SpaceTime d) :
    A.hamiltonian 𝓕 J x = 1/2 * 𝓕.ε₀ * (‖A.electricField 𝓕.c (x.time 𝓕.c) x.space‖ ^ 2
      + 𝓕.c ^ 2 / 2 * ∑ i, ∑ j, ‖A.magneticFieldMatrix 𝓕.c (x.time 𝓕.c) x.space (i, j)‖ ^ 2)
      + 𝓕.ε₀ * ⟪A.electricField 𝓕.c (x.time 𝓕.c) x.space,
        Space.grad (A.scalarPotential 𝓕.c (x.time 𝓕.c) ·) x.space⟫_ℝ
      + A.scalarPotential 𝓕.c (x.time 𝓕.c) x.space * J.chargeDensity 𝓕.c (x.time 𝓕.c) x.space
      - ∑ i, A.vectorPotential 𝓕.c (x.time 𝓕.c) x.space i *
        J.currentDensity 𝓕.c (x.time 𝓕.c) x.space i := by
  rw [hamiltonian_eq_electricField_scalarPotential A hA J x]
  rw [lagrangian_eq_electric_magnetic A hA J x]
  simp [FreeSpace.c_sq 𝓕]
  field_simp
  ring

end ElectromagneticPotential

end Electromagnetism
