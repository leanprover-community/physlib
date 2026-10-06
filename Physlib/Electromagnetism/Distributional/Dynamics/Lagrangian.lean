/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Distributional.Dynamics.CurrentDensity
public import Physlib.Electromagnetism.Distributional.Dynamics.KineticTerm
/-!

# The Lagrangian in electromagnetism

## i. Overview

In this module we define the Lagrangian density for the electromagnetic field in
presence of a current density. We prove properties of this lagrangian density,
and find it's variational gradient.

The lagrangian density is given by
`L = -1/(4 μ₀) F_{μν} F^{μν} - A_μ J^μ`

In this implementation we set `μ₀ = 1`. It is a TODO to introduce this constant.

## ii. Key results

- `gradFreeCurrentPotential` : The variational gradient of the free current potential.
- `gradLagrangian` : The variational gradient of the lagrangian density.

## iii. Table of contents

- A. The gradient of the lagrangian density for distributions
  - A.1. The gradient of the free current potential
    - A.1.1. Free current potential as a tensor
  - A.2. The gradient of the lagrangian density
    - A.2.1. The lagrangian gradient as a tensor

## iv. References

* https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html. [ref: ucsd_ph130a_node452]
* https://ph.qmul.ac.uk/sites/default/files/EMT10new.pdf. [ref: qmul_emt10_notes]
-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor ContDiff

/-!

## A. The gradient of the lagrangian density for distributions

-/

namespace DistElectromagneticPotential
open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
open InnerProductSpace
open Lorentz.Vector SchwartzMap
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one
/-!

### A.1. The gradient of the free current potential

We define this through the lemma `gradFreeCurrentPotential_eq_sum_basis`
-/

/-- The variational gradient of the free current potential for distributional potentials. -/
noncomputable def gradFreeCurrentPotential {d} :
    DistLorentzCurrentDensity d →ₗ[ℝ] ((SpaceTime d) →d[ℝ] Lorentz.Vector d) where
  toFun J := {
    toFun ε := ∑ μ, (η μ μ • (J ε μ) • Lorentz.Vector.basis μ)
    map_add' ε₁ ε₂ := by
      simp [Finset.sum_add_distrib, add_smul]
    map_smul' r ε := by
      simp only [map_smul, apply_smul, smul_smul, Real.ringHom_apply, Finset.smul_sum]
      congr
      funext i
      ring_nf
    cont := by fun_prop
  }
  map_add' J₁ J₂ := by
    ext1 ε
    simp [Finset.sum_add_distrib, add_smul]
  map_smul' r J := by
    ext1 ε
    simp [Finset.smul_sum, smul_smul]
    congr
    funext i
    ring_nf

lemma gradFreeCurrentPotential_eq_sum_basis {d}
    (J : DistLorentzCurrentDensity d) (ε : 𝓢(SpaceTime d, ℝ)) :
    (gradFreeCurrentPotential J) ε =
    (∑ μ, (η μ μ • (J ε μ) • Lorentz.Vector.basis μ)) := rfl

lemma gradFreeCurrentPotential_sum_inl_0 (𝓕 : FreeSpace) {d}
    (J : DistLorentzCurrentDensity d) (ε : 𝓢(SpaceTime d, ℝ)) :
    (gradFreeCurrentPotential J) ε (Sum.inl 0) =
    𝓕.c * (distTimeSlice 𝓕.c).symm (J.chargeDensity 𝓕.c) ε := by
  simp only [gradFreeCurrentPotential, LinearMap.coe_mk, AddHom.coe_mk, Fin.isValue,
    ContinuousLinearMap.coe_mk', apply_sum, apply_smul, Lorentz.Vector.basis_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, inl_0_inl_0, one_mul,
    DistLorentzCurrentDensity.chargeDensity, one_div, temporalCLM, map_smul,
    FunLike.coe_smul, Pi.smul_apply, distTimeSlice_symm_apply,
    ContinuousLinearMap.coe_comp, LinearMap.coe_toContinuousLinearMap', Function.comp_apply,
    smul_eq_mul, ne_eq, SpeedOfLight.val_ne_zero, not_false_eq_true, mul_inv_cancel_left₀]
  rw [← distTimeSlice_symm_apply]
  simp

lemma gradFreeCurrentPotential_sum_inr_i (𝓕 : FreeSpace) {d}
    (J : DistLorentzCurrentDensity d) (ε : 𝓢(SpaceTime d, ℝ)) (i : Fin d) :
    (gradFreeCurrentPotential J) ε (Sum.inr i) =
    - (distTimeSlice 𝓕.c).symm (J.currentDensity 𝓕.c) ε i := by
  simp only [gradFreeCurrentPotential, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_mk',
    apply_sum, apply_smul, Lorentz.Vector.basis_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, inr_i_inr_i,
    DistLorentzCurrentDensity.currentDensity, spatialCLM, distTimeSlice_symm_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [← distTimeSlice_symm_apply]
  simp

/-!

#### A.1.1. Free current potential as a tensor

-/

lemma gradFreeCurrentPotential_eq_tensor {d}
    (J : DistLorentzCurrentDensity d) (ε : 𝓢(SpaceTime d, ℝ))
    (ν : Fin 1 ⊕ Fin d) :
    gradFreeCurrentPotential J ε ν = η ν ν * ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
    (permT id (IsReindexing.auto) {J ε | ν'}ᵀ)) ν:= by
  trans η ν ν * (Lorentz.Vector.basis.repr ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
    (permT id (IsReindexing.auto) {J ε | ν'}ᵀ))) ν
  swap
  · simp [Lorentz.Vector.basis_repr_apply]
  simp [Lorentz.Vector.basis_repr_apply]
  rw [gradFreeCurrentPotential_eq_sum_basis]
  simp [Lorentz.Vector.apply_sum]

/-!

### D.2. The gradient of the lagrangian density

Defined through `gradLagrangian_eq_kineticTerm_sub`.

-/

/-- The variational gradient of lagrangian for an electromagnetic potential which is
  a distribution. -/
noncomputable def gradLagrangian {d} (𝓕 : FreeSpace) (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) : ((SpaceTime d) →d[ℝ] Lorentz.Vector d) :=
  A.gradKineticTerm 𝓕 - gradFreeCurrentPotential J

lemma gradLagrangian_sum_inl_0 {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d) (J : DistLorentzCurrentDensity d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    A.gradLagrangian 𝓕 J ε (Sum.inl 0) =
    (1/(𝓕.μ₀ * 𝓕.c) * (distTimeSlice 𝓕.c).symm (Space.distSpaceDiv (A.electricField 𝓕.c)) ε)
    - 𝓕.c * (distTimeSlice 𝓕.c).symm (J.chargeDensity 𝓕.c) ε := by
  simp [gradLagrangian, gradKineticTerm_sum_inl_eq, gradFreeCurrentPotential_sum_inl_0 𝓕]

lemma gradLagrangian_sum_inr_i {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d) (J : DistLorentzCurrentDensity d)
    (ε : 𝓢(SpaceTime d, ℝ)) (i : Fin d) :
    A.gradLagrangian 𝓕 J ε (Sum.inr i) =
    𝓕.μ₀⁻¹ * (1 / 𝓕.c ^ 2 *
      (distTimeSlice 𝓕.c).symm (Space.distTimeDeriv (A.electricField 𝓕.c)) ε i -
      ∑ j, ((PiLp.basisFun 2 ℝ (Fin d)).tensorProduct (PiLp.basisFun 2 ℝ (Fin d))).repr
        ((distTimeSlice 𝓕.c).symm (Space.distSpaceDeriv j (A.magneticFieldMatrix 𝓕.c)) ε) (j, i)) +
    (distTimeSlice 𝓕.c).symm (J.currentDensity 𝓕.c) ε i := by
  simp [gradLagrangian, gradKineticTerm_sum_inr_eq, gradFreeCurrentPotential_sum_inr_i 𝓕]

/-!

#### A.2.1. The lagrangian gradient as a tensor

-/

attribute [-simp] Nat.reduceAdd Nat.reduceSucc Fin.isValue in
lemma gradLagrangian_eq_tensor {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d) (J : DistLorentzCurrentDensity d)
    (ε : 𝓢(SpaceTime d, ℝ)) (ν : Fin 1 ⊕ Fin d) :
    A.gradLagrangian 𝓕 J ε ν =
    η ν ν * ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
    (permT id (IsReindexing.auto) {((1/ 𝓕.μ₀ : ℝ) • (distTensorDeriv A.fieldStrength ε) | κ κ ν') +
    - (J ε | ν')}ᵀ)) ν := by
  rw [gradLagrangian]
  simp only [FunLike.coe_sub, Pi.sub_apply, apply_sub, one_div,
    map_smul, map_neg, map_add, permT_permT, CompTriple.comp_eq, apply_add,
    apply_smul, Lorentz.Vector.neg_apply]
  rw [gradKineticTerm_eq_distTensorDeriv, gradFreeCurrentPotential_eq_tensor J ε ν]
  simp only [one_div, map_smul, apply_smul,
    permT_id_self, LinearEquiv.symm_apply_apply]
  ring_nf
  congr
  rw [permT_congr_eq_id]
  simp only [LinearEquiv.symm_apply_apply]
  funext i
  fin_cases i
  simp

end DistElectromagneticPotential
end Electromagnetism
