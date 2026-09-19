/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Distributional.MagneticField
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

- `DistElectromagneticPotential.gradKineticTerm` is the variational gradient of the kinetic term
  for distributional electromagnetic potentials.

## iii. Table of contents

- A. The gradient of the kinetic term for distributions
  - A.1. The gradient of the kinetic term as a tensor

## iv. References

* https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html. [ref: ucsd_ph130a_node452]
-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor ContDiff Physlib

/-!

## A. The gradient of the kinetic term for distributions

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
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
      simp only [one_div, map_add, Lorentz.Vector.apply_add, ← add_smul]
      ring_nf
    map_smul' r ε := by
      simp [Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
      ring_nf
    cont := by fun_prop}
  map_add' A1 A2 := by
    ext1 ε
    simp only [one_div, map_add, add_apply, Lorentz.Vector.apply_add,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
    simp only [← add_smul]
    ring_nf
  map_smul' r A := by
    ext1 ε
    simp only [one_div, map_smul, _root_.smul_apply, Lorentz.Vector.apply_smul,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
    simp [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
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

### A.1. The gradient of the kinetic term as a tensor

-/

attribute [-simp] Nat.reduceAdd Nat.reduceSucc Fin.isValue in
lemma gradKineticTerm_eq_distTensorDeriv {d} {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d) (ε : 𝓢(SpaceTime d, ℝ)) (ν : Fin 1 ⊕ Fin d) :
    A.gradKineticTerm 𝓕 ε ν = η ν ν * ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
    (permT id (IsReindexing.auto) {(1/ 𝓕.μ₀ : ℝ) •
    distTensorDeriv A.fieldStrength ε | κ κ ν'}ᵀ)) ν := by
  trans η ν ν * (Lorentz.Vector.basis.repr
    ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
    (permT id (IsReindexing.auto) {(1/ 𝓕.μ₀ : ℝ) • distTensorDeriv A.fieldStrength ε | κ κ ν'}ᵀ))) ν
  swap
  · rfl
  simp [Lorentz.Vector.basis_eq_map_tensor_basis]
  rw [permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    rw [gradKineticTerm_eq_fieldStrength A ε]
    simp [Lorentz.Vector.apply_sum]
  ring_nf
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [distTensorDeriv_toTensor_basis_repr]
  trans (Tensor.basis _).repr (Tensorial.toTensor (distDeriv μ (A.fieldStrength) ε))
      (fun | 0 => μ | 1 => ν)
  · generalize (distDeriv μ (A.fieldStrength) ε) = t at *
    rw [Tensorial.basis_toTensor_apply, Tensorial.basis_map_prod]
    simp only [Basis.repr_reindex]
    rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex]
    have hb : (((Lorentz.Vector.basis (d := d)).reindex
        Lorentz.Vector.indexEquiv.symm).tensorProduct
        (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
        ((Lorentz.Vector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
        (Lorentz.Vector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
      ext ⟨i, j⟩
      simp
    rw [hb, Finsupp.equivMapDomain_apply, Module.Basis.repr_reindex_apply]
    rfl
  apply congr
  · simp
    rfl
  funext x
  fin_cases x <;>
    simp [Function.comp_apply, ComponentIdx.prod, ComponentIdx.DropPairSection.ofFinEquiv,
      ComponentIdx.DropPairSection.ofFin]
  · intro _ h
    exact absurd (by decide) h
  · split_ifs with h1 h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide)
    · rfl

end DistElectromagneticPotential
end Electromagnetism
