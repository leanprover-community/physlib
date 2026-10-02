/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Distributional.VectorPotential
public import Physlib.Electromagnetism.Distributional.ScalarPotential
public import Physlib.Electromagnetism.Distributional.FieldStrength
/-!

# The Electric Field

## i. Overview

The electric field is defined in terms of the electromagnetic potential `A` as
`E = - ∇ φ - ∂ₜ \vec A`.

In this module we define the electric field, and prove lemmas about it.

## ii. Key results

- `DistElectromagneticPotential.electricField` : The electric field for
  electromagnetic potentials which are distributions.

## iii. Table of contents

- A. Electric field for distributions

## iv. References

* None.
-/

@[expose] public section
namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor

/-!

## A. Electric field for distributions

-/

namespace DistElectromagneticPotential
open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix SchwartzMap Lorentz
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-- The electric field of an electromagnetic potential which is a distribution. -/
noncomputable def electricField {d} (c : SpeedOfLight) :
    DistElectromagneticPotential d →ₗ[ℝ]
    (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun A := - Space.distSpaceGrad (A.scalarPotential c) -
    Space.distTimeDeriv (A.vectorPotential c)
  map_add' A1 A2 := by
    ext ε i
    simp only [map_add, neg_add_rev, FunLike.coe_sub, Pi.sub_apply,
      add_apply, _root_.neg_apply, PiLp.sub_apply, PiLp.add_apply,
      PiLp.neg_apply]
    ring
  map_smul' r A := by
    ext ε i
    simp only [map_smul, FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply,
      _root_.neg_apply, Pi.smul_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply,
      smul_eq_mul, Real.ringHom_apply]
    ring

lemma electricField_eq_fieldStrength {d} {c : SpeedOfLight}
    (A : DistElectromagneticPotential d) (ε : 𝓢(Time × Space d, ℝ))
    (i : Fin d) : A.electricField c ε i = - c * (Vector.basis.tensorProduct Vector.basis).repr
      (distTimeSlice c (A.fieldStrength) ε) (Sum.inl 0, Sum.inr i) := by
  simp only [distTimeSlice_apply, Fin.isValue, fieldStrength_basis_repr_eq_single, inl_0_inl_0,
    one_mul, inr_i_inr_i, neg_mul, sub_neg_eq_add]
  simp only [electricField, scalarPotential, Vector.temporalCLM, Fin.isValue, map_smul,
    ContinuousLinearMap.comp_smulₛₗ, Real.ringHom_apply, LinearMap.coe_mk, AddHom.coe_mk,
    vectorPotential, Vector.spatialCLM, Space.distTimeDeriv_apply_CLM, FunLike.coe_sub,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_mk', Pi.sub_apply,
    _root_.neg_apply, FunLike.coe_smul, Pi.smul_apply,
    Function.comp_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, Space.distSpaceGrad_apply,
    Space.distSpaceDeriv_apply_CLM, LinearMap.coe_toContinuousLinearMap', smul_eq_mul,
    ← distTimeSlice_apply, distTimeSlice_distDeriv_inl, one_div, Vector.apply_smul,
    distTimeSlice_distDeriv_inr]
  field_simp
  ring

end DistElectromagneticPotential

end Electromagnetism
