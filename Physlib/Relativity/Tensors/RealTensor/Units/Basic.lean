/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Basic
/-!

# Unit tensors for real Lorentz tensors

## i. Overview

This file computes the unit tensors of `realLorentzTensor` in the standard covariant and
contravariant bases.

## ii. Key results

- `realLorentzTensor.unitTensor_repr_apply` identifies the standard-basis components of either
  real Lorentz unit tensor with the Kronecker delta.

## iii. Table of contents

- A. Basis components

## iv. References

* None.
-/

@[expose] public section

open Module TensorProduct

noncomputable section

namespace realLorentzTensor

open TensorSpecies Tensor

/-!

## A. Basis components

-/

set_option backward.isDefEq.respectTransparency false in
/-- In the standard contravariant and covariant bases, either real Lorentz unit tensor has
Kronecker-delta components. -/
lemma unitTensor_repr_apply {d : ℕ} (c : Color)
    (φ : ComponentIdx (S := realLorentzTensor d) ![(realLorentzTensor d).τ c, c]) :
    (Tensor.basis _).repr (unitTensor (S := realLorentzTensor d) c) φ =
      if φ 0 = φ 1 then 1 else 0 := by
  cases c with
  | up =>
      rw [unitTensor_basis_repr,
        show ((realLorentzTensor d).unit Color.up) (1 : ℝ) = Lorentz.preCoContrUnitVal d from
          Lorentz.preCoContrUnit_apply_one]
      rw [Lorentz.preCoContrUnitVal_expand_tmul]
      simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
        Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
      rw [Finset.sum_eq_single (φ 0)] <;> aesop
  | down =>
      rw [unitTensor_basis_repr,
        show ((realLorentzTensor d).unit Color.down) (1 : ℝ) = Lorentz.preContrCoUnitVal d from
          Lorentz.preContrCoUnit_apply_one]
      rw [Lorentz.preContrCoUnitVal_expand_tmul]
      simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
        Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
      rw [Finset.sum_eq_single (φ 0)] <;> aesop

end realLorentzTensor
