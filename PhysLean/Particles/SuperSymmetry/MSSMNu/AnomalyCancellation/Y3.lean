/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Basic
import Mathlib.Tactic.LinearCombination
/-!
# The definition of the solution Y₃ and properties thereof

We define $Y_3$ and show that it is a double point of the cubic.

# References

The main reference for the material in this file is:

- https://arxiv.org/pdf/2107.07926.pdf

-/

namespace MSSMACC
open MSSMCharges
open MSSMACCs
open BigOperators

/-- $Y_3$ is the charge which is hypercharge in all families, but with the third
family of the opposite sign. -/
def Y₃AsCharge : MSSMACC.Charges := toSpecies.symm
  ⟨fun s => fun i =>
    match s, i with
    | 0, 0 => 1
    | 0, 1 => 1
    | 0, 2 => - 1
    | 1, 0 => -4
    | 1, 1 => -4
    | 1, 2 => 4
    | 2, 0 => 2
    | 2, 1 => 2
    | 2, 2 => - 2
    | 3, 0 => -3
    | 3, 1 => -3
    | 3, 2 => 3
    | 4, 0 => 6
    | 4, 1 => 6
    | 4, 2 => - 6
    | 5, 0 => 0
    | 5, 1 => 0
    | 5, 2 => 0,
  fun s =>
    match s with
    | 0 => -3
    | 1 => 3⟩

/-- $Y_3$ as a solution. -/
def Y₃ : MSSMACC.Sols :=
  MSSMACC.AnomalyFreeMk Y₃AsCharge
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

lemma Y₃_val : Y₃.val = Y₃AsCharge := by
  rfl

lemma doublePoint_Y₃_Y₃ (R : MSSMACC.LinSols) :
    cubeTriLin Y₃.val Y₃.val R.val = 0 := by
  simp only [cubeTriLin, TriLinearSymm.mk₃_toFun_apply_apply, cubeTriLinToFun,
    MSSMSpecies_numberCharges]
  rw [Fin.sum_univ_three]
  rw [Y₃_val]
  rw [Y₃AsCharge]
  repeat rw [toSMSpecies_toSpecies_inv]
  rw [Hd_toSpecies_inv, Hu_toSpecies_inv]
  simp only [mul_one, Fin.isValue, toSMSpecies_apply, one_mul, mul_neg, neg_mul, neg_neg, mul_zero,
    zero_mul, add_zero, Hd_apply, Fin.reduceFinMk, Hu_apply]
  have hLin := R.linearSol
  simp only [MSSMACC_numberLinear, MSSMACC_linearACCs, Nat.reduceMul, Fin.isValue,
    Fin.reduceFinMk] at hLin
  have h3 := hLin 3
  simp only [Fin.isValue, Fin.sum_univ_three, Prod.mk_zero_zero, Prod.mk_one_one, LinearMap.coe_mk,
    AddHom.coe_mk] at h3
  linear_combination (norm := ring_nf) 6 * h3
  simp only [Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one, add_add_sub_cancel, add_neg_cancel]

end MSSMACC
