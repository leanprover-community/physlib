/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Basic
public import Mathlib.Tactic.LinearCombination
/-!
# The definition of the solution B₃ and properties thereof

We define `B₃` and show that it is a double point of the cubic.

# References

* The main reference for the material in this file. [ref: Allanach:2021yjy]
-/

@[expose] public section

namespace MSSMACC
open MSSMCharges
open MSSMACCs
open BigOperators

/-- `B₃` is the charge which is $B-L$ in all families, but with the third
family of the opposite sign. -/
def B₃AsCharge : MSSMACC.Charges := toSpecies.symm
  ⟨fun s => fun i =>
    match s, i with
    | 0, 0 => 1
    | 0, 1 => 1
    | 0, 2 => - 1
    | 1, 0 => - 1
    | 1, 1 => - 1
    | 1, 2 => 1
    | 2, 0 => - 1
    | 2, 1 => - 1
    | 2, 2 => 1
    | 3, 0 => - 3
    | 3, 1 => - 3
    | 3, 2 => 3
    | 4, 0 => 3
    | 4, 1 => 3
    | 4, 2 => - 3
    | 5, 0 => 3
    | 5, 1 => 3
    | 5, 2 => - 3,
  fun s =>
    match s with
    | 0 => -3
    | 1 => 3⟩

/-- `B₃` as a solution. -/
def B₃ : MSSMACC.Sols :=
  MSSMACC.AnomalyFreeMk B₃AsCharge (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)

lemma B₃_val : B₃.val = B₃AsCharge := by
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma doublePoint_B₃_B₃ (R : MSSMACC.LinSols) : cubeTriLin B₃.val B₃.val R.val = 0 := by
  simp only [cubeTriLin, TriLinearSymm.mk₃_toFun_apply_apply, cubeTriLinToFun]
  rw [sum_MSSMSpecies_numberCharges_eq_expand]
  rw [B₃_val]
  rw [B₃AsCharge]
  repeat rw [toSMSpecies_toSpecies_inv]
  rw [Hd_toSpecies_inv, Hu_toSpecies_inv]
  simp only [mul_one, Fin.isValue, toSMSpecies_apply, one_mul, mul_neg, neg_neg, neg_mul, Hd_apply,
    Fin.reduceFinMk, Hu_apply]
  have hLin := R.linearSol
  simp only [MSSMACC_linearACCs] at hLin
  have h0 := hLin ⟨0, by simp⟩
  have h2 := hLin ⟨2, by simp⟩
  simp only [accGrav, LinearMap.coe_mk, AddHom.coe_mk, accSU3] at h0 h2
  rw [sum_MSSMSpecies_numberCharges_eq_expand] at h0 h2
  simp only [Fin.isValue, toSMSpecies_apply, Nat.reduceMul, Hd_apply, Fin.reduceFinMk,
    Hu_apply] at h0 h2
  linear_combination (norm := ring_nf) 9 * (h0) - 24 * (h2)

end MSSMACC
