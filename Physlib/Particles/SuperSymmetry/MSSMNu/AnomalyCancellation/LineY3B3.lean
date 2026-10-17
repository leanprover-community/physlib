/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Y3
public import Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.B3
/-!
# The line through B₃ and Y₃

We give properties of lines through `B₃` and `Y₃`. We show that every point on this line
is a solution to the quadratic `lineY₃B₃Charges_quad` and a double point of the cubic
`lineY₃B₃_doublePoint`.

# References

* The main reference for the material in this file. [ref: Allanach:2021yjy]
-/

@[expose] public section

namespace MSSMACC
open MSSMCharges
open MSSMACCs
open BigOperators

/-- The line through $Y_3$ and $B_3$ as `LinSols`. -/
def lineY₃B₃Charges (a b : ℚ) : MSSMACC.LinSols := a • Y₃.1.1 + b • B₃.1.1

lemma lineY₃B₃Charges_val (a b : ℚ) :
    (lineY₃B₃Charges a b).val = a • Y₃.1.1.val + b • B₃.1.1.val := rfl

set_option backward.isDefEq.respectTransparency false in
lemma lineY₃B₃Charges_quad (a b : ℚ) : accQuad (lineY₃B₃Charges a b).val = 0 := by
  change accQuad (a • Y₃.val + b • B₃.val) = 0
  rw [accQuad, quadBiLin.toHomogeneousQuad_add, quadBiLin.toHomogeneousQuad.map_smul,
    quadBiLin.toHomogeneousQuad.map_smul, quadBiLin.map_smul₁, quadBiLin.map_smul₂, ← accQuad,
    quadSol Y₃.1, quadSol B₃.1, show quadBiLin Y₃.val B₃.val = 0 by with_unfolding_all rfl]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma lineY₃B₃Charges_cubic (a b : ℚ) : accCube (lineY₃B₃Charges a b).val = 0 := by
  change accCube (a • Y₃.val + b • B₃.val) = 0
  rw [accCube, cubeTriLin.toCubic_add, cubeTriLin.toCubic.map_smul, cubeTriLin.toCubic.map_smul,
    cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃, cubeTriLin.map_smul₁,
    cubeTriLin.map_smul₂, cubeTriLin.map_smul₃, ← cubicACC_apply, ← cubicACC_apply, Y₃.cubicSol,
    B₃.cubicSol, show cubeTriLin Y₃.val Y₃.val B₃.val = 0 by with_unfolding_all rfl,
    show cubeTriLin B₃.val B₃.val Y₃.val = 0 by with_unfolding_all rfl]
  simp

/-- The line through $Y_3$ and $B_3$ as `Sols`. -/
def lineY₃B₃ (a b : ℚ) : MSSMACC.Sols :=
  AnomalyFreeMk' (lineY₃B₃Charges a b) (lineY₃B₃Charges_quad a b) (lineY₃B₃Charges_cubic a b)

lemma lineY₃B₃_val (a b : ℚ) : (lineY₃B₃ a b).val = a • Y₃.val + b • B₃.val :=
  lineY₃B₃Charges_val a b

set_option backward.isDefEq.respectTransparency false in
lemma doublePoint_Y₃_B₃ (R : MSSMACC.LinSols) :
    cubeTriLin Y₃.val B₃.val R.val = 0 := by
  simp only [cubeTriLin, TriLinearSymm.mk₃_toFun_apply_apply, cubeTriLinToFun]
  rw [sum_MSSMSpecies_numberCharges_eq_expand, B₃_val, Y₃_val, B₃AsCharge, Y₃AsCharge]
  repeat rw [toSMSpecies_toSpecies_inv]
  rw [Hd_toSpecies_inv, Hu_toSpecies_inv, Hd_toSpecies_inv, Hu_toSpecies_inv]
  simp only [mul_one, Fin.isValue, toSMSpecies_apply, one_mul, mul_neg, neg_neg, neg_mul, zero_mul,
    add_zero, neg_zero, Hd_apply, Fin.reduceFinMk, Hu_apply]
  have hLin := R.linearSol
  simp only [MSSMACC_linearACCs] at hLin
  have h1 := hLin (1 : Fin 4)
  have h2 := hLin (2 : Fin 4)
  have h3 := hLin (3 : Fin 4)
  simp only [accSU2, LinearMap.coe_mk, AddHom.coe_mk, accSU3, accYY] at h1 h2 h3
  rw [sum_MSSMSpecies_numberCharges_eq_expand] at h1 h2 h3
  simp only [Fin.isValue, toSMSpecies_apply, Nat.reduceMul, Hd_apply, Fin.reduceFinMk,
    Hu_apply] at h1 h2 h3
  linear_combination (norm := ring_nf) -(12 * h2) + 9 * h1 + 3 * h3

set_option backward.isDefEq.respectTransparency false in
lemma lineY₃B₃_doublePoint (R : MSSMACC.LinSols) (a b : ℚ) :
    cubeTriLin (lineY₃B₃ a b).val (lineY₃B₃ a b).val R.val = 0 := by
  change cubeTriLin (a • Y₃.val + b • B₃.val) (a • Y₃.val + b • B₃.val) R.val = 0
  rw [cubeTriLin.map_add₂, cubeTriLin.map_add₁, cubeTriLin.map_add₁]
  repeat rw [cubeTriLin.map_smul₂, cubeTriLin.map_smul₁]
  simp only [cubeTriLin.swap₁ B₃.val Y₃.val R.val, doublePoint_B₃_B₃, doublePoint_Y₃_Y₃,
    doublePoint_Y₃_B₃, mul_zero, add_zero]

end MSSMACC
