/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.FamilyMaps
/-!
# B Minus L in SM with RHN.

Relevant definitions for the SM `B-L`.

-/

@[expose] public section

namespace SMRHN
namespace PlusU1

open SMνCharges
open SMνACCs
open BigOperators

variable {n : ℕ}

/-- $B - L$ in the 1-family case. -/
@[simps!]
def BL₁ : (PlusU1 1).Sols where
  val := fun i =>
    match i with
    | (0 : Fin 6) => 1
    | (1 : Fin 6) => -1
    | (2 : Fin 6) => -1
    | (3 : Fin 6) => -3
    | (4 : Fin 6) => 3
    | (5 : Fin 6) => 3
  linearSol := by
    intro i
    simp only [PlusU1_numberLinear] at i
    match i with
    | 0 => with_unfolding_all rfl
    | 1 => with_unfolding_all rfl
    | 2 => with_unfolding_all rfl
    | 3 => with_unfolding_all rfl
  quadSol := by
    intro i
    simp only [PlusU1_numberQuadratic] at i
    match i with
    | 0 => with_unfolding_all rfl
  cubicSol := by with_unfolding_all rfl

/-- $B - L$ in the $n$-family case. -/
@[simps!]
def BL (n : ℕ) : (PlusU1 n).Sols :=
  familyUniversalAF n BL₁

namespace BL

variable {n : ℕ}

lemma on_quadBiLin (S : (PlusU1 n).Charges) :
    quadBiLin (BL n).val S = 1/2 * accYY S + 3/2 * accSU2 S - 2 * accSU3 S := by
  erw [familyUniversal_quadBiLin]
  rw [accYY_decomp, accSU2_decomp, accSU3_decomp]
  simp only [Fin.isValue, BL₁_val, SMνSpecies_numberCharges, toSpecies_apply, one_mul, mul_neg,
    mul_one, neg_mul, sub_neg_eq_add, one_div]
  ring

lemma on_quadBiLin_AFL (S : (PlusU1 n).LinSols) : quadBiLin (BL n).val S.val = 0 := by
  rw [on_quadBiLin, YYsol S, SU2Sol S, SU3Sol S]
  with_unfolding_all rfl

lemma add_AFL_quad (S : (PlusU1 n).LinSols) (a b : ℚ) :
    accQuad (a • S.val + b • (BL n).val) = a ^ 2 * accQuad S.val := by
  erw [BiLinearSymm.toHomogeneousQuad_add, quadSol (b • (BL n)).1]
  rw [quadBiLin.map_smul₁, quadBiLin.map_smul₂, quadBiLin.swap, on_quadBiLin_AFL]
  erw [accQuad.map_smul]
  simp

lemma add_quad (S : (PlusU1 n).QuadSols) (a b : ℚ) :
    accQuad (a • S.val + b • (BL n).val) = 0 := by
  rw [add_AFL_quad, quadSol S]
  exact Rat.mul_zero (a ^ 2)

/-- The `QuadSol` obtained by adding $B-L$ to a `QuadSol`. -/
def addQuad (S : (PlusU1 n).QuadSols) (a b : ℚ) : (PlusU1 n).QuadSols :=
  linearToQuad (a • S.1 + b • (BL n).1.1) (add_quad S a b)

lemma addQuad_zero (S : (PlusU1 n).QuadSols) (a : ℚ) : addQuad S a 0 = a • S := by
  simp only [addQuad, linearToQuad, zero_smul, add_zero]
  rfl

lemma on_cubeTriLin (S : (PlusU1 n).Charges) :
    cubeTriLin (BL n).val (BL n).val S = 9 * accGrav S - 24 * accSU3 S := by
  erw [familyUniversal_cubeTriLin']
  rw [accGrav_decomp, accSU3_decomp]
  simp only [Fin.isValue, BL₁_val, mul_one, SMνSpecies_numberCharges, toSpecies_apply, mul_neg,
    neg_neg, neg_mul]
  ring

lemma on_cubeTriLin_AFL (S : (PlusU1 n).LinSols) :
    cubeTriLin (BL n).val (BL n).val S.val = 0 := by
  rw [on_cubeTriLin, gravSol S, SU3Sol S]
  with_unfolding_all rfl

lemma add_AFL_cube (S : (PlusU1 n).LinSols) (a b : ℚ) :
    accCube (a • S.val + b • (BL n).val) =
    a ^ 2 * (a * accCube S.val + 3 * b * cubeTriLin S.val S.val (BL n).val) := by
  erw [TriLinearSymm.toCubic_add, cubeSol (b • (BL n)), accCube.map_smul]
  repeat rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃]
  rw [on_cubeTriLin_AFL]
  simp only [HomogeneousCubic, accCube, TriLinearSymm.toCubic_apply,
    add_zero, BL_val, mul_zero]
  ring

end BL
end PlusU1
end SMRHN
