/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.Basic
/-!
# Properties of Quad Sols for SM with RHN

We give a series of properties held by solutions to the quadratic equation.

In particular given a quad solution we define a map from linear solutions to quadratic solutions
and show that it is a surjection. The main reference for this is:

- https://arxiv.org/abs/2006.03588

-/

namespace SMRHN
namespace PlusU1

open SMνCharges
open SMνACCs
open BigOperators

namespace QuadSol

variable {n : ℕ}
variable (C : (PlusU1 n).QuadSols)

lemma add_AFL_quad (S : (PlusU1 n).LinSols) (a b : ℚ) :
    accQuad (a • S.val + b • C.val) =
    a * (a * accQuad S.val + 2 * b * quadBiLin S.val C.val) := by
  erw [BiLinearSymm.toHomogeneousQuad_add, quadSol (b • C)]
  rw [quadBiLin.map_smul₁, quadBiLin.map_smul₂]
  erw [accQuad.map_smul]
  ring

/-- A helper function for what comes later. -/
def α₁ (S : (PlusU1 n).LinSols) : ℚ := - 2 * quadBiLin S.val C.val

/-- A helper function for what comes later. -/
def α₂ (S : (PlusU1 n).LinSols) : ℚ := accQuad S.val

lemma α₂_AFQ (S : (PlusU1 n).QuadSols) : α₂ S.1 = 0 := quadSol S

lemma accQuad_α₁_α₂ (S : (PlusU1 n).LinSols) :
    accQuad ((α₁ C S) • S + α₂ S • C.1).val = 0 := by
  erw [add_AFL_quad]
  rw [α₁, α₂]
  ring

lemma accQuad_α₁_α₂_zero (S : (PlusU1 n).LinSols) (h1 : α₁ C S = 0)
    (h2 : α₂ S = 0) (a b : ℚ) : accQuad (a • S + b • C.1).val = 0 := by
  erw [add_AFL_quad]
  simp only [α₁, quadBiLin_toFun_apply, Fin.isValue, neg_mul, neg_eq_zero, mul_eq_zero,
    OfNat.ofNat_ne_zero, false_or, α₂, HomogeneousQuadratic.eq_1, accQuad,
    BiLinearSymm.toHomogeneousQuad_apply] at h1 h2
  simp [h1, h2]

/-- The construction of a `QuadSol` from a `LinSols` in the generic case. -/
def genericToQuad (S : (PlusU1 n).LinSols) :
    (PlusU1 n).QuadSols :=
  linearToQuad ((α₁ C S) • S + α₂ S • C.1) (accQuad_α₁_α₂ C S)

lemma genericToQuad_on_quad (S : (PlusU1 n).QuadSols) :
    genericToQuad C S.1 = (α₁ C S.1) • S := by
  apply ACCSystemQuad.QuadSols.ext
  change ((α₁ C S.1) • S.val + α₂ S.1 • C.val) = (α₁ C S.1) • S.val
  rw [α₂_AFQ]
  simp

lemma genericToQuad_ne_zero (S : (PlusU1 n).QuadSols) (h : α₁ C S.1 ≠ 0) :
    (α₁ C S.1)⁻¹ • genericToQuad C S.1 = S := by
  rw [genericToQuad_on_quad, smul_smul, Rat.inv_mul_cancel _ h, one_smul]

/-- The construction of a `QuadSol` from a `LinSols` in the special case when `α₁ C S = 0` and
  `α₂ S = 0`. -/
def specialToQuad (S : (PlusU1 n).LinSols) (a b : ℚ) (h1 : α₁ C S = 0)
    (h2 : α₂ S = 0) : (PlusU1 n).QuadSols :=
  linearToQuad (a • S + b • C.1) (accQuad_α₁_α₂_zero C S h1 h2 a b)

lemma special_on_quad (S : (PlusU1 n).QuadSols) (h1 : α₁ C S.1 = 0) :
    specialToQuad C S.1 1 0 h1 (α₂_AFQ S) = S := by
  apply ACCSystemQuad.QuadSols.ext
  change (1 • S.val + 0 • C.val) = S.val
  simp

/-- The construction of a `QuadSols` from a `LinSols` and two rationals taking account of the
generic and special cases. This function is a surjection. -/
def toQuad : (PlusU1 n).LinSols × ℚ × ℚ → (PlusU1 n).QuadSols := fun S =>
  if h : α₁ C S.1 = 0 ∧ α₂ S.1 = 0 then
    specialToQuad C S.1 S.2.1 S.2.2 h.1 h.2
  else
    S.2.1 • genericToQuad C S.1

/-- A function from `QuadSols` to `LinSols × ℚ × ℚ` which is a right inverse to `toQuad`. -/
@[simp]
def toQuadInv : (PlusU1 n).QuadSols → (PlusU1 n).LinSols × ℚ × ℚ := fun S =>
  if α₁ C S.1 = 0 then
    (S.1, 1, 0)
  else
    (S.1, (α₁ C S.1)⁻¹, 0)

lemma toQuadInv_fst (S : (PlusU1 n).QuadSols) :
    (toQuadInv C S).1 = S.1 := by
  rw [toQuadInv]
  split <;> rfl

lemma toQuadInv_α₁_α₂ (S : (PlusU1 n).QuadSols) :
    α₁ C S.1 = 0 ↔ α₁ C (toQuadInv C S).1 = 0 ∧ α₂ (toQuadInv C S).1 = 0 := by
  rw [toQuadInv_fst, α₂_AFQ]
  simp

lemma toQuadInv_special (S : (PlusU1 n).QuadSols) (h : α₁ C S.1 = 0) :
    specialToQuad C (toQuadInv C S).1 (toQuadInv C S).2.1 (toQuadInv C S).2.2
    ((toQuadInv_α₁_α₂ C S).mp h).1 ((toQuadInv_α₁_α₂ C S).mp h).2 = S := by
  simp only [toQuadInv_fst]
  rw [show (toQuadInv C S).2.1 = 1 by rw [toQuadInv, if_pos h]]
  rw [show (toQuadInv C S).2.2 = 0 by rw [toQuadInv, if_pos h]]
  rw [special_on_quad]

lemma toQuadInv_generic (S : (PlusU1 n).QuadSols) (h : α₁ C S.1 ≠ 0) :
    (toQuadInv C S).2.1 • genericToQuad C (toQuadInv C S).1 = S := by
  simp only [toQuadInv_fst]
  rw [show (toQuadInv C S).2.1 = (α₁ C S.1)⁻¹ by rw [toQuadInv, if_neg h]]
  rw [genericToQuad_ne_zero C S h]

lemma toQuad_rightInverse : Function.RightInverse (@toQuadInv n C) (toQuad C) := by
  intro S
  by_cases h : α₁ C S.1 = 0
  · rw [toQuad, dif_pos ((toQuadInv_α₁_α₂ C S).mp h)]
    exact toQuadInv_special C S h
  · rw [toQuad, dif_neg ((toQuadInv_α₁_α₂ C S).mpr.mt h)]
    exact toQuadInv_generic C S h

theorem toQuad_surjective : Function.Surjective (toQuad C) :=
  Function.RightInverse.surjective (toQuad_rightInverse C)

end QuadSol
end PlusU1
end SMRHN
