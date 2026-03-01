/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.BMinusL
/-!
# Solutions from quad solutions

We use $B-L$ to form a surjective map from quad solutions to solutions. The main reference
for this material is:

- https://arxiv.org/abs/2006.03588

-/

namespace SMRHN
namespace PlusU1

namespace QuadSolToSol

open SMνCharges
open SMνACCs
open BigOperators

variable {n : ℕ}
/-- A helper function for what follows. -/
@[simp]
def α₁ (S : (PlusU1 n).QuadSols) : ℚ := - 3 * cubeTriLin S.val S.val (BL n).val

/-- A helper function for what follows. -/
@[simp]
def α₂ (S : (PlusU1 n).QuadSols) : ℚ := accCube S.val

lemma cube_α₁_α₂_zero (S : (PlusU1 n).QuadSols) (a b : ℚ) (h1 : α₁ S = 0) (h2 : α₂ S = 0) :
    accCube (BL.addQuad S a b).val = 0 := by
  erw [BL.add_AFL_cube]
  simp_all

lemma α₂_AF (S : (PlusU1 n).Sols) : α₂ S.toQuadSols = 0 := S.2

lemma BL_add_α₁_α₂_cube (S : (PlusU1 n).QuadSols) :
    accCube (BL.addQuad S (α₁ S) (α₂ S)).val = 0 := by
  erw [BL.add_AFL_cube]
  simp only [α₁, BL_val, neg_mul, even_two, Even.neg_pow, α₂, mul_eq_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, false_or]
  right
  field_simp
  ring

lemma BL_add_α₁_α₂_AF (S : (PlusU1 n).Sols) :
    BL.addQuad S.1 (α₁ S.1) (α₂ S.1) = (α₁ S.1) • S.1 := by
  rw [α₂_AF, BL.addQuad_zero]

/-- The construction of a `Sol` from a `QuadSol` in the generic case. -/
def generic (S : (PlusU1 n).QuadSols) : (PlusU1 n).Sols :=
  quadToAF (BL.addQuad S (α₁ S) (α₂ S)) (BL_add_α₁_α₂_cube S)

lemma generic_on_AF (S : (PlusU1 n).Sols) : generic S.1 = (α₁ S.1) • S := by
  apply ACCSystem.Sols.ext
  change (BL.addQuad S.1 (α₁ S.1) (α₂ S.1)).val = _
  rw [BL_add_α₁_α₂_AF]
  rfl

lemma generic_on_AF_α₁_ne_zero (S : (PlusU1 n).Sols) (h : α₁ S.1 ≠ 0) :
    (α₁ S.1)⁻¹ • generic S.1 = S := by
  rw [generic_on_AF, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- The construction of a `Sol` from a `QuadSol` in the case when `α₁ S = 0` and `α₂ S = 0`. -/
def special (S : (PlusU1 n).QuadSols) (a b : ℚ) (h1 : α₁ S = 0) (h2 : α₂ S = 0) :
    (PlusU1 n).Sols :=
  quadToAF (BL.addQuad S a b) (cube_α₁_α₂_zero S a b h1 h2)

lemma special_on_AF (S : (PlusU1 n).Sols) (h1 : α₁ S.1 = 0) :
    special S.1 1 0 h1 (α₂_AF S) = S := by
  apply ACCSystem.Sols.ext
  change (BL.addQuad S.1 1 0).val = _
  rw [BL.addQuad_zero]
  simp

end QuadSolToSol

open QuadSolToSol
/-- A map from `QuadSols × ℚ × ℚ` to `Sols` taking account of the special and generic cases.
We will show that this map is a surjection. -/
def quadSolToSol {n : ℕ} : (PlusU1 n).QuadSols × ℚ × ℚ → (PlusU1 n).Sols := fun S =>
  if h1 : α₁ S.1 = 0 ∧ α₂ S.1 = 0 then
    special S.1 S.2.1 S.2.2 h1.1 h1.2
  else
    S.2.1 • generic S.1

/-- A map from `Sols` to `QuadSols × ℚ × ℚ` which forms a right-inverse to `quadSolToSol`, as
shown in `quadSolToSolInv_rightInverse`. -/
def quadSolToSolInv {n : ℕ} : (PlusU1 n).Sols → (PlusU1 n).QuadSols × ℚ × ℚ :=
    fun S =>
  if α₁ S.1 = 0 then
    (S.1, 1, 0)
  else
    (S.1, (α₁ S.1)⁻¹, 0)

lemma quadSolToSolInv_1 (S : (PlusU1 n).Sols) :
    (quadSolToSolInv S).1 = S.1 := by
  simp only [quadSolToSolInv, α₁, BL_val, SMνACCs.cubeTriLin_toFun_apply_apply, Fin.isValue,
    neg_mul, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
  split <;> rfl

lemma quadSolToSolInv_α₁_α₂_zero (S : (PlusU1 n).Sols) (h : α₁ S.1 = 0) :
    α₁ (quadSolToSolInv S).1 = 0 ∧ α₂ (quadSolToSolInv S).1 = 0 := by
  rw [quadSolToSolInv_1, α₂_AF S, h]
  exact Prod.mk_eq_zero.mp rfl

lemma quadSolToSolInv_α₁_α₂_ne_zero (S : (PlusU1 n).Sols) (h : α₁ S.1 ≠ 0) :
    ¬ (α₁ (quadSolToSolInv S).1 = 0 ∧ α₂ (quadSolToSolInv S).1 = 0) := by
  rw [not_and, quadSolToSolInv_1, α₂_AF S]
  intro hn
  simp_all

lemma quadSolToSolInv_special (S : (PlusU1 n).Sols) (h : α₁ S.1 = 0) :
    special (quadSolToSolInv S).1 (quadSolToSolInv S).2.1 (quadSolToSolInv S).2.2
    (quadSolToSolInv_α₁_α₂_zero S h).1 (quadSolToSolInv_α₁_α₂_zero S h).2 = S := by
  simp only [quadSolToSolInv_1]
  rw [show (quadSolToSolInv S).2.1 = 1 by rw [quadSolToSolInv, if_pos h]]
  rw [show (quadSolToSolInv S).2.2 = 0 by rw [quadSolToSolInv, if_pos h]]
  rw [special_on_AF]

lemma quadSolToSolInv_generic (S : (PlusU1 n).Sols) (h : α₁ S.1 ≠ 0) :
    (quadSolToSolInv S).2.1 • generic (quadSolToSolInv S).1 = S := by
  simp only [quadSolToSolInv_1]
  rw [show (quadSolToSolInv S).2.1 = (α₁ S.1)⁻¹ by rw [quadSolToSolInv, if_neg h]]
  rw [generic_on_AF_α₁_ne_zero S h]

lemma quadSolToSolInv_rightInverse : Function.RightInverse (@quadSolToSolInv n) quadSolToSol := by
  intro S
  by_cases h : α₁ S.1 = 0
  · rw [quadSolToSol, dif_pos (quadSolToSolInv_α₁_α₂_zero S h)]
    exact quadSolToSolInv_special S h
  · rw [quadSolToSol, dif_neg (quadSolToSolInv_α₁_α₂_ne_zero S h)]
    exact quadSolToSolInv_generic S h

theorem quadSolToSol_surjective : Function.Surjective (@quadSolToSol n) :=
  Function.RightInverse.surjective quadSolToSolInv_rightInverse

end PlusU1
end SMRHN
