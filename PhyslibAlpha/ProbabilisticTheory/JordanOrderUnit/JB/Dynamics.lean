/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.JB.Basic
public import PhyslibAlpha.ProbabilisticTheory.Dynamics.GeneratorIsDerivation

/-!

# Generators of JB automorphism groups

The Jordan product is bounded, and generators of Jordan automorphism families are derivations.

## i. Overview

The Jordan product of a normed Jordan algebra is a bounded bilinear map, so multiplication operators
and quadratic representations are continuous linear maps. The generator of a differentiable
one-parameter family of Jordan automorphisms is a Jordan derivation.

## ii. Key results

- `NormedJordanAlgebra.isBoundedBilinearMap_mul` : the Jordan product is bounded bilinear.
- `NormedJordanAlgebra.mulLeftCLM`, `NormedJordanAlgebra.quadRepCLM` : `L_a` and `U_a` as continuous
  linear maps.
- `NormedJordanAlgebra.isDerivation_of_isAutomorphismFamily` : the generator of a family of
  automorphisms is a derivation.
- `NormedJordanAlgebra.norm_quadRep_le` : `‖U_a b‖ ≤ 3 ‖a‖² ‖b‖`.

## iii. Table of contents

- A. The Jordan product is bounded bilinear
- B. Continuous multiplication and quadratic operators
- C. The derivation corollary

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace NormedJordanAlgebra

variable {E : Type*} [NormedJordanAlgebra E]

/-! ## A. The Jordan product is bounded bilinear -/

/-- The Jordan product of a normed Jordan algebra is bounded bilinear, with bound constant `1`. -/
lemma isBoundedBilinearMap_mul :
    IsBoundedBilinearMap ℝ (fun p : E × E => p.1 * p.2) where
  add_left := add_mul
  smul_left c x y := smul_mul_assoc c x y
  add_right := mul_add
  smul_right c x y := mul_smul_comm c x y
  bound := ⟨1, one_pos, fun x y => by simpa using NormedJordanAlgebra.norm_mul_le x y⟩

/-- Left Jordan multiplication by a fixed element is continuous. -/
lemma continuous_mul_left (a : E) : Continuous fun x : E => a * x :=
  isBoundedBilinearMap_mul.continuous.comp (continuous_const.prodMk continuous_id)

/-- Right Jordan multiplication by a fixed element is continuous. -/
lemma continuous_mul_right (a : E) : Continuous fun x : E => x * a :=
  isBoundedBilinearMap_mul.continuous.comp (continuous_id.prodMk continuous_const)

/-! ## B. Continuous multiplication and quadratic operators -/

open JordanAlgebra
open scoped JordanAlgebra

/-- Left Jordan multiplication as a bounded linear operator, with operator bound `‖a‖`. -/
noncomputable def mulLeftCLM (a : E) : E →L[ℝ] E :=
  LinearMap.mkContinuous (L a) ‖a‖ fun b => NormedJordanAlgebra.norm_mul_le a b

@[simp]
lemma mulLeftCLM_apply (a b : E) : mulLeftCLM a b = a * b := rfl

/-- A uniform norm bound for the quadratic representation:
`‖U_a b‖ ≤ 3 ‖a‖² ‖b‖`. The sharp constant is not needed for continuity. -/
lemma norm_quadRep_le (a b : E) : ‖U a b‖ ≤ 3 * ‖a‖ ^ 2 * ‖b‖ := by
  rw [quadRep_apply, jpow_two]
  have hleft : ‖(2 : ℝ) • (a * (a * b))‖ ≤ 2 * (‖a‖ * (‖a‖ * ‖b‖)) := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    exact mul_le_mul_of_nonneg_left
      (le_trans (NormedJordanAlgebra.norm_mul_le a (a * b))
        (mul_le_mul_of_nonneg_left (NormedJordanAlgebra.norm_mul_le a b) (norm_nonneg a)))
      (by norm_num)
  have hright : ‖(a * a) * b‖ ≤ (‖a‖ * ‖a‖) * ‖b‖ := by
    exact le_trans (NormedJordanAlgebra.norm_mul_le (a * a) b)
      (mul_le_mul_of_nonneg_right (NormedJordanAlgebra.norm_mul_le a a) (norm_nonneg b))
  calc
    ‖(2 : ℝ) • (a * (a * b)) - (a * a) * b‖
        ≤ ‖(2 : ℝ) • (a * (a * b))‖ + ‖(a * a) * b‖ := norm_sub_le _ _
    _ ≤ 2 * (‖a‖ * (‖a‖ * ‖b‖)) + (‖a‖ * ‖a‖) * ‖b‖ := by
      exact add_le_add hleft hright
    _ = 3 * ‖a‖ ^ 2 * ‖b‖ := by ring

/-- The quadratic representation as a bounded linear operator. -/
noncomputable def quadRepCLM (a : E) : E →L[ℝ] E :=
  LinearMap.mkContinuous (U a) (3 * ‖a‖ ^ 2) (norm_quadRep_le a)

@[simp]
lemma quadRepCLM_apply (a b : E) : quadRepCLM a b = U a b := rfl

/-! ## C. The derivation corollary -/

/-- **The generator of a differentiable family of Jordan automorphisms is a Jordan derivation.** -/
lemma isDerivation_of_isAutomorphismFamily {α : ℝ → E → E}
    (hα0 : ∀ a, α 0 a = a) (hmul : ∀ t a b, α t (a * b) = α t a * α t b)
    {D : E →ₗ[ℝ] E} (hD : IsGenerator α D) : IsDerivation D :=
  IsGenerator.isDerivation_of_isAutomorphismFamily isBoundedBilinearMap_mul hα0 hmul hD

end NormedJordanAlgebra

end ProbabilisticTheory
