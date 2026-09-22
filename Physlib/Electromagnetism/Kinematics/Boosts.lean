/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Kinematics.MagneticField
public import Physlib.SpaceAndTime.SpaceTime.Boosts
/-!

# Boosts on the electric and magnetic fields

## i. Overview

We find the transformations of the electric and magnetic field matrix under
boosts in the 'x' direction. We do this in full-generality for `d+1` space dimensions.

## ii. Key results

- `electricField_apply_x_boost_zero` : The transformation of the x-component of the electric
  field under a boost in the 'x' direction.
- `electricField_apply_x_boost_succ` : The transformation of the other components of the electric
  field under a boost in the 'x' direction.
- `magneticFieldMatrix_apply_x_boost_zero_succ` : The transformation of the 'x-components' of the
  magnetic field matrix under a boost in the 'x' direction
- `magneticFieldMatrix_apply_x_boost_succ_succ` : The transformation of the other components of the
  magnetic field matrix under a boost in the 'x' direction.

## iii. Table of contents

- A. Boost of the electric field
  - A.1. Boost of the x-component of the electric field
  - A.2. Boost of other components of the electric field
- B. Boost of the magnetic field
  - B.1. Boost of the 'x-components' of the magnetic field matrix
  - B.2. Boost of the other components of the magnetic field matrix

## iv. References

* https://en.wikipedia.org/wiki/Classical_electromagnetism_and_special_relativity.
  [ref: wiki_classical_em_and_sr]
-/

@[expose] public section

namespace Electromagnetism

namespace ElectromagneticPotential
open LorentzGroup
open TensorSpecies Tensor

attribute [-simp] Fin.succAbove_zero

/-!

## A. Boost of the electric field

-/

/-!

### A.1. Boost of the x-component of the electric field

-/
lemma electricField_apply_x_boost_zero {d : ℕ} {c : SpeedOfLight} (β : ℝ) (hβ : |β| < 1)
    (A : ElectromagneticPotential d.succ) (hA : Differentiable ℝ A) (t : Time) (x : Space d.succ) :
    let Λ := LorentzGroup.boost (d := d.succ) 0 β hβ
    let t' : Time := γ β * (t.val + β /c * x 0)
    let x' : Space d.succ := ⟨fun
      | 0 => γ β * (x 0 + c * β * t.val)
      | ⟨Nat.succ n, ih⟩ => x ⟨Nat.succ n, ih⟩⟩
    electricField c (Λ • A) t x 0 =
    A.electricField c t' x' 0 := by
  dsimp
  rw [electricField_eq_toFieldStrength_eval, toFieldStrength_eval_equivariant _ _ hA]
  simp [Fintype.sum_sum_type, Fin.sum_univ_succ, toFieldStrength_eval_diag_eq_zero]
  rw [electricField_eq_toFieldStrength_eval (hA := hA)]
  simp only [Fin.isValue, neg_mul, neg_inj, mul_eq_mul_left_iff, SpeedOfLight.val_ne_zero, or_false]
  conv_lhs =>
    enter [2]
    rw [toFieldStrength_eval_antisymm]
  trans γ β ^ 2 * (1 - β ^ 2) *
      toScalar {A.toFieldStrength
      ((boost (d := d.succ) 0 β hβ)⁻¹ • (SpaceTime.toTimeAndSpace c).symm (t, x)) |
      [Sum.inl 0] [Sum.inr 0]}ᵀ
  · ring
  rw [γ_sq β hβ]
  field_simp
  rw [SpaceTime.boost_zero_apply_time_space]
  field_simp
  rfl
  · fun_prop

/-!

### A.2. Boost of other components of the electric field

-/

lemma electricField_apply_x_boost_succ {d : ℕ} {c : SpeedOfLight} (β : ℝ) (hβ : |β| < 1)
    (A : ElectromagneticPotential d.succ) (hA : Differentiable ℝ A) (t : Time) (x : Space d.succ)
    (i : Fin d) :
    let Λ := LorentzGroup.boost (d := d.succ) 0 β hβ
    let t' : Time := γ β * (t.val + β /c * x 0)
    let x' : Space d.succ := ⟨fun
      | 0 => γ β * (x 0 + c * β * t.val)
      | ⟨Nat.succ n, ih⟩ => x ⟨Nat.succ n, ih⟩⟩
    electricField c (Λ • A) t x i.succ =
    γ β * (A.electricField c t' x' i.succ + c * β * A.magneticFieldMatrix c t' x' (0, i.succ)) := by
  dsimp
  rw [electricField_eq_toFieldStrength_eval,
    toFieldStrength_eval_equivariant _ _ hA]
  simp [Fintype.sum_sum_type, boost_zero_inr_succ_inr_succ, Fin.sum_univ_succ]
  rw [toFieldStrength_eval_inl_inr_eq_electricField (c := c) (hA := hA),
    toFieldStrength_eval_inr_inr_eq_magneticFieldMatrix (c := c),
    SpaceTime.boost_zero_apply_time_space]
  simp only [one_div, Nat.succ_eq_add_one, SpaceTime.time_toTimeAndSpace_symm,
    SpaceTime.space_toTimeAndSpace_symm, neg_mul, mul_neg]
  field_simp
  ring_nf
  rfl
  · fun_prop

/-!

## B. Boost of the magnetic field

-/

/-!

### B.1. Boost of the 'x-components' of the magnetic field matrix

-/

lemma magneticFieldMatrix_apply_x_boost_zero_succ {d : ℕ} {c : SpeedOfLight} (β : ℝ) (hβ : |β| < 1)
    (A : ElectromagneticPotential d.succ) (hA : Differentiable ℝ A) (t : Time) (x : Space d.succ)
    (i : Fin d) :
    let Λ := LorentzGroup.boost (d := d.succ) 0 β hβ
    let t' : Time := γ β * (t.val + β /c * x 0)
    let x' : Space d.succ := ⟨fun
      | 0 => γ β * (x 0 + c * β * t.val)
      | ⟨Nat.succ n, ih⟩ => x ⟨Nat.succ n, ih⟩⟩
    magneticFieldMatrix c (Λ • A) t x (0, i.succ) =
    γ β * (A.magneticFieldMatrix c t' x' (0, i.succ) + β / c * A.electricField c t' x' i.succ) := by
  dsimp [magneticFieldMatrix_eq]
  rw [toFieldStrength_eval_equivariant _ _ hA]
  simp [Fintype.sum_sum_type, boost_zero_inr_succ_inr_succ, Fin.sum_univ_succ]
  rw [toFieldStrength_eval_inl_inr_eq_electricField (c := c) (hA := hA),
    toFieldStrength_eval_inr_inr_eq_magneticFieldMatrix (c := c),
    SpaceTime.boost_zero_apply_time_space]
  simp only [one_div, Nat.succ_eq_add_one, SpaceTime.time_toTimeAndSpace_symm,
    SpaceTime.space_toTimeAndSpace_symm, neg_mul, mul_neg, neg_neg]
  field_simp
  ring_nf
  rfl

/-!

### B.2. Boost of the other components of the magnetic field matrix

-/

lemma magneticFieldMatrix_apply_x_boost_succ_succ {d : ℕ} {c : SpeedOfLight} (β : ℝ) (hβ : |β| < 1)
    (A : ElectromagneticPotential d.succ) (hA : Differentiable ℝ A) (t : Time) (x : Space d.succ)
    (i j : Fin d) :
    let Λ := LorentzGroup.boost (d := d.succ) 0 β hβ
    let t' : Time := γ β * (t.val + β /c * x 0)
    let x' : Space d.succ := ⟨fun
      | 0 => γ β * (x 0 + c * β * t.val)
      | ⟨Nat.succ n, ih⟩ => x ⟨Nat.succ n, ih⟩⟩
    magneticFieldMatrix c (Λ • A) t x (i.succ, j.succ) =
    A.magneticFieldMatrix c t' x' (i.succ, j.succ) := by
  dsimp [magneticFieldMatrix_eq]
  rw [toFieldStrength_eval_equivariant _ _ hA]
  simp [Fintype.sum_sum_type, boost_zero_inr_succ_inr_succ, Fin.sum_univ_succ]
  rw [SpaceTime.boost_zero_apply_time_space]
  rfl

end ElectromagneticPotential
end Electromagnetism
