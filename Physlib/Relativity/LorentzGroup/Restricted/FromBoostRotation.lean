/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Rotations
public import Physlib.Relativity.LorentzGroup.Boosts.Generalized
/-!
# The construction of an element of the Lorentz group from a boost and a rotation

The main result of this module is the homeomorphism `toBoostRotation`
from the restricted Lorentz group to the product of Lorentz velocities and rotations.

The inverse of this homeomorphism writes elements of the restricted Lorentz group
as a product of a generalized boost and a rotation.

-/

@[expose] public section

noncomputable section

namespace LorentzGroup

open Matrix
open minkowskiMatrix

/-- The Lorentz velocity obtained from `toVector Λ` where `Λ` is an element
  of the restricted Lorentz group. -/
def toVelocity {d} (Λ : LorentzGroup.restricted d) : Lorentz.Velocity d :=
  ⟨toVector Λ, by
    simp [Lorentz.Velocity.mem_iff]
    have h := isOrthochronous_of_restricted Λ
    rw [isOrthochronous_iff_ge_one] at h
    linarith⟩

lemma toVelocity_val {d} (Λ : LorentzGroup.restricted d) :
    (toVelocity Λ).1 = toVector Λ := rfl

@[fun_prop]
lemma toVelocity_continuous {d} :
    Continuous (toVelocity : LorentzGroup.restricted d → Lorentz.Velocity d) := by
  apply Continuous.subtype_mk
  fun_prop

/-- A map from the restricted Lorentz group to rotations. -/
def toRotation {d} (Λ : LorentzGroup.restricted d) : Rotations d :=
  ⟨(generalizedBoost 0 (toVelocity Λ))⁻¹ * Λ, by
  constructor
  · rw [generalizedBoost_inv]
    rw [← toVector_timeComponent]
    rw [toVector_mul]
    rw [← toVelocity_val, generalizedBoost_apply_fst]
    simp
  · refine isProper_mul ?_ Λ.2.1
    rw [generalizedBoost_inv]
    exact generalizedBoost_isProper _ _⟩

@[fun_prop]
lemma toRotation_continuous {d} :
    Continuous (toRotation : LorentzGroup.restricted d → Rotations d) := by
  apply Continuous.subtype_mk
  change Continuous (fun Λ => (generalizedBoost 0 (toVelocity Λ))⁻¹ * Λ)
  fun_prop

/-- The homeomorphism from the restricted Lorentz group to the product of
  `Lorentz.Velocity d` and `Matrix.specialOrthogonalGroup (Fin d) ℝ`. The
  inverse of this map writes an element of the restricted Lorentz group
  as a product of a boost and a rotation. -/
def toBoostRotation {d} : LorentzGroup.restricted d ≃ₜ Lorentz.Velocity d ×
    Matrix.specialOrthogonalGroup (Fin d) ℝ where
  toFun Λ := (toVelocity Λ, ofSpecialOrthogonal.symm (toRotation Λ))
  invFun p := ⟨generalizedBoost 0 p.1 * (ofSpecialOrthogonal p.2).1, by
    refine (Subgroup.mul_mem_cancel_right (restricted d) ?_).mpr ?_
    · exact rotations_subset_restricted d (ofSpecialOrthogonal p.2).2
    · refine ⟨generalizedBoost_isProper 0 p.1, generalizedBoost_isOrthochronous 0 p.1⟩⟩
  left_inv Λ := by
    apply Subtype.ext
    simp only [toRotation, MulEquiv.apply_symm_apply]
    rw [mul_inv_cancel_left]
  right_inv p := by
    simp only
    match p with
    | ⟨⟨v, hv⟩, R⟩ =>
    simp [toVelocity]
    have h0 : toVector (generalizedBoost 0 ⟨v, hv⟩ * (ofSpecialOrthogonal R).1) = v := by
      rw [toVector_mul]
      simp only [toVector_rotation, Fin.isValue]
      change generalizedBoost 0 ⟨v, hv⟩ • (0 : Lorentz.Velocity d).1 = _
      rw [generalizedBoost_apply_fst]
    apply And.intro h0
    rw [toRotation]
    apply ofSpecialOrthogonal.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp only
    trans (generalizedBoost 0 ⟨v, hv⟩)⁻¹
      * ((generalizedBoost 0 ⟨v, hv⟩) * (ofSpecialOrthogonal R).1)
    · congr
      apply Subtype.ext
      simp [toVelocity, h0]
    group
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Every element of the restricted Lorentz group can be written as a product of a
  generalized boost and a rotation. -/
theorem exists_boost_mul_rotation {d} (Λ : LorentzGroup.restricted d) :
    ∃ (v : Lorentz.Velocity d) (R : Rotations d),
      (Λ : LorentzGroup d) = generalizedBoost 0 v * (R : LorentzGroup d) := by
  have h : toRotation Λ = (generalizedBoost 0 (toVelocity Λ))⁻¹ * Λ := rfl
  exact ⟨toVelocity Λ, toRotation Λ, by rw [h, mul_inv_cancel_left]⟩

end LorentzGroup

end
