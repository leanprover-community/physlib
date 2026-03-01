/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.Basic

/-!

## Properties of time like vectors

-/

noncomputable section
namespace Lorentz
open realLorentzTensor
open InnerProductSpace
namespace Vector

/-- For timelike vectors with negative time components,
    their time components multiply to give a positive number -/
@[simp]
lemma timelike_neg_time_component_product {d : ℕ} (v w : Vector d)
    (hv_neg : v (Sum.inl 0) < 0) (hw_neg : w (Sum.inl 0) < 0) :
    v (Sum.inl 0) * w (Sum.inl 0) > 0 := by
  exact mul_pos_of_neg_of_neg hv_neg hw_neg

/-- For timelike vectors, the Minkowski inner product is positive -/
lemma timeLike_iff_norm_sq_pos {d : ℕ} (p : Vector d) :
    causalCharacter p = CausalCharacter.timeLike ↔ 0 < ⟪p, p⟫ₘ := by
  simp only [causalCharacter]
  split
  · rename_i h
    simp_all
  · split
    · rename_i h
      simp [h]
    · rename_i h
      simp_all

/-- For timeLike vectors in Minkowski space, the inner product of the spatial part
    is less than the square of the time component -/
lemma timelike_time_dominates_space {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ⟪spatialPart v, spatialPart v⟫_ℝ < (timeComponent v) * (timeComponent v) := by
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [minkowskiProduct_toCoord] at hv
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have h_spatial_sum : ∑ x, spatialPart v x * spatialPart v x =
                    ∑ i, v (Sum.inr i) * v (Sum.inr i) := by
      simp only
  have h_time : timeComponent v = v (Sum.inl 0) := rfl
  rw [h_spatial_sum, h_time]
  have h_norm_pos : 0 < v (Sum.inl 0) * v (Sum.inl 0) -
                  ∑ i, v (Sum.inr i) * v (Sum.inr i) := hv
  -- Rearrange the inequality
  have h : ∑ i, v (Sum.inr i) * v (Sum.inr i) <
          v (Sum.inl 0) * v (Sum.inl 0) := by
    exact lt_of_sub_pos h_norm_pos
  exact h

/-- For nonzero timelike vectors, the time component is nonzero -/
@[simp]
lemma time_component_ne_zero_of_timelike {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    v (Sum.inl 0) ≠ 0 := by
  by_contra h
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [minkowskiProduct_toCoord] at hv
  simp at hv
  rw [h] at hv
  simp at hv
  have h_spatial_nonneg : 0 ≤ ∑ i, v (Sum.inr i) * v (Sum.inr i) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (v (Sum.inr i)))
  exact lt_irrefl 0 (h_spatial_nonneg.trans_lt hv)

/-- For timelike vectors, the time component is nonzero -/
lemma timelike_time_component_ne_zero {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    timeComponent v ≠ 0 := time_component_ne_zero_of_timelike hv

/-- A vector is timelike if and only if its time component squared is less than
    the sum of its spatial components squared -/
lemma timeLike_iff_time_lt_space {d : ℕ} {v : Vector d} :
    causalCharacter v = .timeLike ↔
    ⟪spatialPart v, spatialPart v⟫_ℝ < v (Sum.inl 0) * v (Sum.inl 0) := by
  constructor
  · intro h_timelike
    rw [timeLike_iff_norm_sq_pos, minkowskiProduct_toCoord] at h_timelike
    simp only [Fin.isValue, sub_pos] at h_timelike; exact h_timelike
  · intro h_time_lt_space
    rw [timeLike_iff_norm_sq_pos, minkowskiProduct_toCoord]
    simp only [Fin.isValue, sub_pos]
    exact h_time_lt_space

/-- Time component squared is positive for timelike vectors -/
@[simp]
lemma timeComponent_squared_pos_of_timelike {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    0 < (timeComponent v)^2 := by
  exact pow_two_pos_of_ne_zero (time_component_ne_zero_of_timelike hv)

/-- For timelike vectors, the spatial norm squared is strictly less
    than the time component squared -/
lemma timelike_spatial_lt_time_squared {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ⟪spatialPart v, spatialPart v⟫_ℝ < (timeComponent v)^2 := by
  rw [timeLike_iff_norm_sq_pos, minkowskiProduct_toCoord] at hv
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have h_time : timeComponent v = v (Sum.inl 0) := rfl
  simp [h_time, pow_two]
  have h_norm_pos : 0 < v (Sum.inl 0) * v (Sum.inl 0) -
                  ∑ i, v (Sum.inr i) * v (Sum.inr i) := hv
  exact lt_of_sub_pos h_norm_pos

end Vector
end Lorentz
