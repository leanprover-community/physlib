/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.Basic

/-!

## Properties of light like vectors

-/

@[expose] public section

noncomputable section
namespace Lorentz
open realLorentzTensor
open InnerProductSpace
namespace Vector

lemma lightLike_iff_norm_sq_zero {d : ℕ} (p : Vector d) :
    causalCharacter p = CausalCharacter.lightLike ↔ ⟪p, p⟫ₘ = 0 := by
  simp only [causalCharacter]
  split
  · rename_i h
    simp only [h]
  · rename_i h
    simp only [h, iff_false]
    split
    · simp only [reduceCtorEq, not_false_eq_true]
    · simp only [reduceCtorEq, not_false_eq_true]

  -- Zero vector has zero Minkowski norm squared
@[simp]
lemma causalCharacter_zero {d : ℕ} : causalCharacter (0 : Vector d) =
    CausalCharacter.lightLike := by
  simp [causalCharacter]

/-- Causally preceding is reflexive -/
@[simp]
lemma causallyPrecedes_refl {d : ℕ} (p : Vector d) : causallyPrecedes p p := by
  right
  simp [pastLightConeBoundary]

/-- For two lightlike vectors with equal time components, their spatial parts
    have equal Euclidean norms -/
lemma lightlike_eq_spatial_norm_of_eq_time {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .lightLike) (hw : causalCharacter w = .lightLike)
    (h_time : timeComponent v = timeComponent w) :
    ⟪spatialPart v, spatialPart v⟫_ℝ = ⟪spatialPart w, spatialPart w⟫_ℝ := by
  rw [lightLike_iff_norm_sq_zero, minkowskiProduct_toCoord] at hv hw
  have hv_eq : v (Sum.inl 0) * v (Sum.inl 0) = ∑ i, v (Sum.inr i) * v (Sum.inr i) := by
    dsimp only [Fin.isValue]; linarith
  have hw_eq : w (Sum.inl 0) * w (Sum.inl 0) = ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
    dsimp only [Fin.isValue];linarith
  have h_time_sq : v (Sum.inl 0) * v (Sum.inl 0) = w (Sum.inl 0) * w (Sum.inl 0) := by
    change timeComponent v * timeComponent v = timeComponent w * timeComponent w
    rw [h_time]
  simp only [PiLp.inner_apply, spatialPart, RCLike.inner_apply, conj_trivial]
  rw [← hv_eq, ← hw_eq, h_time_sq]

/-- If two lightlike vectors have parallel spatial components, their temporal components
must also be proportional, which implies the entire vectors are proportional -/
lemma lightlike_spatial_parallel_implies_proportional {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .lightLike) (hw : causalCharacter w = .lightLike)
    (h_spatial_parallel : ∃ (r : ℝ), v = r • w) :
    ∃ (r : ℝ), |v (Sum.inl 0)| = |r| * |w (Sum.inl 0)| := by
  rcases h_spatial_parallel with ⟨r, hr⟩
  rw [lightLike_iff_norm_sq_zero] at hv hw
  rw [minkowskiProduct_toCoord] at hv hw
  have hv_eq : v (Sum.inl 0) * v (Sum.inl 0) = ∑ i, v (Sum.inr i) * v (Sum.inr i) := by
    simp_all only [Fin.isValue]
    linarith
  have hw_eq : w (Sum.inl 0) * w (Sum.inl 0) = ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
    simp_all only [Fin.isValue, sub_self]
    linarith
  have h_spatial_sum : ∑ i, v (Sum.inr i) * v (Sum.inr i) =
      r^2 * ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
    calc ∑ i, v (Sum.inr i) * v (Sum.inr i)
      _ = ∑ i, (r * w (Sum.inr i)) * (r * w (Sum.inr i)) := by
          rw [hr]
          simp
      _ = ∑ i, r^2 * (w (Sum.inr i) * w (Sum.inr i)) := by
          apply Finset.sum_congr rfl; intro i _; ring
      _ = r^2 * ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
          rw [Finset.mul_sum]
  have h_time_sq : v (Sum.inl 0) * v (Sum.inl 0) = r^2 * (w (Sum.inl 0) * w (Sum.inl 0)) := by
    rw [hv_eq, h_spatial_sum, hw_eq]
  have h_abs : |v (Sum.inl 0)| * |v (Sum.inl 0)| = |r|^2 * (|w (Sum.inl 0)| *
      |w (Sum.inl 0)|) := by
    have h2 : |w (Sum.inl 0)|^2 = |w (Sum.inl 0)| * |w (Sum.inl 0)| := by ring
    have h3 : |v (Sum.inl 0)|^2 = |v (Sum.inl 0) * v (Sum.inl 0)| := by rw [pow_two, ← abs_mul]
    have h4 : |w (Sum.inl 0)|^2 = |w (Sum.inl 0) * w (Sum.inl 0)| := by rw [pow_two, ← abs_mul]
    have h5 : |v (Sum.inl 0) * v (Sum.inl 0)| = |r^2 * (w (Sum.inl 0) * w (Sum.inl 0))| := by
      rw [h_time_sq]
    have h6 : |r^2 * (w (Sum.inl 0) * w (Sum.inl 0))| =
      |r^2| * |w (Sum.inl 0) * w (Sum.inl 0)| := by rw [abs_mul]
    have h7 : |r^2| = |r|^2 := by rw [abs_pow]
    calc |v (Sum.inl 0)| * |v (Sum.inl 0)|
      _ = |v (Sum.inl 0)|^2 := by rw [pow_two]
      _ = |v (Sum.inl 0) * v (Sum.inl 0)| := h3
      _ = |r^2 * (w (Sum.inl 0) * w (Sum.inl 0))| := h5
      _ = |r^2| * |w (Sum.inl 0) * w (Sum.inl 0)| := h6
      _ = |r|^2 * |w (Sum.inl 0) * w (Sum.inl 0)| := by rw [h7]
      _ = |r|^2 * |w (Sum.inl 0) * w (Sum.inl 0)| := by rfl
      _ = |r|^2 * |w (Sum.inl 0)|^2 := by rw [← h4]
      _ = |r|^2 * (|w (Sum.inl 0)| * |w (Sum.inl 0)|) := by
        rw [pow_two]; exact congrArg (HMul.hMul (|r| * |r|)) h2
  have h_abs_eq : |v (Sum.inl 0)| = |r| * |w (Sum.inl 0)| := by
    have h_sq : |v (Sum.inl 0)|^2 = (|r| * |w (Sum.inl 0)|)^2 := by
      calc |v (Sum.inl 0)|^2
        _ = |v (Sum.inl 0)| * |v (Sum.inl 0)| := by rw [pow_two]
        _ = |r|^2 * (|w (Sum.inl 0)| * |w (Sum.inl 0)|) := by exact h_abs
        _ = |r|^2 * |w (Sum.inl 0)|^2 := by rw [← pow_two]
        _ = (|r| * |w (Sum.inl 0)|)^2 := by ring
    have h_both_nonneg : |v (Sum.inl 0)| ≥ 0 ∧ |r| * |w (Sum.inl 0)| ≥ 0 := by
      constructor
      · exact abs_nonneg (v (Sum.inl 0))
      · exact mul_nonneg (abs_nonneg r) (abs_nonneg (w (Sum.inl 0)))
    have h_sqrt : ∀ (a b : ℝ), a ≥ 0 → b ≥ 0 → a^2 = b^2 → a = b := by
      intros a b ha hb h_eq
      apply le_antisymm
      · by_contra h_not_le
        push_neg at h_not_le
        have : a^2 > b^2 := by
          exact (sq_lt_sq₀ hb ha).mpr h_not_le
        linarith
      · by_contra h_not_ge
        push_neg at h_not_ge
        have : a^2 < b^2 := by
          exact (sq_lt_sq₀ ha hb).mpr h_not_ge
        linarith
    exact h_sqrt |v (Sum.inl 0)| (|r| * |w (Sum.inl 0)|)
      h_both_nonneg.1 h_both_nonneg.2 h_sq
  use r

end Vector

end Lorentz
