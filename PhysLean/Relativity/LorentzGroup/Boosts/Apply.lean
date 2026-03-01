/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.LorentzGroup.Boosts.Basic
/-!

## Boosts applied to Lorentz vectors

These recover what one would describe as the ordinary Lorentz transformations
of Lorentz vectors.

-/

namespace Lorentz
open realLorentzTensor
open LorentzGroup
variable {d : ℕ}

namespace Vector

lemma boost_time_eq (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Vector d) :
    (boost i β hβ • p) (Sum.inl 0) = γ β * (p (Sum.inl 0) - β * p (Sum.inr i)) := by
  rw [smul_eq_sum]
  simp [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  rw [Finset.sum_eq_single i]
  · simp
    ring
  · intro b _ hbi
    rw [boost_inl_0_inr_other]
    · simp
    · exact hbi
  · simp

lemma boost_inr_self_eq (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Vector d) :
    (boost i β hβ • p) (Sum.inr i) = γ β * (p (Sum.inr i) - β * p (Sum.inl 0)) := by
  rw [smul_eq_sum]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, boost_inr_self_inl_0, neg_mul]
  rw [Finset.sum_eq_single i]
  · simp only [Fin.isValue, boost_inr_self_inr_self]
    ring
  · intro b _ hbi
    rw [boost_inr_self_inr_other]
    · simp
    · exact hbi
  · simp

lemma boost_inr_other_eq (i j : Fin d) (hji : j ≠ i) (β : ℝ) (hβ : |β| < 1) (p : Vector d) :
    (boost i β hβ • p) (Sum.inr j) = p (Sum.inr j) := by
  rw [smul_eq_sum]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton]
  rw [boost_inr_other_inl_0 hβ hji]
  rw [Finset.sum_eq_single j]
  · rw [boost_inr_other_inr hβ hji]
    simp
  · intro b _ hbj
    rw [boost_inr_other_inr hβ hji]
    rw [if_neg ((Ne.symm hbj))]
    simp
  · simp

lemma boost_toCoord_eq (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Vector d) :
    (boost i β hβ • p) = fun j =>
      match j with
      | Sum.inl 0 => γ β * (p (Sum.inl 0) - β * p (Sum.inr i))
      | Sum.inr j =>
        if j = i then γ β * (p (Sum.inr i) - β * p (Sum.inl 0))
        else p (Sum.inr j) := by
  funext j
  match j with
  | Sum.inl 0 => rw [boost_time_eq]
  | Sum.inr j =>
    by_cases hj : j = i
    · subst hj
      rw [boost_inr_self_eq]
      simp
    · rw [boost_inr_other_eq _ _ hj]
      simp [hj]

end Vector

end Lorentz
