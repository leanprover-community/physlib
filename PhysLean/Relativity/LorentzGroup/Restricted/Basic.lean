/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.Relativity.LorentzGroup.Orthochronous.Basic
/-!
# The Restricted Lorentz Group

This file is currently a stub.

-/

TODO "6VZNP" "Prove that every member of the restricted Lorentz group is
  combination of a boost and a rotation."

namespace LorentzGroup

open Matrix
open minkowskiMatrix

/-- The restricted Lorentz group comprises the proper and orthochronous elements of the
Lorentz group. -/
def restricted (d : ℕ) : Subgroup (LorentzGroup d) where
  carrier := { Λ : LorentzGroup d | IsProper Λ ∧ IsOrthochronous Λ }
  one_mem' := ⟨
    by rw [IsProper]; exact det_one,
    by rw [IsOrthochronous]; exact zero_le_one⟩
  mul_mem' := by
    rintro Λ₁ Λ₂ ⟨Λ₁_proper, Λ₁_ortho⟩ ⟨Λ₂_proper, Λ₂_ortho⟩
    exact ⟨
      by exact isProper_mul Λ₁_proper Λ₂_proper,
      by exact isOrthochronous_mul Λ₁_ortho Λ₂_ortho⟩
  inv_mem' := by
    rintro Λ ⟨Λ_proper, Λ_ortho⟩

    have h_η₀₀ : @minkowskiMatrix d (Sum.inl 0) (Sum.inl 0) = 1 := by rfl
    have h_dual : (dual Λ.1) (Sum.inl 0) (Sum.inl 0) = Λ.1 (Sum.inl 0) (Sum.inl 0) := by
      rw [dual_apply, h_η₀₀, one_mul, mul_one]

    exact ⟨
      by rw [IsProper, inv_eq_dual, det_dual, Λ_proper],
      by simp [IsOrthochronous, inv_eq_dual, h_dual]; exact Λ_ortho⟩

lemma isOrthochronous_of_restricted {d : ℕ} (Λ : restricted d) :
    IsOrthochronous Λ.1 := Λ.2.2

/-- The restricted Lorentz group is a normal subgroup of the Lorentz group. -/
lemma restricted_normal_subgroup {d : ℕ} : (restricted d).Normal := by
  have h_proper {Λ P : LorentzGroup d} (hP : IsProper P) : IsProper (Λ * P * Λ⁻¹) := by
    simp only [IsProper, lorentzGroupIsGroup_mul_coe, det_mul]
    rw [hP, mul_one, ← det_mul, coe_inv, mul_inv_of_invertible, det_one]
  have h_ortho {Λ O : LorentzGroup d} (hO : IsOrthochronous O) : IsOrthochronous (Λ * O * Λ⁻¹) := by
    by_cases hΛ : IsOrthochronous Λ
    · exact isOrthochronous_mul
        (isOrthochronous_mul hΛ hO)
        (isOrthochronous_inv_iff.mpr hΛ)
    · rw [isOrthochronous_mul_iff, isOrthochronous_inv_iff]
      simp_all
      rw [isOrthochronous_mul_iff]
      simp_all
  constructor
  rintro R ⟨R_proper, R_ortho⟩ Λ
  exact ⟨h_proper R_proper, h_ortho R_ortho⟩

open TopologicalSpace

/-- The restricted Lorentz group is connected. -/
semiformal_result "FXNL5" restricted_isConnected {d : ℕ} :
  IsConnected (restricted d : Set (LorentzGroup d))

/-- Given the hypothesis that the restricted Lorentz group is connected,
  the proof that the restricted lorentz group is equal to the connected component of the
  identity. -/
lemma restricted_eq_identity_component_of_isConnected {d : ℕ}
    (h1 : IsConnected (restricted d : Set (LorentzGroup d))) :
    (restricted d) = connectedComponent (1 : LorentzGroup d) := by
  ext x
  constructor
  · intro hx
    have h_id : 1 ∈ restricted d := by simp [restricted, IsOrthochronous]
    exact IsConnected.subset_connectedComponent h1 h_id hx
  · intro h
    exact ⟨(isProper_on_connected_component h).mp isProper_id,
          (isOrthochronous_on_connected_component h).mp id_isOrthochronous⟩

end LorentzGroup
