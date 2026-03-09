/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.PlaneNonSols
/-!
# Bound on plane dimension

We place an upper bound on the dimension of a plane of charges on which every point is a solution.
The upper bound is 7, proven in the theorem `plane_exists_dim_le_7`.

-/

@[expose] public section

namespace SMRHN
namespace PlusU1

open SMνCharges
open SMνACCs
open BigOperators

/-- A proposition which is true if for a given `n`, a plane of charges of dimension `n` exists
in which each point is a solution. -/
def ExistsPlane (n : ℕ) : Prop := ∃ (B : Fin n → (PlusU1 3).Charges),
  LinearIndependent ℚ B ∧ ∀ (f : Fin n → ℚ), (PlusU1 3).IsSolution (∑ i, f i • B i)

lemma exists_plane_exists_basis {n : ℕ} (hE : ExistsPlane n) :
    ∃ (B : Fin 11 ⊕ Fin n → (PlusU1 3).Charges), LinearIndependent ℚ B := by
  obtain ⟨E, hE1, hE2⟩ := hE
  obtain ⟨B, hB1, hB2⟩ := eleven_dim_plane_of_no_sols_exists
  let Y := Sum.elim B E
  refine ⟨Y, Fintype.linearIndependent_iff.mpr fun g hg ↦ ?_⟩
  rw [@Fintype.sum_sum_type, @add_eq_zero_iff_eq_neg, ← @Finset.sum_neg_distrib] at hg
  have h1 : ∑ x : Fin n, -(g (Sum.inr x) • Y (Sum.inr x)) =
      ∑ x : Fin n, (-g (Sum.inr x)) • Y (Sum.inr x) := by
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [h1] at hg
  have h2 : ∑ a₁ : Fin 11, g (Sum.inl a₁) • Y (Sum.inl a₁) = 0 := by
    apply hB2
    erw [hg]
    exact hE2 fun i => -g (Sum.inr i)
  rw [Fintype.linearIndependent_iff] at hB1 hE1
  have h3 : ∀ i, g (Sum.inl i) = 0 := hB1 (fun i => (g (Sum.inl i))) h2
  rw [h2] at hg
  have h4 : ∀ i, - g (Sum.inr i) = 0 := hE1 (fun i => (- g (Sum.inr i))) hg.symm
  simp only [neg_eq_zero] at h4
  intro i
  match i with
  | Sum.inl i => exact h3 i
  | Sum.inr i => exact h4 i

theorem plane_exists_dim_le_7 {n : ℕ} (hn : ExistsPlane n) : n ≤ 7 := by
  obtain ⟨B, hB⟩ := exists_plane_exists_basis hn
  have h1 := LinearIndependent.fintype_card_le_finrank hB
  simp only [Fintype.card_sum, Fintype.card_fin] at h1
  rw [show Module.finrank ℚ (PlusU1 3).Charges = 18 from
    Module.finrank_fin_fun ℚ] at h1
  exact Nat.le_of_add_le_add_left h1

end PlusU1
end SMRHN
