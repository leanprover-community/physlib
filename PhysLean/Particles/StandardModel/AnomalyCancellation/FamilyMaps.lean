/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.StandardModel.AnomalyCancellation.Basic
/-!
# Family maps for the Standard Model ACCs

We define the a series of maps between the charges for different numbers of families.

-/

@[expose] public section

namespace SM
open SMCharges
open SMACCs
open BigOperators

/-- Given a map of for a generic species, the corresponding map for charges. -/
@[simps!]
def chargesMapOfSpeciesMap {n m : ℕ} (f : (SMSpecies n).Charges →ₗ[ℚ] (SMSpecies m).Charges) :
    (SMCharges n).Charges →ₗ[ℚ] (SMCharges m).Charges where
  toFun S := toSpeciesEquiv.symm (fun i => (LinearMap.comp f (toSpecies i)) S)
  map_add' S T := by
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [map_add]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rw [map_add]
  map_smul' a S := by
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [map_smul]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rw [map_smul]
    rfl

/-- The projection of the `m`-family charges onto the first `n`-family charges for species. -/
@[simps!]
def speciesFamilyProj {m n : ℕ} (h : n ≤ m) :
    (SMSpecies m).Charges →ₗ[ℚ] (SMSpecies n).Charges where
  toFun S := S ∘ Fin.castLE h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projection of the `m`-family charges onto the first `n`-family charges. -/
def familyProjection {m n : ℕ} (h : n ≤ m) : (SMCharges m).Charges →ₗ[ℚ] (SMCharges n).Charges :=
  chargesMapOfSpeciesMap (speciesFamilyProj h)

/-- For species, the embedding of the `m`-family charges onto the `n`-family charges, with all
other charges zero. -/
@[simps!]
def speciesEmbed (m n : ℕ) :
    (SMSpecies m).Charges →ₗ[ℚ] (SMSpecies n).Charges where
  toFun S := fun i =>
    if hi : i.val < m then
      S ⟨i, hi⟩
    else
      0
  map_add' S T := by
    funext i
    simp only [SMSpecies_numberCharges, ACCSystemCharges.chargesAddCommMonoid_add]
    by_cases hi : i.val < m
    · erw [dif_pos hi, dif_pos hi, dif_pos hi]
    · erw [dif_neg hi, dif_neg hi, dif_neg hi]
      with_unfolding_all rfl
  map_smul' a S := by
    funext i
    simp only [SMSpecies_numberCharges, HSMul.hSMul, ACCSystemCharges.chargesModule_smul,
      eq_ratCast, Rat.cast_eq_id, id_eq]
    by_cases hi : i.val < m
    · erw [dif_pos hi, dif_pos hi]
    · erw [dif_neg hi, dif_neg hi]
      exact Eq.symm (Rat.mul_zero a)

/-- The embedding of the `m`-family charges onto the `n`-family charges, with all
other charges zero. -/
def familyEmbedding (m n : ℕ) : (SMCharges m).Charges →ₗ[ℚ] (SMCharges n).Charges :=
  chargesMapOfSpeciesMap (speciesEmbed m n)

/-- For species, the embedding of the `1`-family charges into the `n`-family charges in
a universal manner. -/
@[simps!]
def speciesFamilyUniversial (n : ℕ) :
    (SMSpecies 1).Charges →ₗ[ℚ] (SMSpecies n).Charges where
  toFun S _ := S ⟨0, Nat.zero_lt_succ 0⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The embedding of the `1`-family charges into the `n`-family charges in
a universal manner. -/
def familyUniversal (n : ℕ) : (SMCharges 1).Charges →ₗ[ℚ] (SMCharges n).Charges :=
  chargesMapOfSpeciesMap (speciesFamilyUniversial n)

end SM
