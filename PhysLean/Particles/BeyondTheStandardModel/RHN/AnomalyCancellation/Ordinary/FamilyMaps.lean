/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Ordinary.Basic
public import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.FamilyMaps
/-!
# Family Maps for SM with RHN (no hypercharge)

We give some properties of the family maps for the SM with RHN, in particular, we
define family universal maps in the case of `LinSols`, `QuadSols`, and `Sols`.
-/

@[expose] public section

namespace SMRHN
namespace SM

open SMνCharges
open SMνACCs
open BigOperators

variable {n : ℕ}

/-- The family universal maps on `LinSols`. -/
def familyUniversalLinear (n : ℕ) :
    (SM 1).LinSols →ₗ[ℚ] (SM n).LinSols where
  toFun S := chargeToLinear (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S, mul_zero])
  map_add' S T := ACCSystemLinear.LinSols.ext ((familyUniversal n).map_add' _ _)
  map_smul' a S := ACCSystemLinear.LinSols.ext ((familyUniversal n).map_smul' _ _)

/-- The family universal maps on `QuadSols`. -/
def familyUniversalQuad (n : ℕ) :
    (SM 1).QuadSols → (SM n).QuadSols := fun S =>
  chargeToQuad (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S.1, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S.1, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S.1, mul_zero])

/-- The family universal maps on `Sols`. -/
def familyUniversalAF (n : ℕ) :
    (SM 1).Sols → (SM n).Sols := fun S =>
  chargeToAF (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S.1.1, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S.1.1, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S.1.1, mul_zero])
    (by rw [familyUniversal_accCube, cubeSol S, mul_zero])

end SM
end SMRHN
