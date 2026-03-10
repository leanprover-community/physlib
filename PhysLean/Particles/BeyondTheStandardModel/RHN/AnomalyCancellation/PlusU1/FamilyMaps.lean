/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.Basic
public import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.FamilyMaps
/-!
# Family Maps for SM with RHN

We give some properties of the family maps for the SM with RHN, in particular, we
define family universal maps in the case of `LinSols`, `QuadSols`, and `Sols`.
-/

@[expose] public section

namespace SMRHN
namespace PlusU1

open SMνCharges
open SMνACCs
open BigOperators

variable {n : ℕ}

/-- The family universal maps on `LinSols`. -/
def familyUniversalLinear (n : ℕ) :
    (PlusU1 1).LinSols →ₗ[ℚ] (PlusU1 n).LinSols where
  toFun S := chargeToLinear (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S, mul_zero])
    (by rw [familyUniversal_accYY, YYsol S, mul_zero])
  map_add' S T := rfl
  map_smul' a S := rfl

/-- The family universal maps on `QuadSols`. -/
def familyUniversalQuad (n : ℕ) :
    (PlusU1 1).QuadSols → (PlusU1 n).QuadSols := fun S =>
  chargeToQuad (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S.1, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S.1, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S.1, mul_zero])
    (by rw [familyUniversal_accYY, YYsol S.1, mul_zero])
    (by rw [familyUniversal_accQuad, quadSol S, mul_zero])

/-- The family universal maps on `Sols`. -/
def familyUniversalAF (n : ℕ) :
    (PlusU1 1).Sols → (PlusU1 n).Sols := fun S =>
  chargeToAF (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S.1.1, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S.1.1, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S.1.1, mul_zero])
    (by rw [familyUniversal_accYY, YYsol S.1.1, mul_zero])
    (by rw [familyUniversal_accQuad, quadSol S.1, mul_zero])
    (by rw [familyUniversal_accCube, cubeSol S, mul_zero])

end PlusU1
end SMRHN
