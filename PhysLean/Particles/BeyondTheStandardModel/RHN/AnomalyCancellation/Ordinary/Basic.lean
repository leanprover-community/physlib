/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Permutations
public import PhysLean.QFT.AnomalyCancellation.GroupActions
/-!
# ACC system for SM with RHN (without hypercharge).

We define the ACC system for the Standard Model (without hypercharge) with right-handed neutrinos.
-/

@[expose] public section

namespace SMRHN
open SMνCharges
open SMνACCs
open BigOperators

/-- The ACC system for the SM plus RHN. -/
@[simps!]
def SM (n : ℕ) : ACCSystem where
  toACCSystemCharges := SMνCharges n
  numberLinear := 3
  linearACCs := fun i =>
    match i with
    | 0 => @accGrav n
    | 1 => accSU2
    | 2 => accSU3
  numberQuadratic := 0
  quadraticACCs := fun i ↦ Fin.elim0 i
  cubicACC := accCube

namespace SM

variable {n : ℕ}

lemma gravSol (S : (SM n).LinSols) : accGrav S.val = 0 := by
  have hS := S.linearSol
  simp only [SM_numberLinear, SM_linearACCs, Fin.isValue] at hS
  exact hS 0

lemma SU2Sol (S : (SM n).LinSols) : accSU2 S.val = 0 := by
  have hS := S.linearSol
  simp only [SM_numberLinear, SM_linearACCs, Fin.isValue] at hS
  exact hS 1

lemma SU3Sol (S : (SM n).LinSols) : accSU3 S.val = 0 := by
  have hS := S.linearSol
  simp only [SM_numberLinear, SM_linearACCs, Fin.isValue] at hS
  exact hS 2

lemma cubeSol (S : (SM n).Sols) : accCube S.val = 0 := S.cubicSol

/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `LinSols`. -/
def chargeToLinear (S : (SM n).Charges) (hGrav : accGrav S = 0)
    (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) : (SM n).LinSols :=
  ⟨S, by
    intro i
    simp only [SM_numberLinear] at i
    match i with
    | 0 => exact hGrav
    | 1 => exact hSU2
    | 2 => exact hSU3⟩

/-- An element of `LinSols` which satisfies the quadratic ACCs
  gives us a element of `QuadSols`. -/
def linearToQuad (S : (SM n).LinSols) : (SM n).QuadSols :=
  ⟨S, fun i ↦ Fin.elim0 i⟩

/-- An element of `QuadSols` which satisfies the quadratic ACCs
  gives us a element of `Sols`. -/
def quadToAF (S : (SM n).QuadSols) (hc : accCube S.val = 0) :
    (SM n).Sols := ⟨S, hc⟩

/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `QuadSols`. -/
def chargeToQuad (S : (SM n).Charges) (hGrav : accGrav S = 0)
    (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SM n).QuadSols :=
  linearToQuad $ chargeToLinear S hGrav hSU2 hSU3

/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def chargeToAF (S : (SM n).Charges) (hGrav : accGrav S = 0) (hSU2 : accSU2 S = 0)
    (hSU3 : accSU3 S = 0) (hc : accCube S = 0) : (SM n).Sols :=
  quadToAF (chargeToQuad S hGrav hSU2 hSU3) hc

/-- An element of `LinSols` which satisfies the quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def linearToAF (S : (SM n).LinSols)
    (hc : accCube S.val = 0) : (SM n).Sols :=
  quadToAF (linearToQuad S) hc

/-- The permutations acting on the ACC system corresponding to the SM with RHN. -/
def perm (n : ℕ) : ACCSystemGroupAction (SM n) where
  group := PermGroup n
  groupInst := inferInstance
  rep := repCharges
  linearInvariant := by
    intro i
    simp only [SM_numberLinear] at i
    match i with
    | 0 => exact accGrav_invariant
    | 1 => exact accSU2_invariant
    | 2 => exact accSU3_invariant
  quadInvariant := by
    intro i
    simp only [SM_numberQuadratic] at i
    exact Fin.elim0 i
  cubicInvariant := accCube_invariant

end SM

end SMRHN
