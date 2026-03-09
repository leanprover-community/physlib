/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Permutations
public import PhysLean.QFT.AnomalyCancellation.GroupActions
/-!
# ACC system for SM with RHN

We define the ACC system for the Standard Model with right-handed neutrinos.
-/

@[expose] public section

namespace SMRHN
open SMνCharges
open SMνACCs
open BigOperators

/-- The ACC system for the SM plus RHN with an additional U1. -/
@[simps!]
def PlusU1 (n : ℕ) : ACCSystem where
  toACCSystemCharges := SMνCharges n
  numberLinear := 4
  linearACCs := fun i =>
    match i with
    | 0 => @accGrav n
    | 1 => accSU2
    | 2 => accSU3
    | 3 => accYY
  numberQuadratic := 1
  quadraticACCs := fun i =>
    match i with
    | 0 => accQuad
  cubicACC := accCube

namespace PlusU1

variable {n : ℕ}

lemma gravSol (S : (PlusU1 n).LinSols) : accGrav S.val = 0 := by
  have hS := S.linearSol
  simp only [PlusU1_numberLinear, PlusU1_linearACCs, Fin.isValue] at hS
  exact hS 0

lemma SU2Sol (S : (PlusU1 n).LinSols) : accSU2 S.val = 0 := by
  have hS := S.linearSol
  simp only [PlusU1_numberLinear, PlusU1_linearACCs, Fin.isValue] at hS
  exact hS 1

lemma SU3Sol (S : (PlusU1 n).LinSols) : accSU3 S.val = 0 := by
  have hS := S.linearSol
  simp only [PlusU1_numberLinear, PlusU1_linearACCs, Fin.isValue] at hS
  exact hS 2

lemma YYsol (S : (PlusU1 n).LinSols) : accYY S.val = 0 := by
  have hS := S.linearSol
  simp only [PlusU1_numberLinear, PlusU1_linearACCs, Fin.isValue] at hS
  exact hS 3

lemma quadSol (S : (PlusU1 n).QuadSols) : accQuad S.val = 0 := by
  have hS := S.quadSol
  simp only [PlusU1_numberQuadratic, HomogeneousQuadratic.eq_1, PlusU1_quadraticACCs] at hS
  exact hS 0

lemma cubeSol (S : (PlusU1 n).Sols) : accCube S.val = 0 := by
  exact S.cubicSol

/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `LinSols`. -/
def chargeToLinear (S : (PlusU1 n).Charges) (hGrav : accGrav S = 0)
    (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) (hYY : accYY S = 0) :
    (PlusU1 n).LinSols :=
  ⟨S, by
    intro i
    simp only [PlusU1_numberLinear] at i
    match i with
    | 0 => exact hGrav
    | 1 => exact hSU2
    | 2 => exact hSU3
    | 3 => exact hYY⟩

/-- An element of `LinSols` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def linearToQuad (S : (PlusU1 n).LinSols) (hQ : accQuad S.val = 0) :
    (PlusU1 n).QuadSols :=
  ⟨S, by
    intro i
    simp only [PlusU1_numberQuadratic] at i
    match i with
    | 0 => exact hQ⟩

/-- An element of `QuadSols` which satisfies the quadratic ACCs
  gives us a element of `Sols`. -/
def quadToAF (S : (PlusU1 n).QuadSols) (hc : accCube S.val = 0) :
    (PlusU1 n).Sols := ⟨S, hc⟩

/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `QuadSols`. -/
def chargeToQuad (S : (PlusU1 n).Charges) (hGrav : accGrav S = 0)
    (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) (hYY : accYY S = 0) (hQ : accQuad S = 0) :
    (PlusU1 n).QuadSols :=
  linearToQuad (chargeToLinear S hGrav hSU2 hSU3 hYY) hQ

/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def chargeToAF (S : (PlusU1 n).Charges) (hGrav : accGrav S = 0) (hSU2 : accSU2 S = 0)
    (hSU3 : accSU3 S = 0) (hYY : accYY S = 0) (hQ : accQuad S = 0) (hc : accCube S = 0) :
    (PlusU1 n).Sols :=
  quadToAF (chargeToQuad S hGrav hSU2 hSU3 hYY hQ) hc

/-- An element of `LinSols` which satisfies the quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def linearToAF (S : (PlusU1 n).LinSols) (hQ : accQuad S.val = 0)
    (hc : accCube S.val = 0) : (PlusU1 n).Sols :=
  quadToAF (linearToQuad S hQ) hc

/-- The permutations acting on the ACC system corresponding to the SM with RHN. -/
def perm (n : ℕ) : ACCSystemGroupAction (PlusU1 n) where
  group := PermGroup n
  groupInst := inferInstance
  rep := repCharges
  linearInvariant := by
    intro i
    simp only [PlusU1_numberLinear] at i
    match i with
    | 0 => exact accGrav_invariant
    | 1 => exact accSU2_invariant
    | 2 => exact accSU3_invariant
    | 3 => exact accYY_invariant
  quadInvariant := by
    intro i
    simp only [PlusU1_numberQuadratic] at i
    match i with
    | 0 => exact accQuad_invariant
  cubicInvariant := accCube_invariant

end PlusU1

end SMRHN
