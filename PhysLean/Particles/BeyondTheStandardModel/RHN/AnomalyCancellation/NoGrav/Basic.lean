/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Permutations
public import PhysLean.QFT.AnomalyCancellation.GroupActions
/-!
# ACC system for SM with RHN and no gravitational anomaly.

We define the ACC system for the Standard Model with right-handed neutrinos and no gravitational
anomaly.
-/

@[expose] public section

namespace SMRHN
open SMνCharges
open SMνACCs
open BigOperators

/-- The ACC system for the SM plus RHN with no gravitational anomaly. -/
@[simps!]
def SMNoGrav (n : ℕ) : ACCSystem where
  toACCSystemCharges := SMνCharges n
  numberLinear := 2
  linearACCs := fun i =>
    match i with
    | 0 => @accSU2 n
    | 1 => accSU3
  numberQuadratic := 0
  quadraticACCs := fun i ↦ Fin.elim0 i
  cubicACC := accCube

namespace SMNoGrav

variable {n : ℕ}

lemma SU2Sol (S : (SMNoGrav n).LinSols) : accSU2 S.val = 0 := by
  have hS := S.linearSol
  simp only [SMNoGrav_numberLinear, SMNoGrav_linearACCs, Fin.isValue] at hS
  exact hS 0

lemma SU3Sol (S : (SMNoGrav n).LinSols) : accSU3 S.val = 0 := by
  have hS := S.linearSol
  simp only [SMNoGrav_numberLinear, SMNoGrav_linearACCs, Fin.isValue] at hS
  exact hS 1

lemma cubeSol (S : (SMNoGrav n).Sols) : accCube S.val = 0 := S.cubicSol

/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `LinSols`. -/
def chargeToLinear (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).LinSols :=
  ⟨S, by
    intro i
    simp only [SMNoGrav_numberLinear] at i
    match i with
    | 0 => exact hSU2
    | 1 => exact hSU3⟩

/-- An element of `LinSols` which satisfies the quadratic ACCs
  gives us a element of `QuadSols`. -/
def linearToQuad (S : (SMNoGrav n).LinSols) : (SMNoGrav n).QuadSols := ⟨S, fun i ↦ Fin.elim0 i⟩

/-- An element of `QuadSols` which satisfies the quadratic ACCs
  gives us a element of `LinSols`. -/
def quadToAF (S : (SMNoGrav n).QuadSols) (hc : accCube S.val = 0) :
    (SMNoGrav n).Sols := ⟨S, hc⟩

/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `QuadSols`. -/
def chargeToQuad (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).QuadSols :=
  linearToQuad $ chargeToLinear S hSU2 hSU3

/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def chargeToAF (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0)
    (hc : accCube S = 0) : (SMNoGrav n).Sols :=
  quadToAF (chargeToQuad S hSU2 hSU3) hc

/-- An element of `LinSols` which satisfies the quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def linearToAF (S : (SMNoGrav n).LinSols)
    (hc : accCube S.val = 0) : (SMNoGrav n).Sols :=
  quadToAF (linearToQuad S) hc

/-- The permutations acting on the ACC system corresponding to the SM with RHN,
and no gravitational anomaly. -/
def perm (n : ℕ) : ACCSystemGroupAction (SMNoGrav n) where
  group := PermGroup n
  groupInst := inferInstance
  rep := repCharges
  linearInvariant := by
    intro i
    simp only [SMNoGrav_numberLinear] at i
    match i with
    | 0 => exact accSU2_invariant
    | 1 => exact accSU3_invariant
  quadInvariant := by
    intro i
    simp only [SMNoGrav_numberQuadratic] at i
    exact Fin.elim0 i
  cubicInvariant := accCube_invariant

end SMNoGrav

end SMRHN
