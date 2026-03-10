/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.StandardModel.AnomalyCancellation.Basic
/-!
# Anomaly Cancellation in the Standard Model without Gravity

This file defines the system of anomaly equations for the SM without RHN, and
without the gravitational ACC.

-/

@[expose] public section

namespace SM
open SMCharges
open SMACCs
open BigOperators

/-- The ACC system for the standard model without RHN and without the gravitational ACC. -/
@[simps!]
def SMNoGrav (n : ℕ) : ACCSystem where
  toACCSystemCharges := SMCharges n
  numberLinear := 2
  linearACCs := fun i =>
    match i with
    | 0 => @accSU2 n
    | 1 => accSU3
  numberQuadratic := 0
  quadraticACCs := by
    intro i
    exact Fin.elim0 i
  cubicACC := accCube

namespace SMNoGrav

variable {n : ℕ}

/-- The charges in `(SMNoGrav n).LinSols` satisfy the `SU(2)` anomaly-equation. -/
lemma SU2Sol (S : (SMNoGrav n).LinSols) : accSU2 S.val = 0 := by
  have hS := S.linearSol
  simp only [SMNoGrav_numberLinear, SMNoGrav_linearACCs, Fin.isValue] at hS
  exact hS 0

/-- The charges in `(SMNoGrav n).LinSols` satisfy the `SU(3)` anomaly-equation. -/
lemma SU3Sol (S : (SMNoGrav n).LinSols) : accSU3 S.val = 0 := by
  have hS := S.linearSol
  simp only [SMNoGrav_numberLinear, SMNoGrav_linearACCs, Fin.isValue] at hS
  exact hS 1

/-- The charges in `(SMNoGrav n).Sols` satisfy the cubic anomaly-equation. -/
lemma cubeSol (S : (SMNoGrav n).Sols) : accCube S.val = 0 := by
  exact S.cubicSol

/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `AnomalyFreeLinear`. -/
def chargeToLinear (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).LinSols :=
  ⟨S, by
    intro i
    simp only [SMNoGrav_numberLinear] at i
    match i with
    | 0 => exact hSU2
    | 1 => exact hSU3⟩

/-- An element of `AnomalyFreeLinear` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def linearToQuad (S : (SMNoGrav n).LinSols) : (SMNoGrav n).QuadSols :=
  ⟨S, by
    intro i
    exact Fin.elim0 i⟩

/-- An element of `AnomalyFreeQuad` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFree`. -/
def quadToAF (S : (SMNoGrav n).QuadSols) (hc : accCube S.val = 0) :
    (SMNoGrav n).Sols := ⟨S, hc⟩

/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def chargeToQuad (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).QuadSols :=
  linearToQuad $ chargeToLinear S hSU2 hSU3

/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `AnomalyFree`. -/
def chargeToAF (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0)
    (hc : accCube S = 0) : (SMNoGrav n).Sols :=
  quadToAF (chargeToQuad S hSU2 hSU3) hc

/-- An element of `AnomalyFreeLinear` which satisfies the quadratic and cubic ACCs
  gives us a element of `AnomalyFree`. -/
def linearToAF (S : (SMNoGrav n).LinSols)
    (hc : accCube S.val = 0) : (SMNoGrav n).Sols :=
  quadToAF (linearToQuad S) hc

end SMNoGrav

end SM
