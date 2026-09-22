/-
Copyright (c) 2026 Huanhai Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanhai Zhou
-/
module

public import PhyslibAlpha.QuantumThermodynamics.ThermalState

/-!
# Landauer processes

This file models a finite-dimensional Landauer process. A system and a thermal reservoir begin in
a product state and evolve jointly by a unitary. The resulting entropy bookkeeping gives the exact
Landauer identity and its usual lower bound.

## A. Landauer process data

## B. Initial and final states

## C. Thermodynamic changes

## D. The Landauer identity and bound
-/

@[expose] public section

noncomputable section

open scoped MState

namespace QuantumThermodynamics

/-!
## A. Landauer process data
-/

/-- A finite-dimensional Landauer process consisting of a system state, a thermal reservoir, and
a joint unitary evolution. -/
structure LandauerProcess (S R : Type*) [Fintype S] [DecidableEq S]
    [Fintype R] [DecidableEq R] [Nonempty R] where
  /-- The initial state of the system. -/
  initialSystem : MState S
  /-- The Hamiltonian of the reservoir. -/
  reservoirHamiltonian : HermitianMat R ℂ
  /-- The temperature of the reservoir. -/
  reservoirTemperature : Temperature
  /-- The joint unitary evolution of the system and reservoir. -/
  evolution : Matrix.unitaryGroup (S × R) ℂ

variable {S R : Type*} [Fintype S] [DecidableEq S]
  [Fintype R] [DecidableEq R] [Nonempty R]

namespace LandauerProcess

/-!
## B. Initial and final states
-/

/-- The initial thermal state of the reservoir. -/
def initialReservoir (P : LandauerProcess S R) : MState R :=
  MState.thermal P.reservoirHamiltonian P.reservoirTemperature

/-- The initial product state of the system and reservoir. -/
def initialJoint (P : LandauerProcess S R) : MState (S × R) :=
  P.initialSystem ⊗ᴹ P.initialReservoir

/-- The joint state after the unitary evolution. -/
def finalJoint (P : LandauerProcess S R) : MState (S × R) :=
  P.initialJoint.U_conj P.evolution

/-- The final system marginal obtained by tracing out the reservoir. -/
def finalSystem (P : LandauerProcess S R) : MState S :=
  P.finalJoint.traceRight

/-- The final reservoir marginal obtained by tracing out the system. -/
def finalReservoir (P : LandauerProcess S R) : MState R :=
  P.finalJoint.traceLeft

/-!
## C. Thermodynamic changes
-/

/-- The decrease in the system's von Neumann entropy. -/
def systemEntropyDecrease (P : LandauerProcess S R) : ℝ :=
  Sᵥₙ P.initialSystem - Sᵥₙ P.finalSystem

/-- The increase in the reservoir's von Neumann entropy. -/
def reservoirEntropyIncrease (P : LandauerProcess S R) : ℝ :=
  Sᵥₙ P.finalReservoir - Sᵥₙ P.initialReservoir

/-- The heat transferred to the reservoir, defined as its increase in expected energy. -/
def reservoirHeat (P : LandauerProcess S R) : ℝ :=
  P.finalReservoir.exp_val P.reservoirHamiltonian -
    P.initialReservoir.exp_val P.reservoirHamiltonian

/-- The relative entropy of the final reservoir state from its initial thermal state. -/
def reservoirRelativeEntropy (P : LandauerProcess S R) : ℝ :=
  (qRelativeEnt P.finalReservoir P.initialReservoir).toReal

/-!
## D. The Landauer identity and bound
-/

/-- The reservoir entropy increase is the system entropy decrease plus the final mutual
information between system and reservoir. -/
lemma entropyBalance (P : LandauerProcess S R) :
    P.reservoirEntropyIncrease =
      P.systemEntropyDecrease + qMutualInfo P.finalJoint := by
  have hFinalEntropy : Sᵥₙ P.finalJoint = Sᵥₙ P.initialJoint := by
    simp [finalJoint, Sᵥₙ]
  have hInitialMutualInfo : qMutualInfo P.initialJoint = 0 := by
    have h := qMutualInfo_as_qRelativeEnt P.initialJoint
    simpa [initialJoint] using h
  have hInitialEntropy :
      Sᵥₙ P.initialJoint = Sᵥₙ P.initialSystem + Sᵥₙ P.initialReservoir := by
    rw [qMutualInfo] at hInitialMutualInfo
    simpa [initialJoint, add_comm] using (eq_add_of_sub_eq hInitialMutualInfo).symm
  rw [reservoirEntropyIncrease, systemEntropyDecrease, qMutualInfo,
    finalSystem, finalReservoir]
  rw [hFinalEntropy, hInitialEntropy]
  ring

/-- The exact Landauer identity: the scaled reservoir heat is the system entropy decrease plus
the final mutual information and reservoir relative entropy. -/
lemma landauerIdentity (P : LandauerProcess S R) :
    (P.reservoirTemperature.β : ℝ) * P.reservoirHeat =
      P.systemEntropyDecrease + qMutualInfo P.finalJoint +
        P.reservoirRelativeEntropy := by
  rw [← P.entropyBalance]
  exact MState.gibbsRelativeEntropyBalance P.finalReservoir P.reservoirHamiltonian
    P.reservoirTemperature

/-- Landauer's bound: the system entropy decrease does not exceed the reservoir heat multiplied
by the inverse temperature. -/
lemma landauerBound (P : LandauerProcess S R) :
    P.systemEntropyDecrease ≤
      (P.reservoirTemperature.β : ℝ) * P.reservoirHeat := by
  rw [P.landauerIdentity]
  have hMutualInfo : 0 ≤ qMutualInfo P.finalJoint := by
    have h := congrArg EReal.toReal (qMutualInfo_as_qRelativeEnt P.finalJoint)
    have hToReal :
        qMutualInfo P.finalJoint =
          (qRelativeEnt P.finalJoint
            (P.finalJoint.traceRight ⊗ᴹ P.finalJoint.traceLeft)).toReal := by
      simpa [EReal.toReal_coe_ennreal] using h
    rw [hToReal]
    exact ENNReal.toReal_nonneg
  have hRelativeEntropy : 0 ≤ P.reservoirRelativeEntropy :=
    ENNReal.toReal_nonneg
  linarith

end LandauerProcess

end QuantumThermodynamics
