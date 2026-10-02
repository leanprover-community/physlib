/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Meta.Informal.Basic
public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.Operators.Multiplication
/-!

# The rectangular potential barrier

## i. Overview

The rectangular potential barrier in one dimension provides the simplest example of quantum
tunnelling. A particle of mass `m` is subject to a piece-wise constant potential which is `V₀`
on a closed interval and zero elsewhere.

## ii. Key results

## iii. Table of contents

- A. Basic properties
- B. Potential function
- C. Hilbert space
- D. Operators
  - D.1. Kinetic
  - D.2. Potential
  - D.3. Hamiltonian
- E. As a quantum system

## iv. References

* None.
-/

@[expose] public section

noncomputable section
namespace QuantumMechanics

open Set MeasureTheory SpaceDHilbertSpace

/-- A quantum particle with mass `m > 0` on `Space 1` subject to a rectangular potential barrier.

  The potential is `V₀` on the interval `Icc lower upper` and zero elsewhere. -/
structure RectangularBarrier where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The lower bound of the barrier. -/
  lower : ℝ
  /-- The upper bound of the barrier. -/
  upper : ℝ
  h_bounds : lower < upper
  /-- The height of the potential barrier. -/
  V₀ : ℝ

variable (Q : RectangularBarrier)

namespace RectangularBarrier

/-!
## A. Basic properties
-/

@[simp]
lemma m_pos : 0 < Q.m := Q.hm

@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le

@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'

/-!
## B. Potential function
-/

/-- The piece-wise constant potential, equal to `Q.V₀` for `x.val 0 ∈ Icc Q.lower Q.upper`
  and zero otherwise. -/
def potentialFunction : Space 1 → ℝ := fun x ↦ (Icc Q.lower Q.upper).indicator (fun _ ↦ Q.V₀) (x 0)

lemma potentialFunction_eq :
    Q.potentialFunction = fun x ↦ (Icc Q.lower Q.upper).indicator (fun _ ↦ Q.V₀) (x 0) := rfl

/-- The piecewise-constant potential of the rectangular barrier is a.e. strongly measurable. -/
-- This relies on `Space.val` being measure-preserving.
lemma potentialFunction_aestronglyMeasurable: AEStronglyMeasurable Q.potentialFunction volume := by
  unfold potentialFunction
  apply AEStronglyMeasurable.indicator
  · fun_prop
  · change (MeasurableSet ((Icc Q.lower Q.upper) ∘ (fun (x: Space 1) => x.val 0)))
    have hi : MeasurableSet (Icc Q.lower Q.upper) := by measurability
    have hf : Measurable ((fun x => x.val 0) : Space 1 → ℝ) := by measurability
    exact MeasurableSet.preimage hi hf

/-!
## C. Hilbert space
-/

/-- The Hilbert space for the 1d rectangular barrier. -/
@[nolint unusedArguments]
abbrev HS (_ : RectangularBarrier) : Type _ := SpaceDHilbertSpace 1

/-!
## D. Operators
-/

/-!
### D.1. Kinetic
-/

/-- The kinetic energy operator, `p²/2m`. -/
def kineticOperator : Q.HS →ₗ.[ℂ] Q.HS := (2 * Q.m)⁻¹ • momentumSqOperator

/-!
### D.2. Potential
-/

/-- The potential energy operator, defined by multiplication by `Q.potentialFunction`. -/
def potentialOperator : Q.HS →ₗ.[ℂ] Q.HS := 𝓜 volume (Complex.ofReal ∘ Q.potentialFunction)

/-- The potential operator for the rectangular barrier is self-adjoint. -/
lemma potentialOperator_isSelfAdjoint (Q : RectangularBarrier) :
    IsSelfAdjoint Q.potentialOperator := by
  unfold IsSelfAdjoint
  unfold potentialOperator
  rw [mulOperator_isSelfAdjoint_ofReal]
  swap
  ext x
  simp only [Function.comp_apply, Complex.conj_ofReal]
  have hQ := potentialFunction_aestronglyMeasurable
  fun_prop

/-!
### D.3. Hamiltonian
-/

/-- The Hamiltonian for the rectangular barrier. -/
informal_definition hamiltonian where
  deps := [``RectangularBarrier]
  tag := "QM-RB-ham"

/-- The Hamiltonian for the rectangular barrier is essentially self-adjoint. -/
informal_lemma hamiltonian_essentially_self_adjoint where
  deps := [``RectangularBarrier.hamiltonian]
  tag := "QM-RB-hamESA"

/-!
## E. As a quantum system
-/

/-- The rectangular barrier as a quantum system
  (self-adjoint Hamiltonian acting on a Hilbert space). -/
informal_definition toQuantumSystem where
  deps := [``RectangularBarrier.hamiltonian_essentially_self_adjoint]
  tag := "QM-RB-sys"

end RectangularBarrier
end QuantumMechanics
end
