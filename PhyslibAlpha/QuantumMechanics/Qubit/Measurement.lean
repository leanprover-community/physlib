/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.OrthonormalMeasurement
public import QuantumInfo.States.Pure.Braket
public import QuantumInfo.States.Pure.Qubit

/-!
# Computational-basis measurement of a qubit

A measurement on a qubit with outcomes indexed by its computational basis.

## i. Overview

The two coordinate vectors form an orthonormal basis of the qubit's Hilbert space.
On a normalized ket, the probability of either outcome is the squared norm of the
corresponding amplitude. Since the amplitudes have total squared norm one, the
remainder in the orthonormal-family measurement vanishes.

## ii. Key results

- `computationalBasisMeasurement` measures a qubit in the standard basis.
- `expectation_computationalBasisMeasurement_singleton` gives each outcome probability.

## iii. Table of contents

- A. Computational-basis measurement

## iv. References

- See the qubit API map in `Physlib/QuantumMechanics/Qubit/API-map.md`.

## A. Computational-basis measurement
-/

@[expose] public noncomputable section

namespace PhyslibAlpha.Qubit

open PhyslibAlpha.ProbabilisticTheory UnitalPositiveLinearMap

/-- The computational-basis measurement with outcomes `0` and `1`. -/
def computationalBasisMeasurement :
    Measurement Qubit (Observable (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit)) :=
  Measurement.ofOrthonormal (EuclideanSpace.basisFun Qubit ℂ).orthonormal 0

/-- In a pure state, the probability of outcome `i` is the squared norm of its amplitude. -/
lemma expectation_computationalBasisMeasurement_singleton (ψ : Ket Qubit) (i : Qubit) :
    (ofVec ψ.norm_toEuclideanSpace)⟨computationalBasisMeasurement {i}
      (measurableSet_singleton i)⟩ = ‖ψ i‖ ^ 2 := by
  rw [computationalBasisMeasurement, Measurement.expectation_ofOrthonormal_singleton]
  simp only [EuclideanSpace.basisFun_inner]
  change ‖ψ i‖ ^ 2 + (if i = 0 then 1 - ∑ j, ‖ψ.vec j‖ ^ 2 else 0) = ‖ψ i‖ ^ 2
  simp [ψ.normalized']

end PhyslibAlpha.Qubit
