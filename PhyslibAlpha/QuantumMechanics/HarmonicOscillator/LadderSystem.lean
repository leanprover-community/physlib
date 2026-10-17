/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges, Tom Diem
-/
module

public import Physlib.QuantumMechanics.HarmonicOscillator.NumberOperator
public import PhyslibAlpha.Mathematics.LadderSystem.SymmetricPower
/-!

# The harmonic oscillator as a ladder system

The ladder operators of the d-dimensional harmonic oscillator form a `LadderSystem`.

## i. Overview

The lowering and raising operators `loweringCLM`/`raisingCLM` of the `d`-dimensional quantum
harmonic oscillator satisfy the canonical commutation relations, so they form a
`LadderSystem` on Schwartz space. The number operator of that ladder system is `numberCLM`.

## ii. Key results

- `toLadderSystem` : the lowering and raising operators bundled as a `LadderSystem`.
- `toLadderSystem_N_toLinearMap` : the number operators of `toLadderSystem` are `numberCLM`.

## iii. Table of contents

- A. The ladder system

## iv. References

* None.
-/

@[expose] public section

namespace QuantumMechanics
namespace HarmonicOscillator
noncomputable section
open ContinuousLinearMap SchwartzMap

variable {d : ℕ}

attribute [local instance 100] LieRing.ofAssociativeRing

/-!

## A. The ladder system

-/

/-- The lowering and raising operators on Schwartz space, bundled as a `LadderSystem`. -/
def toLadderSystem (Q : HarmonicOscillator d) : LadderSystem ℂ (𝓢(Space d, ℂ)) d where
  a i := (Q.loweringCLM i).toLinearMap
  ac i := (Q.raisingCLM i).toLinearMap
  comm_a_ac i j := by
    have h := Q.lowering_commutation_raising i j
    apply_fun ContinuousLinearMap.toLinearMap at h
    rcases eq_or_ne i j with rfl | hij
    · simpa [LieRing.of_associative_ring_bracket, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.coe_comp, Module.End.mul_eq_comp, Module.End.one_eq_id,
        ContinuousLinearMap.one_def] using h
    · simpa [LieRing.of_associative_ring_bracket, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.coe_comp, Module.End.mul_eq_comp, hij,
        KroneckerDelta.eq_zero_of_ne hij] using h
  comm_a_a i j := by
    have h := Q.lowering_commutation_lowering i j
    apply_fun ContinuousLinearMap.toLinearMap at h
    simpa [LieRing.of_associative_ring_bracket, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.coe_comp, Module.End.mul_eq_comp] using h
  comm_ac_ac i j := by
    have h := Q.raising_commutation_raising i j
    apply_fun ContinuousLinearMap.toLinearMap at h
    simpa [LieRing.of_associative_ring_bracket, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.coe_comp, Module.End.mul_eq_comp] using h

lemma toLadderSystem_N_toLinearMap (Q : HarmonicOscillator d) (i : Fin d) :
    Q.toLadderSystem.N i = (Q.numberCLM i).toLinearMap := rfl

end
end HarmonicOscillator
end QuantumMechanics
