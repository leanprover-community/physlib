/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic
public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.MandelstamTamm
/-!

# Mandelstam–Tamm and Cramér–Rao on the open tight binding cube

## i. Overview

In the maximal current state of the cube, each axis sees only its own chain, so the
Mandelstam–Tamm ratio `⟨J⟩² / (4 Var H · Var X)` of an axis is the ratio `1 / C²` of the maximal
current state of that chain.

## ii. Key results

- `mandelstamTammRatio_alongX` (and `Y`, `Z`) : each axis of the cube has the ratio of its chain.

## iii. Table of contents

- A. The Mandelstam–Tamm ratio along each axis

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open scoped ComplexOrder selfAdjoint QuantumMechanics.FiniteHilbertSpace
open ProbabilisticTheory
open QuantumMechanics FiniteHilbertSpace UnitalPositiveLinearMap

/-!

## A. The Mandelstam–Tamm ratio along each axis

-/

variable (Tx Ty Tz : TightBindingChain)

/-- Along `x`, the maximal current state of the cube has the ratio `1 / C²` of `Tx`. -/
lemma mandelstamTammRatio_alongX :
    (Tx.maxCurrentCubeVectorState Ty Tz)⟨Tx.alongX Ty Tz Tx.currentObservable⟩ ^ 2 /
      (4 * (variance (Tx.maxCurrentCubeVectorState Ty Tz)
          (Tx.alongX Ty Tz Tx.openHamiltonianObservable) *
        variance (Tx.maxCurrentCubeVectorState Ty Tz)
          (Tx.alongX Ty Tz Tx.positionObservable))) = 1 / Tx.uncertaintyRatio ^ 2 := by
  have h : (Tx.maxCurrentCubeVectorState Ty Tz)⟨Tx.alongX Ty Tz Tx.currentObservable⟩ =
      Tx.maxCurrentVectorState⟨Tx.currentObservable⟩ :=
    expectation_onFstObservable Tx.norm_maxCurrentState
      (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _
  rw [h, variance_alongX, variance_alongX]
  exact Tx.mandelstamTammRatio_maxCurrentState

/-- Along `y`, the maximal current state of the cube has the ratio `1 / C²` of `Ty`. -/
lemma mandelstamTammRatio_alongY :
    (Tx.maxCurrentCubeVectorState Ty Tz)⟨Tx.alongY Ty Tz Ty.currentObservable⟩ ^ 2 /
      (4 * (variance (Tx.maxCurrentCubeVectorState Ty Tz)
          (Tx.alongY Ty Tz Ty.openHamiltonianObservable) *
        variance (Tx.maxCurrentCubeVectorState Ty Tz)
          (Tx.alongY Ty Tz Ty.positionObservable))) = 1 / Ty.uncertaintyRatio ^ 2 := by
  have h : (Tx.maxCurrentCubeVectorState Ty Tz)⟨Tx.alongY Ty Tz Ty.currentObservable⟩ =
      Ty.maxCurrentVectorState⟨Ty.currentObservable⟩ :=
    (expectation_onSndObservable Tx.norm_maxCurrentState
      (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _).trans
    (expectation_onFstObservable Ty.norm_maxCurrentState Tz.norm_maxCurrentState _)
  rw [h, variance_alongY, variance_alongY]
  exact Ty.mandelstamTammRatio_maxCurrentState

/-- Along `z`, the maximal current state of the cube has the ratio `1 / C²` of `Tz`. -/
lemma mandelstamTammRatio_alongZ :
    (Tx.maxCurrentCubeVectorState Ty Tz)⟨Tx.alongZ Ty Tz Tz.currentObservable⟩ ^ 2 /
      (4 * (variance (Tx.maxCurrentCubeVectorState Ty Tz)
          (Tx.alongZ Ty Tz Tz.openHamiltonianObservable) *
        variance (Tx.maxCurrentCubeVectorState Ty Tz)
          (Tx.alongZ Ty Tz Tz.positionObservable))) = 1 / Tz.uncertaintyRatio ^ 2 := by
  have h : (Tx.maxCurrentCubeVectorState Ty Tz)⟨Tx.alongZ Ty Tz Tz.currentObservable⟩ =
      Tz.maxCurrentVectorState⟨Tz.currentObservable⟩ :=
    (expectation_onSndObservable Tx.norm_maxCurrentState
      (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _).trans
    (expectation_onSndObservable Ty.norm_maxCurrentState Tz.norm_maxCurrentState _)
  rw [h, variance_alongZ, variance_alongZ]
  exact Tz.mandelstamTammRatio_maxCurrentState

end TightBindingChain
end CondensedMatter
