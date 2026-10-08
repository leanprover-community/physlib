/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube
public import PhyslibAlpha.CondensedMatter.TightBindingChain.SpeedLimit
/-!

# Mandelstam–Tamm and Cramér–Rao in the maximal current state

## i. Overview

In the maximal current state the current is `⟨J⟩ = 2 a t cos (π / (N + 1))`
(`expectation_current_maxCurrentState`), and the Mandelstam–Tamm ratio
`⟨J⟩² / (4 Var H · Var X)` is exactly `1 / C_Nava²`. Mandelstam–Tamm and Cramér–Rao are therefore
attained together, exactly for `N = 2` and `N = 3`, and both are missed from four sites on.
On the cube, each axis has the ratio `1 / C_Nava²` of its own chain.

## ii. Key results

- `mandelstamTammRatio_maxCurrentState` : the ratio is `1 / C_Nava²`.
- `mandelstamTammRatio_maxCurrentState_eq_one_iff` : both bounds are attained iff `N = 2, 3`.
- `mandelstamTammRatio_maxCurrentState_lt_one` : both are missed for `N ≥ 4`.
- `mandelstamTammRatio_alongX` (and `Y`, `Z`) : each axis of the cube has the ratio of its chain.

## iii. Table of contents

- A. The chain
- B. The cube

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open scoped ComplexOrder selfAdjoint QuantumMechanics.FiniteHilbertSpace
open ProbabilisticTheory
open QuantumMechanics FiniteHilbertSpace UnitalPositiveLinearMap
variable (T : TightBindingChain)

/-!

## A. The chain

-/

/-- In the maximal current state the Mandelstam–Tamm ratio is `1 / C_Nava²`. -/
lemma mandelstamTammRatio_maxCurrentState :
    T.mandelstamTammRatio T.maxCurrentVectorState = 1 / T.CNava ^ 2 := by
  rw [mandelstamTammRatio, expectation_current_maxCurrentState, CNava, div_pow,
    Real.sq_sqrt (mul_nonneg (variance_nonneg _ _) (variance_nonneg _ _)), sq_abs, one_div_div]
  ring

/-- Mandelstam–Tamm and Cramér–Rao are attained in the maximal current state iff `N = 2, 3`. -/
lemma mandelstamTammRatio_maxCurrentState_eq_one_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.mandelstamTammRatio T.maxCurrentVectorState = 1 ↔ T.N = 2 ∨ T.N = 3 := by
  rw [mandelstamTammRatio_maxCurrentState, one_div, inv_eq_one,
    pow_eq_one_iff_of_nonneg (by unfold CNava; positivity) two_ne_zero, CNava_eq_one_iff T ht hN]

/-- From four sites on, the maximal current state misses Mandelstam–Tamm and Cramér–Rao. -/
lemma mandelstamTammRatio_maxCurrentState_lt_one (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    T.mandelstamTammRatio T.maxCurrentVectorState < 1 :=
  (T.mandelstamTammRatio_le_one _).lt_of_ne fun h => by
    rcases (T.mandelstamTammRatio_maxCurrentState_eq_one_iff ht (by omega)).mp h with h | h <;>
      omega

/-!

## B. The cube

-/

variable (Tx Ty Tz : TightBindingChain)

/-- Along `x`, the maximal current state of the cube has the ratio `1 / C_Nava²` of `Tx`. -/
lemma mandelstamTammRatio_alongX :
    (Tx.maxCurrentCubeVectorState Ty Tz)⟨Tx.alongX Ty Tz Tx.currentObservable⟩ ^ 2 /
      (4 * (variance (Tx.maxCurrentCubeVectorState Ty Tz)
          (Tx.alongX Ty Tz Tx.openHamiltonianObservable) *
        variance (Tx.maxCurrentCubeVectorState Ty Tz)
          (Tx.alongX Ty Tz Tx.positionObservable))) = 1 / Tx.CNava ^ 2 := by
  have h : (Tx.maxCurrentCubeVectorState Ty Tz)⟨Tx.alongX Ty Tz Tx.currentObservable⟩ =
      Tx.maxCurrentVectorState⟨Tx.currentObservable⟩ :=
    expectation_onFstObservable Tx.norm_maxCurrentState
      (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _
  rw [h, variance_alongX, variance_alongX]
  exact Tx.mandelstamTammRatio_maxCurrentState

/-- Along `y`, the maximal current state of the cube has the ratio `1 / C_Nava²` of `Ty`. -/
lemma mandelstamTammRatio_alongY :
    (Tx.maxCurrentCubeVectorState Ty Tz)⟨Tx.alongY Ty Tz Ty.currentObservable⟩ ^ 2 /
      (4 * (variance (Tx.maxCurrentCubeVectorState Ty Tz)
          (Tx.alongY Ty Tz Ty.openHamiltonianObservable) *
        variance (Tx.maxCurrentCubeVectorState Ty Tz)
          (Tx.alongY Ty Tz Ty.positionObservable))) = 1 / Ty.CNava ^ 2 := by
  have h : (Tx.maxCurrentCubeVectorState Ty Tz)⟨Tx.alongY Ty Tz Ty.currentObservable⟩ =
      Ty.maxCurrentVectorState⟨Ty.currentObservable⟩ :=
    (expectation_onSndObservable Tx.norm_maxCurrentState
      (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _).trans
    (expectation_onFstObservable Ty.norm_maxCurrentState Tz.norm_maxCurrentState _)
  rw [h, variance_alongY, variance_alongY]
  exact Ty.mandelstamTammRatio_maxCurrentState

/-- Along `z`, the maximal current state of the cube has the ratio `1 / C_Nava²` of `Tz`. -/
lemma mandelstamTammRatio_alongZ :
    (Tx.maxCurrentCubeVectorState Ty Tz)⟨Tx.alongZ Ty Tz Tz.currentObservable⟩ ^ 2 /
      (4 * (variance (Tx.maxCurrentCubeVectorState Ty Tz)
          (Tx.alongZ Ty Tz Tz.openHamiltonianObservable) *
        variance (Tx.maxCurrentCubeVectorState Ty Tz)
          (Tx.alongZ Ty Tz Tz.positionObservable))) = 1 / Tz.CNava ^ 2 := by
  have h : (Tx.maxCurrentCubeVectorState Ty Tz)⟨Tx.alongZ Ty Tz Tz.currentObservable⟩ =
      Tz.maxCurrentVectorState⟨Tz.currentObservable⟩ :=
    (expectation_onSndObservable Tx.norm_maxCurrentState
      (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _).trans
    (expectation_onSndObservable Ty.norm_maxCurrentState Tz.norm_maxCurrentState _)
  rw [h, variance_alongZ, variance_alongZ]
  exact Tz.mandelstamTammRatio_maxCurrentState

end TightBindingChain
end CondensedMatter
