/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Current.SpeedLimit
public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.UncertaintyRatio
/-!

# Mandelstam–Tamm and Cramér–Rao in the maximal current state

## i. Overview

In the maximal current state the current is `⟨J⟩ = 2 a t cos (π / (N + 1))`
(`expectation_current_maxCurrentState`), and the Mandelstam–Tamm ratio
`⟨J⟩² / (4 Var H · Var X)` is exactly `1 / C²`. Mandelstam–Tamm and Cramér–Rao are therefore
attained together, exactly for `N = 2` and `N = 3`, and both are missed from four sites on.

## ii. Key results

- `mandelstamTammRatio_maxCurrentState` : the ratio is `1 / C²`.
- `mandelstamTammRatio_maxCurrentState_eq_one_iff` : both bounds are attained iff `N = 2, 3`.
- `mandelstamTammRatio_maxCurrentState_lt_one` : both are missed for `N ≥ 4`.

## iii. Table of contents

- A. The Mandelstam–Tamm ratio of the maximal current state

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

## A. The Mandelstam–Tamm ratio of the maximal current state

-/

/-- In the maximal current state the Mandelstam–Tamm ratio is `1 / C²`. -/
lemma mandelstamTammRatio_maxCurrentState :
    T.mandelstamTammRatio T.maxCurrentVectorState = 1 / T.uncertaintyRatio ^ 2 := by
  rw [mandelstamTammRatio, expectation_current_maxCurrentState, uncertaintyRatio, div_pow,
    Real.sq_sqrt (mul_nonneg (variance_nonneg _ _) (variance_nonneg _ _)), sq_abs, one_div_div]
  ring

/-- Mandelstam–Tamm and Cramér–Rao are attained in the maximal current state iff `N = 2, 3`. -/
lemma mandelstamTammRatio_maxCurrentState_eq_one_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.mandelstamTammRatio T.maxCurrentVectorState = 1 ↔ T.N = 2 ∨ T.N = 3 := by
  rw [mandelstamTammRatio_maxCurrentState, one_div, inv_eq_one,
    pow_eq_one_iff_of_nonneg (by unfold uncertaintyRatio; positivity) two_ne_zero,
    uncertaintyRatio_eq_one_iff T ht hN]

/-- From four sites on, the maximal current state misses Mandelstam–Tamm and Cramér–Rao. -/
lemma mandelstamTammRatio_maxCurrentState_lt_one (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    T.mandelstamTammRatio T.maxCurrentVectorState < 1 :=
  (T.mandelstamTammRatio_le_one _).lt_of_ne fun h => by
    rcases (T.mandelstamTammRatio_maxCurrentState_eq_one_iff ht (by omega)).mp h with h | h <;>
      omega

end TightBindingChain
end CondensedMatter
