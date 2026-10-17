/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.LongChainMonotonicity
/-!

# The fluctuation angle of the maximal current state

## i. Overview

In the maximal current state the energy and position fluctuations are uncorrelated, so the
pairing `ω(δH δX)` reduces to the bracket term `a t cos (π / (N + 1))`. Its modulus over
`σ_H σ_X` is the cosine of the angle between the two fluctuations: the fluctuation angle, with
`cos θ = 1 / C`. It vanishes exactly for `N = 2, 3`, opens from four sites on, grows
strictly with `N` and stays below `arccos (1 / √(π² / 3 - 2))`. The excess `δ = C - 1` is the
dimensional quantum of the chain, and it fixes the angle.

## ii. Key results

- `fluctuationAngle` : the angle between the energy and position fluctuations.
- `fluctuationAngle_eq` : `θ = arccos (1 / C)`.
- `fluctuationAngle_eq_zero_iff`, `fluctuationAngle_pos` : it vanishes iff `N = 2, 3`, and opens
  from `N = 4`.
- `fluctuationAngle_lt_fluctuationAngle`, `fluctuationAngle_lt` : it grows strictly with `N`, below
  its limit.
- `dimQuantum` : the dimensional quantum `δ = C - 1`.
- `fluctuationAngle_eq_dimQuantum` : `θ = arccos (1 / (1 + δ))`.

## iii. Table of contents

- A. The fluctuation angle
- B. The dimensional quantum

## iv. References

* H. P. Robertson, *A general formulation of the uncertainty principle and its classical
  interpretation*, Phys. Rev. 35 (1930) 667.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open ProbabilisticTheory UnitalPositiveLinearMap

variable (T : TightBindingChain)

/-!

## A. The fluctuation angle

-/

/-- The fluctuation angle: the angle between the energy and position fluctuations in the maximal
current state, `arccos (‖ω(δH δX)‖ / (σ_H σ_X))`. -/
noncomputable def fluctuationAngle : ℝ :=
  Real.arccos (‖T.maxCurrentVectorState
      ((centered T.maxCurrentVectorState T.openHamiltonianObservable : _) *
        centered T.maxCurrentVectorState T.positionObservable)‖ /
    √(variance T.maxCurrentVectorState T.openHamiltonianObservable *
      variance T.maxCurrentVectorState T.positionObservable))

/-- The fluctuation angle: `cos θ = 1 / C`. -/
lemma fluctuationAngle_eq (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.fluctuationAngle = Real.arccos (1 / T.uncertaintyRatio) := by
  have hC := (zero_lt_one.trans_le (T.one_le_uncertaintyRatio ht hN)).ne'
  have hB : |T.a * T.t * Real.cos (Real.pi / (T.N + 1))| ≠ 0 := fun h => by
    rw [uncertaintyRatio, h, div_zero] at hC
    exact hC rfl
  rw [fluctuationAngle, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, normSq_centered_pairing,
    covariance_maxCurrentState, expectation_bracket_maxCurrentState, uncertaintyRatio, one_div_div]
  congr 2
  rw [sq, zero_mul, zero_add, neg_sq, Real.sqrt_sq_eq_abs]

/-- The fluctuation angle vanishes exactly for `N = 2` and `N = 3`. -/
lemma fluctuationAngle_eq_zero_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.fluctuationAngle = 0 ↔ T.N = 2 ∨ T.N = 3 := by
  have h1 := T.one_le_uncertaintyRatio ht hN
  rw [T.fluctuationAngle_eq ht hN, Real.arccos_eq_zero, le_div_iff₀ (by linarith), one_mul,
    ← T.uncertaintyRatio_eq_one_iff ht hN]
  exact ⟨fun h => le_antisymm h h1, fun h => h.le⟩

/-- From four sites on, the fluctuation angle is open. -/
lemma fluctuationAngle_pos (ht : T.t ≠ 0) (hN : 4 ≤ T.N) : 0 < T.fluctuationAngle :=
  (Real.arccos_nonneg _).lt_of_ne fun h => by
    rcases (T.fluctuationAngle_eq_zero_iff ht (by omega)).mp h.symm with h | h <;> omega

private lemma arccos_inv_lt {C C' : ℝ} (hC : 1 ≤ C) (hCC' : C < C') :
    Real.arccos (1 / C) < Real.arccos (1 / C') :=
  Real.arccos_lt_arccos (by have := one_div_pos.mpr (by linarith : 0 < C'); linarith)
    (one_div_lt_one_div_of_lt (by linarith) hCC') (div_le_one_of_le₀ hC (by linarith))

/-- From four sites on, the fluctuation angle grows strictly with the number of sites. -/
lemma fluctuationAngle_lt_fluctuationAngle {T T' : TightBindingChain} (ht : T.t ≠ 0)
    (ht' : T'.t ≠ 0) (hN : 4 ≤ T.N) (hNN' : T.N < T'.N) :
    T.fluctuationAngle < T'.fluctuationAngle := by
  rw [T.fluctuationAngle_eq ht (by omega), T'.fluctuationAngle_eq ht' (by omega)]
  exact arccos_inv_lt (T.one_le_uncertaintyRatio ht (by omega))
    (uncertaintyRatio_lt_uncertaintyRatio ht ht' hN hNN')

/-- From four sites on, the fluctuation angle stays below `arccos (1 / √(π² / 3 - 2))`. -/
lemma fluctuationAngle_lt (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    T.fluctuationAngle < Real.arccos (1 / √(Real.pi ^ 2 / 3 - 2)) := by
  rw [T.fluctuationAngle_eq ht (by omega)]
  exact arccos_inv_lt (T.one_le_uncertaintyRatio ht (by omega))
    (T.uncertaintyRatio_lt_sqrt_pi_sq_div_three_sub_two ht hN)

/-!

## B. The dimensional quantum

-/

/-- The dimensional quantum of the chain: the excess `C - 1` over saturation. -/
noncomputable def dimQuantum : ℝ := T.uncertaintyRatio - 1

lemma dimQuantum_nonneg (ht : T.t ≠ 0) (hN : 2 ≤ T.N) : 0 ≤ T.dimQuantum :=
  sub_nonneg.mpr (T.one_le_uncertaintyRatio ht hN)

/-- The dimensional quantum vanishes exactly for `N = 2` and `N = 3`. -/
lemma dimQuantum_eq_zero_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.dimQuantum = 0 ↔ T.N = 2 ∨ T.N = 3 := by
  rw [dimQuantum, sub_eq_zero, T.uncertaintyRatio_eq_one_iff ht hN]

/-- From four sites on, the dimensional quantum is positive. -/
lemma dimQuantum_pos (ht : T.t ≠ 0) (hN : 4 ≤ T.N) : 0 < T.dimQuantum :=
  sub_pos.mpr (T.one_lt_uncertaintyRatio ht hN)

/-- From four sites on, the dimensional quantum grows strictly with the number of sites. -/
lemma dimQuantum_lt_dimQuantum {T T' : TightBindingChain} (ht : T.t ≠ 0) (ht' : T'.t ≠ 0)
    (hN : 4 ≤ T.N) (hNN' : T.N < T'.N) : T.dimQuantum < T'.dimQuantum :=
  sub_lt_sub_right (uncertaintyRatio_lt_uncertaintyRatio ht ht' hN hNN') 1

/-- From four sites on, the dimensional quantum stays below `√(π² / 3 - 2) - 1`. -/
lemma dimQuantum_lt (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    T.dimQuantum < √(Real.pi ^ 2 / 3 - 2) - 1 :=
  sub_lt_sub_right (T.uncertaintyRatio_lt_sqrt_pi_sq_div_three_sub_two ht hN) 1

/-- The dimensional quantum fixes the fluctuation angle: `θ = arccos (1 / (1 + δ))`. -/
lemma fluctuationAngle_eq_dimQuantum (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.fluctuationAngle = Real.arccos (1 / (1 + T.dimQuantum)) := by
  rw [T.fluctuationAngle_eq ht hN, dimQuantum, add_sub_cancel]

end TightBindingChain
end CondensedMatter
