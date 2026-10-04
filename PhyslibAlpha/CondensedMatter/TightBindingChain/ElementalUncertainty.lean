/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Saturation
/-!

# The elemental uncertainty of the open tight binding chain

## i. Overview

In the maximal current state of the open chain the energy and position fluctuations are
uncorrelated, so the uncertainty relation closes as an identity: the variance product is the
squared bracket `(a t cos (π / (N + 1)))²` plus the centered Gram defect. The constant
`C_Nava = √(Var H · Var X) / |a t cos (π / (N + 1))|` is therefore at least one, and equals
one exactly for `N = 2` and `N = 3`. From four sites on it is strictly larger than one.

## ii. Key results

- `covariance_maxCurrentState` : `Cov(H, X) = 0` in the maximal current state.
- `variance_mul_variance_maxCurrentState` : `Var H · Var X = (a t cos (π / (N + 1)))² + defect`.
- `CNava` : `C_Nava = √(Var H · Var X) / |a t cos (π / (N + 1))|`.
- `one_le_CNava`, `CNava_eq_one_iff`, `one_lt_CNava`.
- `nava_robertson_schrodinger_elemental_dimensional_uncertainty_inequality` : everything at once.

## iii. Table of contents

- A. No correlation
- B. The constant `C_Nava`

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open scoped ComplexOrder selfAdjoint
open ProbabilisticTheory
open InnerProductSpace UnitalPositiveLinearMap
variable (T : TightBindingChain)

/-!

## A. No correlation

-/

/-- The energy and position fluctuations of the maximal current state are uncorrelated. -/
lemma covariance_maxCurrentState :
    covariance T.maxCurrentVectorState T.openHamiltonianObservable T.positionObservable = 0 := by
  rw [covariance_eq_re_apply_centered_mul, apply_centered_mul_centered_ofVec,
    ← localizedState.sum_inner_mul_inner, Complex.re_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [← inner_conj_symm, inner_energyFluctuation_maxCurrentState,
    inner_positionFluctuation_maxCurrentState, inner_maxCurrentState]
  simp only [map_neg, map_mul, Complex.conj_ofReal, map_pow, Complex.conj_I, map_ofNat]
  have hI : (-Complex.I) ^ ((m : ℕ) + 1) * Complex.I ^ (m : ℕ) = -Complex.I := by
    rw [pow_succ, mul_right_comm, ← mul_pow, neg_mul, Complex.I_mul_I, neg_neg, one_pow, one_mul]
  generalize Real.sin (Real.pi / (T.N + 1)) = S
  generalize Real.sin (((m : ℕ) + 1) * (Real.pi / (T.N + 1))) = s
  generalize Real.cos (((m : ℕ) + 1) * (Real.pi / (T.N + 1))) = k
  generalize √(2 / (T.N + 1)) = c
  rw [show -((c : ℂ) * (2 * T.t * S * (-Complex.I) ^ ((m : ℕ) + 1) * k)) *
      ((T.a * ((m : ℕ) - (T.N - 1) / 2) : ℝ) * (c * (Complex.I ^ (m : ℕ) * s))) =
      Complex.I * ((c * (2 * T.t * S * k) * (T.a * ((m : ℕ) - (T.N - 1) / 2) * (c * s)) : ℝ)) by
    push_cast
    linear_combination (-(c : ℂ) * (2 * T.t * S * k) * (T.a * ((m : ℕ) - (T.N - 1) / 2)) *
      (c * s)) * hI,
    Complex.I_mul_re, Complex.ofReal_im, neg_zero]

/-- The uncertainty identity of the maximal current state:
`Var H · Var X = (a t cos (π / (N + 1)))² + defect`. -/
lemma variance_mul_variance_maxCurrentState :
    variance T.maxCurrentVectorState T.openHamiltonianObservable *
        variance T.maxCurrentVectorState T.positionObservable =
      (T.a * T.t * Real.cos (Real.pi / (T.N + 1))) ^ 2 +
        centeredGramDefect T.maxCurrentVectorState T.openHamiltonianObservable
          T.positionObservable := by
  have h := robertson_gap_decomposition T.maxCurrentVectorState T.openHamiltonianObservable
    T.positionObservable
  rw [expectation_bracket_maxCurrentState, neg_sq, covariance_maxCurrentState] at h
  linarith

/-!

## B. The constant `C_Nava`

-/

/-- `C_Nava = √(Var H · Var X) / |a t cos (π / (N + 1))|` in the maximal current state. -/
noncomputable def CNava : ℝ :=
  √(variance T.maxCurrentVectorState T.openHamiltonianObservable *
    variance T.maxCurrentVectorState T.positionObservable) /
      |T.a * T.t * Real.cos (Real.pi / (T.N + 1))|

/-- The bound `a t cos (π / (N + 1))` is nonzero for `t ≠ 0` and `N ≥ 2`. -/
lemma bound_ne_zero (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.a * T.t * Real.cos (Real.pi / (T.N + 1)) ≠ 0 := by
  have hN' : (2 : ℝ) ≤ T.N := by exact_mod_cast hN
  refine mul_ne_zero (mul_ne_zero T.a_pos.ne' ht) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).ne'
  · linarith [show 0 < Real.pi / (T.N + 1) by positivity, Real.pi_pos]
  · rw [div_lt_div_iff_of_pos_left Real.pi_pos (by positivity) two_pos]
    linarith

/-- `C_Nava` is at least one. -/
lemma one_le_CNava (ht : T.t ≠ 0) (hN : 2 ≤ T.N) : 1 ≤ T.CNava := by
  rw [CNava, one_le_div (abs_pos.mpr (T.bound_ne_zero ht hN)), ← Real.sqrt_sq_eq_abs,
    variance_mul_variance_maxCurrentState]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (centeredGramDefect_nonneg _ _ _))

/-- `C_Nava` equals one exactly for `N = 2` and `N = 3`. -/
lemma CNava_eq_one_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.CNava = 1 ↔ T.N = 2 ∨ T.N = 3 := by
  rw [CNava, div_eq_one_iff_eq (abs_pos.mpr (T.bound_ne_zero ht hN)).ne',
    ← Real.sqrt_sq_eq_abs, variance_mul_variance_maxCurrentState,
    Real.sqrt_inj (add_nonneg (sq_nonneg _) (centeredGramDefect_nonneg _ _ _)) (sq_nonneg _),
    add_eq_left, centeredGramDefect_maxCurrentState_eq_zero_iff T ht hN]

/-- From four sites on, `C_Nava` is strictly larger than one. -/
lemma one_lt_CNava (ht : T.t ≠ 0) (hN : 4 ≤ T.N) : 1 < T.CNava :=
  (T.one_le_CNava ht (by omega)).lt_of_ne fun h => by
    rcases (T.CNava_eq_one_iff ht (by omega)).mp h.symm with h | h <;> omega

/-- **Nava–Robertson–Schrödinger elemental dimensional uncertainty inequality.** In the maximal
current state, `Var H · Var X = (a t cos (π / (N + 1)))² + defect`, `C_Nava` is at least one, and
it equals one exactly for `N = 2` and `N = 3`. -/
theorem nava_robertson_schrodinger_elemental_dimensional_uncertainty_inequality (ht : T.t ≠ 0)
    (hN : 2 ≤ T.N) :
    variance T.maxCurrentVectorState T.openHamiltonianObservable *
        variance T.maxCurrentVectorState T.positionObservable =
      (T.a * T.t * Real.cos (Real.pi / (T.N + 1))) ^ 2 +
        centeredGramDefect T.maxCurrentVectorState T.openHamiltonianObservable
          T.positionObservable ∧
      1 ≤ T.CNava ∧ (T.CNava = 1 ↔ T.N = 2 ∨ T.N = 3) :=
  ⟨T.variance_mul_variance_maxCurrentState, T.one_le_CNava ht hN,
    T.CNava_eq_one_iff ht hN⟩

end TightBindingChain
end CondensedMatter
