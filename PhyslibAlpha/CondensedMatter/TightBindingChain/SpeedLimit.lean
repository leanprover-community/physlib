/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.MandelstamTamm
public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState
/-!

# The speed limit of the open tight binding chain

## i. Overview

For `t ≠ 0` the current eigenstates `ψ_1, …, ψ_N` carry distinct currents, so, normalized, they
form an orthonormal basis. Every current `2 a t cos (k π / (N + 1))` is at most
`maxCurrent = 2 |a t| cos (π / (N + 1))` in absolute value, hence so is the current `⟨J⟩` of
every state, pure or mixed: no state moves faster. The maximal current state reaches the bound.

## ii. Key results

- `currentBasis` : the orthonormal basis of normalized current eigenstates.
- `re_inner_current_eq_sum` : `re ⟨ψ|J|ψ⟩ = ∑ k, λ_k |⟨k|ψ⟩|²` in that basis.
- `abs_currentEigenvalue_le` : `|2 a t cos (k π / (N + 1))| ≤ maxCurrent` for `1 ≤ k ≤ N`.
- `expectation_current_maxCurrentState` : `⟨J⟩ = 2 a t cos (π / (N + 1))` in the maximal current
  state.
- `abs_expectation_current_le` : `|⟨J⟩| ≤ maxCurrent` in every state.
- `abs_expectation_current_maxCurrentState` : the maximal current state moves at `maxCurrent`.

## iii. Table of contents

- A. The largest current
- B. The basis of current eigenstates
- C. No state is faster

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

## A. The largest current

-/

/-- The largest current `2 |a t| cos (π / (N + 1))` of the open chain. -/
noncomputable def maxCurrent : ℝ := 2 * |T.a * T.t| * Real.cos (Real.pi / (T.N + 1))

/-- Every current eigenvalue is at most `maxCurrent` in absolute value. -/
lemma abs_currentEigenvalue_le {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ T.N) :
    |T.currentEigenvalue k| ≤ T.maxCurrent := by
  have hN : (0 : ℝ) < T.N + 1 := by positivity
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkN' : (k : ℝ) ≤ T.N := by exact_mod_cast hkN
  have hθ : k * Real.pi / (T.N + 1) ≤ Real.pi - Real.pi / (T.N + 1) := by
    rw [div_le_iff₀ hN, sub_mul, div_mul_cancel₀ _ hN.ne']
    nlinarith [Real.pi_pos]
  have hp : 0 < Real.pi / (T.N + 1) := by positivity
  have h1 := Real.cos_le_cos_of_nonneg_of_le_pi hp.le (by linarith)
    (div_le_div_of_nonneg_right (le_mul_of_one_le_left Real.pi_pos.le hk') hN.le)
  have h2 := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) hθ
  rw [Real.cos_pi_sub] at h2
  calc |T.currentEigenvalue k|
      = 2 * |T.a * T.t| * |Real.cos (k * Real.pi / (T.N + 1))| := by
        rw [currentEigenvalue, show 2 * T.a * T.t = 2 * (T.a * T.t) by ring, abs_mul, abs_mul,
          abs_two]
    _ ≤ T.maxCurrent := by
        unfold maxCurrent
        gcongr
        exact abs_le.mpr ⟨by linarith, h1⟩

/-!

## B. The basis of current eigenstates

-/

/-- The normalized current eigenstates `ψ_{k+1}`, `k < N`. -/
noncomputable def currentBasisVec (k : Fin T.N) : T.HilbertSpace :=
  ((√(2 / (T.N + 1)) : ℝ) : ℂ) • T.currentEigenstate ((k : ℕ) + 1)

lemma norm_currentBasisVec (k : Fin T.N) : ‖T.currentBasisVec k‖ = 1 := by
  rw [currentBasisVec, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    ← Real.sqrt_sq (norm_nonneg _), T.norm_sq_currentEigenstate (by omega) (by omega),
    ← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm (2 : ℝ),
    div_self (by positivity), Real.sqrt_one]

/-- The normalized current eigenstates are orthonormal. -/
lemma orthonormal_currentBasisVec (ht : T.t ≠ 0) : Orthonormal ℂ T.currentBasisVec := by
  rw [orthonormal_iff_ite]
  intro k l
  split_ifs with h
  · subst h
    rw [inner_self_eq_norm_sq_to_K, T.norm_currentBasisVec]
    simp
  · have hN : (0 : ℝ) < T.N + 1 := by positivity
    have hmem (m : Fin T.N) :
        (((m : ℕ) + 1 : ℕ) : ℝ) * Real.pi / (T.N + 1) ∈ Set.Icc 0 Real.pi := by
      have hm : (((m : ℕ) + 1 : ℕ) : ℝ) ≤ T.N + 1 := by
        exact_mod_cast (by omega : (m : ℕ) + 1 ≤ T.N + 1)
      exact ⟨by positivity, by rw [div_le_iff₀ hN]; nlinarith [Real.pi_pos]⟩
    have hne : T.currentEigenvalue ((k : ℕ) + 1) ≠ T.currentEigenvalue ((l : ℕ) + 1) := by
      intro he
      have hc := mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero T.a_pos.ne') ht) he
      have := Real.injOn_cos (hmem k) (hmem l) hc
      rw [div_left_inj' hN.ne', mul_left_inj' Real.pi_pos.ne', Nat.cast_inj] at this
      exact h (Fin.ext (by omega))
    have hJ (m : Fin T.N) : T.current (T.currentBasisVec m) =
        (T.currentEigenvalue ((m : ℕ) + 1) : ℂ) • T.currentBasisVec m := by
      rw [currentBasisVec, map_smul, current_currentEigenstate, smul_comm]
    have key := T.current_hermitian (T.currentBasisVec k) (T.currentBasisVec l)
    rw [hJ, hJ, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at key
    exact (mul_eq_mul_right_iff.mp key.symm).resolve_left
      (fun h' => hne (by exact_mod_cast h'.symm))

/-- The orthonormal basis of normalized current eigenstates. -/
noncomputable def currentBasis (ht : T.t ≠ 0) : OrthonormalBasis (Fin T.N) ℂ T.HilbertSpace :=
  OrthonormalBasis.mk (T.orthonormal_currentBasisVec ht)
    ((T.orthonormal_currentBasisVec ht).linearIndependent.span_eq_top_of_card_eq_finrank
      (by rw [Module.finrank_eq_card_basis localizedState.toBasis])).ge

/-!

## C. No state is faster

-/

/-- The current on the basis of current eigenstates. -/
lemma current_currentBasis (ht : T.t ≠ 0) (k : Fin T.N) :
    T.current (T.currentBasis ht k) =
      (T.currentEigenvalue ((k : ℕ) + 1) : ℂ) • T.currentBasis ht k := by
  simp only [currentBasis, OrthonormalBasis.coe_mk, currentBasisVec, map_smul,
    current_currentEigenstate, smul_comm _ (T.currentEigenvalue _ : ℂ)]

/-- The mean current in the basis of current eigenstates:
`re ⟨ψ|J|ψ⟩ = ∑ k, λ_k |⟨k|ψ⟩|²`. -/
lemma re_inner_current_eq_sum (ht : T.t ≠ 0) (ψ : T.HilbertSpace) :
    (⟪ψ, T.current ψ⟫_ℂ).re =
      ∑ k : Fin T.N, T.currentEigenvalue ((k : ℕ) + 1) * ‖⟪T.currentBasis ht k, ψ⟫_ℂ‖ ^ 2 := by
  rw [← (T.currentBasis ht).sum_inner_mul_inner, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← T.current_hermitian, current_currentBasis, inner_smul_left, Complex.conj_ofReal,
    ← inner_conj_symm ψ, mul_left_comm, Complex.conj_mul', ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- In every vector, `|re ⟨ψ|J|ψ⟩| ≤ maxCurrent ‖ψ‖²`. -/
lemma abs_re_inner_current_le (ht : T.t ≠ 0) (ψ : T.HilbertSpace) :
    |(⟪ψ, T.current ψ⟫_ℂ).re| ≤ T.maxCurrent * ‖ψ‖ ^ 2 := by
  let b := T.currentBasis ht
  have hsum := T.re_inner_current_eq_sum ht ψ
  rw [hsum, ← b.sum_sq_norm_inner_right, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hk := k.isLt
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖⟪b k, ψ⟫_ℂ‖)]
  exact mul_le_mul_of_nonneg_right (T.abs_currentEigenvalue_le (by omega) (by omega))
    (sq_nonneg _)

/-- **Speed limit.** In every state, `|⟨J⟩| ≤ maxCurrent`: no state of the open chain moves
faster than `2 |a t| cos (π / (N + 1))`. -/
theorem abs_expectation_current_le (ht : T.t ≠ 0)
    (ω : 𝓢[ℂ, T.HilbertSpace →L[ℂ] T.HilbertSpace]) :
    |ω⟨T.currentObservable⟩| ≤ T.maxCurrent := by
  have hpos (s : ℝ) (hs : |s| = 1) :
      0 ≤ ((T.maxCurrent : ℂ) • 1 - (s : ℂ) • (T.currentObservable :
        T.HilbertSpace →L[ℂ] T.HilbertSpace)) := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · change ⟪(T.maxCurrent : ℂ) • x - (s : ℂ) • T.current x, y⟫_ℂ =
        ⟪x, (T.maxCurrent : ℂ) • y - (s : ℂ) • T.current y⟫_ℂ
      rw [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_left, inner_smul_right,
        inner_smul_right, Complex.conj_ofReal, Complex.conj_ofReal, current_hermitian]
    · change 0 ≤ (⟪(T.maxCurrent : ℂ) • x - (s : ℂ) • T.current x, x⟫_ℂ).re
      rw [inner_sub_left, inner_smul_left, inner_smul_left, Complex.sub_re, Complex.conj_ofReal,
        Complex.conj_ofReal, Complex.re_ofReal_mul, Complex.re_ofReal_mul, current_hermitian]
      have hn : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
      have h1 := le_abs_self (s * (⟪x, T.current x⟫_ℂ).re)
      rw [abs_mul, hs, one_mul] at h1
      rw [hn]
      linarith [T.abs_re_inner_current_le ht x]
  have hω (s : ℝ) (hs : |s| = 1) : s * ω⟨T.currentObservable⟩ ≤ T.maxCurrent := by
    have h : 0 ≤ ω ((T.maxCurrent : ℂ) • 1 - (s : ℂ) • (T.currentObservable :
        T.HilbertSpace →L[ℂ] T.HilbertSpace)) := ω.map_nonneg (hpos s hs)
    rw [map_sub, map_smul, map_smul, map_one, apply_observable_eq_expectation] at h
    have := (Complex.nonneg_iff.mp h).1
    simpa using this
  exact abs_le.mpr ⟨by linarith [hω (-1) (by simp)], by linarith [hω 1 (by simp)]⟩

/-- The maximal current state carries the current `⟨J⟩ = 2 a t cos (π / (N + 1))`. -/
lemma expectation_current_maxCurrentState :
    T.maxCurrentVectorState⟨T.currentObservable⟩ =
      2 * (T.a * T.t * Real.cos (Real.pi / (T.N + 1))) := by
  have h := T.expectation_bracket_openHamiltonian_position T.maxCurrentVectorState
  rw [expectation_bracket_maxCurrentState] at h
  linarith

/-- The maximal current state moves at the speed limit. -/
lemma abs_expectation_current_maxCurrentState :
    |T.maxCurrentVectorState⟨T.currentObservable⟩| = T.maxCurrent := by
  have hN : (1 : ℝ) ≤ T.N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne T.N)
  have hc : 0 ≤ Real.cos (Real.pi / (T.N + 1)) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [show 0 < Real.pi / (T.N + 1) by positivity, Real.pi_pos],
      div_le_div_of_nonneg_left Real.pi_pos.le two_pos (by linarith)⟩
  rw [expectation_current_maxCurrentState, maxCurrent, abs_mul, abs_two, abs_mul (T.a * T.t),
    abs_of_nonneg hc]
  ring

end TightBindingChain
end CondensedMatter
