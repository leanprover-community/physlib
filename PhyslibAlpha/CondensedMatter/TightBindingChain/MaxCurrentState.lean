/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.CurrentEigenstates
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Uncertainty
/-!

# The maximal current state of the open tight binding chain

## i. Overview

The longest standing wave, the current eigenstate with `k = 1`, carries the largest current
`2 a t cos (π / (N + 1))` among the current eigenstates when `t ≥ 0`. Normalized, it is the
maximal current state. It sits at
the centre of the chain, `⟨X⟩ = a (N - 1) / 2`, at the centre of the band, `⟨H⟩ = E0`, and
`⟨⁅H, X⁆⟩ = -a t cos (π / (N + 1))` is the bound of its energy–position uncertainty relation.

## ii. Key results

- `currentEigenvalue_le_one` : for `t ≥ 0`, `k = 1` carries the largest current.
- `inner_openHamiltonian_currentEigenstate` : the Hamiltonian on the current eigenstates.
- `maxCurrentState` : the maximal current state, of norm one by `norm_maxCurrentState`.
- `expectation_openHamiltonian_maxCurrentState` : `⟨H⟩ = E0`.
- `expectation_position_maxCurrentState` : `⟨X⟩ = a (N - 1) / 2`.
- `expectation_bracket_maxCurrentState` : `⟨⁅H, X⁆⟩ = -a t cos (π / (N + 1))`.
- `robertson_schrodinger_maxCurrentState` : the energy–position uncertainty relation of the maximal
  current state.

## iii. Table of contents

- A. The largest current
- B. The Hamiltonian on the current eigenstates
- C. The maximal current state
- D. Expectations

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

/-- For `t ≥ 0`, the current eigenstate with `k = 1` carries the largest current. -/
lemma currentEigenvalue_le_one (ht : 0 ≤ T.t) {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ T.N) :
    T.currentEigenvalue k ≤ T.currentEigenvalue 1 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkN' : (k : ℝ) ≤ T.N + 1 := by exact_mod_cast hkN.trans (Nat.le_succ _)
  have hpi : (k : ℝ) * Real.pi / (T.N + 1) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have ha := T.a_pos
  refine mul_le_mul_of_nonneg_left (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hpi ?_)
    (by positivity)
  gcongr

/-!

## B. The Hamiltonian on the current eigenstates

-/

/-- The Hamiltonian on the current eigenstates:
`⟨m|H ψ_k⟩ = E0 ⟨m|ψ_k⟩ - 2 t sin θ iᵐ⁺¹ cos ((m + 1) θ)` with `θ = k π / (N + 1)`. -/
lemma inner_openHamiltonian_currentEigenstate (k : ℕ) (m : Fin T.N) :
    ⟪|m⟩, T.openHamiltonian (T.currentEigenstate k)⟫_ℂ =
      T.E0 * ⟪|m⟩, T.currentEigenstate k⟫_ℂ - 2 * T.t * Real.sin (k * Real.pi / (T.N + 1)) *
        Complex.I ^ ((m : ℕ) + 1) * Real.cos (((m : ℕ) + 1) * (k * Real.pi / (T.N + 1))) := by
  have hN : Real.sin (((T.N : ℝ) + 1) * (k * Real.pi / (T.N + 1))) = 0 := by
    rw [mul_div_cancel₀ _ (by positivity)]
    exact Real.sin_nat_mul_pi k
  rw [inner_currentEigenstate]
  simp only [currentEigenstate, map_sum, map_smul, inner_sum, inner_smul_right,
    inner_openHamiltonian]
  generalize (k : ℝ) * Real.pi / (T.N + 1) = θ at hN ⊢
  have key (n : Fin T.N) : Complex.I ^ (n : ℕ) * Real.sin (((n : ℕ) + 1) * θ) *
      (if m = n then (T.E0 : ℂ)
        else if (m : ℕ) + 1 = n ∨ (n : ℕ) + 1 = m then -(T.t : ℂ) else 0) =
      (if m = n then T.E0 * (Complex.I ^ (m : ℕ) * Real.sin (((m : ℕ) + 1) * θ)) else 0) +
      ((if (m : ℕ) + 1 = n then -(T.t * Complex.I ^ ((m : ℕ) + 1) *
        Real.sin (((m : ℕ) + 2) * θ)) else 0) +
      if (n : ℕ) + 1 = m then T.t * Complex.I ^ ((m : ℕ) + 1) *
        Real.sin ((m : ℕ) * θ) else 0) := by
    by_cases hmn : m = n
    · subst hmn
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega)]
      ring
    by_cases hA : (m : ℕ) + 1 = n
    · have hn : (n : ℕ) = m + 1 := hA.symm
      simp only [hmn, hn, true_or, show ¬ ((m : ℕ) + 1 + 1 = m) by omega, ite_true,
        ite_false, zero_add, add_zero]
      rw [show (((m + 1 : ℕ) : ℝ) + 1) = (m : ℕ) + 2 by push_cast; ring]
      ring
    by_cases hB : (n : ℕ) + 1 = m
    · simp only [hmn, hA, hB, or_true, ite_true, ite_false, zero_add]
      rw [← hB, Nat.cast_add_one, pow_succ, pow_succ]
      linear_combination (-(T.t : ℂ) * Complex.I ^ (n : ℕ) *
        Real.sin (((n : ℕ) + 1) * θ)) * Complex.I_sq
    · simp [hmn, hA, hB]
  have hv1 (h : ∀ n : Fin T.N, ¬ ((m : ℕ) + 1 = n)) : Real.sin (((m : ℕ) + 2) * θ) = 0 := by
    have hm : (m : ℕ) + 1 = T.N := by
      by_contra hne
      exact h ⟨(m : ℕ) + 1, by omega⟩ rfl
    have hm' : ((m : ℕ) : ℝ) + 1 = T.N := by exact_mod_cast hm
    rw [show ((m : ℕ) + 2 : ℝ) = T.N + 1 by linarith, hN]
  have hv2 (h : ∀ n : Fin T.N, ¬ ((n : ℕ) + 1 = m)) : Real.sin ((m : ℕ) * θ) = 0 := by
    have hm : (m : ℕ) = 0 := by
      by_contra hne
      exact h ⟨(m : ℕ) - 1, by omega⟩ (Nat.sub_add_cancel (by omega))
    simp [hm]
  have hr : Real.sin (((m : ℕ) + 2) * θ) - Real.sin ((m : ℕ) * θ) =
      2 * Real.sin θ * Real.cos (((m : ℕ) + 1) * θ) := by
    rw [show ((m : ℕ) + 2) * θ = ((m : ℕ) + 1) * θ + θ by ring,
      show ((m : ℕ) : ℝ) * θ = ((m : ℕ) + 1) * θ - θ by ring, Real.sin_add, Real.sin_sub]
    ring
  rw [Finset.sum_congr rfl fun n _ => key n, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _),
    sum_ite_eq_of_unique _ _ (fun n n' h h' => Fin.ext (by omega)) fun h => by simp [hv1 h],
    sum_ite_eq_of_unique _ _ (fun n n' h h' => Fin.ext (by omega)) fun h => by simp [hv2 h]]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  push_cast at hc ⊢
  linear_combination (-(T.t : ℂ) * Complex.I ^ ((m : ℕ) + 1)) * hc

/-!

## C. The maximal current state

-/

/-- The maximal current state: the current eigenstate with `k = 1`, times `√(2 / (N + 1))`. -/
noncomputable def maxCurrentState : T.HilbertSpace :=
  ((√(2 / (T.N + 1)) : ℝ) : ℂ) • T.currentEigenstate 1

/-- The maximal current state has norm one. -/
lemma norm_maxCurrentState : ‖T.maxCurrentState‖ = 1 := by
  have h := T.norm_sq_currentEigenstate le_rfl (Nat.one_le_iff_ne_zero.mpr (NeZero.ne T.N))
  rw [maxCurrentState, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    ← Real.sqrt_sq (norm_nonneg _), h, ← Real.sqrt_mul (by positivity),
    div_mul_div_comm, mul_comm (2 : ℝ), div_self (by positivity), Real.sqrt_one]

/-- The amplitude of the maximal current state on the site `m`. -/
lemma inner_maxCurrentState (m : Fin T.N) :
    ⟪|m⟩, T.maxCurrentState⟫_ℂ = (√(2 / (T.N + 1)) : ℝ) *
      (Complex.I ^ (m : ℕ) * Real.sin (((m : ℕ) + 1) * (Real.pi / (T.N + 1)))) := by
  rw [maxCurrentState, inner_smul_right, inner_currentEigenstate, Nat.cast_one, one_mul]

/-- The Hamiltonian on the maximal current state, site by site. -/
lemma inner_openHamiltonian_maxCurrentState (m : Fin T.N) :
    ⟪|m⟩, T.openHamiltonian T.maxCurrentState⟫_ℂ = T.E0 * ⟪|m⟩, T.maxCurrentState⟫_ℂ -
      (√(2 / (T.N + 1)) : ℝ) * (2 * T.t * Real.sin (Real.pi / (T.N + 1)) *
        Complex.I ^ ((m : ℕ) + 1) * Real.cos (((m : ℕ) + 1) * (Real.pi / (T.N + 1)))) := by
  rw [maxCurrentState, map_smul, inner_smul_right, inner_openHamiltonian_currentEigenstate,
    inner_smul_right, Nat.cast_one, one_mul]
  ring

/-- The maximal current state carries the current `2 a t cos (π / (N + 1))`. -/
lemma current_maxCurrentState :
    T.current T.maxCurrentState = (T.currentEigenvalue 1 : ℂ) • T.maxCurrentState := by
  rw [maxCurrentState, map_smul, current_currentEigenstate, smul_comm]

/-- The maximal current state as a state on the operators of the chain. -/
noncomputable abbrev maxCurrentVectorState :
    𝓢[ℂ, T.HilbertSpace →L[ℂ] T.HilbertSpace] :=
  ofVec T.norm_maxCurrentState

/-!

## D. Expectations

-/

/-- Expectations in the maximal current state are real parts of its diagonal matrix elements. -/
lemma expectation_maxCurrentState (A : Observable (T.HilbertSpace →L[ℂ] T.HilbertSpace)) :
    T.maxCurrentVectorState⟨A⟩ =
      (⟪T.maxCurrentState, (A : T.HilbertSpace →L[ℂ] T.HilbertSpace) T.maxCurrentState⟫_ℂ).re := by
  rw [← Complex.ofReal_re (T.maxCurrentVectorState⟨A⟩), ← apply_observable_eq_expectation,
    ofVec_apply]
  rfl

/-- `conj (iᵐ) iᵐ = 1`. -/
private lemma conj_I_pow_mul (m : ℕ) : (starRingEnd ℂ) (Complex.I ^ m) * Complex.I ^ m = 1 := by
  rw [map_pow, Complex.conj_I, ← mul_pow, neg_mul, Complex.I_mul_I, neg_neg, one_pow]

/-- The squared amplitudes of the maximal current state add up to one. -/
private lemma sum_norm_sq_inner_maxCurrentState :
    ∑ m, ‖⟪|m⟩, T.maxCurrentState⟫_ℂ‖ ^ 2 = 1 := by
  rw [localizedState.sum_sq_norm_inner_right, T.norm_maxCurrentState, one_pow]

/-- The maximal current state sits at the centre of the band, `⟨H⟩ = E0`. -/
lemma expectation_openHamiltonian_maxCurrentState :
    T.maxCurrentVectorState⟨T.openHamiltonianObservable⟩ = T.E0 := by
  rw [expectation_maxCurrentState, ← localizedState.sum_inner_mul_inner, Complex.re_sum,
    ← mul_one T.E0, ← T.sum_norm_sq_inner_maxCurrentState, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  change (⟪T.maxCurrentState, |m⟩⟫_ℂ * ⟪|m⟩, T.openHamiltonian T.maxCurrentState⟫_ℂ).re = _
  have hX : (starRingEnd ℂ) ⟪|m⟩, T.maxCurrentState⟫_ℂ * ((√(2 / (T.N + 1)) : ℝ) *
      (2 * T.t * Real.sin (Real.pi / (T.N + 1)) * Complex.I ^ ((m : ℕ) + 1) *
        Real.cos (((m : ℕ) + 1) * (Real.pi / (T.N + 1))))) =
      Complex.I * ((√(2 / (T.N + 1)) ^ 2 * Real.sin (((m : ℕ) + 1) * (Real.pi / (T.N + 1))) *
        (2 * T.t * Real.sin (Real.pi / (T.N + 1)) *
          Real.cos (((m : ℕ) + 1) * (Real.pi / (T.N + 1))))) : ℝ) := by
    rw [inner_maxCurrentState, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      pow_succ]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
    linear_combination (Complex.I * (√(2 / (T.N + 1)) : ℂ) ^ 2 *
      Real.sin (((m : ℕ) + 1) * (Real.pi / (T.N + 1))) * (2 * T.t *
        Real.sin (Real.pi / (T.N + 1)) * Real.cos (((m : ℕ) + 1) * (Real.pi / (T.N + 1))))) *
      conj_I_pow_mul (m : ℕ)
  rw [← inner_conj_symm, inner_openHamiltonian_maxCurrentState, mul_sub, hX, mul_left_comm,
    Complex.conj_mul', ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.sub_re, Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im,
    neg_zero, sub_zero]

/-- The maximal current state sits at the centre of the chain, `⟨X⟩ = a (N - 1) / 2`. -/
lemma expectation_position_maxCurrentState :
    T.maxCurrentVectorState⟨T.positionObservable⟩ = T.a * (T.N - 1) / 2 := by
  have hterm (m : Fin T.N) : (⟪T.maxCurrentState, |m⟩⟫_ℂ *
      ⟪|m⟩, T.position T.maxCurrentState⟫_ℂ).re =
      T.a * ((m : ℕ) * ‖⟪|m⟩, T.maxCurrentState⟫_ℂ‖ ^ 2) := by
    rw [← position_hermitian, position_apply_localizedState, inner_smul_left,
      Complex.conj_ofReal, ← inner_conj_symm, mul_left_comm, Complex.conj_mul']
    simp [← Complex.ofReal_pow, mul_assoc]
  have hrev (m : Fin T.N) :
      ‖⟪|Fin.rev m⟩, T.maxCurrentState⟫_ℂ‖ = ‖⟪|m⟩, T.maxCurrentState⟫_ℂ‖ := by
    have hm : ((Fin.rev m : ℕ) : ℝ) + 1 = T.N - (m : ℕ) := by
      rw [Fin.val_rev, Nat.cast_sub (by omega)]
      push_cast
      ring
    simp only [inner_maxCurrentState, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
      Complex.norm_real, hm]
    rw [show ((T.N : ℝ) - (m : ℕ)) * (Real.pi / (T.N + 1)) =
      Real.pi - ((m : ℕ) + 1) * (Real.pi / (T.N + 1)) by field_simp; ring, Real.sin_pi_sub]
  have hsum : ∑ m : Fin T.N, ((m : ℕ) : ℝ) * ‖⟪|m⟩, T.maxCurrentState⟫_ℂ‖ ^ 2 =
      (T.N - 1) / 2 := by
    have h := (Equiv.sum_comp Fin.revPerm
      fun m : Fin T.N => ((m : ℕ) : ℝ) * ‖⟪|m⟩, T.maxCurrentState⟫_ℂ‖ ^ 2).symm
    have hc (x : Fin T.N) : ((T.N - ((x : ℕ) + 1) : ℕ) : ℝ) = T.N - 1 - (x : ℕ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    simp only [Fin.revPerm_apply, hrev, Fin.val_rev, hc] at h
    have h2 : ∑ x : Fin T.N, ((T.N : ℝ) - 1 - (x : ℕ)) * ‖⟪|x⟩, T.maxCurrentState⟫_ℂ‖ ^ 2 =
        (T.N - 1) * 1 - ∑ x : Fin T.N, ((x : ℕ) : ℝ) * ‖⟪|x⟩, T.maxCurrentState⟫_ℂ‖ ^ 2 := by
      rw [← T.sum_norm_sq_inner_maxCurrentState, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    linarith
  rw [expectation_maxCurrentState, ← localizedState.sum_inner_mul_inner, Complex.re_sum]
  change ∑ m, (⟪T.maxCurrentState, |m⟩⟫_ℂ * ⟪|m⟩, T.position T.maxCurrentState⟫_ℂ).re = _
  simp only [hterm, ← Finset.mul_sum, hsum]
  ring

/-- The bracket of the maximal current state: `⟨⁅H, X⁆⟩ = -a t cos (π / (N + 1))`. -/
lemma expectation_bracket_maxCurrentState :
    T.maxCurrentVectorState⟨⁅T.openHamiltonianObservable, T.positionObservable⁆⟩ =
      -(T.a * T.t * Real.cos (Real.pi / (T.N + 1))) := by
  have hJ := T.current_maxCurrentState
  rw [current, LinearMap.smul_apply] at hJ
  have hv : (T.openHamiltonian ∘ₗ T.position - T.position ∘ₗ T.openHamiltonian)
      T.maxCurrentState = (-Complex.I * T.currentEigenvalue 1) • T.maxCurrentState := by
    rw [mul_smul, ← hJ, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  rw [expectation_maxCurrentState, selfAdjoint.coe_bracket]
  change (⟪T.maxCurrentState, (-(Complex.I / 2)) • (T.openHamiltonian ∘ₗ T.position -
    T.position ∘ₗ T.openHamiltonian) T.maxCurrentState⟫_ℂ).re = _
  rw [hv, smul_smul, inner_smul_right, inner_self_eq_norm_sq_to_K, T.norm_maxCurrentState,
    currentEigenvalue]
  simp only [Nat.cast_one, one_mul]
  generalize Real.cos (Real.pi / (T.N + 1)) = c
  rw [← Complex.ofReal_re (-(T.a * T.t * c))]
  congr 1
  push_cast
  linear_combination (T.a * T.t * c : ℂ) * Complex.I_sq

/-- **Energy–position uncertainty of the maximal current state.**
`Cov(H, X)² + (a t cos (π / (N + 1)))² ≤ Var H · Var X` in the maximal current state. -/
lemma robertson_schrodinger_maxCurrentState :
    covariance T.maxCurrentVectorState T.openHamiltonianObservable T.positionObservable ^ 2 +
        (T.a * T.t * Real.cos (Real.pi / (T.N + 1))) ^ 2 ≤
      variance T.maxCurrentVectorState T.openHamiltonianObservable *
        variance T.maxCurrentVectorState T.positionObservable := by
  have h := T.robertson_schrodinger_openHamiltonian_position T.maxCurrentVectorState
  rwa [expectation_bracket_maxCurrentState, neg_sq] at h

end TightBindingChain
end CondensedMatter
