/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState
/-!

# Saturation of the uncertainty relation in the maximal current state

## i. Overview

The energy–position uncertainty relation is an equality exactly when the centered Gram defect
vanishes, that is when the energy and position fluctuations of the state are parallel. In the
maximal current state of an open chain with `N ≥ 2` sites and hopping `t ≠ 0` this happens only
for `N = 2` and `N = 3`: the first two sites force `4 cos² (π / (N + 1)) = N - 1`. From four
sites on, the relation is strict.

## ii. Key results

- `inner_energyFluctuation_maxCurrentState` : the energy fluctuation, site by site.
- `inner_positionFluctuation_maxCurrentState` : the position fluctuation, site by site.
- `centeredGramDefect_maxCurrentState_eq_zero_iff` : the defect vanishes iff `N = 2, 3`.
- `robertson_schrodinger_maxCurrentState_eq_iff` : the relation is an equality iff `N = 2, 3`.
- `robertson_schrodinger_maxCurrentState_lt` : the relation is strict for `N ≥ 4`.

## iii. Table of contents

- A. The fluctuations
- B. Saturation

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

## A. The fluctuations

-/

/-- The energy fluctuation of the maximal current state, site by site. -/
lemma inner_energyFluctuation_maxCurrentState (m : Fin T.N) :
    ⟪|m⟩, (T.openHamiltonianObservable : T.HilbertSpace →L[ℂ] T.HilbertSpace) T.maxCurrentState -
      T.maxCurrentVectorState⟨T.openHamiltonianObservable⟩ • T.maxCurrentState⟫_ℂ =
      -((√(2 / (T.N + 1)) : ℝ) * (2 * T.t * Real.sin (Real.pi / (T.N + 1)) *
        Complex.I ^ ((m : ℕ) + 1) * Real.cos (((m : ℕ) + 1) * (Real.pi / (T.N + 1))))) := by
  rw [expectation_openHamiltonian_maxCurrentState, inner_sub_right, ← Complex.coe_smul,
    inner_smul_right]
  change ⟪|m⟩, T.openHamiltonian T.maxCurrentState⟫_ℂ - _ = _
  rw [inner_openHamiltonian_maxCurrentState]
  ring

/-- The position fluctuation of the maximal current state, site by site. -/
lemma inner_positionFluctuation_maxCurrentState (m : Fin T.N) :
    ⟪|m⟩, (T.positionObservable : T.HilbertSpace →L[ℂ] T.HilbertSpace) T.maxCurrentState -
      T.maxCurrentVectorState⟨T.positionObservable⟩ • T.maxCurrentState⟫_ℂ =
      (T.a * ((m : ℕ) - (T.N - 1) / 2) : ℝ) * ⟪|m⟩, T.maxCurrentState⟫_ℂ := by
  rw [expectation_position_maxCurrentState, inner_sub_right, ← Complex.coe_smul,
    inner_smul_right]
  change ⟪|m⟩, T.position T.maxCurrentState⟫_ℂ - _ = _
  rw [← position_hermitian, position_apply_localizedState, inner_smul_left, Complex.conj_ofReal]
  push_cast
  ring

/-!

## B. Saturation

-/

/-- In the maximal current state, `(2 m - N + 1) cos θ sin ((m + 1) θ) + (N - 1) sin θ
cos ((m + 1) θ) = 0` on every site when `N = 2, 3`, where `θ = π / (N + 1)`. -/
private lemma parallel_of_two_or_three (h : T.N = 2 ∨ T.N = 3) (m : Fin T.N) :
    (2 * ((m : ℕ) : ℝ) - T.N + 1) * Real.cos (Real.pi / (T.N + 1)) *
        Real.sin (((m : ℕ) + 1) * (Real.pi / (T.N + 1))) +
      (T.N - 1) * Real.sin (Real.pi / (T.N + 1)) *
        Real.cos (((m : ℕ) + 1) * (Real.pi / (T.N + 1))) = 0 := by
  have hm := m.isLt
  rcases (by omega : (m : ℕ) = 0 ∨ (m : ℕ) + 1 = T.N ∨ (T.N = 3 ∧ (m : ℕ) = 1)) with
    h0 | hl | ⟨h3, h1⟩
  · simp only [h0, Nat.cast_zero, zero_add, one_mul]
    ring
  · have hl' : ((m : ℕ) : ℝ) + 1 = T.N := by exact_mod_cast hl
    rw [hl', show (T.N : ℝ) * (Real.pi / (T.N + 1)) = Real.pi - Real.pi / (T.N + 1) by
      field_simp; ring, Real.sin_pi_sub, Real.cos_pi_sub, ← hl']
    ring
  · simp only [h1, h3, Nat.cast_one, Nat.cast_ofNat]
    rw [show ((1 : ℝ) + 1) * (Real.pi / (3 + 1)) = Real.pi / 2 by ring, Real.cos_pi_div_two]
    ring

/-- In the maximal current state of a chain with `N ≥ 2` sites and hopping `t ≠ 0`, the centered
Gram defect of `H` and `X` vanishes exactly for `N = 2` and `N = 3`. -/
theorem centeredGramDefect_maxCurrentState_eq_zero_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    centeredGramDefect T.maxCurrentVectorState T.openHamiltonianObservable
      T.positionObservable = 0 ↔ T.N = 2 ∨ T.N = 3 := by
  have hu := T.inner_energyFluctuation_maxCurrentState
  have hw := T.inner_positionFluctuation_maxCurrentState
  rw [centeredGramDefect_ofVec]
  generalize (T.openHamiltonianObservable : T.HilbertSpace →L[ℂ] T.HilbertSpace)
    T.maxCurrentState - T.maxCurrentVectorState⟨T.openHamiltonianObservable⟩ •
      T.maxCurrentState = u at hu ⊢
  generalize (T.positionObservable : T.HilbertSpace →L[ℂ] T.HilbertSpace) T.maxCurrentState -
    T.maxCurrentVectorState⟨T.positionObservable⟩ • T.maxCurrentState = w at hw ⊢
  have hpar := T.parallel_of_two_or_three
  simp only [inner_maxCurrentState] at hw
  generalize hθ : Real.pi / (T.N + 1) = θ at hu hw hpar
  have hN' : (2 : ℝ) ≤ T.N := by exact_mod_cast hN
  have hθ0 : 0 < θ := hθ ▸ by positivity
  have hθ2 : θ < Real.pi / 2 := hθ ▸ by
    rw [div_lt_div_iff_of_pos_left Real.pi_pos (by positivity) two_pos]
    linarith
  have hS := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hC := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ2⟩
  have hc : 0 < √(2 / (T.N + 1)) := Real.sqrt_pos.mpr (by positivity)
  have ha := T.a_pos
  have hu0 := hu ⟨0, by omega⟩
  have hw0 := hw ⟨0, by omega⟩
  simp only [Nat.cast_zero, zero_add, one_mul, pow_zero, pow_one] at hu0 hw0
  have hune : u ≠ 0 := fun h => by
    rw [h, inner_zero_right, zero_eq_neg] at hu0
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne') (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr ht)) (Complex.ofReal_ne_zero.mpr
        hS.ne')) Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hC.ne')) hu0
  have hwne : w ≠ 0 := fun h => by
    rw [h, inner_zero_right] at hw0
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_neg_of_pos_of_neg ha (by linarith)).ne)
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne') (Complex.ofReal_ne_zero.mpr hS.ne')) hw0.symm
  rw [sub_eq_zero, ← mul_pow, eq_comm, pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero,
    norm_inner_eq_norm_iff hune hwne]
  constructor
  · rintro ⟨r, -, rfl⟩
    have hw1 := hw ⟨1, by omega⟩
    rw [inner_smul_right, hu] at hw1 hw0
    simp only [Nat.cast_zero, Nat.cast_one, zero_add, one_mul, pow_one, one_add_one_eq_two,
      Real.sin_two_mul, Real.cos_two_mul] at hw1 hw0
    have hSC := Real.sin_sq_add_cos_sq θ
    generalize Real.sin θ = S at hS hw0 hw1 hSC
    generalize hCθ : Real.cos θ = C at hC hw0 hw1 hSC
    generalize √(2 / (T.N + 1)) = c at hc hw0 hw1
    push_cast at hw0 hw1
    have key : ((T.a * c ^ 2 * T.t * S ^ 2 * (4 * C ^ 2 - (T.N - 1)) : ℝ) : ℂ) = 0 := by
      push_cast
      linear_combination (-(c * (2 * T.t * S * Complex.I ^ 2 * (2 * C ^ 2 - 1)))) * hw0 -
        (-(c * (2 * T.t * S * Complex.I * C))) * hw1 +
          (T.a * c ^ 2 * T.t * S ^ 2 * (4 * C ^ 2 - (T.N - 1))) * Complex.I_sq
    have h4 : 4 * C ^ 2 = T.N - 1 := by
      rcases mul_eq_zero.mp (Complex.ofReal_eq_zero.mp key) with h | h
      · simp [ha.ne', hc.ne', ht, hS.ne'] at h
      · linarith
    by_contra hne
    rcases (by omega : T.N = 4 ∨ 5 ≤ T.N) with h4' | h5
    · rw [h4'] at hθ h4
      rw [← hθ, show ((4 : ℕ) : ℝ) + 1 = 5 by norm_num, Real.cos_pi_div_five] at hCθ
      subst hCθ
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    · have : (5 : ℝ) ≤ T.N := by exact_mod_cast h5
      nlinarith
  · intro h
    have hC' := hC.ne'
    refine ⟨-Complex.I * (T.a * (T.N - 1) / (4 * T.t * Real.cos θ) : ℝ),
      mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr
        (div_ne_zero (mul_pos ha (by linarith)).ne' (mul_ne_zero (mul_ne_zero four_ne_zero ht)
          hC'))), ?_⟩
    apply localizedState.repr.injective
    ext m
    simp only [OrthonormalBasis.repr_apply_apply]
    rw [inner_smul_right, hw, hu]
    have hf := congrArg (fun x : ℝ => (x : ℂ)) (hpar h m)
    have htt := mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht)
    have hCC := mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hC')
    generalize Real.sin (((m : ℕ) + 1) * θ) = s at hf ⊢
    generalize Real.cos (((m : ℕ) + 1) * θ) = k at hf ⊢
    generalize Real.sin θ = S at hf ⊢
    generalize Real.cos θ = C at hf hCC ⊢
    generalize √(2 / (T.N + 1)) = c
    push_cast at hf ⊢
    linear_combination (T.a * c * Complex.I ^ (m : ℕ) * (C : ℂ)⁻¹ / 2) * hf -
      T.a * c * Complex.I ^ (m : ℕ) * ((m : ℕ) - (T.N - 1) / 2) * s * hCC -
      T.a * c * Complex.I ^ (m : ℕ) * (T.N - 1) * S * k * (C : ℂ)⁻¹ / 2 * (T.t * (T.t : ℂ)⁻¹) *
        Complex.I_sq +
      T.a * c * Complex.I ^ (m : ℕ) * (T.N - 1) * S * k * (C : ℂ)⁻¹ / 2 * htt

/-- **Saturation.** In the maximal current state of a chain with `N ≥ 2` sites and hopping
`t ≠ 0`, the energy–position uncertainty relation is an equality exactly for `N = 2, 3`. -/
theorem robertson_schrodinger_maxCurrentState_eq_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    covariance T.maxCurrentVectorState T.openHamiltonianObservable T.positionObservable ^ 2 +
        (T.a * T.t * Real.cos (Real.pi / (T.N + 1))) ^ 2 =
      variance T.maxCurrentVectorState T.openHamiltonianObservable *
        variance T.maxCurrentVectorState T.positionObservable ↔ T.N = 2 ∨ T.N = 3 := by
  rw [← neg_sq (T.a * _ * _), ← expectation_bracket_maxCurrentState,
    robertson_schrodinger_eq_iff_gram_zero,
    centeredGramDefect_maxCurrentState_eq_zero_iff T ht hN]

/-- From four sites on, the uncertainty relation of the maximal current state is strict. -/
theorem robertson_schrodinger_maxCurrentState_lt (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    covariance T.maxCurrentVectorState T.openHamiltonianObservable T.positionObservable ^ 2 +
        (T.a * T.t * Real.cos (Real.pi / (T.N + 1))) ^ 2 <
      variance T.maxCurrentVectorState T.openHamiltonianObservable *
        variance T.maxCurrentVectorState T.positionObservable :=
  (T.robertson_schrodinger_maxCurrentState).lt_of_ne fun h => by
    rcases (T.robertson_schrodinger_maxCurrentState_eq_iff ht (by omega)).mp h with h | h <;> omega

end TightBindingChain
end CondensedMatter
