/-
Copyright (c) 2026 Brent Yee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brent Yee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The choice of the PBR phases

The choice of the number of copies, the angle and the unit-modulus phases in the PBR measurement.

## i. Overview

The entangled measurement in the Pusey–Barrett–Rudolph (PBR) theorem acts on `n` qubits and
involves a family of unit-modulus phases `ω z`. The product states it is tested against have real
amplitudes `∏ i, ![c, s] (z i)` on the computational basis vectors `z`, with `0 ≤ s ≤ c`. This
file makes the two choices on which the construction rests: a number of copies `n` with
`2 cⁿ ≤ (c + s)ⁿ`, and phases with `∑ z, ω z * ∏ i, ![c, s] (z i) = 0`, found with the
intermediate value theorem. In the PBR proof the latter makes every outcome of the measurement
orthogonal to one product state.

## ii. Key results

- `PBR.exists_two_mul_pow_le` : the choice of the number of copies.
- `PBR.exists_norm_pow_sub_pow_eq` : the choice of the angle.
- `PBR.exists_phases` : the choice of the unit-modulus phases.

## iii. Table of contents

- A. Choosing the number of copies
- B. Choosing the phases
  - B.1. Choosing the angle
  - B.2. Products of amplitudes
  - B.3. The phases

## iv. References

- M. F. Pusey, J. Barrett and T. Rudolph, *On the reality of the quantum state*,
  Nature Phys. 8, 475–478 (2012), arXiv:1111.3328. [ref: Pusey:2011de]

-/

@[expose] public section

noncomputable section

namespace QuantumMechanics.PBR

/-!
## A. Choosing the number of copies

-/

/-- For `0 < c` and `0 < s`, some number of copies `n` gives `2 cⁿ ≤ (c + s)ⁿ`. -/
lemma exists_two_mul_pow_le {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ∃ n : ℕ, 2 * c ^ n ≤ (c + s) ^ n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ)
    ((one_lt_div hc).mpr (by linarith) : 1 < (c + s) / c)
  rw [div_pow, lt_div_iff₀ (pow_pos hc n)] at hn
  exact ⟨n, hn.le⟩

/-!
## B. Choosing the phases

### B.1. Choosing the angle

-/

/-- If `0 ≤ s ≤ c` and `2 cⁿ ≤ (c + s)ⁿ`, some angle `α` gives
`‖(c + e^{iα} s)ⁿ - cⁿ‖ = cⁿ` (intermediate value theorem on `[0, π]`). -/
lemma exists_norm_pow_sub_pow_eq {c s : ℝ} {n : ℕ} (hs : 0 ≤ s) (hsc : s ≤ c)
    (hn : 2 * c ^ n ≤ (c + s) ^ n) :
    ∃ α : ℝ, ‖((c : ℂ) + Complex.exp (α * Complex.I) * s) ^ n - (c : ℂ) ^ n‖ = c ^ n := by
  have hc : 0 ≤ c := hs.trans hsc
  have hf : ContinuousOn
      (fun α : ℝ => ‖((c : ℂ) + Complex.exp (α * Complex.I) * s) ^ n - (c : ℂ) ^ n‖)
      (Set.Icc 0 Real.pi) := by
    fun_prop
  have h0 : c ^ n ≤
      ‖((c : ℂ) + Complex.exp ((0 : ℝ) * Complex.I) * s) ^ n - (c : ℂ) ^ n‖ := by
    have h : ((c : ℂ) + Complex.exp ((0 : ℝ) * Complex.I) * s) ^ n - (c : ℂ) ^ n =
        (((c + s) ^ n - c ^ n : ℝ) : ℂ) := by
      rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      push_cast
      ring
    rw [h, Complex.norm_real, Real.norm_eq_abs]
    exact (by linarith : c ^ n ≤ (c + s) ^ n - c ^ n).trans (le_abs_self _)
  have hπ : ‖((c : ℂ) + Complex.exp (Real.pi * Complex.I) * s) ^ n - (c : ℂ) ^ n‖ ≤
      c ^ n := by
    have h : ((c : ℂ) + Complex.exp (Real.pi * Complex.I) * s) ^ n - (c : ℂ) ^ n =
        (((c - s) ^ n - c ^ n : ℝ) : ℂ) := by
      rw [Complex.exp_pi_mul_I]
      push_cast
      ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h1 : (c - s) ^ n ≤ c ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    have h2 : 0 ≤ (c - s) ^ n := pow_nonneg (by linarith) n
    have h3 : 0 ≤ c ^ n := pow_nonneg hc n
    constructor <;> linarith
  obtain ⟨α, -, hα⟩ := intermediate_value_Icc' Real.pi_pos.le hf ⟨hπ, h0⟩
  exact ⟨α, hα⟩

/-!
### B.2. Products of amplitudes

-/

/-- The phase product `∏ i, ![1, e] (z i)` times the amplitude product `∏ i, ![c, s] (z i)` is
the amplitude product `∏ i, ![c, e * s] (z i)`. -/
lemma prod_phase_mul_prod_amp {n : ℕ} (e c s : ℂ) (z : Fin n → Fin 2) :
    (∏ i, ![1, e] (z i)) * ∏ i, ![c, s] (z i) = ∏ i, ![c, e * s] (z i) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  generalize z i = k
  fin_cases k <;> simp

/-- The phase product `∏ i, ![1, e] (z i)` has unit norm when `e` does. -/
lemma norm_prod_phase {n : ℕ} {e : ℂ} (he : ‖e‖ = 1) (z : Fin n → Fin 2) :
    ‖∏ i, ![1, e] (z i)‖ = 1 := by
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  generalize z i = k
  fin_cases k <;> simp [he]

/-!
### B.3. The phases

-/

/-- The phases `ω 0 = -((c + e s)ⁿ - cⁿ) / cⁿ` and `ω z = ∏ i, ![1, e] (z i)` for `z ≠ 0`
cancel the amplitude products. -/
lemma sum_phases_mul_amp {n : ℕ} (c s e : ℂ) (hc : c ^ n ≠ 0) :
    ∑ z : Fin n → Fin 2, (if z = 0 then -(((c + e * s) ^ n - c ^ n) / c ^ n)
      else ∏ i, ![1, e] (z i)) * ∏ i, ![c, s] (z i) = 0 := by
  have key : ∀ z : Fin n → Fin 2, (if z = 0 then -(((c + e * s) ^ n - c ^ n) / c ^ n)
      else ∏ i, ![1, e] (z i)) * ∏ i, ![c, s] (z i) =
      ∏ i, ![c, e * s] (z i) - if z = 0 then (c + e * s) ^ n else 0 := by
    intro z
    split_ifs with h
    · subst h
      have hA : ∏ i : Fin n, ![c, s] ((0 : Fin n → Fin 2) i) = c ^ n := by simp
      have hF : ∏ i : Fin n, ![c, e * s] ((0 : Fin n → Fin 2) i) = c ^ n := by simp
      rw [hA, hF, neg_mul, div_mul_cancel₀ _ hc]
      ring
    · rw [prod_phase_mul_prod_amp, sub_zero]
  rw [Finset.sum_congr rfl fun z _ => key z, Finset.sum_sub_distrib, ← Fintype.sum_pow,
    Fin.sum_univ_two]
  simp

/-- Unit-modulus phases `ω z` with `∑ z, ω z * ∏ i, ![c, s] (z i) = 0`, for `0 ≤ s ≤ c`,
`0 < c` and `2 cⁿ ≤ (c + s)ⁿ`. -/
lemma exists_phases {c s : ℝ} {n : ℕ} (hc : 0 < c) (hs : 0 ≤ s) (hsc : s ≤ c)
    (hn : 2 * c ^ n ≤ (c + s) ^ n) :
    ∃ ω : (Fin n → Fin 2) → ℂ,
      (∀ z, ‖ω z‖ = 1) ∧ ∑ z, ω z * ∏ i, ![(c : ℂ), (s : ℂ)] (z i) = 0 := by
  obtain ⟨α, hα⟩ := exists_norm_pow_sub_pow_eq hs hsc hn
  have hcn : (c : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hc.ne')
  refine ⟨fun z => if z = 0 then
      -((((c : ℂ) + Complex.exp (α * Complex.I) * s) ^ n - (c : ℂ) ^ n) / (c : ℂ) ^ n)
      else ∏ i, ![1, Complex.exp (α * Complex.I)] (z i),
    fun z => ?_, sum_phases_mul_amp _ _ _ hcn⟩
  dsimp only
  split_ifs
  · rw [norm_neg, norm_div, hα, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc.le,
      div_self (pow_ne_zero _ hc.ne')]
  · exact norm_prod_phase (Complex.norm_exp_ofReal_mul_I α) z

end QuantumMechanics.PBR
