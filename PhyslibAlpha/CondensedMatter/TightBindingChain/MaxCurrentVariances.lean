/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.ElementalUncertainty
/-!

# The variances of the maximal current state

## i. Overview

In the maximal current state of the open chain with `N` sites, write `θ = π / (N + 1)`. The energy
and position variances are

  `Var H = 4 t² sin² θ (N - 1) / (N + 1)`,
  `Var X = a² (((N + 1)² + 2) / 12 - 1 / (2 sin² θ))`.

The position variance rests on one sum over the `(N + 1)`-th roots of unity,
`∑ j < N + 1, (j - (N + 1) / 2)² cos (2 j θ) = (N + 1) / (2 sin² θ)`, obtained by summation by
parts. Hence `C_Nava²` has the closed form
`2 (N - 1) / ((N + 1) cos² θ) · (((N + 1)² + 2) / 6 · sin² θ - 1)`.

## ii. Key results

- `variance_openHamiltonian_maxCurrentState` : `Var H = 4 t² sin² θ (N - 1) / (N + 1)`.
- `variance_position_maxCurrentState` : `Var X = a² (((N + 1)² + 2) / 12 - 1 / (2 sin² θ))`.
- `CNava_sq_eq` : the closed form of `C_Nava²`.

## iii. Table of contents

- A. Sums over the roots of unity
- B. The energy variance
- C. The position variance
- D. The closed form of `C_Nava`

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

## A. Sums over the roots of unity

-/

/-- Summation by parts against the powers of `z`. -/
private lemma sub_one_mul_sum_mul_pow (g : ℕ → ℂ) (z : ℂ) (m : ℕ) :
    (z - 1) * ∑ j ∈ Finset.range m, g j * z ^ j =
      g m * z ^ m - g 0 - ∑ j ∈ Finset.range m, (g (j + 1) - g j) * z ^ (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]
    ring

/-- At a root of unity `z ≠ 1` of order `n`, `∑ j < n, (j - n / 2)² zʲ = -2 n z / (z - 1)²`. -/
private lemma sum_sq_mul_pow {z : ℂ} {n : ℕ} (hz : z ^ n = 1) (hz1 : z ≠ 1) :
    ∑ j ∈ Finset.range n, ((j : ℂ) - n / 2) ^ 2 * z ^ j = -2 * n * z / (z - 1) ^ 2 := by
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have h0 : ∑ j ∈ Finset.range n, z ^ j = 0 := by
    rw [geom_sum_eq hz1, hz, sub_self, zero_div]
  have h1 : (z - 1) * ∑ j ∈ Finset.range n, (j : ℂ) * z ^ j = n := by
    rw [sub_one_mul_sum_mul_pow (fun j => (j : ℂ)), hz]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_mul, pow_succ,
      ← Finset.sum_mul, h0]
    simp
  have h2 := sub_one_mul_sum_mul_pow (fun j => ((j : ℂ) - n / 2) ^ 2) z n
  simp only [hz, Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h2
  have h3 : ∑ j ∈ Finset.range n, ((((j : ℂ) + 1 - n / 2) ^ 2 - ((j : ℂ) - n / 2) ^ 2) *
      z ^ (j + 1)) = z * (2 * ∑ j ∈ Finset.range n, (j : ℂ) * z ^ j +
        (1 - n) * ∑ j ∈ Finset.range n, z ^ j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h3, h0] at h2
  rw [eq_div_iff (pow_ne_zero 2 hz1')]
  linear_combination (z - 1) * h2 + (-2 * z) * h1

/-- `∑ j < N + 1, (j - (N + 1) / 2)² cos (2 j θ) = (N + 1) / (2 sin² θ)` for `θ = π / (N + 1)`. -/
private lemma sum_sq_mul_cos :
    ∑ j ∈ Finset.range (T.N + 1), (((j : ℕ) : ℝ) - (T.N + 1) / 2) ^ 2 *
        Real.cos (2 * (j * (Real.pi / (T.N + 1)))) =
      (T.N + 1) / (2 * Real.sin (Real.pi / (T.N + 1)) ^ 2) := by
  set θ := Real.pi / (T.N + 1) with hθ
  have hζ := Complex.isPrimitiveRoot_exp (T.N + 1) (by omega)
  set z := Complex.exp (2 * Real.pi * Complex.I / ((T.N + 1 : ℕ) : ℂ)) with hz
  have hz1 : z ≠ 1 := hζ.ne_one (by have := NeZero.ne T.N; omega)
  have hzθ : z = Complex.exp ((2 * θ : ℝ) * Complex.I) := by
    rw [hz, hθ]
    congr 1
    push_cast
    ring
  have hsum := sum_sq_mul_pow hζ.pow_eq_one hz1
  have hcos : z + z⁻¹ = 2 * (Real.cos (2 * θ) : ℂ) := by
    rw [hzθ, ← Complex.exp_neg, Complex.ofReal_cos, Complex.cos]
    ring_nf
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hN : (0 : ℝ) < T.N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T.N)
  have hsin : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by rw [hθ]; positivity)
    (by rw [hθ]; exact div_lt_self Real.pi_pos (by linarith))).ne'
  have hc1 : (1 : ℂ) - Real.cos (2 * θ) = 2 * (Real.sin θ : ℂ) ^ 2 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Real.cos_two_mul, Real.cos_sq']
    ring_nf
  have hrhs : -2 * ((T.N + 1 : ℕ) : ℂ) * z / (z - 1) ^ 2 =
      (((T.N + 1) / (2 * Real.sin θ ^ 2) : ℝ) : ℂ) := by
    have hs : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsin
    have hsq : (z - 1) ^ 2 = z * (-(4 * (Real.sin θ : ℂ) ^ 2)) := by
      have h : (z - 1) ^ 2 = z * (z + z⁻¹ - 2) := by field_simp; ring
      rw [h, hcos]
      linear_combination z * (-2) * hc1
    rw [hsq, div_eq_iff (mul_ne_zero hz0 (neg_ne_zero.mpr (mul_ne_zero four_ne_zero
      (pow_ne_zero 2 hs))))]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have h := congrArg Complex.re (hsum.trans hrhs)
  rw [Complex.ofReal_re, Complex.re_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hzθ, ← Complex.exp_nat_mul, show ((j : ℂ) - ((T.N + 1 : ℕ) : ℂ) / 2) ^ 2 =
    (((j : ℝ) - (T.N + 1) / 2) ^ 2 : ℝ) by push_cast; ring, Complex.re_ofReal_mul,
    show (j : ℂ) * ((2 * θ : ℝ) * Complex.I) = ((2 * (j * θ) : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_ofReal_mul_I_re]

/-- `∑ j < m, (j - c)² = m (m - 1) (2 m - 1) / 6 - c m (m - 1) + c² m`. -/
private lemma sum_sub_sq (c : ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range m, ((j : ℝ) - c) ^ 2 =
      m * (m - 1) * (2 * m - 1) / 6 - c * m * (m - 1) + c ^ 2 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `∑ m, sin² ((m + 1) θ) = (N + 1) / 2` over the sites, for `θ = π / (N + 1)`. -/
private lemma sum_sin_sq_sites :
    ∑ m : Fin T.N, Real.sin (((m : ℕ) + 1) * (Real.pi / (T.N + 1))) ^ 2 = (T.N + 1) / 2 := by
  have h := localizedState.sum_sq_norm_inner_right T.maxCurrentState
  rw [T.norm_maxCurrentState] at h
  simp only [inner_maxCurrentState, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 / (T.N + 1) by positivity), ← Finset.mul_sum] at h
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq (by positivity)] at h
  linarith

/-!

## B. The energy variance

-/

/-- The energy variance of the maximal current state, `Var H = 4 t² sin² θ (N - 1) / (N + 1)`. -/
lemma variance_openHamiltonian_maxCurrentState :
    variance T.maxCurrentVectorState T.openHamiltonianObservable =
      4 * T.t ^ 2 * Real.sin (Real.pi / (T.N + 1)) ^ 2 * (T.N - 1) / (T.N + 1) := by
  rw [variance_ofVec, ← localizedState.sum_sq_norm_inner_right]
  simp only [inner_energyFluctuation_maxCurrentState, norm_neg, norm_mul, norm_pow,
    Complex.norm_I, one_pow, mul_one, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs,
    mul_pow, sq_abs, Real.sq_sqrt (show (0 : ℝ) ≤ 2 / (T.N + 1) by positivity),
    ← Finset.mul_sum, Real.cos_sq', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, T.sum_sin_sq_sites]
  field_simp
  ring

/-!

## C. The position variance

-/

/-- The position variance of the maximal current state,
`Var X = a² (((N + 1)² + 2) / 12 - 1 / (2 sin² θ))`. -/
lemma variance_position_maxCurrentState :
    variance T.maxCurrentVectorState T.positionObservable =
      T.a ^ 2 * (((T.N + 1) ^ 2 + 2) / 12 - 1 / (2 * Real.sin (Real.pi / (T.N + 1)) ^ 2)) := by
  rw [variance_ofVec, ← localizedState.sum_sq_norm_inner_right]
  simp only [inner_positionFluctuation_maxCurrentState, inner_maxCurrentState, norm_mul,
    norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs, Real.sq_sqrt (show (0 : ℝ) ≤ 2 / (T.N + 1) by positivity)]
  set θ := Real.pi / (T.N + 1) with hθ
  have hshift : ∑ m : Fin T.N, T.a ^ 2 * (((m : ℕ) : ℝ) - (T.N - 1) / 2) ^ 2 *
      (2 / (T.N + 1) * Real.sin (((m : ℕ) + 1) * θ) ^ 2) =
      T.a ^ 2 * (2 / (T.N + 1)) * ∑ j ∈ Finset.range (T.N + 1),
        ((j : ℝ) - (T.N + 1) / 2) ^ 2 * Real.sin (j * θ) ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => T.a ^ 2 * ((m : ℝ) - (T.N - 1) / 2) ^ 2 *
        (2 / (T.N + 1) * Real.sin ((m + 1) * θ) ^ 2)), Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, Real.sin_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hshift]
  conv_lhs => simp only [Real.sin_sq_eq_half_sub, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, sum_sub_sq]
  have hc := T.sum_sq_mul_cos
  rw [← hθ] at hc
  have hsin : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by rw [hθ]; positivity)
    (by rw [hθ]; exact div_lt_self Real.pi_pos (by
      have : (0 : ℝ) < T.N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T.N)
      linarith))).ne'
  rw [show ∑ j ∈ Finset.range (T.N + 1), ((j : ℝ) - (T.N + 1) / 2) ^ 2 *
      (Real.cos (2 * (j * θ)) / 2) = (T.N + 1) / (2 * Real.sin θ ^ 2) / 2 by
    rw [← hc, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring]
  push_cast
  field_simp
  ring

/-!

## D. The closed form of `C_Nava`

-/

/-- The closed form of `C_Nava²` in the maximal current state, with `θ = π / (N + 1)`:
`C_Nava² = 2 (N - 1) / ((N + 1) cos² θ) · (((N + 1)² + 2) / 6 · sin² θ - 1)`. -/
theorem CNava_sq_eq (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.CNava ^ 2 = 2 * (T.N - 1) / ((T.N + 1) * Real.cos (Real.pi / (T.N + 1)) ^ 2) *
      (((T.N + 1) ^ 2 + 2) / 6 * Real.sin (Real.pi / (T.N + 1)) ^ 2 - 1) := by
  have hN' : (2 : ℝ) ≤ T.N := by exact_mod_cast hN
  have hθ : 0 < Real.pi / (T.N + 1) := by positivity
  have hcos : Real.cos (Real.pi / (T.N + 1)) ≠ 0 := by
    refine (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).ne'
    · linarith [Real.pi_pos]
    · rw [div_lt_div_iff_of_pos_left Real.pi_pos (by positivity) two_pos]
      linarith
  have hsin : Real.sin (Real.pi / (T.N + 1)) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ
    (div_lt_self Real.pi_pos (by linarith))).ne'
  rw [CNava, div_pow, Real.sq_sqrt (mul_nonneg (variance_nonneg _ _) (variance_nonneg _ _)),
    sq_abs, variance_openHamiltonian_maxCurrentState, variance_position_maxCurrentState]
  have ha := T.a_pos.ne'
  field_simp
  ring

end TightBindingChain
end CondensedMatter
