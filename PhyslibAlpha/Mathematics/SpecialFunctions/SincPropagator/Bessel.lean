/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.SpecialFunctions.SincPropagator.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!

# The Bessel function `J₀` and the massive sine propagation function on the line

The sine propagation function with mass is the cosine transform of the Bessel kernel on the
interval `[-r, r]`.

## i. Overview

The Bessel function `J₀` is defined by its power series. The kernel `½ J₀ (m √(r² - u²))` on the
interval `[-r, r]` has the cosine transform `sin (r √(k² + m²)) / √(k² + m²)`. This is the retarded
Green function of the Klein–Gordon equation in one space dimension. The proof expands both sides in
power series in `m²`. The moments of `(1 - s²)ⁿ` are computed by a recurrence. The derivative of
the series in `y = z²` is expressed by the Bessel function `J₁`.

## ii. Key results

- `moment_eq` : the moments of `(1 - s²)ⁿ`.
- `besselSq` : `J₀ (√y)` as a power series in `y`.
- `integral_besselSq_cos` : the cosine transform of the Bessel kernel.
- `besselJ1` : the Bessel function `J₁`.
- `mul_besselSqDeriv_eq_besselJ1` : the tail of the Green function in terms of `J₁`.

## iii. Table of contents

- A. Moments
- B. The Bessel series
- C. The cosine transform
- D. The derivative and `J₁`

## iv. References

None.

## A. Moments

- `moment_eq` : the moments of `(1 - s²)ⁿ`.
- `moment_scaled` : the moments of `(r² - u²)ⁿ` on `[-r, r]`.

## B. The Bessel series

- `besselSq` : `J₀ (√y)` as a power series in `y`.
- `continuousOn_besselSq` : the Bessel series is continuous on bounded sets.

## C. The cosine transform

- `hasSum_integral_besselSq_cos` : the cosine transform as a double series.
- `hasSum_integral_besselSq_cos_series` : the cosine transform as a series in `k² + M`.
- `integral_besselSq_cos` : the cosine transform of the Bessel kernel.

## D. The derivative and `J₁`

- `besselSqDeriv` : the derivative of the Bessel series.
- `hasDerivAt_besselSq` : the derivative of the Bessel series.
- `besselJ1` : the Bessel function `J₁`.
- `besselSqDeriv_sq` : the derivative at `z²` in terms of `J₁`.
- `mul_besselSqDeriv_eq_besselJ1` : the tail of the Green function in terms of `J₁`.
-/

@[expose] public section

noncomputable section

open MeasureTheory intervalIntegral Nat

namespace Real

/-- The closed form of the moments of `(1 - s²)ⁿ`. -/
def momentFormula (n j : ℕ) : ℝ :=
  2 * 4 ^ n * n ! * (n + j)! * (2 * j)! / (j ! * (2 * n + 2 * j + 1)!)

lemma momentFormula_succ (n j : ℕ) :
    momentFormula (n + 1) j = momentFormula n j - momentFormula n (j + 1) := by
  unfold momentFormula
  have e1 : (((n + 1) ! : ℕ) : ℝ) = (n + 1) * (n ! : ℕ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have e2 : (((n + 1 + j) ! : ℕ) : ℝ) = (n + j + 1) * ((n + j) ! : ℕ) := by
    rw [show n + 1 + j = (n + j) + 1 from by ring, Nat.factorial_succ]; push_cast; ring
  have e3 : (((n + (j + 1)) ! : ℕ) : ℝ) = (n + j + 1) * ((n + j) ! : ℕ) := by
    rw [show n + (j + 1) = (n + j) + 1 from by ring, Nat.factorial_succ]; push_cast; ring
  have e4 : (((j + 1) ! : ℕ) : ℝ) = (j + 1) * (j ! : ℕ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have e5 : (((2 * (j + 1)) ! : ℕ) : ℝ) = (2 * j + 2) * (2 * j + 1) * ((2 * j) ! : ℕ) := by
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have e6 : (((2 * (n + 1) + 2 * j + 1) ! : ℕ) : ℝ) =
      (2 * n + 2 * j + 3) * (2 * n + 2 * j + 2) * ((2 * n + 2 * j + 1) ! : ℕ) := by
    rw [show 2 * (n + 1) + 2 * j + 1 = ((2 * n + 2 * j + 1) + 1) + 1 from by ring,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have e7 : (((2 * n + 2 * (j + 1) + 1) ! : ℕ) : ℝ) =
      (2 * n + 2 * j + 3) * (2 * n + 2 * j + 2) * ((2 * n + 2 * j + 1) ! : ℕ) := by
    rw [show 2 * n + 2 * (j + 1) + 1 = ((2 * n + 2 * j + 1) + 1) + 1 from by ring,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [e1, e2, e3, e4, e5, e6, e7]
  have h1 : (((2 * n + 2 * j + 1) ! : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((j ! : ℕ) : ℝ) ≠ 0 := by positivity
  have h3 : (2 * (n : ℝ) + 2 * j + 3) ≠ 0 := by positivity
  have h4 : (2 * (n : ℝ) + 2 * j + 2) ≠ 0 := by positivity
  have h5 : ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The moments of `(1 - s²)ⁿ` on `[-1, 1]`. -/
lemma moment_eq (n j : ℕ) :
    ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) ^ n * s ^ (2 * j) = momentFormula n j := by
  induction n generalizing j with
  | zero =>
    simp only [pow_zero, one_mul, integral_pow]
    unfold momentFormula
    have h1 : (((2 * 0 + 2 * j + 1) ! : ℕ) : ℝ) = (2 * j + 1) * ((2 * j) ! : ℕ) := by
      rw [show 2 * 0 + 2 * j + 1 = (2 * j) + 1 from by ring, Nat.factorial_succ]; push_cast; ring
    have h2 : ((j ! : ℕ) : ℝ) ≠ 0 := by positivity
    have h3 : (((2 * j) ! : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show 0 + j = j from by ring, h1]
    simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one]
    rw [show (2 * j + 1 : ℕ) = 2 * j + 1 from rfl]
    have : (-1 : ℝ) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; simp
    rw [this]
    push_cast
    field_simp
    ring
  | succ n ih =>
    rw [momentFormula_succ, ← ih j, ← ih (j + 1)]
    rw [← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [pow_succ]
      ring
    · exact (by fun_prop : Continuous fun s : ℝ => (1 - s ^ 2) ^ n * s ^ (2 * j)).intervalIntegrable
        _ _
    · exact (by fun_prop :
        Continuous fun s : ℝ => (1 - s ^ 2) ^ n * s ^ (2 * (j + 1))).intervalIntegrable _ _

/-- `J₀ (√y)` as a power series in `y`: `∑ (-y / 4)ⁿ / (n !)²`. -/
def besselSq (y : ℝ) : ℝ := ∑' n : ℕ, (-y / 4) ^ n / (n ! : ℝ) ^ 2

lemma summable_pow_div_factorial_sq (a : ℝ) : Summable fun n : ℕ => a ^ n / (n ! : ℝ) ^ 2 := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |a|) fun n => ?_
  rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  have h1 : (1 : ℝ) ≤ (n ! : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : (0 : ℝ) < n ! := by positivity
  rw [div_le_div_iff₀ (by positivity) h2]
  have := pow_nonneg (abs_nonneg a) n
  nlinarith [mul_nonneg (mul_nonneg this h2.le) (sub_nonneg.2 h1)]

lemma summable_even_pow_div_factorial (x : ℝ) :
    Summable fun j : ℕ => x ^ (2 * j) / ((2 * j) ! : ℝ) :=
  (Real.summable_pow_div_factorial x).comp_injective (fun a b h => by omega)

lemma hasSum_besselSq (y : ℝ) : HasSum (fun n : ℕ => (-y / 4) ^ n / (n ! : ℝ) ^ 2) (besselSq y) :=
  (summable_pow_div_factorial_sq (-y / 4)).hasSum

/-- The moments of `(r² - u²)ⁿ` on `[-r, r]`. -/
lemma moment_scaled {r : ℝ} (hr : 0 ≤ r) (n j : ℕ) :
    ∫ u in (-r)..r, (r ^ 2 - u ^ 2) ^ n * u ^ (2 * j) =
      r ^ (2 * n + 2 * j + 1) * momentFormula n j := by
  rcases hr.eq_or_lt with h | h
  · subst h
    simp
  · have := intervalIntegral.integral_comp_mul_left
      (fun u : ℝ => (r ^ 2 - u ^ 2) ^ n * u ^ (2 * j)) (c := r) h.ne' (a := -1) (b := 1)
    rw [← moment_eq n j]
    simp only [mul_neg, mul_one, smul_eq_mul] at this
    have h2 : ∫ u in (-r)..r, (r ^ 2 - u ^ 2) ^ n * u ^ (2 * j) =
        r * ∫ x in (-1 : ℝ)..1, (r ^ 2 - (r * x) ^ 2) ^ n * (r * x) ^ (2 * j) := by
      rw [this]
      field_simp
    rw [h2, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show r ^ 2 - (r * s) ^ 2 = r ^ 2 * (1 - s ^ 2) by ring, mul_pow, ← pow_mul, mul_pow]
    ring

/-- The cosine transform of the Bessel kernel as a double series. -/
lemma hasSum_integral_besselSq_cos {r : ℝ} (hr : 0 ≤ r) (k M : ℝ) :
    HasSum (fun p : ℕ × ℕ => (-M / 4) ^ p.1 / (p.1 ! : ℝ) ^ 2 *
      ((-1) ^ p.2 * k ^ (2 * p.2) / ((2 * p.2) ! : ℝ)) *
        (r ^ (2 * p.1 + 2 * p.2 + 1) * momentFormula p.1 p.2))
      (∫ u in (-r)..r, besselSq (M * (r ^ 2 - u ^ 2)) * Real.cos (k * u)) := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  set F : ℕ × ℕ → ℝ → ℝ := fun p u => (-(M * (r ^ 2 - u ^ 2)) / 4) ^ p.1 / (p.1 ! : ℝ) ^ 2 *
    ((-1) ^ p.2 * (k * u) ^ (2 * p.2) / ((2 * p.2) ! : ℝ)) with hF
  set bd : ℕ × ℕ → ℝ := fun p => (|M| * r ^ 2 / 4) ^ p.1 / (p.1 ! : ℝ) ^ 2 *
    ((|k| * r) ^ (2 * p.2) / ((2 * p.2) ! : ℝ)) with hbd
  have hbs : Summable bd := by
    refine Summable.mul_of_nonneg (f := fun n : ℕ => (|M| * r ^ 2 / 4) ^ n / (n ! : ℝ) ^ 2)
      (g := fun j : ℕ => (|k| * r) ^ (2 * j) / ((2 * j) ! : ℝ)) ?_ ?_ ?_ ?_
    · exact summable_pow_div_factorial_sq _
    · exact summable_even_pow_div_factorial _
    · exact fun n => by positivity
    · exact fun j => by positivity
  have key := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc (-r) r)) (F := F)
    (f := fun u => besselSq (M * (r ^ 2 - u ^ 2)) * Real.cos (k * u)) (fun p _ => bd p)
    ?_ ?_ ?_ ?_ ?_
  · convert key using 1
    funext p
    rw [← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
    have hFp : ∀ u : ℝ, F p u = ((-M / 4) ^ p.1 / (p.1 ! : ℝ) ^ 2 *
        ((-1) ^ p.2 * k ^ (2 * p.2) / ((2 * p.2) ! : ℝ))) *
          ((r ^ 2 - u ^ 2) ^ p.1 * u ^ (2 * p.2)) := fun u => by
      simp only [hF]
      rw [show -(M * (r ^ 2 - u ^ 2)) / 4 = (-M / 4) * (r ^ 2 - u ^ 2) by ring, mul_pow, mul_pow]
      ring
    simp_rw [hFp]
    rw [intervalIntegral.integral_const_mul, moment_scaled hr]
  · intro p
    refine Continuous.aestronglyMeasurable ?_
    simp only [hF]
    fun_prop
  · intro p
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨Set.Ioc (-r) r, self_mem_ae_restrict measurableSet_Ioc, fun u hu => ?_⟩
    have hur : |u| ≤ r := abs_le.2 ⟨hu.1.le, hu.2⟩
    have hu2 : u ^ 2 ≤ r ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
    simp only [hF, hbd, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((2 * p.2)! : ℕ) : ℝ))]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 4),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p.1 ! : ℝ)),
      abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ r ^ 2 - u ^ 2)]
    have h1 : |M| * (r ^ 2 - u ^ 2) / 4 ≤ |M| * r ^ 2 / 4 := by
      have := abs_nonneg M
      nlinarith
    have h2 : |k| * |u| ≤ |k| * r := mul_le_mul_of_nonneg_left hur (abs_nonneg k)
    have h3 : 0 ≤ |M| * (r ^ 2 - u ^ 2) / 4 := by
      have := abs_nonneg M
      have : 0 ≤ r ^ 2 - u ^ 2 := by nlinarith
      positivity
    gcongr
  · exact Filter.Eventually.of_forall fun _ => hbs
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun u => ?_
    have h1 := hasSum_besselSq (M * (r ^ 2 - u ^ 2))
    have h2 := Real.hasSum_cos (k * u)
    have hs1 : Summable fun n : ℕ => ‖(-(M * (r ^ 2 - u ^ 2)) / 4) ^ n / (n ! : ℝ) ^ 2‖ := by
      have := summable_pow_div_factorial_sq (|M * (r ^ 2 - u ^ 2)| / 4)
      refine this.congr fun n => ?_
      simp [norm_div, norm_pow]
    have hs2 : Summable fun j : ℕ => ‖(-1 : ℝ) ^ j * (k * u) ^ (2 * j) / ((2 * j) ! : ℝ)‖ := by
      have := summable_even_pow_div_factorial |k * u|
      refine this.congr fun n => ?_
      simp [norm_div, norm_mul, norm_pow]
    have hsm := summable_mul_of_summable_norm hs1 hs2
    exact HasSum.mul h1 h2 hsm

/-- The coefficient of the double series, simplified. -/
lemma coeff_eq (r k M : ℝ) (n j : ℕ) :
    (-M / 4) ^ n / (n ! : ℝ) ^ 2 * ((-1) ^ j * k ^ (2 * j) / ((2 * j) ! : ℝ)) *
        (r ^ (2 * n + 2 * j + 1) * momentFormula n j) =
      2 * (-1) ^ (n + j) * r ^ (2 * (n + j) + 1) / ((2 * (n + j) + 1) ! : ℝ) *
        (((n + j).choose n : ℝ) * M ^ n * (k ^ 2) ^ j) := by
  unfold momentFormula
  have hc : (((n + j).choose n : ℕ) : ℝ) = ((n + j) ! : ℝ) / ((n ! : ℝ) * (j ! : ℝ)) := by
    rw [Nat.cast_choose ℝ (Nat.le_add_right n j)]
    rw [show n + j - n = j from by omega]
  have h1 : ((n ! : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((j ! : ℕ) : ℝ) ≠ 0 := by positivity
  have h3 : (((2 * j) ! : ℕ) : ℝ) ≠ 0 := by positivity
  have h4 : (((2 * n + 2 * j + 1) ! : ℕ) : ℝ) ≠ 0 := by positivity
  rw [hc, show 2 * (n + j) + 1 = 2 * n + 2 * j + 1 from by ring,
    show (-M / 4) ^ n = (-1) ^ n * M ^ n / 4 ^ n by rw [div_pow, neg_pow]]
  field_simp
  ring

/-- **The cosine transform of the Bessel kernel as a series in the frequency squared.** -/
lemma hasSum_integral_besselSq_cos_series {r : ℝ} (hr : 0 ≤ r) (k M : ℝ) :
    HasSum (fun N : ℕ => 2 * ((-1) ^ N * (k ^ 2 + M) ^ N * r ^ (2 * N + 1) /
      ((2 * N + 1) ! : ℝ)))
      (∫ u in (-r)..r, besselSq (M * (r ^ 2 - u ^ 2)) * Real.cos (k * u)) := by
  have H := hasSum_integral_besselSq_cos hr k M
  have H1 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.2 H
  refine H1.sigma (fun N => ?_)
  convert hasSum_fintype _ using 1
  set c : ℕ × ℕ → ℝ := fun p => (-M / 4) ^ p.1 / (p.1 ! : ℝ) ^ 2 *
      ((-1) ^ p.2 * k ^ (2 * p.2) / ((2 * p.2) ! : ℝ)) *
        (r ^ (2 * p.1 + 2 * p.2 + 1) * momentFormula p.1 p.2) with hc
  have hfib : ∑ b : ↥(Finset.antidiagonal N), c b.1 = ∑ p ∈ Finset.antidiagonal N, c p :=
    Finset.sum_coe_sort (Finset.antidiagonal N) c
  show _ = ∑ b : ↥(Finset.antidiagonal N), c b.1
  rw [hfib]
  have hterm : ∀ p ∈ Finset.antidiagonal N, c p = 2 * (-1) ^ N * r ^ (2 * N + 1) /
      ((2 * N + 1) ! : ℝ) * ((N.choose p.1 : ℝ) * M ^ p.1 * (k ^ 2) ^ p.2) := fun p hp => by
    rw [Finset.mem_antidiagonal] at hp
    simp only [hc]
    rw [coeff_eq r k M p.1 p.2, hp]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hbin := (Commute.all M (k ^ 2)).add_pow' N
  simp only [nsmul_eq_mul] at hbin
  have hsum : ∑ p ∈ Finset.antidiagonal N, (N.choose p.1 : ℝ) * M ^ p.1 * (k ^ 2) ^ p.2 =
      (k ^ 2 + M) ^ N := by
    rw [add_comm, hbin]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hsum]
  ring

/-- The sine propagation function as a power series in the frequency squared. -/
lemma hasSum_sincPropagator_series (r a : ℝ) (ha : 0 ≤ a) :
    HasSum (fun N : ℕ => (-1) ^ N * a ^ N * r ^ (2 * N + 1) / ((2 * N + 1) ! : ℝ))
      (Real.sincPropagator r (Real.sqrt a)) := by
  rcases ha.eq_or_lt with h | h
  · subst h
    simp only [Real.sqrt_zero, Real.sincPropagator_zero_right]
    convert hasSum_single 0 (fun N hN => ?_) using 1
    · simp
    · simp [zero_pow hN]
  · have hω : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 h).ne'
    have hs := (Real.hasSum_sin (Real.sqrt a * r)).div_const (Real.sqrt a)
    rw [Real.sincPropagator_eq_sin_div hω r]
    convert hs using 1
    funext N
    have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
    have hp : Real.sqrt a ^ (2 * N + 1) = a ^ N * Real.sqrt a := by
      rw [pow_succ, pow_mul, hsq]
    rw [mul_pow, hp]
    field_simp

/-- **The cosine transform of the Bessel kernel.** For `r ≥ 0` and `k² + M ≥ 0`
`∫_{-r}^{r} J₀ (√M √(r² - u²)) cos (k u) du = 2 sin (r √(k² + M)) / √(k² + M)`. -/
lemma integral_besselSq_cos {r : ℝ} (hr : 0 ≤ r) (k M : ℝ) (h : 0 ≤ k ^ 2 + M) :
    ∫ u in (-r)..r, besselSq (M * (r ^ 2 - u ^ 2)) * Real.cos (k * u) =
      2 * Real.sincPropagator r (Real.sqrt (k ^ 2 + M)) := by
  have h1 := hasSum_integral_besselSq_cos_series hr k M
  have h2 := (hasSum_sincPropagator_series r (k ^ 2 + M) h).mul_left 2
  refine h1.unique ?_
  convert h2 using 1

/-- The Bessel series is continuous on bounded sets. -/
lemma continuousOn_besselSq (R : ℝ) : ContinuousOn besselSq (Set.Icc (-R) R) := by
  unfold besselSq
  refine continuousOn_tsum (u := fun n : ℕ => (|R| / 4) ^ n / (n ! : ℝ) ^ 2) (fun n => ?_)
    (summable_pow_div_factorial_sq _) (fun n y hy => ?_)
  · exact (by fun_prop : Continuous fun y : ℝ => (-y / 4) ^ n / (n ! : ℝ) ^ 2).continuousOn
  · have hy' : |y| ≤ |R| :=
      abs_le.2 ⟨by linarith [hy.1, le_abs_self R], by linarith [hy.2, le_abs_self R]⟩
    rw [norm_div, norm_pow, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity),
      abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    gcongr

/-- The termwise derivative of the Bessel series. -/
def besselSqDeriv (y : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) * (-1 / 4) * (-y / 4) ^ (n - 1) / (n ! : ℝ) ^ 2

lemma summable_besselSqDeriv_bound (a : ℝ) (ha : 0 ≤ a) :
    Summable fun n : ℕ => (n : ℝ) * (1 / 4) * a ^ (n - 1) / (n ! : ℝ) ^ 2 := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_pow_div_factorial_sq a).mul_left (1 / 4 : ℝ))
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have h1 : (0 : ℝ) < (k ! : ℝ) := by positivity
  have h2 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [div_le_iff₀ (by positivity)]
  field_simp
  have : (1 : ℝ) ≤ ((k : ℝ) + 1) := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hak : 0 ≤ a ^ k := pow_nonneg ha k
  nlinarith [mul_nonneg hak (sub_nonneg.2 this),
    mul_nonneg (mul_nonneg hak h1.le) (sub_nonneg.2 this)]

/-- **The derivative of the Bessel series.** -/
lemma hasDerivAt_besselSq (y : ℝ) : HasDerivAt besselSq (besselSqDeriv y) y := by
  set R : ℝ := |y| + 1 with hR
  have hR0 : 0 < R := by positivity
  have hterm : ∀ (n : ℕ) (z : ℝ), HasDerivAt (fun z : ℝ => (-z / 4) ^ n / (n ! : ℝ) ^ 2)
      ((n : ℝ) * (-1 / 4) * (-z / 4) ^ (n - 1) / (n ! : ℝ) ^ 2) z := fun n z => by
    have h1 : HasDerivAt (fun z : ℝ => -z / 4) (-1 / 4) z := by
      simpa using ((hasDerivAt_id z).neg.div_const 4)
    have h2 := (h1.pow n).div_const ((n ! : ℝ) ^ 2)
    convert h2 using 1
    ring
  unfold besselSq besselSqDeriv
  exact hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ =>
    (n : ℝ) * (1 / 4) * (R / 4) ^ (n - 1) / (n ! : ℝ) ^ 2)
    (summable_besselSqDeriv_bound (R / 4) (by positivity)) isOpen_Ioo
    isPreconnected_Ioo (fun n z _ => hterm n z) (fun n z hz => by
      have hz' : |z| ≤ R := abs_le.2 ⟨hz.1.le, hz.2.le⟩
      have e : ‖(n : ℝ) * (-1 / 4) * (-z / 4) ^ (n - 1) / (n ! : ℝ) ^ 2‖ =
          (n : ℝ) * (1 / 4) * (|z| / 4) ^ (n - 1) / (n ! : ℝ) ^ 2 := by
        simp [norm_div, norm_mul, norm_pow]
      rw [e]
      gcongr) (show (0 : ℝ) ∈ Set.Ioo (-R) R from ⟨by linarith, hR0⟩)
    (by simpa using summable_pow_div_factorial_sq (0 : ℝ))
    (show y ∈ Set.Ioo (-R) R from ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩)

lemma continuous_besselSqDeriv : Continuous besselSqDeriv := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  set R : ℝ := |y| + 1 with hR
  have hcon : ContinuousOn besselSqDeriv (Set.Icc (-R) R) := by
    unfold besselSqDeriv
    refine continuousOn_tsum
      (u := fun n : ℕ => (n : ℝ) * (1 / 4) * (R / 4) ^ (n - 1) / (n ! : ℝ) ^ 2)
      (fun n => ?_) (summable_besselSqDeriv_bound (R / 4) (by positivity)) (fun n z hz => ?_)
    · exact (by fun_prop : Continuous fun z : ℝ =>
        (n : ℝ) * (-1 / 4) * (-z / 4) ^ (n - 1) / (n ! : ℝ) ^ 2).continuousOn
    · have hz' : |z| ≤ R := abs_le.2 hz
      have e : ‖(n : ℝ) * (-1 / 4) * (-z / 4) ^ (n - 1) / (n ! : ℝ) ^ 2‖ =
          (n : ℝ) * (1 / 4) * (|z| / 4) ^ (n - 1) / (n ! : ℝ) ^ 2 := by
        simp [norm_div, norm_mul, norm_pow]
      rw [e]
      gcongr
  exact hcon.continuousAt (Icc_mem_nhds (by linarith [neg_abs_le y]) (by linarith [le_abs_self y]))

/-- The Bessel function `J₁` by its power series. -/
def besselJ1 (z : ℝ) : ℝ :=
  ∑' n : ℕ, (-1) ^ n * (z / 2) ^ (2 * n + 1) / ((n ! : ℝ) * ((n + 1) ! : ℝ))

lemma summable_besselSqDeriv (y : ℝ) :
    Summable fun n : ℕ => (n : ℝ) * (-1 / 4) * (-y / 4) ^ (n - 1) / (n ! : ℝ) ^ 2 := by
  refine Summable.of_norm_bounded (summable_besselSqDeriv_bound (|y| / 4) (by positivity))
    fun n => ?_
  have e : ‖(n : ℝ) * (-1 / 4) * (-y / 4) ^ (n - 1) / (n ! : ℝ) ^ 2‖ =
      (n : ℝ) * (1 / 4) * (|y| / 4) ^ (n - 1) / (n ! : ℝ) ^ 2 := by
    simp [norm_div, norm_mul, norm_pow]
  rw [e]

/-- The derivative of the Bessel series is `-J₁ (z) / (2 z)` at `y = z²`. -/
lemma besselSqDeriv_sq {z : ℝ} (hz : z ≠ 0) : besselSqDeriv (z ^ 2) = -besselJ1 z / (2 * z) := by
  unfold besselSqDeriv besselJ1
  rw [(summable_besselSqDeriv (z ^ 2)).tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_div, zero_add, Nat.add_sub_cancel, Nat.cast_add,
    Nat.cast_one]
  have hterm : ∀ k : ℕ, ((k : ℝ) + 1) * (-1 / 4) * (-z ^ 2 / 4) ^ k / ((k + 1) ! : ℝ) ^ 2 =
      -(1 / (2 * z)) * ((z / 2) * ((-z ^ 2 / 4) ^ k / ((k ! : ℝ) * ((k + 1) ! : ℝ)))) := by
    intro k
    have h1 : ((k + 1) ! : ℝ) = ((k : ℝ) + 1) * (k ! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h2 : (k ! : ℝ) ≠ 0 := by positivity
    have h3 : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [h1]
    field_simp
    ring
  have hterm2 : ∀ k : ℕ, (-1) ^ k * (z / 2) ^ (2 * k + 1) / ((k ! : ℝ) * ((k + 1) ! : ℝ)) =
      (z / 2) * ((-z ^ 2 / 4) ^ k / ((k ! : ℝ) * ((k + 1) ! : ℝ))) := by
    intro k
    have : ((-1 : ℝ) ^ k * (z / 2) ^ (2 * k + 1)) = (z / 2) * (-z ^ 2 / 4) ^ k := by
      rw [pow_succ, pow_mul, show (-z ^ 2 / 4 : ℝ) = -1 * ((z / 2) ^ 2) by ring, mul_pow]
      ring
    rw [this]
    ring
  simp_rw [hterm, hterm2]
  rw [tsum_mul_left, tsum_mul_left]
  field_simp

lemma continuous_besselSq : Continuous besselSq :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_besselSq y).continuousAt

@[simp] lemma besselSq_zero : besselSq 0 = 1 := by
  unfold besselSq
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- **The Bessel tail in terms of `J₁`.** For `|u| < τ` the derivative of the Bessel series at
`m² (τ² - u²)` is `J₁ (m √(τ² - u²)) / √(τ² - u²)` up to the factor `-1 / (2 m)`. -/
lemma mul_besselSqDeriv_eq_besselJ1 {m τ u : ℝ} (hm : m ≠ 0) (hu : |u| < τ) (c : ℝ) :
    2 * m ^ 2 * (c * besselSqDeriv (m ^ 2 * (τ ^ 2 - u ^ 2))) =
      -(m * (c * (besselJ1 (m * Real.sqrt (τ ^ 2 - u ^ 2)) / Real.sqrt (τ ^ 2 - u ^ 2)))) := by
  have hpos : 0 < τ ^ 2 - u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
  have hw : 0 < Real.sqrt (τ ^ 2 - u ^ 2) := Real.sqrt_pos.2 hpos
  have hmw : m * Real.sqrt (τ ^ 2 - u ^ 2) ≠ 0 := mul_ne_zero hm hw.ne'
  have h1 : m ^ 2 * (τ ^ 2 - u ^ 2) = (m * Real.sqrt (τ ^ 2 - u ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hpos.le]
  rw [h1, besselSqDeriv_sq hmw]
  field_simp

end Real
