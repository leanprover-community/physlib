/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.Hydrogen.Degeneracy
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Polynomially bounded functions and integrability on `Space d`

## i. Overview

A function `f : Space d → ℝ` is polynomially bounded if `|f y| ≤ C (1 + ‖y‖)^k`. Such functions
form an algebra containing the coordinates, `‖y‖` and polynomials; multiplied by `e^(-c‖y‖)`
(`c > 0`) they are square integrable, multiplied by a Schwartz map they are integrable, and for
`d ≥ 2` this stays true after an additional factor `‖y‖⁻¹`.

## ii. Key results

- `IsPolyBounded` : at most polynomial growth `|f y| ≤ C (1 + ‖y‖)^k`.
- `integrable_sq_of_le_mul_exp` : `f²` is integrable if `|f| ≤ |g| e^(-c‖y‖)` with `g` polynomially
  bounded and `c > 0`.
- `IsPolyBounded.integrable_ofReal_mul_schwartz` : polynomially bounded times Schwartz is
  integrable.
- `IsPolyBounded.integrable_inv_norm_mul` : the same with an extra factor `‖y‖⁻¹`, for `d ≥ 2`.

## iii. Table of contents

- A. Polynomially bounded functions
- B. Exponential decay and integrability

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Hydrogen

open MeasureTheory Space
open scoped SchwartzMap LineDeriv

/-!

## A. Polynomially bounded functions

-/

/-- `f` grows at most polynomially: `|f y| ≤ C (1 + ‖y‖)^k` for some `C ≥ 0` and `k`. -/
def IsPolyBounded {d : ℕ} (f : Space d → ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k

namespace IsPolyBounded

variable {d : ℕ} {f g : Space d → ℝ}

lemma one_le_one_add_norm (y : Space d) : 1 ≤ 1 + ‖y‖ :=
  le_add_of_nonneg_right (norm_nonneg _)

lemma const (a : ℝ) : IsPolyBounded (fun _ : Space d => a) :=
  ⟨|a|, 0, abs_nonneg a, fun y => by simp⟩

lemma add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded (fun y => f y + g y) := by
  obtain ⟨C₁, k₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, k₂, hC₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, max k₁ k₂, by positivity, fun y => ?_⟩
  have e₁ : (1 + ‖y‖) ^ k₁ ≤ (1 + ‖y‖) ^ max k₁ k₂ :=
    pow_le_pow_right₀ (one_le_one_add_norm y) (le_max_left _ _)
  have e₂ : (1 + ‖y‖) ^ k₂ ≤ (1 + ‖y‖) ^ max k₁ k₂ :=
    pow_le_pow_right₀ (one_le_one_add_norm y) (le_max_right _ _)
  calc |f y + g y| ≤ |f y| + |g y| := abs_add_le _ _
    _ ≤ C₁ * (1 + ‖y‖) ^ k₁ + C₂ * (1 + ‖y‖) ^ k₂ := add_le_add (h₁ y) (h₂ y)
    _ ≤ C₁ * (1 + ‖y‖) ^ max k₁ k₂ + C₂ * (1 + ‖y‖) ^ max k₁ k₂ := by gcongr
    _ = (C₁ + C₂) * (1 + ‖y‖) ^ max k₁ k₂ := by ring

lemma mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded (fun y => f y * g y) := by
  obtain ⟨C₁, k₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, k₂, hC₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, k₁ + k₂, mul_nonneg hC₁ hC₂, fun y => ?_⟩
  rw [abs_mul, pow_add]
  calc |f y| * |g y| ≤ (C₁ * (1 + ‖y‖) ^ k₁) * (C₂ * (1 + ‖y‖) ^ k₂) :=
        mul_le_mul (h₁ y) (h₂ y) (abs_nonneg _) (by positivity)
    _ = C₁ * C₂ * ((1 + ‖y‖) ^ k₁ * (1 + ‖y‖) ^ k₂) := by ring

lemma pow (hf : IsPolyBounded f) (n : ℕ) : IsPolyBounded (fun y => f y ^ n) := by
  induction n with
  | zero => exact ⟨1, 0, zero_le_one, fun y => by simp⟩
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma coord (i : Fin d) : IsPolyBounded (fun y : Space d => y i) :=
  ⟨1, 1, zero_le_one, fun y => by
    have := Space.abs_eval_le_norm y i
    simp only [one_mul, pow_one]
    linarith [norm_nonneg y]⟩

lemma norm : IsPolyBounded (fun y : Space d => ‖y‖) :=
  ⟨1, 1, zero_le_one, fun y => by
    rw [abs_of_nonneg (norm_nonneg y), one_mul, pow_one]
    linarith⟩

/-- Polynomials in the coordinates are polynomially bounded. -/
lemma toFun (P : MvPolynomial (Fin d) ℝ) : IsPolyBounded (toFun P) := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [toFun_C]; exact const a
  | add P Q hP hQ => rw [toFun_add]; exact hP.add hQ
  | mul_X P j hP => rw [toFun_mul_X]; exact hP.mul (coord j)

/-- A polynomial of a polynomially bounded function is polynomially bounded. -/
lemma polynomial_eval (p : Polynomial ℝ) (hf : IsPolyBounded f) :
    IsPolyBounded (fun y => p.eval (f y)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    exact (const a).mul (hf.pow n)

lemma sum {ι : Type*} (s : Finset ι) {F : ι → Space d → ℝ} (h : ∀ i ∈ s, IsPolyBounded (F i)) :
    IsPolyBounded (fun y => ∑ i ∈ s, F i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, le_rfl, fun y => by simp⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma mono (hf : IsPolyBounded f) {c : ℝ} (hc : 0 ≤ c) (h : ∀ y, |g y| ≤ c * |f y|) :
    IsPolyBounded g := by
  obtain ⟨C, k, hC, hb⟩ := hf
  exact ⟨c * C, k, mul_nonneg hc hC, fun y => (h y).trans (by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hb y) hc)⟩

lemma of_abs_le_const {c : ℝ} (h : ∀ y, |g y| ≤ c) : IsPolyBounded g :=
  ⟨max c 0, 0, le_max_right _ _, fun y => by
    rw [pow_zero, mul_one]; exact (h y).trans (le_max_left _ _)⟩

lemma neg (hf : IsPolyBounded f) : IsPolyBounded (fun y => -f y) :=
  hf.mono zero_le_one fun y => by rw [abs_neg, one_mul]

end IsPolyBounded

/-!

## B. Exponential decay and integrability

-/

/-- `(1 + t)^m e^(-c t) ≤ e^c m! / c^m` for `c > 0` and `t ≥ 0`, from `x^m / m! ≤ e^x`. -/
lemma one_add_pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ m * Real.exp (-(c * t)) ≤ Real.exp c * m.factorial / c ^ m := by
  have h := Real.pow_div_factorial_le_exp (x := c * (1 + t)) (by positivity) m
  rw [mul_pow, div_le_iff₀ (by positivity), show c * (1 + t) = c + c * t by ring,
    Real.exp_add] at h
  rw [le_div_iff₀ (by positivity)]
  calc (1 + t) ^ m * Real.exp (-(c * t)) * c ^ m
      = c ^ m * (1 + t) ^ m * Real.exp (-(c * t)) := by ring
    _ ≤ Real.exp c * Real.exp (c * t) * m.factorial * Real.exp (-(c * t)) := by gcongr
    _ = Real.exp c * m.factorial := by
      rw [mul_right_comm _ (m.factorial : ℝ), mul_assoc _ (Real.exp (c * t)), ← Real.exp_add,
        add_neg_cancel, Real.exp_zero, mul_one]

/-- If `|f y| ≤ |g y| e^(-c‖y‖)` with `g` polynomially bounded and `c > 0`, then `f²` is
integrable: it is bounded by a multiple of `(1 + ‖y‖)^(-(d+1))`. -/
lemma integrable_sq_of_le_mul_exp {d : ℕ} {f g : Space d → ℝ} {c : ℝ} (hc : 0 < c)
    (hfm : AEStronglyMeasurable f) (hg : IsPolyBounded g)
    (hfg : ∀ y, |f y| ≤ |g y| * Real.exp (-(c * ‖y‖))) :
    Integrable (fun y => f y ^ 2) := by
  obtain ⟨C, k, hC, hgC⟩ := hg
  set m := 2 * k + (d + 1)
  set B := C ^ 2 * (Real.exp (2 * c) * m.factorial / (2 * c) ^ m)
  have hint : Integrable (fun y : Space d => B * (1 + ‖y‖) ^ (-((d + 1 : ℕ) : ℝ))) :=
    (integrable_one_add_norm (by simp [Space.finrank_eq_dim])).const_mul B
  refine hint.mono' (hfm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
  have hpos : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hdec := one_add_pow_mul_exp_neg_le (c := 2 * c) (by positivity) m (norm_nonneg y)
  rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
  have hf2 : f y ^ 2 ≤ (C * (1 + ‖y‖) ^ k) ^ 2 * Real.exp (-(2 * c * ‖y‖)) := by
    have h1 : |f y| ≤ C * (1 + ‖y‖) ^ k * Real.exp (-(c * ‖y‖)) :=
      (hfg y).trans (by gcongr; exact hgC y)
    have h2 : f y ^ 2 ≤ (C * (1 + ‖y‖) ^ k * Real.exp (-(c * ‖y‖))) ^ 2 := by
      rw [← sq_abs]; gcongr
    rw [mul_pow, ← Real.exp_nat_mul] at h2
    convert h2 using 3
    push_cast; ring
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc f y ^ 2 ≤ (C * (1 + ‖y‖) ^ k) ^ 2 * Real.exp (-(2 * c * ‖y‖)) := hf2
    _ = C ^ 2 * ((1 + ‖y‖) ^ m * Real.exp (-(2 * c * ‖y‖))) * ((1 + ‖y‖) ^ (d + 1))⁻¹ := by
      field_simp
      ring
    _ ≤ B * ((1 + ‖y‖) ^ (d + 1))⁻¹ := by
      simp only [B]
      gcongr

/-- A polynomially bounded function times a Schwartz map is integrable. -/
lemma IsPolyBounded.integrable_ofReal_mul_schwartz {d : ℕ} {u : Space d → ℝ}
    (hu : IsPolyBounded u) (hm : AEStronglyMeasurable u) (g : 𝓢(Space d, ℂ)) :
    Integrable (fun y => (u y : ℂ) * g y) := by
  obtain ⟨C, k, hC, hb⟩ := hu
  set m := k + (d + 1)
  set B := 2 ^ m * (Finset.Iic (m, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
  have hint : Integrable (fun y : Space d => (C * B) * (1 + ‖y‖) ^ (-((d + 1 : ℕ) : ℝ))) :=
    (integrable_one_add_norm (by simp [Space.finrank_eq_dim])).const_mul _
  refine hint.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hm).mul
    g.continuous.aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
  have hg := g.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, 0)) (k := m) (n := 0)
    le_rfl le_rfl y
  rw [norm_iteratedFDeriv_zero] at hg
  have hpos : 0 < 1 + ‖y‖ := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg hpos.le, Real.rpow_natCast]
  calc |u y| * ‖g y‖ ≤ C * (1 + ‖y‖) ^ k * ‖g y‖ := by gcongr; exact hb y
    _ = C * ((1 + ‖y‖) ^ m * ‖g y‖) * ((1 + ‖y‖) ^ (d + 1))⁻¹ := by
      simp only [m, pow_add]
      field_simp
    _ ≤ C * B * ((1 + ‖y‖) ^ (d + 1))⁻¹ := by gcongr

/-- `‖y‖⁻¹ (1 + ‖y‖)^(-M)` is integrable on `Space d` for `d ≥ 2` and `M ≥ d`, by polar
coordinates: the radial integrand `r^(d-2) (1 + r)^(-M)` is at most `(1 + r)^(-2)`. -/
lemma integrable_inv_norm_mul_one_add_norm_pow {d : ℕ} (hd : 2 ≤ d) {M : ℕ} (hM : d ≤ M) :
    Integrable (fun y : Space d => ‖y‖⁻¹ * ((1 + ‖y‖) ^ M)⁻¹) := by
  have : Nontrivial (Space d) :=
    Module.nontrivial_of_finrank_pos (by rw [Space.finrank_eq_dim]; omega)
  rw [integrable_fun_norm_addHaar (μ := volume) (f := fun r : ℝ => r⁻¹ * ((1 + r) ^ M)⁻¹),
    Space.finrank_eq_dim]
  have h2 : Integrable (fun r : ℝ => (1 + ‖r‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (by simp)
  refine (h2.integrableOn (s := Set.Ioi 0)).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun r : ℝ => r ^ (d - 1)).aestronglyMeasurable.smul
      ((measurable_inv.mul (by fun_prop)).aestronglyMeasurable)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr => ?_)
    have hr : 0 < r := hr
    have hn : ‖r‖ = r := by rw [Real.norm_eq_abs, abs_of_pos hr]
    rw [hn, Real.rpow_neg (by positivity), Real.rpow_two, smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have h1 : r ^ (d - 1) * r⁻¹ = r ^ (d - 2) := by
      rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]
      field_simp
    have h3 : r ^ (d - 2) ≤ (1 + r) ^ (d - 2) := pow_le_pow_left₀ hr.le (by linarith) _
    have h4 : (1 + r) ^ (d - 2) * (1 + r) ^ 2 ≤ (1 + r) ^ M := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by linarith) (by omega)
    rw [← mul_assoc, h1]
    calc r ^ (d - 2) * ((1 + r) ^ M)⁻¹ ≤ (1 + r) ^ (d - 2) * ((1 + r) ^ M)⁻¹ := by gcongr
      _ ≤ ((1 + r) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        calc (1 + r) ^ (d - 2) = (1 + r) ^ (d - 2) * (1 + r) ^ 2 * ((1 + r) ^ 2)⁻¹ := by
              field_simp
          _ ≤ (1 + r) ^ M * ((1 + r) ^ 2)⁻¹ := by gcongr
          _ = ((1 + r) ^ 2)⁻¹ * (1 + r) ^ M := mul_comm _ _

/-- A real polynomial grows at most polynomially: `|p(t)| ≤ C (1 + |t|)^k`. -/
lemma Polynomial.exists_abs_eval_le (p : Polynomial ℝ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ t, |p.eval t| ≤ C * (1 + |t|) ^ k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨C₁, k₁, hC₁, h₁⟩ := hp
    obtain ⟨C₂, k₂, hC₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, max k₁ k₂, by positivity, fun t => ?_⟩
    have ht : 1 ≤ 1 + |t| := le_add_of_nonneg_right (abs_nonneg t)
    rw [Polynomial.eval_add]
    calc |p.eval t + q.eval t| ≤ |p.eval t| + |q.eval t| := abs_add_le _ _
      _ ≤ C₁ * (1 + |t|) ^ max k₁ k₂ + C₂ * (1 + |t|) ^ max k₁ k₂ := by
        gcongr
        · exact (h₁ t).trans (by gcongr; exact le_max_left _ _)
        · exact (h₂ t).trans (by gcongr; exact le_max_right _ _)
      _ = (C₁ + C₂) * (1 + |t|) ^ max k₁ k₂ := by ring
  | monomial n a =>
    refine ⟨|a|, n, abs_nonneg a, fun t => ?_⟩
    rw [Polynomial.eval_monomial, abs_mul, abs_pow]
    gcongr
    linarith [abs_nonneg t]

/-- A polynomially bounded function times the norm of a Schwartz map is integrable. -/
lemma IsPolyBounded.integrable_abs_mul_norm_schwartz {d : ℕ} {u : Space d → ℝ}
    (hu : IsPolyBounded u) (hm : AEStronglyMeasurable u) (g : 𝓢(Space d, ℂ)) :
    Integrable (fun y => |u y| * ‖g y‖) := by
  simpa [norm_mul, Complex.norm_real] using (hu.integrable_ofReal_mul_schwartz hm g).norm

/-- `‖y‖⁻¹` times a polynomially bounded function times the norm of a Schwartz map is integrable
in dimension `d ≥ 2`. -/
lemma IsPolyBounded.integrable_inv_norm_mul {d : ℕ} (hd : 2 ≤ d) {u : Space d → ℝ}
    (hu : IsPolyBounded u) (hm : AEStronglyMeasurable u) (g : 𝓢(Space d, ℂ)) :
    Integrable (fun y => ‖y‖⁻¹ * (|u y| * ‖g y‖)) := by
  obtain ⟨C, k, hC, hb⟩ := hu
  set m := k + d
  set B := 2 ^ m * (Finset.Iic (m, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
  have hint := (integrable_inv_norm_mul_one_add_norm_pow hd (M := d) le_rfl).const_mul (C * B)
  refine hint.mono' ((measurable_norm.inv.aestronglyMeasurable).mul
    (hm.norm.mul g.continuous.norm.aestronglyMeasurable)) (Filter.Eventually.of_forall fun y => ?_)
  have hg := g.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, 0)) (k := m) (n := 0)
    le_rfl le_rfl y
  rw [norm_iteratedFDeriv_zero] at hg
  have hpos : 0 < 1 + ‖y‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖y‖⁻¹ * (|u y| * ‖g y‖) ≤ ‖y‖⁻¹ * (C * (1 + ‖y‖) ^ k * ‖g y‖) := by gcongr; exact hb y
    _ = C * ((1 + ‖y‖) ^ m * ‖g y‖) * (‖y‖⁻¹ * ((1 + ‖y‖) ^ d)⁻¹) := by
      simp only [m, pow_add]
      field_simp
    _ ≤ C * B * (‖y‖⁻¹ * ((1 + ‖y‖) ^ d)⁻¹) := by gcongr

end PhyslibAlpha.Hydrogen
