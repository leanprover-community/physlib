/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Eigenfunction
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Gaussians
/-!

# Completeness of the eigenfunctions of the Harmonic Oscillator

Completeness of the eigenfunctions follows from Plancherel's theorem.

The steps of this proof are:

1. Prove that if `f` is orthogonal to all eigenvectors then the Fourier transform of
  it multiplied by `exp(-c x^2)` for a `0<c` is zero.
  Part of this is using the concept of `dominated_convergence`.
2. Use 'Plancherel's theorem' to show that `f` is zero.

-/

namespace QuantumMechanics

namespace OneDimension
namespace HarmonicOscillator
variable (Q : HarmonicOscillator)

open Module Nat
open PhysLean
open MeasureTheory HilbertSpace InnerProductSpace

/-

Integrability conditions related to eigenfunctions.

-/

lemma mul_eigenfunction_integrable (f : ℝ → ℂ) (hf : MemHS f) :
    MeasureTheory.Integrable (fun x => Q.eigenfunction n x * f x) := by
  have h1 := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (HilbertSpace.mk (Q.eigenfunction_memHS n))
    (HilbertSpace.mk hf)
  refine (integrable_congr ?_).mp h1
  simp only [RCLike.inner_apply]
  conv_lhs => enter [x]; rw [mul_comm]
  apply Filter.EventuallyEq.mul
  swap
  · exact coe_mk_ae hf
  trans (fun x => (starRingEnd ℂ) (Q.eigenfunction n x))
  · apply Filter.EventuallyEq.fun_comp
    exact coe_mk_ae (eigenfunction_memHS Q n)
  · apply Filter.EventuallyEq.of_eq
    funext x
    simp

lemma mul_physHermite_integrable (f : ℝ → ℂ) (hf : MemHS f) (n : ℕ) :
    MeasureTheory.Integrable (fun x => physHermite n (x/Q.ξ) *
      (f x * ↑(Real.exp (- x ^ 2 / (2 * Q.ξ^2))))) := by
  have h2 : (1 / ↑√(2 ^ n * ↑n !) * (1/ √(√Real.pi * Q.ξ)) : ℂ) • (fun (x : ℝ) =>
      (physHermite n (x / Q.ξ) *
      (f x * Real.exp (- x ^ 2 / (2 * Q.ξ^2))))) = fun x =>
      Q.eigenfunction n x * f x := by
    funext x
    simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div, mul_inv_rev,
      Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_ofNat, Pi.smul_apply, smul_eq_mul, eigenfunction_eq]
    ring
  have h1 := Q.mul_eigenfunction_integrable f hf (n := n)
  rw [← h2] at h1
  rw [IsUnit.integrable_smul_iff] at h1
  · exact h1
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div, mul_inv_rev,
    isUnit_iff_ne_zero, ne_eq, _root_.mul_eq_zero, inv_eq_zero, Complex.ofReal_eq_zero, cast_nonneg,
    Real.sqrt_eq_zero, cast_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, or_false,
    Real.sqrt_nonneg, not_or]
  apply And.intro
  · exact factorial_ne_zero n
  · apply And.intro
    · exact Real.sqrt_ne_zero'.mpr Q.ξ_pos
    · exact Real.sqrt_ne_zero'.mpr Real.pi_pos

lemma mul_polynomial_integrable (f : ℝ → ℂ) (hf : MemHS f) (P : Polynomial ℤ) :
    MeasureTheory.Integrable (fun x => (P (x /Q.ξ)) *
      (f x * Real.exp (- x^2 / (2 * Q.ξ^2)))) volume := by
  have h1 := polynomial_mem_physHermite_span P
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h1
  obtain ⟨a, ha⟩ := h1
  have h2 : (fun x => ↑(P (x/Q.ξ)) * (f x * ↑(Real.exp (- x ^ 2 / (2 * Q.ξ^2)))))
    = (fun x => ∑ r ∈ a.support, a r * (physHermite r (x/Q.ξ)) *
    (f x * Real.exp (- x ^ 2 / (2 * Q.ξ^2)))) := by
    funext x
    rw [← ha]
    rw [← Finset.sum_mul]
    congr
    rw [Finsupp.sum]
    simp
  rw [h2]
  apply MeasureTheory.integrable_finset_sum
  intro i hi
  simp only [mul_assoc]
  have hf' : (fun x => ↑(a i) * (physHermite i (x/Q.ξ) *
    (f x * Real.exp (- (x ^ 2) / (2 * Q.ξ^2)))))
    = fun x => (a i) • (physHermite i (x/Q.ξ) * (f x * Real.exp (- x ^ 2 / (2 * Q.ξ^2)))) := by
    funext x
    simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.real_smul]
  rw [hf']
  apply MeasureTheory.Integrable.fun_smul
  exact Q.mul_physHermite_integrable f hf i

lemma mul_power_integrable (f : ℝ → ℂ) (hf : MemHS f) (r : ℕ) :
    MeasureTheory.Integrable (fun x => x ^ r * (f x * Real.exp (- x^2 / (2 * Q.ξ^2)))) volume := by
  by_cases hr : r ≠ 0
  · have h1 := Q.mul_polynomial_integrable f hf (Polynomial.X ^ r)
    simp only [map_pow, Polynomial.aeval_X, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] at h1
    have h2 : (fun x => (x /Q.ξ) ^ r * (f x * Complex.exp (- x ^ 2/ (2 * Q.ξ^2))))
      = (1/Q.ξ : ℂ) ^ r • (fun x => (x ^r * (f x * Real.exp (- ↑x ^ 2 / (2 * Q.ξ^2))))) := by
      funext x
      simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul,
        Complex.ofReal_pow, Complex.ofReal_ofNat, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h2] at h1
    suffices h2 : IsUnit (↑((1/Q.ξ)^ r : ℂ)) by
      rw [IsUnit.integrable_smul_iff h2] at h1
      simpa using h1
    simp only [isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not]
    simp
  · simp only [ne_eq, Decidable.not_not] at hr
    subst hr
    simpa using Q.mul_physHermite_integrable f hf 0

/-!

## Orthogonality conditions

-/

lemma orthogonal_eigenfunction_of_mem_orthogonal (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n), HilbertSpace.mk hf⟫_ℂ = 0)
    (n : ℕ) : ∫ (x : ℝ), Q.eigenfunction n x * f x = 0 := by
  rw [← hOrth n]
  rw [inner_mk_mk]
  simp

local notation "m" => Q.m
local notation "ℏ" => Q.ℏ
local notation "ω" => Q.ω
local notation "hm" => Q.hm
local notation "hℏ" => Q.hℏ
local notation "hω" => Q.hω

lemma orthogonal_physHermite_of_mem_orthogonal (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n), HilbertSpace.mk hf⟫_ℂ = 0)
    (n : ℕ) : ∫ (x : ℝ), (physHermite n (x / Q.ξ)) * (f x * ↑(Real.exp (- x ^ 2 / (2 * Q.ξ ^ 2))))
    = 0 := by
  have h1 := Q.orthogonal_eigenfunction_of_mem_orthogonal f hf hOrth n
  have h2 : (fun (x : ℝ) => (1 / ↑√(2 ^ n * ↑n !) * (1/ √(√Real.pi * Q.ξ)) : ℂ) *
      (physHermite n (x/Q.ξ) * f x * Real.exp (- x ^ 2 / (2 * Q.ξ^2))))
      = fun x => Q.eigenfunction n x * f x := by
    funext x
    simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div, mul_inv_rev,
      Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_ofNat, eigenfunction_eq]
    ring
  rw [← h2, MeasureTheory.integral_const_mul] at h1
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div, mul_inv_rev,
    Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_ofNat, _root_.mul_eq_zero, inv_eq_zero, Complex.ofReal_eq_zero, cast_nonneg,
    Real.sqrt_eq_zero, cast_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and,
    or_false, Real.sqrt_nonneg] at h1
  have h0 : n ! ≠ 0 := factorial_ne_zero n
  have h0' : ¬ (√Q.ξ = 0 ∨ √Real.pi = 0) := by
    simpa using And.intro (Real.sqrt_ne_zero'.mpr Q.ξ_pos) (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  simp only [h0, h0', or_self, false_or] at h1
  rw [← h1]
  congr
  funext x
  simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

lemma orthogonal_polynomial_of_mem_orthogonal (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n), HilbertSpace.mk hf⟫_ℂ = 0)
    (P : Polynomial ℤ) :
    ∫ x : ℝ, (P (x /Q.ξ)) * (f x * Real.exp (- x^2 / (2 * Q.ξ^2))) = 0 := by
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp <|
    polynomial_mem_physHermite_span P
  have h2 : (fun x => ↑(P (x /Q.ξ)) * (f x * ↑(Real.exp (- x ^ 2 / (2 * Q.ξ^2)))))
      = (fun x => ∑ r ∈ a.support, a r * (physHermite r (x/Q.ξ)) *
      (f x * Real.exp (- x ^ 2 / (2 * Q.ξ^2)))) := by
    funext x
    rw [← ha]
    simp [← Finset.sum_mul, Finsupp.sum]
  rw [h2, MeasureTheory.integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro x hx
    simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_mul, Complex.ofReal_ofNat, mul_assoc, integral_const_mul, _root_.mul_eq_zero,
      Complex.ofReal_eq_zero]
    right
    simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_mul, Complex.ofReal_ofNat,
      ← Q.orthogonal_physHermite_of_mem_orthogonal f hf hOrth x]
  · /- Integrablility -/
    intro i hi
    have hf' : (fun x => ↑(a i) * ↑(physHermite i (x /Q.ξ)) *
        (f x * ↑(Real.exp (- x ^ 2 / (2 * Q.ξ^2)))))
        = a i • (fun x => (physHermite i (x/Q.ξ)) *
        (f x * ↑(Real.exp (- x ^ 2 / (2 * Q.ξ^2))))) := by
      funext x
      simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Pi.smul_apply,
        Complex.real_smul]
      ring
    exact hf' ▸ (MeasureTheory.Integrable.smul _ (Q.mul_physHermite_integrable f hf i))

/-- If `f` is a function `ℝ → ℂ` satisfying `MemHS f` such that it is orthogonal
  to all `eigenfunction n` then it is orthogonal to

  `x ^ r * e ^ (- x ^ 2 / (2 ξ^2))`

  the proof of this result relies on the fact that Hermite polynomials span polynomials. -/
lemma orthogonal_power_of_mem_orthogonal (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n), HilbertSpace.mk hf⟫_ℂ = 0)
    (r : ℕ) : ∫ x : ℝ, (x ^ r * (f x * Real.exp (- x^2 / (2 * Q.ξ^2)))) = 0 := by
  by_cases hr : r ≠ 0
  · have h1 := Q.orthogonal_polynomial_of_mem_orthogonal f hf hOrth (Polynomial.X ^ r)
    simp only [map_pow, Polynomial.aeval_X, Complex.ofReal_pow, Complex.ofReal_div,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat] at h1
    have h2 : (fun x => (x /Q.ξ) ^ r *
      (f x * Complex.exp (- x ^ 2 / (2 * Q.ξ^2))))
      = (fun x => (1/Q.ξ : ℂ) ^ r * (↑x ^r *
      (f x * Complex.exp (- x ^ 2 / (2 * Q.ξ^2))))) := by
      funext x
      ring
    rw [h2, MeasureTheory.integral_const_mul] at h1
    simp only [one_div, inv_pow, _root_.mul_eq_zero, inv_eq_zero, pow_eq_zero_iff',
      Complex.ofReal_eq_zero, ξ_ne_zero, ne_eq, false_and, false_or] at h1
    rw [← h1]
    congr
    funext x
    simp
  · simp only [ne_eq, Decidable.not_not] at hr
    subst hr
    simp only [pow_zero, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, one_mul]
    rw [← Q.orthogonal_physHermite_of_mem_orthogonal f hf hOrth 0]
    congr
    funext x
    simp

open Finset

/-- If `f` is a function `ℝ → ℂ` satisfying `MemHS f` such that it is orthogonal
  to all `eigenfunction n` then it is orthogonal to

  `e ^ (I c x) * e ^ (- x ^ 2 / (2 ξ^2))`

  for any real `c`.
  The proof of this result relies on the expansion of `e ^ (I c x)`
  in terms of `x^r/r!` and using `orthogonal_power_of_mem_orthogonal`
  along with integrability conditions. -/
lemma orthogonal_exp_of_mem_orthogonal (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n), HilbertSpace.mk hf⟫_ℂ = 0)
    (c : ℝ) : ∫ x : ℝ, Complex.exp (Complex.I * c * x) *
    (f x * Real.exp (- x^2 / (2 * Q.ξ^2))) = 0 := by
  /- Rewriting the integrand as a limit. -/
  have h1 (y : ℝ) : Filter.Tendsto (fun n => ∑ r ∈ range n,
        (Complex.I * ↑c * ↑y) ^ r / r ! * (f y * Real.exp (- y^2 / (2 * Q.ξ^2))))
      Filter.atTop (nhds (Complex.exp (Complex.I * c * y) *
      (f y * Real.exp (- y^2 / (2 * Q.ξ^2))))) := by
    have h11 : (fun n => ∑ r ∈ range n,
        (Complex.I * ↑c * ↑y) ^ r / r !
        * (f y * Real.exp (- y^2 / (2 * Q.ξ^2)))) =
        fun n => (∑ r ∈ range n,
        (Complex.I * ↑c * ↑y) ^ r / r !)
        * ((f y * Real.exp (- y^2 / (2 * Q.ξ^2)))) := by
      funext s
      simp [Finset.sum_mul]
    rw [h11]
    have h12 : (Complex.exp (Complex.I * c * y) * (f y * Real.exp (- y^2 / (2 * Q.ξ^2))))
      = (Complex.exp (Complex.I * c * y)) * (f y * Real.exp (- y^2 / (2 * Q.ξ^2))) := by
      simp
    rw [h12]
    apply Filter.Tendsto.mul_const
    simp only [Complex.exp, Complex.exp']
    haveI hi : CauSeq.IsComplete ℂ norm :=
      inferInstanceAs (CauSeq.IsComplete ℂ norm)
    exact CauSeq.tendsto_limit (Complex.exp' (Complex.I * c * y))
  /- End of rewriting the integrand as a limit. -/
  /- Rewriting the integral as a limit using dominated_convergence -/
  have h1' : Filter.Tendsto (fun n => ∫ y : ℝ, ∑ r ∈ range n,
      (Complex.I * ↑c * ↑y) ^ r / r ! * (f y * Real.exp (- y^2 / (2 * Q.ξ^2))))
      Filter.atTop (nhds (∫ y : ℝ, Complex.exp (Complex.I * c * y) *
      (f y * Real.exp (- y^2 / (2 * Q.ξ^2))))) := by
    let bound : ℝ → ℝ := fun x => Real.exp (|c * x|) * norm (f x) *
      (Real.exp (- x ^ 2 / (2 * Q.ξ^2)))
    apply MeasureTheory.tendsto_integral_of_dominated_convergence bound
    · intro n
      refine aestronglyMeasurable_fun_sum (range n) ?_
      intro r hr
      have h1 : (fun a => (Complex.I * ↑c * ↑a) ^ r / ↑r ! *
        (f a * ↑(Real.exp (- a ^ 2 / (2 * Q.ξ^2)))))
        = fun a => (Complex.I * ↑c) ^ r / ↑r ! *
        (f a * Complex.ofReal (a ^ r * (Real.exp (- a ^ 2 / (2 * Q.ξ^2))))) := by
        funext a
        simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
          Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
        ring
      rw [h1]
      apply MeasureTheory.AEStronglyMeasurable.const_mul
      apply MeasureTheory.AEStronglyMeasurable.mul
      · exact aeStronglyMeasurable_of_memHS hf
      · apply MeasureTheory.Integrable.aestronglyMeasurable
        apply MeasureTheory.Integrable.ofReal
        change Integrable (fun x => (x ^ r) * (Real.exp (- x ^ 2 / (2 * Q.ξ^2))))
        have h1 : (fun x => (x ^ r)*(Real.exp (- x ^ 2 / (2 * Q.ξ^2)))) =
            (fun x => (Polynomial.X ^ r : Polynomial ℤ).aeval x *
            (Real.exp (- (1/ (2* Q.ξ^2)) * x ^ 2))) := by
          funext x
          simp only [neg_mul, map_pow, Polynomial.aeval_X, mul_eq_mul_left_iff, Real.exp_eq_exp,
            pow_eq_zero_iff', ne_eq]
          left
          field_simp
        rw [h1]
        apply guassian_integrable_polynomial
        simp
    · /- Prove the bound is integrable. -/
      have hbound : bound = (fun x => Real.exp |c * x| * norm (f x) *
          Real.exp (-(1/ (2 * Q.ξ^2)) * x ^ 2)) := by
        simp only [neg_mul, bound]
        funext x
        congr
        field_simp
      rw [hbound]
      apply HilbertSpace.exp_abs_mul_abs_mul_gaussian_integrable
      · exact hf
      · simp
    · intro n
      apply Filter.Eventually.of_forall
      intro y
      rw [← Finset.sum_mul]
      simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, norm_mul,
        bound]
      rw [mul_assoc]
      conv_rhs =>
        rw [mul_assoc]
      have h1 : (norm (f y) * norm (Complex.exp (-(↑y ^ 2) / (2 * Q.ξ^2))))
        = norm (f y) * Real.exp (-(y ^ 2) / (2 * Q.ξ^2)) := by
        simp only [mul_eq_mul_left_iff]
        left
        rw [Complex.norm_exp]
        congr
        trans (Complex.ofReal (- y ^ 2 / (2 * Q.ξ^2))).re
        · congr
          simp
        · rw [Complex.ofReal_re]
      rw [h1]
      by_cases hf : norm (f y) = 0
      · simp [hf]
      rw [mul_le_mul_iff_left₀]
      · have h1 := Real.sum_le_exp_of_nonneg (x := |c * y|) (abs_nonneg (c * y)) n
        refine le_trans ?_ h1
        have h2 : norm (∑ i ∈ range n, (Complex.I * (↑c * ↑y)) ^ i / ↑i !) ≤
          ∑ i ∈ range n, norm ((Complex.I * (↑c * ↑y)) ^ i / ↑i !) := by
          exact norm_sum_le _ _
        refine le_trans h2 ?_
        apply le_of_eq
        congr
        funext i
        simp only [Complex.norm_div, norm_pow, Complex.norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, one_mul, RCLike.norm_natCast]
        congr
        rw [abs_mul]
      · refine mul_pos ?_ ?_
        have h1 : 0 ≤ norm (f y) := norm_nonneg (f y)
        apply lt_of_le_of_ne h1 (fun a => hf (id (Eq.symm a)))
        exact Real.exp_pos (- y ^ 2 / (2 * Q.ξ^2))
    · apply Filter.Eventually.of_forall
      intro y
      exact h1 y
  have h3b : (fun n => ∫ y : ℝ, ∑ r ∈ range n,
      (Complex.I * ↑c * ↑y) ^ r / r ! *
      (f y * Real.exp (- y^2 / (2 * Q.ξ^2)))) = fun (n : ℕ) => 0 := by
    funext n
    rw [MeasureTheory.integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro r hr
      have hf' : (fun a => (Complex.I * ↑c * ↑a) ^ r / ↑r ! *
        (f a * ↑(Real.exp (- a ^ 2 / (2 * Q.ξ^2)))))
        = fun a => ((Complex.I * ↑c) ^ r / ↑r !) *
        (a^ r * (f a * ↑(Real.exp (- a ^ 2 / (2 * Q.ξ^2))))) := by
        funext a
        simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
          Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
        ring
      rw [hf']
      rw [MeasureTheory.integral_const_mul]
      rw [Q.orthogonal_power_of_mem_orthogonal f hf hOrth r]
      simp
    · intro r hr
      have hf' : (fun a => (Complex.I * ↑c * ↑a) ^ r / ↑r ! *
        (f a * ↑(Real.exp (- a ^ 2 / (2 * Q.ξ^2)))))
        = ((Complex.I * ↑c) ^ r / ↑r !) •
        fun a => (a^ r * (f a * ↑(Real.exp (- a ^ 2 / (2 * Q.ξ^2))))) := by
        funext a
        simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
          Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hf']
      apply MeasureTheory.Integrable.smul
      exact Q.mul_power_integrable f hf r
  rw [h3b] at h1'
  apply tendsto_nhds_unique h1'
  rw [tendsto_const_nhds_iff]

open FourierTransform MeasureTheory Real Lp MemLp Filter Complex Topology
  ComplexInnerProductSpace ComplexConjugate

/-- If `f` is a function `ℝ → ℂ` satisfying `MemHS f` such that it is orthogonal
  to all `eigenfunction n` then the fourier transform of

  `f (x) * e ^ (- x ^ 2 / (2 ξ^2))`

  is zero.

  The proof of this result relies on `orthogonal_exp_of_mem_orthogonal`. -/
lemma fourierIntegral_zero_of_mem_orthogonal (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n), HilbertSpace.mk hf⟫_ℂ = 0) :
    𝓕 (fun x => f x * Real.exp (- x^2 / (2 * Q.ξ^2))) = 0 := by
  funext c
  rw [Real.fourier_eq]
  simp only [RCLike.inner_apply, conj_trivial, ofReal_exp, ofReal_div, ofReal_neg,
    ofReal_mul, ofReal_pow, ofReal_ofNat, Pi.zero_apply]
  rw [← Q.orthogonal_exp_of_mem_orthogonal f hf hOrth (- 2 * Real.pi * c)]
  congr
  funext x
  simp only [fourierChar, Circle.exp, ContinuousMap.coe_mk, ofReal_mul, ofReal_ofNat,
    AddChar.coe_mk, ofReal_neg, mul_neg, neg_mul, ofReal_exp, ofReal_div, ofReal_pow]
  change cexp (-(2 * ↑π * (↑c * ↑x) * I)) *
    (f x * Complex.exp (- x ^ 2 / (2 * Q.ξ^2))) = _
  congr 2
  ring

lemma zero_of_orthogonal_mk (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n), HilbertSpace.mk hf⟫_ℂ = 0)
    (plancherel_theorem: ∀ {f : ℝ → ℂ} (hf : Integrable f volume) (_ : MemLp f 2),
      eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume) :
    HilbertSpace.mk hf = 0 := by
  have hf' : (fun x => f x * ↑(rexp (- x ^ 2 / (2 * Q.ξ^2))))
        = (fun x => f x * ↑(rexp (- (1/ (2 * Q.ξ^2)) * (x - 0) ^ 2))) := by
    funext x
    simp only [neg_mul, ofReal_exp, ofReal_div, ofReal_neg, ofReal_mul, ofReal_pow,
      ofReal_ofNat, sub_zero, mul_eq_mul_left_iff]
    left
    congr
    field_simp
    simp
  have h1 : eLpNorm (fun x => f x * Real.exp (- x^2 / (2 * Q.ξ^2))) 2 volume = 0 := by
    rw [← plancherel_theorem]
    rw [Q.fourierIntegral_zero_of_mem_orthogonal f hf hOrth]
    simp only [eLpNorm_zero]
    · /- f x * Real.exp (- x^2 / (2 * ξ^2)) is integrable -/
      rw [hf']
      rw [← memLp_one_iff_integrable]
      apply HilbertSpace.mul_gaussian_mem_Lp_one f hf (1/ (2 * Q.ξ^2)) 0
      simp
    · /- f x * Real.exp (- x^2 / (2 * ξ^2)) is square-integrable -/
      rw [hf']
      refine HilbertSpace.mul_gaussian_mem_Lp_two f hf (1 / (2 * Q.ξ^2)) 0 ?_
      simp
  refine (norm_eq_zero_iff (by simp)).mp ?_
  simp only [Norm.norm, eLpNorm_mk]
  have h2 : eLpNorm f 2 volume = 0 := by
    rw [MeasureTheory.eLpNorm_eq_zero_iff] at h1 ⊢
    rw [Filter.eventuallyEq_iff_all_subsets] at h1 ⊢
    simp only [ofReal_exp, ofReal_div, ofReal_neg, ofReal_mul, ofReal_pow, ofReal_ofNat,
      Pi.zero_apply, _root_.mul_eq_zero, Complex.exp_ne_zero, or_false] at h1
    exact h1
    exact aeStronglyMeasurable_of_memHS hf
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    · /- f x * Real.exp (- x^2 / (2 * ξ^2)) is strongly measurable -/
      rw [hf']
      apply Integrable.aestronglyMeasurable
      rw [← memLp_one_iff_integrable]
      apply HilbertSpace.mul_gaussian_mem_Lp_one f hf (1/ (2 * Q.ξ^2)) 0
      simp
    · simp
  rw [h2]
  simp

lemma zero_of_orthogonal_eigenVector (f : HilbertSpace)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n), f⟫_ℂ = 0)
    (plancherel_theorem: ∀ {f : ℝ → ℂ} (hf : Integrable f volume) (_ : MemLp f 2),
      eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume) : f = 0 := by
  obtain ⟨f, hf, rfl⟩ := HilbertSpace.mk_surjective f
  exact zero_of_orthogonal_mk Q f hf hOrth plancherel_theorem

/--
  Assuming Plancherel's theorem (which is not yet in Mathlib),
  the topological closure of the span of the eigenfunctions of the harmonic oscillator
  is the whole Hilbert space.

  The proof of this result relies on `fourierIntegral_zero_of_mem_orthogonal`
  and Plancherel's theorem which together give us that the norm of

  `f x * e ^ (- x^2 / (2 * ξ^2))`

  is zero for `f` orthogonal to all eigenfunctions, and hence the norm of `f` is zero.
-/
theorem eigenfunction_completeness
    (plancherel_theorem : ∀ {f : ℝ → ℂ} (hf : Integrable f volume) (_ : MemLp f 2),
      eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume) :
    (Submodule.span ℂ
    (Set.range (fun n => HilbertSpace.mk (Q.eigenfunction_memHS n)))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff]
  refine (Submodule.eq_bot_iff (Submodule.span ℂ
    (Set.range (fun n => HilbertSpace.mk (Q.eigenfunction_memHS n))))ᗮ).mpr ?_
  intro f hf
  apply Q.zero_of_orthogonal_eigenVector f ?_ plancherel_theorem
  intro n
  rw [@Submodule.mem_orthogonal'] at hf
  rw [← inner_conj_symm]
  have hl : ⟪f, HilbertSpace.mk (Q.eigenfunction_memHS n)⟫_ℂ = 0 := by
    apply hf
    refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ?_
    use Finsupp.single n 1
    simp
  rw [hl]
  simp

end HarmonicOscillator
end OneDimension
end QuantumMechanics
