/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Existence.GardingVectors
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.MeasureTheory.Function.L2Space

/-!

# Growth of the derivatives of the heat kernel

Hermite polynomial bounds on the L¹ norms of the heat kernel's derivatives.

## i. Overview

The `n`-th derivative of the heat kernel is a Hermite polynomial times a Gaussian. The probabilists'
Hermite polynomials satisfy `∫ Hₙ(x)² exp(-x²/2) dx = √(2π) n!`, proved by one integration by parts
per step using `Hₙ₊₁' = (n + 1) Hₙ`. Cauchy–Schwarz then bounds the `L¹` norm of the `n`-th
derivative of the heat kernel by `C^(n + 1) √(n!)`.

## ii. Key results

- `hermite_derivative_succ` : `Hₙ₊₁' = (n + 1) Hₙ`.
- `hermite_gaussian_sq_integral` : `∫ Hₙ(x)² exp(-x²/2) dx = √(2π) n!`.
- `gaussianKernel_iteratedDeriv_eq` : the derivatives of the heat kernel in terms of Hermite
  polynomials.
- `gaussianKernel_iteratedDeriv_L1_bound` : the `L¹` bound on the derivatives of the heat kernel.

## iii. Table of contents

- A. The Hermite derivative identity
- B. Integrability against Gaussian weights
- C. The norm of the Hermite polynomials
- D. Derivatives of the heat kernel

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace QuantumMechanics

noncomputable section

open MeasureTheory Polynomial

/-!

## A. The Hermite derivative identity

-/

/-- The polynomial identity `Hₙ₊₁' = (n+1) · Hₙ`, absent from Mathlib, proved directly from the
defining recursion `hermite_succ : Hₙ₊₁ = X·Hₙ - Hₙ'` by induction. -/
lemma hermite_derivative_succ :
    ∀ n : ℕ, derivative (hermite (n + 1)) = C ((n : ℤ) + 1) * hermite n
  | 0 => by simp [hermite_zero]
  | (n + 1) => by
      have ih := hermite_derivative_succ n
      have hsucc1 : hermite (n + 1 + 1) = X * hermite (n + 1) - derivative (hermite (n + 1)) :=
        hermite_succ (n + 1)
      have hsucc0 : hermite (n + 1) = X * hermite n - derivative (hermite n) :=
        hermite_succ n
      have key : derivative (hermite (n + 1 + 1)) =
          derivative (X * hermite (n + 1)) - derivative (derivative (hermite (n + 1))) := by
        rw [hsucc1, derivative_sub]
      rw [derivative_mul, derivative_X, one_mul] at key
      rw [ih, derivative_C_mul] at key
      have hCsplit : C ((n : ℤ) + 1 + 1) = C ((n : ℤ) + 1) + 1 := by rw [← C_1, ← map_add]
      have hfin : hermite (n + 1) + X * (C ((n : ℤ) + 1) * hermite n) -
          C ((n : ℤ) + 1) * derivative (hermite n) = C ((n : ℤ) + 1 + 1) * hermite (n + 1) := by
        rw [hCsplit, hsucc0]; ring
      rw [key, hfin]
      push_cast
      ring

/-- The `aeval`/real-valued specialization of `hermite_derivative_succ`. -/
lemma hermite_aeval_deriv_succ (n : ℕ) (x : ℝ) :
    aeval x (derivative (hermite (n + 1))) = ((n : ℝ) + 1) * aeval x (hermite n) := by
  have h := congrArg (fun p : Polynomial ℤ => aeval x p) (hermite_derivative_succ n)
  simpa using h

/-- The `aeval`/real-valued specialization of the defining recursion `hermite_succ`. -/
lemma hermite_aeval_succ (n : ℕ) (x : ℝ) :
    aeval x (hermite (n + 1)) = x * aeval x (hermite n) - aeval x (derivative (hermite n)) := by
  simp [hermite_succ]

/-!

## B. Integrability against Gaussian weights

-/

/-- A monomial times a Gaussian weight is integrable (the `n`-th-power case of
`integrable_aeval_mul_gaussian`, via the real-exponent Gaussian-tail estimate specialized to a
natural-number exponent through `Real.rpow_natCast`). -/
lemma integrable_pow_mul_exp_neg_mul_sq (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-(c * x ^ 2))) := by
  have hs : (-1 : ℝ) < (n : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := c) hc hs
  simpa [Real.rpow_natCast, neg_mul] using h

/-- Any (integer) polynomial times a Gaussian weight is integrable — the integrability fact needed
throughout `hermite_gaussian_sq_integral_succ`'s integration-by-parts argument. Proved by
`Polynomial.induction_on'`, reducing to the monomial case. -/
lemma integrable_aeval_mul_gaussian (q : Polynomial ℤ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => aeval x q * Real.exp (-(c * x ^ 2))) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
      have h : Integrable (fun x : ℝ =>
          aeval x p * Real.exp (-(c * x ^ 2)) + aeval x r * Real.exp (-(c * x ^ 2))) :=
        hp.add hr
      simpa [add_mul] using h
  | monomial n a =>
      have := (integrable_pow_mul_exp_neg_mul_sq n hc).const_mul (a : ℝ)
      simpa [mul_assoc] using this

/-- The derivative of the standard Gaussian, packaged as `HasDerivAt` (Mathlib only records the
`deriv`-value form privately, inside the proof of `deriv_gaussian_eq_hermite_mul_gaussian`). -/
lemma gaussian_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (-x * Real.exp (-(x ^ 2 / 2))) x := by
  have hdiff : DifferentiableAt ℝ (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x :=
    DifferentiableAt.exp (by fun_prop)
  have heq : deriv (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x = -x * Real.exp (-(x ^ 2 / 2)) := by
    rw [deriv_exp (by fun_prop)]
    simp [mul_comm]
  have h := hdiff.hasDerivAt
  rwa [heq] at h

/-!

## C. The norm of the Hermite polynomials

-/

/-- `Iₙ₊₁ = (n + 1) Iₙ` for `Iₙ = ∫ Hₙ(x)² exp(-x²/2) dx`, by integration by parts. -/
lemma hermite_gaussian_sq_integral_succ (n : ℕ) :
    (∫ x : ℝ, (aeval x (hermite (n + 1))) ^ 2 * Real.exp (-(x ^ 2 / 2))) =
      ((n : ℝ) + 1) * ∫ x : ℝ, (aeval x (hermite n)) ^ 2 * Real.exp (-(x ^ 2 / 2)) := by
  set u : ℝ → ℝ := fun x => aeval x (hermite (n + 1)) with hu_def
  set v : ℝ → ℝ := fun x => aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) with hv_def
  set u' : ℝ → ℝ := fun x => aeval x (derivative (hermite (n + 1))) with hu'_def
  set v' : ℝ → ℝ := fun x => -(aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2))) with hv'_def
  have hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x := fun x _ =>
    Polynomial.hasDerivAt_aeval (hermite (n + 1)) x
  have hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => aeval y (hermite n)) (aeval x (derivative (hermite n))) x :=
      Polynomial.hasDerivAt_aeval (hermite n) x
    have h2 := h1.mul (gaussian_hasDerivAt x)
    have heq : aeval x (derivative (hermite n)) * Real.exp (-(x ^ 2 / 2)) +
        aeval x (hermite n) * (-x * Real.exp (-(x ^ 2 / 2))) = v' x := by
      simp only [hv'_def]
      have hsucc : aeval x (hermite (n + 1)) =
          x * aeval x (hermite n) - aeval x (derivative (hermite n)) := hermite_aeval_succ n x
      rw [hsucc]; ring
    rw [← heq]
    exact h2
  have huv' : Integrable (u * v') := by
    have hbase := (integrable_aeval_mul_gaussian ((hermite (n + 1)) ^ 2) (c := 1 / 2)
      (by norm_num)).neg
    have heq : (u * v') =
        -fun x => aeval x ((hermite (n + 1)) ^ 2) * Real.exp (-(1 / 2 * x ^ 2)) := by
      funext x
      simp only [hu_def, hv'_def, Pi.mul_apply, Pi.neg_apply, map_pow]
      ring_nf
    rwa [heq]
  have hu'v : Integrable (u' * v) := by
    have hbase := integrable_aeval_mul_gaussian (derivative (hermite (n + 1)) * hermite n)
      (c := 1 / 2) (by norm_num)
    have heq : (u' * v) = fun x =>
        aeval x (derivative (hermite (n + 1)) * hermite n) * Real.exp (-(1 / 2 * x ^ 2)) := by
      funext x
      simp only [hu'_def, hv_def, Pi.mul_apply, map_mul]
      ring_nf
    rwa [heq]
  have huv : Integrable (u * v) := by
    have hbase := integrable_aeval_mul_gaussian (hermite (n + 1) * hermite n)
      (c := 1 / 2) (by norm_num)
    have heq : (u * v) = fun x =>
        aeval x (hermite (n + 1) * hermite n) * Real.exp (-(1 / 2 * x ^ 2)) := by
      funext x
      simp only [hu_def, hv_def, Pi.mul_apply, map_mul]
      ring_nf
    rwa [heq]
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv huv' hu'v huv
  have hlhs : (∫ x : ℝ, u x * v' x) =
      -(∫ x : ℝ, (aeval x (hermite (n + 1))) ^ 2 * Real.exp (-(x ^ 2 / 2))) := by
    have heq : (fun x => u x * v' x) =
        fun x => -((aeval x (hermite (n + 1))) ^ 2 * Real.exp (-(x ^ 2 / 2))) := by
      funext x; simp only [hu_def, hv'_def]; ring
    rw [show (∫ x : ℝ, u x * v' x) = ∫ x : ℝ, (fun x => u x * v' x) x from rfl, heq]
    exact MeasureTheory.integral_neg _
  have hrhs : (∫ x : ℝ, u' x * v x) =
      ((n : ℝ) + 1) * ∫ x : ℝ, (aeval x (hermite n)) ^ 2 * Real.exp (-(x ^ 2 / 2)) := by
    have heq : (fun x => u' x * v x) =
        fun x => ((n : ℝ) + 1) * ((aeval x (hermite n)) ^ 2 * Real.exp (-(x ^ 2 / 2))) := by
      funext x
      simp only [hu'_def, hv_def]
      rw [hermite_aeval_deriv_succ n x]
      ring
    rw [show (∫ x : ℝ, u' x * v x) = ∫ x : ℝ, (fun x => u' x * v x) x from rfl, heq]
    exact MeasureTheory.integral_const_mul _ _
  rw [hlhs, hrhs] at hIBP
  linarith

/-- **The norm of the Hermite polynomials**: `∫ Hₙ(x)² exp(-x²/2) dx = √(2π) n!`. -/
lemma hermite_gaussian_sq_integral (n : ℕ) :
    ∫ x : ℝ, (aeval x (hermite n)) ^ 2 * Real.exp (-(x ^ 2 / 2)) =
      Real.sqrt (2 * Real.pi) * n.factorial := by
  induction n with
  | zero =>
      simp only [hermite_zero, map_one, one_pow, one_mul, Nat.factorial_zero, Nat.cast_one,
        mul_one]
      have h := integral_gaussian (1 / 2 : ℝ)
      have hb : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring
      rw [hb] at h
      convert h using 2
      ring_nf
  | succ n ih =>
      rw [hermite_gaussian_sq_integral_succ n, ih]
      push_cast [Nat.factorial_succ]
      ring

/-- The weighted `L¹` bound `∫ |Hₙ(x)| exp(-x²/2) dx ≤ √(2π) √(n!)`. -/
lemma hermite_gaussian_L1_bound (n : ℕ) :
    ∫ x : ℝ, |aeval x (hermite n)| * Real.exp (-(x ^ 2 / 2)) ≤
      Real.sqrt (2 * Real.pi) * Real.sqrt n.factorial := by
  set A : ℝ := Real.sqrt (2 * Real.pi) with hA
  set f : ℝ → ℝ := fun x => |aeval x (hermite n)| * Real.exp (-(x ^ 2 / 4)) with hf
  set g : ℝ → ℝ := fun x => Real.exp (-(x ^ 2 / 4)) with hg
  have hfg : ∀ x : ℝ, f x * g x = |aeval x (hermite n)| * Real.exp (-(x ^ 2 / 2)) := by
    intro x
    simp only [hf, hg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hf_nonneg : 0 ≤ᵐ[volume] f := ae_of_all _ fun x => by positivity
  have hg_nonneg : 0 ≤ᵐ[volume] g := ae_of_all _ fun x => (Real.exp_pos _).le
  have hf_cont : Continuous f := by rw [hf]; fun_prop
  have hg_cont : Continuous g := by rw [hg]; fun_prop
  have hAsq_int : Integrable
      (fun x : ℝ => (aeval x (hermite n)) ^ 2 * Real.exp (-(x ^ 2 / 2))) := by
    by_contra hni
    have h0 := MeasureTheory.integral_undef hni
    rw [hermite_gaussian_sq_integral n] at h0
    have hpos : (0 : ℝ) < A * n.factorial := by rw [hA]; positivity
    linarith
  have hf_sq_int : Integrable (fun x : ℝ => f x ^ 2) := by
    have heq : (fun x : ℝ => f x ^ 2) =
        fun x : ℝ => (aeval x (hermite n)) ^ 2 * Real.exp (-(x ^ 2 / 2)) := by
      funext x
      simp only [hf, pow_two]
      rw [mul_mul_mul_comm, abs_mul_abs_self, ← Real.exp_add]
      congr 2
      ring
    rwa [heq]
  have hg_sq_int : Integrable (fun x : ℝ => g x ^ 2) := by
    have heq : (fun x : ℝ => g x ^ 2) = fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2) := by
      funext x; simp only [hg, pow_two, ← Real.exp_add]; congr 1; ring
    rw [heq]
    exact integrable_exp_neg_mul_sq (by norm_num)
  have hfMemLp : MemLp f 2 volume := (memLp_two_iff_integrable_sq hf_cont.aestronglyMeasurable).mpr
    hf_sq_int
  have hgMemLp : MemLp g 2 volume := (memLp_two_iff_integrable_sq hg_cont.aestronglyMeasurable).mpr
    hg_sq_int
  have hEOfReal : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    hf_nonneg hg_nonneg (hEOfReal ▸ hfMemLp) (hEOfReal ▸ hgMemLp)
  have hcongr : (∫ x : ℝ, f x * g x) = ∫ x : ℝ, |aeval x (hermite n)| * Real.exp (-(x ^ 2 / 2)) :=
    integral_congr_ae (ae_of_all _ hfg)
  rw [hcongr] at hCS
  have hf2 : (∫ x : ℝ, f x ^ 2) = A * n.factorial := by
    have heq : (fun x : ℝ => f x ^ 2) =
        fun x : ℝ => (aeval x (hermite n)) ^ 2 * Real.exp (-(x ^ 2 / 2)) := by
      funext x
      simp only [hf, pow_two]
      rw [mul_mul_mul_comm, abs_mul_abs_self, ← Real.exp_add]
      congr 2
      ring
    rw [heq, hermite_gaussian_sq_integral]
  have hg2 : (∫ x : ℝ, g x ^ 2) = A := by
    have heq : (fun x : ℝ => g x ^ 2) = fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2) := by
      funext x; simp only [hg, pow_two, ← Real.exp_add]; congr 1; ring
    rw [heq, integral_gaussian, hA]
    norm_num
    ring
  have hApos : 0 ≤ A := by rw [hA]; positivity
  have hRHS_eq : (∫ a : ℝ, f a ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
      (∫ a : ℝ, g a ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = A * Real.sqrt n.factorial := by
    simp only [Real.rpow_two]
    rw [hf2, hg2, ← Real.sqrt_eq_rpow (A * n.factorial), ← Real.sqrt_eq_rpow A,
      ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ A * (n.factorial : ℝ)),
      mul_comm (A * (n.factorial : ℝ)) A, ← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg A),
      Real.sqrt_sq hApos]
  exact hCS.trans_eq hRHS_eq

/-!

## D. Derivatives of the heat kernel

-/

/-- The `n`-th derivative of the heat kernel is a rescaled Hermite polynomial times the kernel. -/
lemma gaussianKernel_iteratedDeriv_eq {ε : ℝ} (hε : 0 < ε) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (gaussianKernel ε) t =
      (Real.pi * ε) ^ (-(1 : ℝ) / 2) * (Real.sqrt (2 / ε) ^ n *
        ((-1 : ℝ) ^ n * aeval (Real.sqrt (2 / ε) * t) (hermite n) *
          Real.exp (-((Real.sqrt (2 / ε) * t) ^ 2 / 2)))) := by
  set c : ℝ := Real.sqrt (2 / ε) with hc_def
  set K : ℝ := (Real.pi * ε) ^ (-(1 : ℝ) / 2) with hK_def
  set ψ : ℝ → ℝ := fun x => Real.exp (-(x ^ 2 / 2)) with hψ_def
  have hc_sq : c ^ 2 = 2 / ε := by rw [hc_def, Real.sq_sqrt (by positivity)]
  have hgk_eq : gaussianKernel ε = fun t => K * ψ (c * t) := by
    funext t
    show gaussianKernel ε t = K * ψ (c * t)
    unfold gaussianKernel
    rw [hK_def, hψ_def]
    congr 1
    have hexp_eq : -(t ^ 2) / ε = -((c * t) ^ 2 / 2) := by
      rw [mul_pow, hc_sq]; field_simp
    rw [hexp_eq]
  have hψ_smooth : ContDiff ℝ n ψ := by rw [hψ_def]; fun_prop
  rw [hgk_eq]
  have step1 : iteratedDeriv n (fun t => K * ψ (c * t)) t
      = K * iteratedDeriv n (fun t => ψ (c * t)) t :=
    iteratedDeriv_const_mul_field (n := n) (x := t) K (fun t => ψ (c * t))
  have step2 : iteratedDeriv n (fun t => ψ (c * t)) t = c ^ n * iteratedDeriv n ψ (c * t) :=
    congrFun (iteratedDeriv_comp_const_mul (n := n) hψ_smooth c) t
  rw [step1, step2, iteratedDeriv_eq_iterate, hψ_def, deriv_gaussian_eq_hermite_mul_gaussian]

/-- **The `L¹` norm of the `n`-th derivative of the heat kernel** is at most `C^(n + 1) √(n!)`. -/
lemma gaussianKernel_iteratedDeriv_L1_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      Integrable (iteratedDeriv n (gaussianKernel ε)) ∧
      ∫ t : ℝ, |iteratedDeriv n (gaussianKernel ε) t| ≤ C ^ (n + 1) * Real.sqrt n.factorial := by
  set c : ℝ := Real.sqrt (2 / ε) with hc_def
  have hc_pos : 0 < c := Real.sqrt_pos.mpr (by positivity)
  set K : ℝ := (Real.pi * ε) ^ (-(1 : ℝ) / 2) with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; positivity
  set ψ : ℝ → ℝ := fun x => Real.exp (-(x ^ 2 / 2)) with hψ_def
  have hc_sq : c ^ 2 = 2 / ε := by
    rw [hc_def, Real.sq_sqrt (by positivity)]
  -- `gaussianKernel ε` is `K` times `ψ` rescaled by `c`.
  have hgk_eq : gaussianKernel ε = fun t => K * ψ (c * t) := by
    funext t
    show gaussianKernel ε t = K * ψ (c * t)
    unfold gaussianKernel
    rw [hK_def, hψ_def]
    congr 1
    have hexp_eq : -(t ^ 2) / ε = -((c * t) ^ 2 / 2) := by
      rw [mul_pow, hc_sq]; field_simp
    rw [hexp_eq]
  -- `ψ` is smooth, so `iteratedDeriv_comp_const_mul` applies at every order.
  have hψ_smooth : ∀ n : ℕ, ContDiff ℝ n ψ := fun n => by rw [hψ_def]; fun_prop
  -- The `n`-th derivative identity, reducing `iteratedDeriv n (gaussianKernel ε)` to Hermite data.
  have hderiv_eq : ∀ n : ℕ, iteratedDeriv n (gaussianKernel ε) =
      fun t => K * (c ^ n * ((-1 : ℝ) ^ n * aeval (c * t) (hermite n) * ψ (c * t))) := by
    intro n
    rw [hgk_eq]
    funext t
    have step1 : iteratedDeriv n (fun t => K * ψ (c * t)) t
        = K * iteratedDeriv n (fun t => ψ (c * t)) t :=
      iteratedDeriv_const_mul_field (n := n) (x := t) K (fun t => ψ (c * t))
    have step2 : iteratedDeriv n (fun t => ψ (c * t)) t = c ^ n * iteratedDeriv n ψ (c * t) :=
      congrFun (iteratedDeriv_comp_const_mul (n := n) (hψ_smooth n) c) t
    rw [step1, step2, iteratedDeriv_eq_iterate, hψ_def, deriv_gaussian_eq_hermite_mul_gaussian]
  -- The exact normalization constant: `K · c⁻¹ · √(2π) = 1`.
  have hKe : K * Real.sqrt (Real.pi * ε) = 1 := by
    rw [hK_def, Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : (0 : ℝ) < Real.pi * ε)]
    norm_num
  have hcinv : c⁻¹ = Real.sqrt (ε / 2) := by
    rw [hc_def, ← Real.sqrt_inv]
    congr 1
    field_simp
  have hsplit : Real.sqrt (Real.pi * ε) = Real.sqrt (2 * Real.pi) * Real.sqrt (ε / 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  have hKc : K * c⁻¹ * Real.sqrt (2 * Real.pi) = 1 := by
    rw [hcinv]
    calc K * Real.sqrt (ε / 2) * Real.sqrt (2 * Real.pi)
        = K * (Real.sqrt (2 * Real.pi) * Real.sqrt (ε / 2)) := by ring
      _ = K * Real.sqrt (Real.pi * ε) := by rw [← hsplit]
      _ = 1 := hKe
  refine ⟨max c 1, lt_max_of_lt_right one_pos, fun n => ?_⟩
  have hg_integrable : Integrable (fun x : ℝ => aeval x (hermite n) * ψ x) := by
    have h := integrable_aeval_mul_gaussian (hermite n) (c := 1 / 2) (by norm_num)
    have heq : (fun x : ℝ => aeval x (hermite n) * Real.exp (-(1 / 2 * x ^ 2))) =
        fun x : ℝ => aeval x (hermite n) * ψ x := by
      funext x; rw [hψ_def]; congr 2; ring
    rwa [heq] at h
  have hpt : ∀ t : ℝ, iteratedDeriv n (gaussianKernel ε) t =
      K * (c ^ n * ((-1 : ℝ) ^ n * aeval (c * t) (hermite n) * ψ (c * t))) :=
    fun t => congrFun (hderiv_eq n) t
  refine ⟨?_, ?_⟩
  · have heq : iteratedDeriv n (gaussianKernel ε) =
        fun t => (K * c ^ n * (-1 : ℝ) ^ n) * (fun x => aeval x (hermite n) * ψ x) (c * t) := by
      funext t; rw [hpt]; ring
    rw [heq]
    exact (hg_integrable.comp_mul_left' hc_pos.ne').const_mul _
  · set g : ℝ → ℝ := fun x => |aeval x (hermite n)| * ψ x with hg_def
    have habs_eq : (fun t => |iteratedDeriv n (gaussianKernel ε) t|)
        = fun t => K * c ^ n * g (c * t) := by
      funext t
      rw [hpt, hg_def]
      have hψ_pos : 0 < ψ (c * t) := by rw [hψ_def]; positivity
      have h1 : |(-1 : ℝ) ^ n * aeval (c * t) (hermite n) * ψ (c * t)|
          = |aeval (c * t) (hermite n)| * ψ (c * t) := by
        rw [abs_mul, abs_mul, abs_of_pos hψ_pos]
        norm_num
      rw [abs_mul, abs_mul, h1, abs_of_pos hK_pos, abs_of_pos (pow_pos hc_pos n)]
      ring
    have hscale : (∫ t : ℝ, g (c * t)) = c⁻¹ * ∫ x : ℝ, g x := by
      have h := MeasureTheory.Measure.integral_comp_mul_left g c
      simpa [abs_of_pos (inv_pos.mpr hc_pos)] using h
    have hL1 : (∫ x : ℝ, g x) ≤ Real.sqrt (2 * Real.pi) * Real.sqrt n.factorial := by
      have heq2 : g = fun x : ℝ => |aeval x (hermite n)| * Real.exp (-(x ^ 2 / 2)) := by
        rw [hg_def, hψ_def]
      rw [heq2]
      exact hermite_gaussian_L1_bound n
    calc ∫ t : ℝ, |iteratedDeriv n (gaussianKernel ε) t|
        = ∫ t : ℝ, K * c ^ n * g (c * t) := by rw [habs_eq]
      _ = K * c ^ n * ∫ t : ℝ, g (c * t) := MeasureTheory.integral_const_mul _ _
      _ = K * c ^ n * (c⁻¹ * ∫ x : ℝ, g x) := by rw [hscale]
      _ = (K * c⁻¹) * (c ^ n * ∫ x : ℝ, g x) := by ring
      _ ≤ (K * c⁻¹) * (c ^ n * (Real.sqrt (2 * Real.pi) * Real.sqrt n.factorial)) := by
          have hKcinv_nonneg : (0 : ℝ) ≤ K * c⁻¹ := (mul_pos hK_pos (inv_pos.mpr hc_pos)).le
          have hcn_nonneg : (0 : ℝ) ≤ c ^ n := (pow_pos hc_pos n).le
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL1 hcn_nonneg) hKcinv_nonneg
      _ = c ^ n * Real.sqrt n.factorial := by
          have h1 : K * c⁻¹ * (c ^ n * (Real.sqrt (2 * Real.pi) * Real.sqrt n.factorial))
              = (K * c⁻¹ * Real.sqrt (2 * Real.pi)) * (c ^ n * Real.sqrt n.factorial) := by ring
          rw [h1, hKc, one_mul]
      _ ≤ (max c 1) ^ (n + 1) * Real.sqrt n.factorial := by
          have h1 : c ^ n ≤ (max c 1) ^ n :=
            pow_le_pow_left₀ hc_pos.le (le_max_left c 1) n
          have hge1 : (1 : ℝ) ≤ max c 1 := le_max_right c 1
          have h2 : (max c 1 : ℝ) ^ n ≤ (max c 1) ^ (n + 1) := by
            calc (max c 1 : ℝ) ^ n = (max c 1) ^ n * 1 := (mul_one _).symm
              _ ≤ (max c 1) ^ n * (max c 1) :=
                  mul_le_mul_of_nonneg_left hge1 (pow_nonneg (zero_le_one.trans hge1) n)
              _ = (max c 1) ^ (n + 1) := (pow_succ _ _).symm
          exact mul_le_mul_of_nonneg_right (h1.trans h2) (Real.sqrt_nonneg _)

end

end QuantumMechanics

end ProbabilisticTheory
