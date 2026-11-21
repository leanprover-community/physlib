/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Physlib.QuantumMechanics.HarmonicOscillator.Eigenstates
/-!

# Completeness of the eigenstates of the quantum harmonic oscillator

The ground state and the span of the eigenfunctions of the `d`-dimensional quantum harmonic
oscillator, towards the completeness of the eigenstates.

## i. Overview

The ground state `ψ₀` has no zero, and `ψ₀ conj(ψ)` is integrable for every `ψ` in the Hilbert
space. The position operators are sums of ladder operators, so the span of the eigenfunctions is
stable under them, and `x ↦ ⟪x, w⟫ ^ r ψ₀(x)` lies in this span for every `w` and `r`. If `ψ` is
orthogonal to every eigenstate `ψₙ`, then `∫ conj(ψ) f = 0` for every `f` in this span.

## ii. Key results

- `exists_mem_span_eigenfunction_inner_pow_mul`: `x ↦ ⟪x, w⟫ ^ r ψ₀(x)` lies in the span of the
  eigenfunctions.
- `integral_conj_mul_eq_zero_of_mem_span`: if `ψ` is orthogonal to every eigenstate, then
  `∫ conj(ψ) f = 0` for every `f` in the span of the eigenfunctions.

## iii. Table of contents

- A. Completeness of the eigenstates
  - A.1. The ground state
  - A.2. Polynomials times the ground state

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace QuantumMechanics.HarmonicOscillator

open MeasureTheory SchwartzMap SpaceDHilbertSpace InnerProductSpace
open scoped InnerProductSpace FourierTransform ComplexConjugate Nat Real

variable {d : ℕ} (Q : HarmonicOscillator d)

/-!
## A. Completeness of the eigenstates
-/

/-!
### A.1. The ground state
-/

/-- The ground-state eigenfunction is a multiple of the Gaussian `gaussian ℂ Q.ξEquiv 0`. -/
lemma eigenfunction_zero_apply (x : Space d) :
    Q.eigenfunction 0 x = (∏ i, (Q.eigenCoeff 0 i : ℂ)) * gaussian ℂ Q.ξEquiv 0 x := by
  rw [eigenfunction_eq, compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    smulLeftCLM_apply_apply (by fun_prop)]
  simp

/-- The ground-state eigenfunction has no zero. -/
lemma eigenfunction_zero_apply_ne_zero (x : Space d) : Q.eigenfunction 0 x ≠ 0 := by
  rw [eigenfunction_apply]
  refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_
  have hp : 0 < (2 : ℝ) ^ ((0 : Fin d → ℕ) i) * (((0 : Fin d → ℕ) i).factorial : ℝ) *
      √Real.pi * Q.ξ i :=
    mul_pos (mul_pos (mul_pos (by positivity) (by positivity)) (by positivity)) (Q.ξ_pos i)
  have hc : Q.eigenCoeff 0 i ≠ 0 := by
    rw [eigenCoeff_eq]
    exact one_div_ne_zero (Real.sqrt_pos.mpr hp).ne'
  simp [hc, Complex.exp_ne_zero]

/-- The function `ψ₀ conj(ψ)` is integrable, as a product of two square-integrable functions. -/
lemma integrable_eigenfunction_zero_mul_conj (ψ : Q.HS) :
    Integrable (fun x ↦ Q.eigenfunction 0 x * conj (ψ x)) :=
  ((Q.eigenfunction 0).memLp 2 volume).integrable_mul (Lp.memLp ψ).star

/-!
### A.2. Polynomials times the ground state
-/

/-- The span of the eigenfunctions is stable under the position operators, which are sums of the
  ladder operators. -/
lemma positionCLM_mem_span_eigenfunction (j : Fin d) {f : 𝓢(Space d, ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range Q.eigenfunction)) :
    𝐱 j f ∈ Submodule.span ℂ (Set.range Q.eigenfunction) := by
  have hle : Submodule.span ℂ (Set.range Q.eigenfunction) ≤
      (Submodule.span ℂ (Set.range Q.eigenfunction)).comap
        (𝐱 j : 𝓢(Space d, ℂ) →ₗ[ℂ] 𝓢(Space d, ℂ)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe,
      Q.position_eq_lowering_add_raising j, _root_.smul_apply, _root_.add_apply,
      lowering_eigenfunction, raising_eigenfunction]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))
  exact hle hf

/-- For `w : Space d` and `r : ℕ`, the function `x ↦ ⟪x, w⟫ ^ r ψ₀(x)` lies in the span of the
  eigenfunctions. -/
lemma exists_mem_span_eigenfunction_inner_pow_mul (w : Space d) (r : ℕ) :
    ∃ f ∈ Submodule.span ℂ (Set.range Q.eigenfunction),
      ∀ x, f x = ((⟪x, w⟫_ℝ : ℝ) : ℂ) ^ r * Q.eigenfunction 0 x := by
  induction r with
  | zero => exact ⟨Q.eigenfunction 0, Submodule.subset_span ⟨0, rfl⟩, fun x ↦ by simp⟩
  | succ r ih =>
    obtain ⟨f, hf, hfx⟩ := ih
    refine ⟨∑ j, ((w j : ℝ) : ℂ) • 𝐱 j f, Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Q.positionCLM_mem_span_eigenfunction j hf), fun x ↦ ?_⟩
    have key (t : ℂ) : ∑ j, ((w j : ℝ) : ℂ) * (((x j : ℝ) : ℂ) * t) =
        ((⟪x, w⟫_ℝ : ℝ) : ℂ) * t := by
      rw [Space.inner_eq_sum, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      push_cast
      ring
    simp only [FunLike.coe_sum, Finset.sum_apply, _root_.smul_apply, positionCLM_apply, hfx,
      smul_eq_mul]
    rw [key, pow_succ', mul_assoc]

/-- If `ψ` is orthogonal to every eigenstate, then `∫ conj(ψ) f = 0` for every `f` in the span of
  the eigenfunctions. -/
lemma integral_conj_mul_eq_zero_of_mem_span {ψ : Q.HS}
    (h : ∀ n : Fin d → ℕ, ⟪(Q.eigenstate n : Q.HS), ψ⟫_ℂ = 0) {f : 𝓢(Space d, ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range Q.eigenfunction)) :
    ∫ x, conj (ψ x) * f x = 0 := by
  have hint : ⟪ψ, (schwartzEquiv volume f : Q.HS)⟫_ℂ = ∫ x, conj (ψ x) * f x := by
    refine integral_congr_ae ?_
    filter_upwards [SchwartzSubmodule.schwartzEquiv_coe_ae (μ := volume) f] with x hx
    simp [hx, mul_comm]
  rw [← hint]
  let Λ : 𝓢(Space d, ℂ) →ₗ[ℂ] ℂ :=
    innerₛₗ ℂ ψ ∘ₗ (SchwartzSubmodule d).subtype ∘ₗ (schwartzEquiv volume).toLinearMap
  have hker : Submodule.span ℂ (Set.range Q.eigenfunction) ≤ LinearMap.ker Λ :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun n ↦ inner_eq_zero_symm.mp (h n))
  exact hker hf

end QuantumMechanics.HarmonicOscillator

end
