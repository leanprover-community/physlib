/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Covariance
public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.CStarAlgebra.Basic
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.SpectralMeasure

/-!

# Spectral formulas for Jordan moments

Jordan moments and the variance of an observable as integrals against its spectral measure.

## i. Overview

The statistics of an observable `a` in a state `ω` of a C⋆-algebra are given by its spectral
measure `μ_{ω,a}`: `ω(f(a)) = ∫ f dμ_{ω,a}`. The Jordan moments of `a` are defined through Jordan
powers `a^{[n]}`. For a single observable these agree with the ordinary powers `aⁿ` of the
C⋆-algebra, so every moment, and in particular the variance, is an integral against the spectral
measure.

## ii. Key results

- `JB.jpow_eq_pow` : Jordan powers of a single observable are ordinary powers.
- `JB.moment_eq_integral` : `moment n (ω.onObservables) a = ∫ y, y^n ∂(realSpectralMeasure ω a)`
- `JB.variance_eq_integral_sq_sub` : the variance as `∫y² dμ - (∫y dμ)²`
- `JB.apply_eq_integral` : the expectation `ω a` as `∫ y dμ`.

## iii. Table of contents

- A. Jordan powers of a single element are ordinary powers
- B. Moments as integrals against the outcome distribution

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ComplexOrder

namespace JB

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped selfAdjoint

/-! ## A. Jordan powers of a single element are ordinary powers -/

omit [PartialOrder A] [StarOrderedRing A] in
/-- Jordan powers of a self-adjoint element are its ordinary powers. -/
lemma jpow_eq_pow (a : selfAdjoint A) (n : ℕ) :
    ((JordanAlgebra.jpow a n : selfAdjoint A) : A) = (a : A) ^ n := by
  induction n with
  | zero => simp [JordanAlgebra.jpow_zero]
  | succ n ih =>
      rw [JordanAlgebra.jpow_succ, selfAdjoint.mul_def, selfAdjoint.val_jordanMul, ih]
      have hcomm : (a:A) * (a:A) ^ n = (a:A) ^ n * (a:A) := (Commute.refl (a:A)).pow_right n
      rw [← hcomm, ← two_smul ℝ ((a:A) * (a:A)^n), smul_smul,
        inv_mul_cancel₀ (two_ne_zero (α := ℝ)), one_smul, pow_succ']

/-! ## B. Moments as integrals against the outcome distribution -/

open MeasureTheory

/-- The `n`-th moment of `a` in the
state `ω` (restricted from a state on the whole C⋆-algebra) is `∫ y^n dμ_{ω,a}` — exactly
`m_n(a) = ∫λⁿ dμ_{ω,a}`. -/
lemma moment_eq_integral (ω : 𝓢[ℂ, A]) (a : selfAdjoint A) (n : ℕ) :
    IsJordanOrderUnit.moment n ω.onObservables a =
      ∫ y, y ^ n ∂(realSpectralMeasure ω a) := by
  have hcfc : cfc (fun x : ℝ => x ^ n) (a : A) = (a : A) ^ n := by
    rw [cfc_pow (fun x : ℝ => x) n (a : A) continuousOn_id, cfc_id' (R := ℝ) (a := (a : A))]
  have hval : ((JordanAlgebra.jpow a n : selfAdjoint A) : A) =
      cfc (fun x : ℝ => x ^ n) (a : A) := by rw [jpow_eq_pow, hcfc]
  unfold IsJordanOrderUnit.moment
  rw [show (JordanAlgebra.jpow a n : Observable A) =
      ⟨cfc (fun x : ℝ => x ^ n) (a : A), cfc_predicate (R := ℝ) _ (a : A)⟩ from Subtype.ext hval]
  exact realSpectralMeasure_integral ω a _ (continuousOn_pow n)

/-- **The mean is the first moment, as an integral.** Specializing `moment_eq_integral` to `n = 1`
gives `ω(a) = ∫ y \, d\mu_{\omega,a}`, since `IsJordanOrderUnit.moment_one` identifies the first
moment with `ω(a)` itself. -/
lemma apply_eq_integral (ω : 𝓢[ℂ, A]) (a : selfAdjoint A) :
    ω.onObservables a = ∫ y, y ∂(realSpectralMeasure ω a) := by
  have h := moment_eq_integral ω a 1
  simp only [IsJordanOrderUnit.moment_one, pow_one] at h
  exact h

/-- **The variance is `∫ y² dμ - (∫ y dμ)²`** for the distribution `μ` of the observable. -/
lemma variance_eq_integral_sq_sub (ω : 𝓢[ℂ, A]) (a : selfAdjoint A) :
    IsJordanOrderUnit.variance ω.onObservables a =
      (∫ y, y ^ 2 ∂(realSpectralMeasure ω a)) - (∫ y, y ∂(realSpectralMeasure ω a)) ^ 2 := by
  calc
    IsJordanOrderUnit.variance ω.onObservables a =
        IsJordanOrderUnit.moment 2 ω.onObservables a - (ω.onObservables a) ^ 2 := by
      simp [IsJordanOrderUnit.variance, LinearMap.variance, IsJordanOrderUnit.moment,
        JordanAlgebra.jpow_two, pow_two]
    _ = _ := by rw [moment_eq_integral, apply_eq_integral]

end JB

end ProbabilisticTheory
