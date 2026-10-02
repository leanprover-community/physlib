/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Algebra.Statistics
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Jordan

/-!

# Expectation, variance and covariance

## i. Overview

A state assigns expectation values `ω⟨a⟩` to observables. Subtracting the expectation gives the
centered observable, and from it the covariance and the variance of observables in a state. None of
this needs a norm, and positivity of the variance uses only that `star x * x ≥ 0`.

## ii. Key results

- `UnitalPositiveLinearMap.expectation` : the expectation value `ω⟨a⟩`.
- `UnitalPositiveLinearMap.centered` : an observable minus its expectation.
- `UnitalPositiveLinearMap.covariance`, `UnitalPositiveLinearMap.variance` : covariance and
  variance.
- `UnitalPositiveLinearMap.variance_nonneg` : the variance is nonnegative.

## iii. Table of contents

- A. Expectation
- B. Centering
- C. Reversing a product
- D. Covariance and variance

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ComplexOrder
open scoped selfAdjoint

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A]
    [SelfAdjointDecompose A] [Module ℂ A] [StarModule ℂ A]
    [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]

namespace UnitalPositiveLinearMap

/-! ## A. Expectation -/

/-- The expectation `ω⟨a⟩` of observables in the state `ω`: the average of repeated measurements of
`a` on systems prepared in `ω`. -/
noncomputable def expectation (ω : 𝓢[ℂ, A]) : 𝓢[ℝ, Observable A] :=
  ω.onObservables

@[inherit_doc expectation]
scoped notation:max ω "⟨" a "⟩" => UnitalPositiveLinearMap.expectation ω a

attribute [nolint docBlame] UnitalPositiveLinearMap.«term_⟨_⟩»

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
/-- The complex-valued state functional agrees with the real expectation notation `ω⟨a⟩` on
observables: no information is lost, since self-adjoint elements have vanishing imaginary part. -/
lemma apply_observable_eq_expectation (ω : 𝓢[ℂ, A]) (a : Observable A) :
    ω (a : A) = (ω⟨a⟩ : ℂ) :=
  (coe_onObservables_apply ω a).symm

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
/-- The trivial "do-nothing" observable `1` is measured with certainty: probabilities sum to one. -/
@[simp]
lemma expectation_one (ω : 𝓢[ℂ, A]) :
    ω⟨(1 : Observable A)⟩ = 1 := by
  simp [expectation]

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
/-- Positive observables have nonnegative expectation. -/
lemma expectation_nonneg (ω : 𝓢[ℂ, A]) {a : Observable A} (ha : 0 ≤ (a : A)) :
    0 ≤ ω⟨a⟩ :=
  (expectation ω).map_nonneg ha

/-! ## B. Centering -/

/-- The fluctuation of an observable around its mean: `a` with `ω⟨a⟩` subtracted off. Its
statistics (`covariance`, `variance`) describe the spread of `a`'s outcomes. -/
noncomputable def centered (ω : 𝓢[ℂ, A]) (a : Observable A) : Observable A :=
  LinearMap.centered (expectation ω).toLinearMap a

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
/-- A fluctuation has zero mean by construction: the average deviation from the average is zero. -/
@[simp]
lemma expectation_centered (ω : 𝓢[ℂ, A]) (a : Observable A) :
    ω⟨centered ω a⟩ = 0 := by
  exact LinearMap.apply_centered (expectation ω).toLinearMap (expectation_one ω) a

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
/-- Shifting an observable by a deterministic constant `c` shifts its mean by `c` too, so the
fluctuation around the new mean is unchanged. -/
@[simp]
lemma centered_add_smul_one (ω : 𝓢[ℂ, A]) (a : Observable A) (c : ℝ) :
    centered ω (a + c • 1) = centered ω a := by
  simp only [centered, LinearMap.centered, map_add, map_smul]
  rw [show (expectation ω).toLinearMap 1 = 1 from expectation_one ω]
  module

/-! ## C. Reversing a product -/

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
/-- Reversing a product of two observables conjugates its value in a state. -/
lemma apply_mul_comm_eq_star (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    ω ((b : A) * a) = star (ω ((a : A) * b)) := by
  rw [← map_star, star_mul, a.property.star_eq, b.property.star_eq]

/-! ## D. Covariance and variance -/

/-- The covariance of two observables in the state `ω`, the real part of the expectation of the
product of their fluctuations. -/
noncomputable def covariance (ω : 𝓢[ℂ, A]) (a b : Observable A) : ℝ :=
  LinearMap.covarianceForm (expectation ω).toLinearMap a b

/-- The spread of `a`'s measurement outcomes about its mean — the quantum analogue of a random
variable's variance, whose square root is the uncertainty `Δa` in `CStarAlgebra.Uncertainty`. -/
noncomputable def variance (ω : 𝓢[ℂ, A]) (a : Observable A) : ℝ :=
  covariance ω a a

/-- Unfolds `variance` as covariance of an observable with itself. -/
@[simp]
lemma covariance_self (ω : 𝓢[ℂ, A]) (a : Observable A) :
    covariance ω a a = variance ω a :=
  rfl

/-- The canonical covariance form on the Jordan algebra of observables is the real part of the
state applied to the ordinary associative product of the centered observables. This is a
specialization theorem, not a second definition of covariance. -/
lemma covariance_eq_re_apply_centered_mul (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    covariance ω a b = (ω ((centered ω a : A) * centered ω b)).re := by
  rw [covariance]
  rw [← LinearMap.apply_centered_mul_centered (expectation ω).toLinearMap (expectation_one ω)
    selfAdjoint.one_jordanMul selfAdjoint.jordanMul_one]
  set x := centered ω a
  set y := centered ω b
  have hstar : ω ((y : A) * x) = star (ω ((x : A) * y)) :=
    apply_mul_comm_eq_star ω x y
  have hval := apply_observable_eq_expectation ω (x * y)
  rw [selfAdjoint.coe_mul, LinearMapClass.map_smul_of_tower, map_add, hstar,
    Complex.real_smul] at hval
  have hsum : ω ((x : A) * y) + star (ω ((x : A) * y)) =
      (2 : ℂ) * (ω ((x : A) * y)).re := by
    rw [Complex.star_def, Complex.add_conj]
    push_cast
    ring
  rw [hsum] at hval
  have hval' : ((expectation ω (x * y) : ℝ) : ℂ) = ((ω ((x : A) * y)).re : ℝ) := by
    calc
      ((expectation ω (x * y) : ℝ) : ℂ) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) *
          (2 * ((ω ((x : A) * y)).re : ℂ)) := hval.symm
      _ = ((ω ((x : A) * y)).re : ℂ) := by
        apply Complex.ext <;> (norm_num <;> ring)
  exact_mod_cast hval'

/-- The variance is the expectation of the squared fluctuation. -/
lemma variance_eq_re_apply_centered_mul_self (ω : 𝓢[ℂ, A]) (a : Observable A) :
    variance ω a = (ω ((centered ω a : A) * centered ω a)).re := by
  rw [variance, covariance_eq_re_apply_centered_mul]

/-- Covariance is symmetric: reversing a product of self-adjoint fluctuations conjugates the
state's value on it, and conjugation does not change the real part. -/
lemma covariance_comm (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    covariance ω a b = covariance ω b a := by
  exact (LinearMap.covarianceForm_isSymm (expectation ω).toLinearMap
    fun x y => mul_comm x y).eq a b

/-- Covariance depends only on fluctuations: shifting the left observable by a constant `c`
leaves it unchanged. -/
lemma covariance_add_smul_one_left (ω : 𝓢[ℂ, A]) (a b : Observable A) (c : ℝ) :
    covariance ω (a + c • 1) b = covariance ω a b := by
  change LinearMap.covarianceForm (expectation ω).toLinearMap (a + c • 1) b =
    LinearMap.covarianceForm (expectation ω).toLinearMap a b
  rw [map_add, map_smul]
  have hone : LinearMap.covarianceForm (expectation ω).toLinearMap (1 : Observable A) b = 0 := by
    rw [LinearMap.covarianceForm_apply]
    change expectation ω (selfAdjoint.jordanMul 1 b) - expectation ω 1 * expectation ω b = 0
    rw [selfAdjoint.one_jordanMul, expectation_one]
    ring
  simp only [LinearMap.add_apply, LinearMap.smul_apply, hone, smul_zero, add_zero]

/-- Covariance depends only on fluctuations: shifting the right observable by a constant `c`
leaves it unchanged. -/
lemma covariance_add_smul_one_right (ω : 𝓢[ℂ, A]) (a b : Observable A) (c : ℝ) :
    covariance ω a (b + c • 1) = covariance ω a b := by
  change LinearMap.covarianceForm (expectation ω).toLinearMap a (b + c • 1) =
    LinearMap.covarianceForm (expectation ω).toLinearMap a b
  rw [map_add, map_smul]
  have hone : LinearMap.covarianceForm (expectation ω).toLinearMap a (1 : Observable A) = 0 := by
    rw [LinearMap.covarianceForm_apply]
    change expectation ω (selfAdjoint.jordanMul a 1) - expectation ω a * expectation ω 1 = 0
    rw [selfAdjoint.jordanMul_one, expectation_one]
    ring
  rw [hone, smul_zero, add_zero]

variable [StarOrderedRing A] in
/-- **The variance is nonnegative.** -/
lemma variance_nonneg (ω : 𝓢[ℂ, A]) (a : Observable A) :
    0 ≤ variance ω a := by
  rw [variance_eq_re_apply_centered_mul_self]
  have h : (0 : A) ≤ (centered ω a : A) * centered ω a := by
    have hpos := star_mul_self_nonneg (centered ω a : A)
    rwa [(centered ω a).property.star_eq] at hpos
  exact (RCLike.nonneg_iff.mp (ω.map_nonneg h)).1

end UnitalPositiveLinearMap

end ProbabilisticTheory
