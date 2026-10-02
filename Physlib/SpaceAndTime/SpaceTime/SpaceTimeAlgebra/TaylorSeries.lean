/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Derivatives
public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Basic
/-!

# Taylor series of functions on spacetime

## i. Overview

The Taylor series of a complex-valued function `f` on spacetime at a point `x₀` is the element of
the spacetime algebra whose base-point derivative values are the iterated derivatives of `f` at
`x₀`. For smooth `f` it is additive and `ℂ`-homogeneous in `f`, and it takes the derivative of `f`
along a direction to the formal partial derivative of the series along the same direction.

## ii. Key results

- `SpaceTimeAlgebra.taylorSeries` : the Taylor series of a function at a point.
- `SpaceTimeAlgebra.constantCoeff_iteratedPDeriv_taylorSeries` : derivative values of `f` at `x₀`.
- `SpaceTimeAlgebra.taylorSeries_deriv` : derivatives become formal partial derivatives.

## iii. Table of contents

- A. The Taylor series of a function
- B. Taylor series of derivatives

## iv. References

* None.
-/

@[expose] public section

namespace SpaceTimeAlgebra

open MvPowerSeries SpaceTime

open scoped ContDiff

/-!

## A. The Taylor series of a function

The iterated derivatives `iteratedDeriv s f` of a function are indexed by multisets of directions,
like the iterated formal partial derivatives of a series. The Taylor series of `f` at `x₀` is the
series `ofDerivValues` built from their values at `x₀`, so that its coefficient of `x^s` is
`(∂^s f)(x₀)` divided by `s!` and the base point of the spacetime algebra is identified with `x₀`.
For smooth functions, iterated derivatives distribute over sums and scalar multiples, and so does
the Taylor series.

-/

/-- The Taylor series at `x₀` of a complex-valued function on spacetime. -/
noncomputable def taylorSeries (x₀ : SpaceTime) (f : SpaceTime → ℂ) : SpaceTimeAlgebra :=
  ofDerivValues fun s => iteratedDeriv s f x₀

lemma coeff_taylorSeries (x₀ : SpaceTime) (f : SpaceTime → ℂ) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff m (taylorSeries x₀ f) =
      ((∏ ν, (m ν).factorial : ℕ) : ℂ)⁻¹ * iteratedDeriv (Finsupp.toMultiset m) f x₀ :=
  rfl

/-- The base-point derivative values of `taylorSeries x₀ f` are the derivatives of `f` at `x₀`. -/
lemma constantCoeff_iteratedPDeriv_taylorSeries (x₀ : SpaceTime) (f : SpaceTime → ℂ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    constantCoeff (iteratedPDeriv s (taylorSeries x₀ f)) = iteratedDeriv s f x₀ :=
  constantCoeff_iteratedPDeriv_ofDerivValues _ s

lemma taylorSeries_add (x₀ : SpaceTime) {f g : SpaceTime → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) :
    taylorSeries x₀ (f + g) = taylorSeries x₀ f + taylorSeries x₀ g := by
  simp only [taylorSeries, ← derivValuesEquiv_symm_apply, iteratedDeriv_add _ hf hg,
    Pi.add_apply, ← map_add]
  rfl

lemma taylorSeries_const_smul (x₀ : SpaceTime) (c : ℂ) {f : SpaceTime → ℂ}
    (hf : ContDiff ℝ ∞ f) :
    taylorSeries x₀ (c • f) = c • taylorSeries x₀ f := by
  simp only [taylorSeries, ← derivValuesEquiv_symm_apply, iteratedDeriv_const_smul _ c hf,
    Pi.smul_apply, ← map_smul]
  rfl

/-!

## B. Taylor series of derivatives

Applying `∂^s` after `∂_μ` is the same as applying `∂^(μ ::ₘ s)`, both for smooth functions and
for series. Hence the Taylor series of `∂_μ f` and the formal partial derivative `pderiv μ` of the
Taylor series of `f` have the same base-point derivative values, namely `(∂^(μ ::ₘ s) f)(x₀)` at
each `s`. A series is determined by its base-point derivative values, so the two are equal.

-/

/-- The Taylor series of a derivative is the formal partial derivative of the Taylor series. -/
lemma taylorSeries_deriv (x₀ : SpaceTime) (μ : Fin 1 ⊕ Fin 3) {f : SpaceTime → ℂ}
    (hf : ContDiff ℝ ∞ f) :
    taylorSeries x₀ (∂_ μ f) = pderiv μ (taylorSeries x₀ f) :=
  ext_of_constantCoeff_iteratedPDeriv fun s => by
    rw [constantCoeff_iteratedPDeriv_taylorSeries, ← iteratedPDeriv_cons,
      constantCoeff_iteratedPDeriv_taylorSeries, iteratedDeriv_cons μ s hf]

end SpaceTimeAlgebra
