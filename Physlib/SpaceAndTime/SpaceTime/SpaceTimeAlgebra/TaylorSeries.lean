/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Derivatives
public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Basic
/-!

# Taylor series of smooth functions

## i. Overview

The Taylor series of a smooth complex-valued function `f` on spacetime at a point `x₀` is the
element of the spacetime algebra whose base-point derivative values are the iterated derivatives of
`f` at `x₀`. It depends `ℂ`-linearly on `f`, and it takes the derivative of `f` along a direction
to the formal partial derivative of the series along the same direction.

## ii. Key results

- `SpaceTimeAlgebra.taylorSeries` : the Taylor series of a smooth function at a point.
- `SpaceTimeAlgebra.constantCoeff_iteratedPDeriv_taylorSeries` : derivative values of `f` at `x₀`.
- `SpaceTimeAlgebra.taylorSeries_smoothDeriv` : derivatives become formal partial derivatives.

## iii. Table of contents

- A. The Taylor series of a smooth function
- B. Taylor series of derivatives

## iv. References

* None.
-/

@[expose] public section

namespace SpaceTimeAlgebra

open MvPowerSeries SpaceTime

/-!

## A. The Taylor series of a smooth function

The iterated derivatives `iteratedSmoothDeriv s f` of a smooth function are indexed by multisets of
directions, like the iterated formal partial derivatives of a series. The Taylor series of `f` at
`x₀` is the series `ofDerivValues` built from their values at `x₀`, so that its coefficient of
`x^s` is `(∂^s f)(x₀)` divided by `s!` and the base point of the spacetime algebra is identified
with `x₀`. Iterated derivatives distribute over sums and scalar multiples, so the Taylor series is
`ℂ`-linear.

-/

/-- The Taylor series at `x₀` of a smooth complex-valued function on spacetime. -/
noncomputable def taylorSeries (x₀ : SpaceTime) : smoothFunctions →ₗ[ℂ] SpaceTimeAlgebra where
  toFun f := ofDerivValues fun s => (iteratedSmoothDeriv s f : SpaceTime → ℂ) x₀
  map_add' f g := by
    simp only [← derivValuesEquiv_symm_apply, iteratedSmoothDeriv_add, Subalgebra.coe_add,
      Pi.add_apply, ← map_add]
    rfl
  map_smul' a f := by
    simp only [← derivValuesEquiv_symm_apply, iteratedSmoothDeriv_smul, Subalgebra.coe_smul,
      Pi.smul_apply, RingHom.id_apply, ← map_smul]
    rfl

lemma taylorSeries_apply (x₀ : SpaceTime) (f : smoothFunctions) :
    taylorSeries x₀ f = ofDerivValues fun s => (iteratedSmoothDeriv s f : SpaceTime → ℂ) x₀ :=
  rfl

lemma coeff_taylorSeries (x₀ : SpaceTime) (f : smoothFunctions) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff m (taylorSeries x₀ f) = ((∏ ν, (m ν).factorial : ℕ) : ℂ)⁻¹ *
      (iteratedSmoothDeriv (Finsupp.toMultiset m) f : SpaceTime → ℂ) x₀ :=
  rfl

/-- The base-point derivative values of `taylorSeries x₀ f` are the derivatives of `f` at `x₀`. -/
lemma constantCoeff_iteratedPDeriv_taylorSeries (x₀ : SpaceTime) (f : smoothFunctions)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    constantCoeff (iteratedPDeriv s (taylorSeries x₀ f)) =
      (iteratedSmoothDeriv s f : SpaceTime → ℂ) x₀ := by
  rw [taylorSeries_apply, constantCoeff_iteratedPDeriv_ofDerivValues]

/-!

## B. Taylor series of derivatives

Applying `∂^s` after `∂_μ` is the same as applying `∂^(μ ::ₘ s)`, both for smooth functions and
for series. Hence the Taylor series of `∂_μ f` and the formal partial derivative `pderiv μ` of the
Taylor series of `f` have the same base-point derivative values, namely `(∂^(μ ::ₘ s) f)(x₀)` at
each `s`. A series is determined by its base-point derivative values, so the two are equal.

-/

/-- The Taylor series of a derivative is the formal partial derivative of the Taylor series. -/
lemma taylorSeries_smoothDeriv (x₀ : SpaceTime) (μ : Fin 1 ⊕ Fin 3) (f : smoothFunctions) :
    taylorSeries x₀ (smoothDeriv μ f) = pderiv μ (taylorSeries x₀ f) :=
  ext_of_constantCoeff_iteratedPDeriv fun s => by
    rw [constantCoeff_iteratedPDeriv_taylorSeries, ← iteratedPDeriv_cons,
      constantCoeff_iteratedPDeriv_taylorSeries, iteratedSmoothDeriv_cons]

end SpaceTimeAlgebra
