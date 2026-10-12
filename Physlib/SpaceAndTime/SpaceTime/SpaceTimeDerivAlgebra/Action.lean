/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeDerivAlgebra.Basic
/-!

# The action of spacetime series on derivative symbols

Series act on derivative symbols by transposing multiplication with respect to the pairing.

## i. Overview

When a field is multiplied by a spacetime-dependent function `χ`, as in a local gauge
transformation, its derivatives change by the product rule `∂_μ (χ φ) = χ ∂_μ φ + (∂_μ χ) φ`.
By the product rule, applying a symbol `P` to a product of series `χ f` and taking the value at
the base point gives a combination of finitely many derivatives of `f` there, which we collect
into a new symbol `seriesAction χ P`. This is the identity
`pairing (seriesAction χ P) f = pairing P (χ * f)`, so `seriesAction χ` is the transpose of
multiplication by `χ` with respect to the pairing. The action respects sums and products of
series, so it is a ring homomorphism from the spacetime algebra to the linear endomorphisms of the
derivative algebra.

Throughout we use the notation of `SpaceTimeDerivAlgebraℂ`, and write `χ(0)` for the base-point
value of a series `χ`.

## ii. Key results

- `SpaceTimeDerivAlgebraℂ.seriesAction` : the action of a series on derivative symbols.
- `SpaceTimeDerivAlgebraℂ.pairing_seriesAction` : the action is the transpose of multiplication.
- `SpaceTimeDerivAlgebraℂ.seriesAction_mul` : the action of a product is the composite.
- `SpaceTimeDerivAlgebraℂ.seriesActionHom` : the action as a ring homomorphism.
- `SpaceTimeDerivAlgebraℂ.seriesAction_basis_singleton` : the product rule for first-order
  symbols.
- `SpaceTimeDerivAlgebraℂ.seriesAction_mul_basis_singleton` : acting on `p ∂_μ` gives the action
  on `p` followed by `∂_μ`, plus the action of `pderiv μ χ` on `p`.

## iii. Table of contents

- A. The action of a series
  - A.1. The action on monomials
  - A.2. The transpose of multiplication
- B. The action as a ring homomorphism
- C. Low-order symbols and derivatives
  - C.1. The unit and first-order symbols
  - C.2. Multiplication by a derivative symbol

## iv. References

* None.
-/

@[expose] public section

namespace SpaceTimeDerivAlgebraℂ

open MvPowerSeries SpaceTimeAlgebra

/-!

## A. The action of a series

### A.1. The action on monomials

The action of `χ` on a monomial `∂^s` comes from the Leibniz rule
`constantCoeff_iteratedPDeriv_mul`, which expands `(∂^s (χ f))(0)` as the sum of
`(∂^t₁ χ)(0) (∂^t₂ f)(0)` over the splittings `s = t₁ + t₂`, counted with multiplicity. Replacing
each `(∂^t₂ f)(0)` by the symbol `∂^t₂` gives a finite sum, so the image is again a derivative
symbol.

-/

/-- The action of a series `χ` on derivative symbols, sending `∂^s` to the sum of
  `(∂^t₁ χ)(0) • ∂^t₂` over the splittings `s = t₁ + t₂`, counted with multiplicity. -/
noncomputable def seriesAction (χ : SpaceTimeAlgebra) : Module.End ℂ SpaceTimeDerivAlgebraℂ :=
  basis.constr ℂ fun s =>
    (s.antidiagonal.map fun t => constantCoeff (iteratedPDeriv t.1 χ) • ∂^[t.2]).sum

/-- The action of `χ` on a monomial is its Leibniz expansion over the splittings of `s`. -/
lemma seriesAction_basis (χ : SpaceTimeAlgebra) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    seriesAction χ ∂^[s] =
      (s.antidiagonal.map fun t => constantCoeff (iteratedPDeriv t.1 χ) • ∂^[t.2]).sum :=
  basis.constr_basis ℂ _ s

/-!

### A.2. The transpose of multiplication

Pairing the image of `∂^s` with a series `f` therefore gives back `(∂^s (χ f))(0)`.

-/

/-- The action of `χ` is the transpose of multiplication by `χ` with respect to the pairing. -/
lemma pairing_seriesAction (χ : SpaceTimeAlgebra) (p : SpaceTimeDerivAlgebraℂ)
    (f : SpaceTimeAlgebra) :
    pairing (seriesAction χ p) f = pairing p (χ * f) := by
  have h : pairing.flip f ∘ₗ seriesAction χ = pairing.flip (χ * f) := basis.ext fun s => by
    simp only [LinearMap.comp_apply, seriesAction_basis, map_multiset_sum, Multiset.map_map,
      LinearMap.flip_apply, pairing_basis, constantCoeff_iteratedPDeriv_mul]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun t _ => ?_)
    simp only [Function.comp_apply, map_smul, LinearMap.flip_apply, pairing_basis, smul_eq_mul]
  exact LinearMap.congr_fun h p

/-!

## B. The action as a ring homomorphism

The constant series `C c` acts as multiplication by `c`. Transposition reverses the order of
composition, but series commute, so the action of `χ * ψ` is `seriesAction χ ∘ₗ seriesAction ψ`.

-/

/-- The zero series acts as zero. -/
@[simp]
lemma seriesAction_zero : seriesAction 0 = 0 :=
  LinearMap.ext fun p => ext_of_pairing_eq fun f => by simp [pairing_seriesAction]

/-- The action of a sum of series is the sum of their actions. -/
lemma seriesAction_add (χ ψ : SpaceTimeAlgebra) :
    seriesAction (χ + ψ) = seriesAction χ + seriesAction ψ :=
  LinearMap.ext fun p => ext_of_pairing_eq fun f => by simp [pairing_seriesAction, add_mul]

/-- The constant series `C c` acts as scalar multiplication by `c`. -/
@[simp]
lemma seriesAction_C (c : ℂ) : seriesAction (C c) = c • LinearMap.id :=
  LinearMap.ext fun p => ext_of_pairing_eq fun f => by
    simp [pairing_seriesAction, ← smul_eq_C_mul]

/-- The unit series acts as the identity. -/
@[simp]
lemma seriesAction_one : seriesAction 1 = LinearMap.id :=
  LinearMap.ext fun p => ext_of_pairing_eq fun f => by simp [pairing_seriesAction]

/-- The action of a product of series is the composite of their actions. -/
lemma seriesAction_mul (χ ψ : SpaceTimeAlgebra) :
    seriesAction (χ * ψ) = seriesAction χ ∘ₗ seriesAction ψ :=
  LinearMap.ext fun p => ext_of_pairing_eq fun f => by
    rw [LinearMap.comp_apply, pairing_seriesAction, pairing_seriesAction, pairing_seriesAction,
      mul_comm χ ψ, mul_assoc]

/-- The action of series on derivative symbols, as a ring homomorphism to the complex-linear
  endomorphisms of the derivative algebra. -/
noncomputable def seriesActionHom : SpaceTimeAlgebra →+* Module.End ℂ SpaceTimeDerivAlgebraℂ where
  toFun := seriesAction
  map_one' := seriesAction_one
  map_mul' := seriesAction_mul
  map_zero' := seriesAction_zero
  map_add' := seriesAction_add

/-!

## C. Low-order symbols and derivatives

### C.1. The unit and first-order symbols

A series acts on the unit symbol by `χ(0)`, and sends `∂_μ` to `χ(0) ∂_μ + (∂_μ χ)(0)`, which is
the product rule at the base point.

-/

/-- A series acts on the unit symbol by its base-point value. -/
@[simp]
lemma seriesAction_apply_one (χ : SpaceTimeAlgebra) :
    seriesAction χ 1 = constantCoeff χ • 1 := by
  rw [← basis_zero, seriesAction_basis, Multiset.antidiagonal_zero]
  simp

/-- A series `χ` sends `∂_μ` to `χ(0) ∂_μ + (∂_μ χ)(0)`, the product rule. -/
lemma seriesAction_basis_singleton (χ : SpaceTimeAlgebra) (μ : Fin 1 ⊕ Fin 3) :
    seriesAction χ ∂[μ] = constantCoeff χ • ∂[μ] + constantCoeff (pderiv μ χ) • 1 := by
  rw [seriesAction_basis, ← Multiset.cons_zero, Multiset.antidiagonal_cons,
    Multiset.antidiagonal_zero]
  simp

/-!

### C.2. Multiplication by a derivative symbol

Appending `∂_μ` to a symbol amounts to differentiating the series it pairs with, by
`pairing_mul_basis_singleton`, so the product rule for `∂_μ (χ f)` relates the action of `χ` to
multiplication by `∂_μ`.

-/

/-- Multiplying by `∂_μ` before the action of `χ` equals the action of `χ` followed by
  multiplication by `∂_μ`, plus the action of `pderiv μ χ`. -/
lemma seriesAction_mul_basis_singleton (χ : SpaceTimeAlgebra) (p : SpaceTimeDerivAlgebraℂ)
    (μ : Fin 1 ⊕ Fin 3) :
    seriesAction χ (p * ∂[μ]) = seriesAction χ p * ∂[μ] + seriesAction (pderiv μ χ) p :=
  ext_of_pairing_eq fun f => by
    rw [map_add, LinearMap.add_apply, pairing_seriesAction, pairing_mul_basis_singleton,
      pairing_mul_basis_singleton, pairing_seriesAction, pairing_seriesAction, Derivation.leibniz,
      smul_eq_mul, smul_eq_mul, map_add, mul_comm f]

end SpaceTimeDerivAlgebraℂ
