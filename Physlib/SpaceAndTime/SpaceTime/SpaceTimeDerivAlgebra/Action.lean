/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeDerivAlgebra.Basic
/-!

# The action of spacetime series on derivative symbols

The action of formal power series in spacetime coordinates on polynomials in derivatives.

## i. Overview

Multiplying a field component `φ` by a spacetime-dependent function `χ`, such as a matrix element
of a local gauge transformation, changes its derivatives by the product rule. At a point `x₀`,
`∂_μ (χ φ)(x₀) = χ(x₀) ∂_μ φ(x₀) + (∂_μ χ)(x₀) φ(x₀)`, so a first derivative of `χ φ` is a
combination of derivatives of `φ`, and the same holds for any derivative symbol `P`. The symbol
`seriesAction χ P` records this combination, applying `P` after multiplying by `χ`. We define the
action on monomials by the product rule, and it respects sums and products of series, so
`seriesAction` is a ring homomorphism from the spacetime algebra to the linear endomorphisms of
the derivative algebra.

In the statements `χ` is a series, the Taylor series of the function at `x₀`, and we use the
notation of `SpaceTimeDerivAlgebraℂ` throughout.

## ii. Key results

- `SpaceTimeDerivAlgebraℂ.seriesAction` : the action of series on derivative symbols.
- `SpaceTimeDerivAlgebraℂ.pairing_seriesAction` : the action applies `P` after multiplying by `χ`.
- `SpaceTimeDerivAlgebraℂ.seriesAction_basis_singleton` : the product rule for first-order
  symbols.
- `SpaceTimeDerivAlgebraℂ.seriesAction_mul_basis_singleton` : the action commutes with
  multiplication by `∂_μ` up to the action of `pderiv μ χ`.

## iii. Table of contents

- A. The action of a series
  - A.1. The action on monomials
  - A.2. Multiplication before differentiation
- B. Low-order symbols and derivatives
  - B.1. The unit and first-order symbols
  - B.2. Multiplication by a derivative symbol

## iv. References

* None.
-/

@[expose] public section

namespace SpaceTimeDerivAlgebraℂ

open MvPowerSeries SpaceTimeAlgebra

/-!

## A. The action of a series

### A.1. The action on monomials

The action of `χ` sends each monomial `∂^s` to its Leibniz expansion with `χ`, a finite sum of
symbols, which pairs with `f` as `∂^s` pairs with `χ f` by `pairing_constr_leibniz`.

-/

/-- The action of series on derivative symbols, defined on monomials by the product rule. -/
noncomputable def seriesAction : SpaceTimeAlgebra →+* Module.End ℂ SpaceTimeDerivAlgebraℂ where
  toFun χ := basis.constr ℂ fun s =>
    (s.antidiagonal.map fun t => constantCoeff (iteratedPDeriv t.1 χ) • ∂^[t.2]).sum
  map_one' := LinearMap.ext fun p => ext_of_pairing_eq fun f => by simp [pairing_constr_leibniz]
  map_mul' χ ψ := LinearMap.ext fun p => ext_of_pairing_eq fun f => by
    simp only [Module.End.mul_apply, pairing_constr_leibniz, mul_comm χ ψ, mul_assoc]
  map_zero' := LinearMap.ext fun p => ext_of_pairing_eq fun f => by simp [pairing_constr_leibniz]
  map_add' χ ψ := LinearMap.ext fun p => ext_of_pairing_eq fun f => by
    simp [pairing_constr_leibniz, add_mul]

/-- The action of `χ` on a monomial `∂^s` is its Leibniz expansion. -/
lemma seriesAction_basis (χ : SpaceTimeAlgebra) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    seriesAction χ ∂^[s] =
      (s.antidiagonal.map fun t => constantCoeff (iteratedPDeriv t.1 χ) • ∂^[t.2]).sum :=
  basis.constr_basis ℂ _ s

/-!

### A.2. Multiplication before differentiation

Pairing a symbol with a series applies it and takes the value at `x₀`, so
`pairing (seriesAction χ P) f = pairing P (χ * f)` says that `seriesAction χ P` applies `P` after
multiplying by `χ`. In particular the constant series `C c` acts as multiplication by `c`.

-/

/-- The action of `χ` multiplies by `χ` before applying the symbol. -/
lemma pairing_seriesAction (χ : SpaceTimeAlgebra) (p : SpaceTimeDerivAlgebraℂ)
    (f : SpaceTimeAlgebra) :
    pairing (seriesAction χ p) f = pairing p (χ * f) :=
  pairing_constr_leibniz χ p f

/-- The constant series `C c` acts as scalar multiplication by `c`. -/
@[simp]
lemma seriesAction_C (c : ℂ) : seriesAction (C c) = c • LinearMap.id :=
  LinearMap.ext fun p => ext_of_pairing_eq fun f => by
    simp [pairing_seriesAction, ← smul_eq_C_mul]

/-!

## B. Low-order symbols and derivatives

### B.1. The unit and first-order symbols

A series `χ` acts on the unit symbol by `χ(x₀)`, and sends `∂_μ` to `χ(x₀) ∂_μ + (∂_μ χ)(x₀)`,
which is the product rule at the base point.

-/

/-- A series acts on the unit symbol by its base-point value. -/
@[simp]
lemma seriesAction_apply_one (χ : SpaceTimeAlgebra) :
    seriesAction χ 1 = constantCoeff χ • 1 := by
  rw [← basis_zero, seriesAction_basis, Multiset.antidiagonal_zero]
  simp

/-- A series `χ` sends `∂_μ` to `χ(x₀) ∂_μ + (∂_μ χ)(x₀)`, the product rule. -/
lemma seriesAction_basis_singleton (χ : SpaceTimeAlgebra) (μ : Fin 1 ⊕ Fin 3) :
    seriesAction χ ∂[μ] = constantCoeff χ • ∂[μ] + constantCoeff (pderiv μ χ) • 1 := by
  rw [seriesAction_basis, ← Multiset.cons_zero, Multiset.antidiagonal_cons,
    Multiset.antidiagonal_zero]
  simp

/-!

### B.2. Multiplication by a derivative symbol

Appending `∂_μ` to a symbol amounts to differentiating the series it pairs with, by
`pairing_mul_basis_singleton`, so the product rule for `∂_μ (χ f)` relates the action of `χ` to
multiplication by `∂_μ`.

-/

/-- The action commutes with multiplication by `∂_μ` up to the action of `pderiv μ χ`. -/
lemma seriesAction_mul_basis_singleton (χ : SpaceTimeAlgebra) (p : SpaceTimeDerivAlgebraℂ)
    (μ : Fin 1 ⊕ Fin 3) :
    seriesAction χ (p * ∂[μ]) = seriesAction χ p * ∂[μ] + seriesAction (pderiv μ χ) p :=
  ext_of_pairing_eq fun f => by
    rw [map_add, LinearMap.add_apply, pairing_seriesAction, pairing_mul_basis_singleton,
      pairing_mul_basis_singleton, pairing_seriesAction, pairing_seriesAction, Derivation.leibniz,
      smul_eq_mul, smul_eq_mul, map_add, mul_comm f]

end SpaceTimeDerivAlgebraℂ
