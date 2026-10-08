/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Basic
/-!

# The spacetime derivative algebra

The algebra of derivative symbols on spacetime, which evaluate on the spacetime algebra.

## i. Overview

In field theory, local quantities are built from a field and finitely many of its derivatives at
a point. A linear combination of such derivatives is the value `(P φ)(x₀)` of a linear
differential operator `P` with constant coefficients, and such an operator is a polynomial in the
partial derivatives `∂_μ`. These polynomials, which we call derivative symbols, form the algebra
`SpaceTimeDerivAlgebraℂ`. The value `(P φ)(x₀)` is determined by the derivatives of `φ` at `x₀`,
which its Taylor series `taylorSeries x₀ φ` records as an element of the spacetime algebra. We
therefore pair a symbol `P` with any series `f` by applying `P` to `f` and taking the value at the
base point, so that pairing with `taylorSeries x₀ φ` gives `(P φ)(x₀)`.

Throughout we use the notation of `SpaceTimeAlgebra`, whose elements we call series. For a
multiset `s` of directions,

- `x^s` is the monomial in which each `x^μ` occurs as often as `μ` occurs in `s`;
- `∂^s f` is the iterated derivative of a series `f`, and `(∂^s f)(0)` is its value at the base
  point;
- `s!` is the product of the factorials of the multiplicities in `s`;
- `∂^s` is the derivative symbol of `∂^s f`, written `∂^[s]` in Lean.

## ii. Key results

- `SpaceTimeDerivAlgebraℂ` : the algebra of derivative symbols.
- `SpaceTimeDerivAlgebraℂ.basis` : the monomial basis indexed by multisets of directions.
- `SpaceTimeDerivAlgebraℂ.basis_mul` : monomials multiply by adding multisets.
- `SpaceTimeDerivAlgebraℂ.pairing` : applies a symbol to a series and evaluates at the base
  point.
- `SpaceTimeDerivAlgebraℂ.pairing_basis` : `∂^s` pairs with `f` to the value `(∂^s f)(0)`.
- `SpaceTimeDerivAlgebraℂ.pairing_injective` : the pairing separates derivative symbols.
- `SpaceTimeDerivAlgebraℂ.pairing_mul_basis_singleton` : multiplying by `∂_μ` differentiates the
  series.

## iii. Table of contents

- A. The derivative algebra
  - A.1. The monomial basis
- B. Pairing symbols with series
  - B.1. Pairing with monomials
  - B.2. Injectivity of the pairing
  - B.3. Multiplication by a derivative symbol

## iv. References

* None.
-/

@[expose] public section

/-!

## A. The derivative algebra

The partial derivatives of a smooth field commute, so these polynomials are in commuting symbols
`∂_μ`. Each symbol involves finitely many derivatives (whereas the Taylor series of a field keeps
all of them). Formally, the derivative algebra is the symmetric algebra on
`Module.Dual ℂ Lorentz.CoℂModule`, the dual of the complex covector module, with `∂_μ` the dual
basis vector in direction `μ` and time coordinate `x⁰ = ct`.

-/

/-- The algebra of derivative symbols on spacetime, the polynomials in four commuting symbols
  `∂_μ`. -/
abbrev SpaceTimeDerivAlgebraℂ : Type := SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)

namespace SpaceTimeDerivAlgebraℂ

open MvPowerSeries SpaceTimeAlgebra

/-!

### A.1. The monomial basis

The order of the monomial `∂^s` is the size of `s`, and multiplying monomials adds their
multisets. The basis is Mathlib's `Module.Basis.symmetricAlgebra`, reindexed by multisets.

-/

/-- The monomial basis of the derivative algebra, in which `basis s` is the monomial `∂^s`. -/
noncomputable def basis : Module.Basis (Multiset (Fin 1 ⊕ Fin 3)) ℂ SpaceTimeDerivAlgebraℂ :=
  Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.reindex Multiset.toFinsupp.toEquiv.symm

@[inherit_doc basis]
scoped notation "∂^[" s "]" => basis s

/-- The derivative symbol `∂_μ` in direction `μ`, the monomial `basis {μ}`. -/
scoped notation "∂[" μ "]" => basis {μ}

/-- The monomial `∂^s` is the polynomial monomial whose exponents are the multiplicities in
  `s`. -/
lemma basis_apply (s : Multiset (Fin 1 ⊕ Fin 3)) :
    ∂^[s] = (SymmetricAlgebra.equivMvPolynomial Lorentz.complexCoBasis.dualBasis).symm
      (MvPolynomial.monomial (Multiset.toFinsupp s) 1) := by
  rw [basis, Module.Basis.reindex_apply, Equiv.symm_symm]
  rfl

/-- The empty monomial is the unit. -/
@[simp]
lemma basis_zero : ∂^[0] = 1 := by
  rw [basis_apply, Multiset.toFinsupp_zero, MvPolynomial.monomial_zero', MvPolynomial.C_1,
    map_one]

/-- The monomial of a single direction `μ` is the derivative symbol `∂_μ`. -/
lemma basis_singleton (μ : Fin 1 ⊕ Fin 3) :
    ∂[μ] = SymmetricAlgebra.ι ℂ _ (Lorentz.complexCoBasis.dualBasis μ) := by
  rw [basis_apply, Multiset.toFinsupp_singleton]
  exact SymmetricAlgebra.equivMvPolynomial_symm_X _ μ

/-- Monomials multiply by adding multisets, `∂^s ∂^t = ∂^(s + t)`. -/
lemma basis_mul (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    ∂^[s] * ∂^[t] = ∂^[s + t] := by
  rw [basis_apply, basis_apply, basis_apply, ← map_mul, MvPolynomial.monomial_mul_monomial,
    mul_one, Multiset.toFinsupp_add]

/-!

## B. Pairing symbols with series

The monomial `∂^s` pairs with a series `f` to `(∂^s f)(0)`, and the pairing extends linearly in
the symbol (in commutative algebra this is the apolarity pairing, with power series in place of
polynomials). On the Taylor series of a field it gives `(∂^s φ)(x₀)`, by
`constantCoeff_iteratedPDeriv_taylorSeries`.

-/

/-- The pairing of a symbol `P` with a series `f`, given by the value of `P f` at the base
  point. -/
noncomputable def pairing : SpaceTimeDerivAlgebraℂ →ₗ[ℂ] SpaceTimeAlgebra →ₗ[ℂ] ℂ :=
  basis.constr ℂ fun s => LinearMap.proj s ∘ₗ derivValuesEquiv.toLinearMap

/-!

### B.1. Pairing with monomials

Since `(∂^s f)(0)` is `s!` times the coefficient of `x^s` in `f` (`constantCoeff_iteratedPDeriv`),
the symbol `∂_μ²` paired with the series `(x^μ)²` gives `2`, while the coefficient of `(x^μ)²` is
`1`.

-/

/-- The monomial `∂^s` pairs with `f` to the base-point value `(∂^s f)(0)`. -/
lemma pairing_basis (s : Multiset (Fin 1 ⊕ Fin 3)) (f : SpaceTimeAlgebra) :
    pairing ∂^[s] f = constantCoeff (iteratedPDeriv s f) := by
  rw [pairing, Module.Basis.constr_basis]
  rfl

/-- The unit symbol pairs with `f` to its base-point value `f(0)`. -/
lemma pairing_one (f : SpaceTimeAlgebra) : pairing 1 f = constantCoeff f := by
  rw [← basis_zero, pairing_basis, iteratedPDeriv_zero]

/-- Pairing a symbol with the series `x^s` gives `s!` times the coefficient of `∂^s` in the
  symbol. -/
lemma pairing_monomial (p : SpaceTimeDerivAlgebraℂ) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    pairing p (monomial (Multiset.toFinsupp s) 1) =
      ((∏ ν, (s.count ν).factorial : ℕ) : ℂ) * basis.repr p s := by
  classical
  rw [pairing, Module.Basis.constr_apply, Finsupp.sum, LinearMap.sum_apply,
    Finset.sum_eq_single s]
  · simp [constantCoeff_iteratedPDeriv, mul_comm]
  · intro t _ hts
    simp [constantCoeff_iteratedPDeriv, coeff_monomial, Multiset.toFinsupp.injective.ne hts]
  · intro hs
    simp [Finsupp.notMem_support_iff.mp hs]

/-!

### B.2. Injectivity of the pairing

The same computation on the monomials `x^s` recovers every coefficient of a symbol, so distinct
symbols take different values on some series.

-/

/-- The pairing separates derivative symbols. -/
lemma pairing_injective : Function.Injective pairing := by
  intro p q h
  refine basis.ext_elem fun s => ?_
  have hs : ((∏ ν, (s.count ν).factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _)
  rw [← mul_right_inj' hs, ← pairing_monomial, ← pairing_monomial, h]

/-- Symbols that pair equally with every series are equal. -/
lemma ext_of_pairing_eq {p q : SpaceTimeDerivAlgebraℂ} (h : ∀ f, pairing p f = pairing q f) :
    p = q :=
  pairing_injective (LinearMap.ext h)

/-!

### B.3. Multiplication by a derivative symbol

Appending `∂_μ` to a symbol amounts to differentiating the series along `μ`, and on
`taylorSeries x₀ φ` to differentiating the field, by `taylorSeries_deriv`.

-/

/-- Multiplying a symbol by `∂_μ` corresponds to applying `pderiv μ` to the series. -/
lemma pairing_mul_basis_singleton (p : SpaceTimeDerivAlgebraℂ) (μ : Fin 1 ⊕ Fin 3)
    (f : SpaceTimeAlgebra) :
    pairing (p * ∂[μ]) f = pairing p (pderiv μ f) := by
  have h : pairing.flip f ∘ₗ LinearMap.mulRight ℂ ∂[μ] =
      pairing.flip (pderiv μ f) := basis.ext fun s => by
    rw [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.flip_apply,
      LinearMap.flip_apply, basis_mul, pairing_basis, pairing_basis, add_comm,
      Multiset.singleton_add, iteratedPDeriv_cons]
  exact LinearMap.congr_fun h p

end SpaceTimeDerivAlgebraℂ
