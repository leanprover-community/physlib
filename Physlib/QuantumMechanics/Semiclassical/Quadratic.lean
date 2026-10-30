/-
Copyright (c) 2026 Zhuoran Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhuoran Li
-/
module

public import Physlib.QuantumMechanics.Semiclassical.Basic

/-!
# Weyl ordering for quadratic symbols

Use one quadratic expression for classical symbols and their Weyl quantization.

## i. Overview

A quadratic symbol is presented by a constant, two linear coefficient vectors,
and three coefficient matrices. In a noncommutative algebra, each quadratic product is
replaced by half the sum of its two orders. Evaluating the expression in `Complex` gives
the classical polynomial; evaluating it on position and momentum gives its Weyl
quantization on Schwartz maps. This coefficient presentation includes all polynomials of
degree at most two, but is not a general pseudodifferential-symbol calculus.

## ii. Key results

- `quadraticPolynomial` : the common Weyl-ordered expression
- `quadraticSymbol_apply` : its classical scalar interpretation
- `weylQuadraticCLM` : its operator interpretation on Schwartz maps

## iii. Table of contents

- A. The Weyl-ordered expression
- B. Classical symbols
- C. Quantization on Schwartz maps

## iv. References

* J. E. Moyal, Quantum mechanics as a statistical theory (1949),
  https://doi.org/10.1017/S0305004100000487.
-/

@[expose] public section

namespace QuantumMechanics.Semiclassical

noncomputable section

open Complex Real MeasureTheory SchwartzMap ContinuousLinearMap
open SpaceDHilbertSpace
open scoped FourierTransform InnerProductSpace

variable {d : ℕ}

/-! ## A. The Weyl-ordered expression -/

/-- A quadratic expression with Weyl ordering, evaluated in any complex algebra.
The three matrix coefficients multiply the symmetrized position-position, position-momentum
and momentum-momentum products. No symmetry of the coefficient matrices is required. -/
def quadraticPolynomial {R : Type*} [Ring R] [Algebra ℂ R]
    (c : ℂ) (a b : Fin d → ℂ) (A B C : Matrix (Fin d) (Fin d) ℂ)
    (X P : Fin d → R) : R :=
  c • 1 + ∑ i, a i • X i + ∑ i, b i • P i +
    (1 / 2 : ℂ) • ∑ i, ∑ j,
      (A i j • (X i * X j + X j * X i) +
        B i j • (X i * P j + P j * X i) +
        C i j • (P i * P j + P j * P i))

/-- Algebra homomorphisms preserve the Weyl-ordered quadratic expression. -/
lemma map_quadraticPolynomial {R S : Type*} [Ring R] [Algebra ℂ R] [Ring S] [Algebra ℂ S]
    (φ : R →ₐ[ℂ] S) (c : ℂ) (a b : Fin d → ℂ) (A B C : Matrix (Fin d) (Fin d) ℂ)
    (X P : Fin d → R) :
    φ (quadraticPolynomial c a b A B C X P) =
      quadraticPolynomial c a b A B C (fun i => φ (X i)) (fun i => φ (P i)) := by
  simp [quadraticPolynomial, map_sum]

/-! ## B. Classical symbols -/

/-- A coefficient presentation of a complex quadratic symbol on classical phase space. -/
def quadraticSymbol (c : ℂ) (a b : Fin d → ℂ) (A B C : Matrix (Fin d) (Fin d) ℂ)
    (z : Space d × Space d) : ℂ :=
  quadraticPolynomial c a b A B C (fun i => z.1 i) (fun i => z.2 i)

/-- In the commutative scalar algebra, the Weyl expression is the usual quadratic polynomial. -/
lemma quadraticSymbol_apply (c : ℂ) (a b : Fin d → ℂ)
    (A B C : Matrix (Fin d) (Fin d) ℂ) (z : Space d × Space d) :
    quadraticSymbol c a b A B C z = c + ∑ i, a i * z.1 i + ∑ i, b i * z.2 i +
      ∑ i, ∑ j, (A i j * z.1 i * z.1 j + B i j * z.1 i * z.2 j +
        C i j * z.2 i * z.2 j) := by
  simp only [quadraticSymbol, quadraticPolynomial, smul_eq_mul, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! ## C. Quantization on Schwartz maps -/

/-- Weyl quantization of a quadratic symbol on Schwartz maps, using the existing position
and the scaled momentum operators. A mixed monomial is ordered as `(x_i p_j + p_j x_i) / 2`. -/
def weylQuadraticCLM (h : ℝ) (c : ℂ) (a b : Fin d → ℂ)
    (A B C : Matrix (Fin d) (Fin d) ℂ) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  quadraticPolynomial c a b A B C QuantumMechanics.positionCLM (momentumCLM h)

end

end QuantumMechanics.Semiclassical
