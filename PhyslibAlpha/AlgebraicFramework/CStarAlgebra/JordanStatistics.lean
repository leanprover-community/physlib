/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Covariance
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.Jordan
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.SpectralMeasure

/-!

# Spectral formulas for Jordan moments

## i. Overview

`JB_ROADMAP.md` item 9 asks for the "headline milestone":
$$ (J, \omega, a) \to C_J(a) \to C(\sigma(a), \mathbb R) \to \mu_{\omega,a}, \qquad
   \omega(f(a)) = \int f \, d\mu_{\omega,a}. $$
This file shows that milestone is *already reached* for the canonical realization
`selfAdjoint A`: `CStarAlgebra/SpectralMeasure.lean` already built `μ_{ω,a}` and
`realSpectralMeasure_integral` (`ω(f(a)) = ∫f dμ_{ω,a}`) via mathlib's own continuous functional
calculus and Riesz–Markov–Kakutani — the C⋆-algebra `A` is already associative, so there was never
a need to build `C_J(a)` from scratch there. What was missing is the *connection* to this file's
own Jordan-algebraic `moment`/`variance` API (`Observable.lean`, `Covariance.lean`), which is
defined via the Jordan powers `a^{[n]}` rather than ordinary powers `aⁿ`.

The connection rests on one clean fact, `jpow_eq_pow`: for the *single* generator `a`, the
Jordan power `a^{[n]}` equals the ordinary associative power `(a:A)ⁿ` — proved directly by
induction from `mul_self_eq`, with **no use of the open `commute_mulLeft_pow` theorem**
(`Power/Associative.lean`). That theorem is about *arbitrary* pairs of Jordan powers commuting as
operators in a general Jordan algebra; here `a` only ever needs to commute with itself, which is
free. This is worth remembering: the single-generator case that item 9 actually needs was never
blocked on the general power-associativity theorem, only the roadmap's abstract, JB-algebra-generic
route to it (`JB/GENERATED_SUBALGEBRA_ROADMAP.md`) was.

## ii. Key definitions and results

- `JB.jpow_eq_pow`
- `JB.moment_eq_integral` : `moment n (ω.onObservables) a = ∫ y, y^n ∂(realSpectralMeasure ω a)`
- `JB.variance_eq_integral_sq_sub` : the variance as `∫y² dμ - (∫y dμ)²`

## iii. Table of contents

- A. Jordan powers of a single element are ordinary powers
- B. Moments as integrals against the outcome distribution

-/

@[expose] public section

open scoped ComplexOrder

namespace JB

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped selfAdjoint

/-! ## A. Jordan powers of a single element are ordinary powers -/

omit [PartialOrder A] [StarOrderedRing A] in
/-- The Jordan power `a^{[n]}` of a single self-adjoint element
equals its ordinary associative power `(a:A)ⁿ`. Unlike the general power-associativity theorem
(`Power/Associative.lean`'s `commute_mulLeft_pow`), this concrete identity follows directly from
self-commutation in the ambient associative algebra. -/
theorem jpow_eq_pow (a : selfAdjoint A) (n : ℕ) :
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

/-- **Item 9's headline result, for the canonical realization.** The `n`-th moment of `a` in the
state `ω` (restricted from a state on the whole C⋆-algebra) is `∫ y^n dμ_{ω,a}` — exactly
`m_n(a) = ∫λⁿ dμ_{ω,a}` from `JB_ROADMAP.md`, obtained by specializing
`realSpectralMeasure_integral` to `f = (· ^ n)` and identifying the Jordan power with the ordinary
one via `jpow_eq_pow`. -/
theorem moment_eq_integral (ω : 𝓢[A]) (a : selfAdjoint A) (n : ℕ) :
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
theorem apply_eq_integral (ω : 𝓢[A]) (a : selfAdjoint A) :
    ω.onObservables a = ∫ y, y ∂(realSpectralMeasure ω a) := by
  have h := moment_eq_integral ω a 1
  simp only [IsJordanOrderUnit.moment_one, pow_one] at h
  exact h

/-- **The variance as `∫y² dμ - (∫y dμ)²`**, exactly `JB_ROADMAP.md` item 9's
`Var_ω(a) = \int (\lambda - \omega(a))^2 \, d\mu_{\omega,a}` in its expanded (Kőnig–Huygens) form:
`variance` (`Covariance.lean`) unfolds to `moment 2 - (moment 1)^2`, and both moments are now
integrals by `moment_eq_integral`. -/
theorem variance_eq_integral_sq_sub (ω : 𝓢[A]) (a : selfAdjoint A) :
    IsJordanOrderUnit.variance ω.onObservables a =
      (∫ y, y ^ 2 ∂(realSpectralMeasure ω a)) - (∫ y, y ∂(realSpectralMeasure ω a)) ^ 2 := by
  calc
    IsJordanOrderUnit.variance ω.onObservables a =
        IsJordanOrderUnit.moment 2 ω.onObservables a - (ω.onObservables a) ^ 2 := by
      simp [IsJordanOrderUnit.variance, LinearMap.variance, IsJordanOrderUnit.moment,
        JordanAlgebra.jpow_two, pow_two]
    _ = _ := by rw [moment_eq_integral, apply_eq_integral]

end JB
