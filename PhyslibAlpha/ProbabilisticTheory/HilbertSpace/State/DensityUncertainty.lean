/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.Uncertainty
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.State.Density
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.State.Vector
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!

# Uncertainty in density-operator states

Expectation, covariance, variance and Robertson–Schrödinger for density-operator states.

## i. Overview

The state of a density operator `ρ` is a state on the C⋆-algebra of bounded operators, so the
uncertainty relations of C⋆-algebras apply to it. Its expectation, covariance and variance are
traces against `ρ`, and the state of a rank-one projection `|ψ⟩⟨ψ|` is the vector state of `ψ`.

## ii. Key results

- `UnitalPositiveLinearMap.expectation_ofDensity` : the expectation of `a` is `Re Tr(a ρ)`.
- `UnitalPositiveLinearMap.covariance_ofDensity`, `UnitalPositiveLinearMap.variance_ofDensity` :
  covariance and variance as traces.
- `UnitalPositiveLinearMap.robertson_schrodinger_ofDensity` : the Robertson–Schrödinger relation for
  density operators.
- `UnitalPositiveLinearMap.ofDensity_rankOne` : rank-one density operators give vector states.

## iii. Table of contents

- A. Statistics of density states as traces
- B. Robertson–Schrödinger for density operators
- C. Vector states as rank-one density states

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ComplexOrder InnerProductSpace selfAdjoint
open ContinuousLinearMap

namespace UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ρ : H →L[ℂ] H} (hpos : 0 ≤ ρ) (hnorm : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1)

/-! ## A. Statistics of density states as traces -/

/-- The expectation of an observable in a density state is the real part of `Tr(a ρ)`. -/
lemma expectation_ofDensity (a : Observable (H →L[ℂ] H)) :
    (ofDensity hpos hnorm)⟨a⟩ = ((↑(a : H →L[ℂ] H) * ↑ρ : H →ₗ[ℂ] H).trace ℂ H).re := by
  rw [← ofDensity_apply hpos hnorm, apply_observable_eq_expectation, Complex.ofReal_re]

/-- The covariance in a density state is `Re Tr(δa δb ρ)` for the centered observables. -/
lemma covariance_ofDensity (a b : Observable (H →L[ℂ] H)) :
    covariance (ofDensity hpos hnorm) a b =
      ((↑((centered (ofDensity hpos hnorm) a : H →L[ℂ] H) *
        centered (ofDensity hpos hnorm) b) * ↑ρ : H →ₗ[ℂ] H).trace ℂ H).re := by
  rw [covariance_eq_re_apply_centered_mul, ofDensity_apply]

/-- The variance in a density state is `Re Tr(δa² ρ)` for the centered observable. -/
lemma variance_ofDensity (a : Observable (H →L[ℂ] H)) :
    variance (ofDensity hpos hnorm) a =
      ((↑((centered (ofDensity hpos hnorm) a : H →L[ℂ] H) *
        centered (ofDensity hpos hnorm) a) * ↑ρ : H →ₗ[ℂ] H).trace ℂ H).re :=
  covariance_ofDensity hpos hnorm a a

/-! ## B. Robertson–Schrödinger for density operators -/

/-- **Robertson–Schrödinger relation for mixed states.** For a density operator `ρ` and
observables `a`, `b` with centered parts `δa`, `δb`,
`(Re Tr(δa δb ρ))² + (Re Tr(⁅a, b⁆ ρ))² ≤ Re Tr(δa² ρ) · Re Tr(δb² ρ)`,
where `⁅a, b⁆ = -(i/2)(ab - ba)`. -/
lemma robertson_schrodinger_ofDensity (a b : Observable (H →L[ℂ] H)) :
    ((↑((centered (ofDensity hpos hnorm) a : H →L[ℂ] H) *
        centered (ofDensity hpos hnorm) b) * ↑ρ : H →ₗ[ℂ] H).trace ℂ H).re ^ 2 +
      ((↑((⁅a, b⁆ : Observable (H →L[ℂ] H)) : H →L[ℂ] H) * ↑ρ : H →ₗ[ℂ] H).trace ℂ H).re ^ 2 ≤
      ((↑((centered (ofDensity hpos hnorm) a : H →L[ℂ] H) *
        centered (ofDensity hpos hnorm) a) * ↑ρ : H →ₗ[ℂ] H).trace ℂ H).re *
      ((↑((centered (ofDensity hpos hnorm) b : H →L[ℂ] H) *
        centered (ofDensity hpos hnorm) b) * ↑ρ : H →ₗ[ℂ] H).trace ℂ H).re := by
  rw [← covariance_ofDensity, ← expectation_ofDensity, ← variance_ofDensity,
    ← variance_ofDensity]
  exact robertson_schrodinger _ a b

/-! ## C. Vector states as rank-one density states -/

variable [FiniteDimensional ℂ H]

omit [CompleteSpace H] in
/-- For a unit vector `ψ`, the projection `|ψ⟩⟨ψ|` has trace one. -/
lemma trace_rankOne_self {ψ : H} (h : ‖ψ‖ = 1) :
    ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H).trace ℂ H = 1 := by
  rw [InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K, h]
  simp

/-- The density state of the projection `|ψ⟩⟨ψ|` is the vector state of `ψ`: pure states are
the rank-one mixed states. -/
lemma ofDensity_rankOne {ψ : H} (h : ‖ψ‖ = 1) :
    ofDensity (nonneg_iff_isPositive.mpr (InnerProductSpace.isPositive_rankOne_self ψ))
      (trace_rankOne_self h) = ofVec h := by
  ext x
  rw [ofDensity_apply, ofVec_apply, ← toLinearMap_mul, mul_def, InnerProductSpace.comp_rankOne,
    InnerProductSpace.trace_rankOne]
  rfl

end UnitalPositiveLinearMap

end ProbabilisticTheory
