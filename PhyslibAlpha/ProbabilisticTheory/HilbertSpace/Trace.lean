/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Traciality

/-!

# The trace as a positive map

## i. Overview

The linear-algebra trace is a positive tracial functional on the bounded operators; on a
finite-dimensional Hilbert space it is the usual trace. For positive `ρ`, `x ↦ Tr (x ρ)` is
positive.

## ii. Key results

- `PositiveLinearMap.conjugateₚ` : conjugation as a positive map.
- `ContinuousLinearMap.traceₚ` : the trace as a positive map.
- `ContinuousLinearMap.traceMulOpₚ` : `x ↦ Tr (x ρ)`.
- `ContinuousLinearMap.traceₚ_isTracial` : the trace is tracial.

-/

@[expose] public section

namespace ProbabilisticTheory

section Conjugate

variable {A : Type*} [NonUnitalSemiring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    (R : Type*) [Semiring R] [StarRing R]
    [Module R A] [StarModule R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-- Conjugation `x ↦ c * x * star x`, as a positive linear map. -/
@[simps!]
def _root_.PositiveLinearMap.conjugateₚ (c : A) : A →ₚ[R] A where
  toLinearMap := LinearMap.mulLeftRight R (c, star c)
  monotone' _ _ h := star_right_conjugate_le_conjugate h c

end Conjugate

open ComplexOrder

end ProbabilisticTheory

section Complex
open ProbabilisticTheory ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace ContinuousLinearMap

/-- The trace on continuous linear maps, bundled as a positive linear map. -/
@[simps!]
noncomputable def traceₚ : (E →L[ℂ] E) →ₚ[ℂ] ℂ := .mk₀
    { toFun x := x.toLinearMap.trace ℂ E
      map_add' x y := by simp
      map_smul' m x := by simp }
    (fun x h ↦ by
      simpa using (x.isPositive_toLinearMap_iff.mpr (x.nonneg_iff_isPositive.mp h)).trace_nonneg)

omit [CompleteSpace E] in
/-- The trace is tracial. -/
lemma traceₚ_isTracial : (traceₚ (E := E)).toLinearMap.IsTracial :=
  fun x y => by simp [traceₚ_apply, toLinearMap_mul, LinearMap.trace_mul_comm]

open PositiveLinearMap

/-- The positive linear functional `x ↦ tr (√ρ * x * √ρ†)`. -/
noncomputable def traceMulOpₚ (ρ : E →L[ℂ] E) : (E →L[ℂ] E) →ₚ[ℂ] ℂ :=
  traceₚ.comp (conjugateₚ ℂ (CFC.sqrt ρ))

@[simp]
lemma traceMulOpₚ_apply_of_nonneg {ρ : E →L[ℂ] E} (h : 0 ≤ ρ) (x : E →L[ℂ] E) :
    ρ.traceMulOpₚ x = (↑x * ↑ρ : E →ₗ[ℂ] E).trace ℂ E := by
  simp_rw [traceMulOpₚ, PositiveLinearMap.comp_apply, coe_toLinearMap, conjugateₚ_apply,
    traceₚ_apply, toLinearMap_mul]
  rw [mul_assoc, LinearMap.trace_mul_comm, mul_assoc, (CFC.sqrt_nonneg ρ).isSelfAdjoint.star_eq]
  have := congrArg toLinearMap (CFC.sqrt_mul_sqrt_self ρ h)
  simp_all

@[simp]
lemma traceMulOpₚ_apply_of_not_nonneg {ρ : E →L[ℂ] E} (h : ¬0 ≤ ρ) (x : E →L[ℂ] E) :
    ρ.traceMulOpₚ x = 0 := by
  simp [traceMulOpₚ, CFC.sqrt_of_not_nonneg h]

end ContinuousLinearMap
