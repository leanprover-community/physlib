/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import PhyslibAlpha.ProbabilisticTheory.State.WeightEquivalence

/-!

# Tracial states and weights

## i. Overview

A state `ω` is tracial when `ω (a⋆ a) = ω (a a⋆)`. For a complex-linear functional this is
equivalent to `f (a b) = f (b a)`. A finite tracial weight gives a tracial state.

## ii. Key results

- `UnitalPositiveLinearMap.IsTracial` : tracial states.
- `Weight.IsTracial` : tracial weights.
- `LinearMap.isTracial_iff_star_mul_self_eq_mul_star_self` : a complex functional is tracial iff `f
  (a⋆ a) = f (a a⋆)`.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace Weight

variable {A : Type*} [OrderUnitSpace A] [Mul A] [Star A]

/-- A weight is tracial when its finite positive-linear extensions assign equal values to `x† x`
and `x x†`. -/
def IsTracial (w : Weight A) : Prop :=
  ∀ (hw : w.IsFinite) (x : A),
    hw.toPositiveLinearMap (star x * x) = hw.toPositiveLinearMap (x * star x)

namespace IsTracial

variable {w : Weight A}

/-- A finite tracial weight's real positive-linear extension has equal values on `x† x` and
`x x†`. -/
lemma toPositiveLinearMap_star_mul_self (ht : w.IsTracial) (hw : w.IsFinite) (x : A) :
    hw.toPositiveLinearMap (star x * x) = hw.toPositiveLinearMap (x * star x) :=
  ht hw x

end IsTracial

end Weight

namespace UnitalPositiveLinearMap

variable {A : Type*} [OrderUnitSpace A] [Mul A] [Star A]

/-- A state is tracial when it assigns equal values to `x† x` and `x x†`. -/
def IsTracial (s : 𝓢[ℝ, A]) : Prop := ∀ x : A, s (star x * x) = s (x * star x)

end UnitalPositiveLinearMap

namespace Weight.IsState

variable {A : Type*} [OrderUnitSpace A] [Mul A] [Star A] {w : Weight A}

/-- The state of a tracial weight assigns equal values to `x†x` and `xx†`. -/
lemma isTracial (hw : w.IsState) (ht : w.IsTracial) :
    ∀ x : A, hw.toState (star x * x) = hw.toState (x * star x) :=
  fun x => ht.toPositiveLinearMap_star_mul_self hw.finite x

end Weight.IsState

end ProbabilisticTheory

namespace LinearMap
open ProbabilisticTheory

variable {A : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]

/-- A complex-linear functional is tracial when it is invariant under cyclic permutations. -/
def IsTracial (f : A →ₗ[ℂ] ℂ) : Prop :=
  ∀ x y : A, f (x * y) = f (y * x)

/-- Equality on `x†x` and `xx†` characterizes tracial complex-linear functionals. -/
lemma isTracial_iff_star_mul_self_eq_mul_star_self (f : A →ₗ[ℂ] ℂ) :
    f.IsTracial ↔ ∀ x : A, f (star x * x) = f (x * star x) := by
  constructor
  · intro ht x
    exact ht (star x) x
  · intro h x y
    have hplus := h (x + star y)
    have hI := h (x + Complex.I • star y)
    have hx := h x
    have hy := h (star y)
    simp only [star_add, star_star, star_smul, Complex.star_def, Complex.conj_I, map_add,
      map_smul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm] at hplus hI
    simp at hI
    simp only [star_star] at hy
    have hp : f (y * x) + f (star x * star y) = f (star y * star x) + f (x * y) := by
      linear_combination hplus - hx - hy
    have hq : -Complex.I • f (y * x) + Complex.I • f (star x * star y) =
        Complex.I • f (star y * star x) - Complex.I • f (x * y) := by
      linear_combination (norm := (ring_nf; simp [Complex.I_sq, hy])) hI - hx - hy
    linear_combination (norm := (ring_nf; simp [Complex.I_sq]; try ring))
      (-Complex.I / 2) * hq - (1 / 2) * hp

end LinearMap

