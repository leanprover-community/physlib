/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.BoundedIntegralCommute
public import Mathlib.Analysis.RCLike.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap

/-!

# The continuous functional calculus of a spectral measure

Integrating continuous functions on a compact space against a spectral measure is a unital
⋆-homomorphism into the bounded operators.

## i. Overview

For a weak spectral measure `P` on a compact Borel space `X`, the integral `f ↦ ∫ f dP` of a
continuous function is a unital ⋆-homomorphism `C(X, ℂ) → B(H)`. This repackages the algebra of the
bounded integral so that it can be composed with other ⋆-homomorphisms, and so that the spectrum
of an integral can be controlled by the spectrum of the integrand.

## ii. Key results

- `WOTSpectralMeasure.continuousCalculus` : the ⋆-homomorphism `f ↦ ∫ f dP`.

## iii. Table of contents

- A. The ⋆-homomorphism

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology
open scoped ComplexOrder InnerProductSpace

namespace QuantumMechanics

namespace WOTSpectralMeasure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [Nonempty X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (P : WOTSpectralMeasure X H)

/-- The bounded integral of a continuous function, as a bounded operator. -/
def integralCLM (f : C(X, ℂ)) : H →L[ℂ] H :=
  ContinuousLinearMapWOT.toCLM
    (P.boundedIntegral f f.continuous.measurable ⟨‖f‖, fun z => f.norm_coe_le_norm z⟩)

/-! ## A. The ⋆-homomorphism -/

omit [BorelSpace X] [Nonempty X] [MeasurableSpace X] in
lemma bound_of_continuous (f : C(X, ℂ)) : ∃ C, ∀ z, ‖f z‖ ≤ C :=
  ⟨‖f‖, fun z => f.norm_coe_le_norm z⟩

/-- The integral of a measurable bounded function that agrees with a continuous function. -/
lemma integralCLM_eq_of_forall_eq (f : C(X, ℂ)) {F : X → ℂ} (hF : Measurable F)
    (hbF : ∃ C, ∀ z, ‖F z‖ ≤ C) (h : ∀ z, f z = F z) :
    P.integralCLM f = ContinuousLinearMapWOT.toCLM (P.boundedIntegral F hF hbF) :=
  congrArg ContinuousLinearMapWOT.toCLM
    (P.boundedIntegral_congr f.continuous.measurable hF (bound_of_continuous f) hbF h)

lemma integralCLM_add (f g : C(X, ℂ)) :
    P.integralCLM (f + g) = P.integralCLM f + P.integralCLM g := by
  have hsum := P.boundedIntegral_add f.continuous.measurable g.continuous.measurable
    (bound_of_continuous f) (bound_of_continuous g)
  rw [integralCLM_eq_of_forall_eq P (f + g) (f.continuous.measurable.add g.continuous.measurable)
    (by obtain ⟨C₁, h₁⟩ := bound_of_continuous f; obtain ⟨C₂, h₂⟩ := bound_of_continuous g
        exact ⟨C₁ + C₂, fun z => (norm_add_le _ _).trans (add_le_add (h₁ z) (h₂ z))⟩)
    (fun z => rfl), hsum]
  rfl

lemma integralCLM_mul (f g : C(X, ℂ)) :
    P.integralCLM (f * g) = P.integralCLM f * P.integralCLM g := by
  have hmul := P.boundedIntegral_mul f.continuous.measurable g.continuous.measurable
    (bound_of_continuous f) (bound_of_continuous g)
  rw [integralCLM_eq_of_forall_eq P (f * g) (f.continuous.measurable.mul g.continuous.measurable)
    (by obtain ⟨C₁, h₁⟩ := bound_of_continuous f; obtain ⟨C₂, h₂⟩ := bound_of_continuous g
        obtain ⟨z₀⟩ := (inferInstance : Nonempty X)
        have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (h₁ z₀)
        exact ⟨C₁ * C₂, fun z => by
          rw [Pi.mul_apply, norm_mul]
          exact mul_le_mul (h₁ z) (h₂ z) (norm_nonneg _) hC₁⟩)
    (fun z => rfl), hmul]
  exact ContinuousLinearMapWOT.toCLM_mul _ _

lemma integralCLM_const (c : ℂ) : P.integralCLM (ContinuousMap.const X c) = c • 1 := by
  have h := P.boundedIntegral_const c
  rw [integralCLM_eq_of_forall_eq P (ContinuousMap.const X c) measurable_const ⟨‖c‖,
    fun _ => le_rfl⟩
    (fun z => rfl), h]
  rfl

lemma integralCLM_star (f : C(X, ℂ)) : P.integralCLM (star f) = star (P.integralCLM f) := by
  have h := P.boundedIntegral_star f.continuous.measurable (bound_of_continuous f)
  rw [integralCLM_eq_of_forall_eq P (star f) (F := fun z => star (f z))
    (continuous_star.measurable.comp f.continuous.measurable)
    (by obtain ⟨C, hC⟩ := bound_of_continuous f; exact ⟨C, fun z => by simpa using hC z⟩)
    (fun z => rfl), h]
  rfl

/-- **The continuous functional calculus of a spectral measure**: `f ↦ ∫ f dP` is a unital
⋆-homomorphism from the continuous functions to the bounded operators. -/
def continuousCalculus : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := P.integralCLM
  map_one' := by
    have := P.integralCLM_const 1
    simpa using this
  map_mul' := P.integralCLM_mul
  map_zero' := by
    have := P.integralCLM_const 0
    simpa using this
  map_add' := P.integralCLM_add
  commutes' c := by
    show P.integralCLM (ContinuousMap.const X c) = algebraMap ℂ (H →L[ℂ] H) c
    rw [P.integralCLM_const, Algebra.algebraMap_eq_smul_one]
  map_star' := P.integralCLM_star

end WOTSpectralMeasure

end QuantumMechanics

end ProbabilisticTheory

end
