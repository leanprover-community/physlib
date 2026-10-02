/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.SelfAdjoint

/-!

# Restricting positive maps

## i. Overview

A positive linear map restricts to submodules, in particular to the self-adjoint elements, where a
complex state becomes a real one.

## ii. Key results

- `PositiveLinearMap.restrict`, `UnitalPositiveLinearMap.restrict` : restriction to a submodule.
- `UnitalPositiveLinearMap.restrictSA` : restriction to self-adjoint elements.

-/

@[expose] public section

namespace ProbabilisticTheory

section Restrict

variable {R S E₁ E₂ : Type*}
    [Semiring R] [Semiring S]
    [AddCommMonoid E₁] [AddCommMonoid E₂]
    [PartialOrder E₁] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] [Module S E₁] [Module S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R]

/-- Restrict a positive linear map to submodules it preserves. -/
@[simps!]
def _root_.PositiveLinearMap.restrict (f : E₁ →ₚ[R] E₂) {F₁ : Submodule S E₁} {F₂ : Submodule S E₂}
    (h : ∀ ⦃x⦄, x ∈ F₁ → f x ∈ F₂) : F₁ →ₚ[S] F₂ where
  toLinearMap := (f.toLinearMap.restrictScalars S).restrict (by simpa)
  monotone' a b h := f.monotone (by simpa)

variable [One E₁] [One E₂]

/-- Restrict a unital positive linear map to submodules it preserves. -/
def UnitalPositiveLinearMap.restrict (f : E₁ →ₚ₁[R] E₂) {F₁ : Submodule S E₁} {F₂ : Submodule S E₂}
    [One F₁] [One F₂] (h₁ : ↑(1 : F₁) = (1 : E₁)) (h₂ : ↑(1 : F₂) = (1 : E₂))
    (h : ∀ ⦃x⦄, x ∈ F₁ → f x ∈ F₂) : F₁ →ₚ₁[S] F₂ where
  toPositiveLinearMap := f.toPositiveLinearMap.restrict h
  map_one' := by
    apply Subtype.ext
    change f (↑(1 : F₁) : E₁) = (↑(1 : F₂) : E₂)
    rw [h₁, h₂, map_one]

end Restrict

end ProbabilisticTheory

section SelfAdjoint
open ProbabilisticTheory

variable {A₁ A₂ : Type*}

namespace PositiveLinearMap

-- `IsSelfAdjoint.map` needs Mathlib's `StarHomClass` instance for positive linear maps.
variable
    [AddCommGroup A₁] [PartialOrder A₁] [StarAddMonoid A₁]
    [NonUnitalRing A₂] [PartialOrder A₂] [StarRing A₂]
    [SelfAdjointDecompose A₁]
    [Module ℂ A₁] [Module ℂ A₂]
    [StarModule ℂ A₁] [StarModule ℂ A₂]
    [StarOrderedRing A₂]

open selfAdjoint

/-- A positive linear map induces a positive real-linear map on self-adjoint elements. -/
noncomputable def restrictSA (f : A₁ →ₚ[ℂ] A₂) : selfAdjoint A₁ →ₚ[ℝ] selfAdjoint A₂ :=
  submodulePLM.comp <|
    (f.restrict (by simp_all [IsSelfAdjoint.map])).comp <| submodulePLMSymm ℝ

@[simp, norm_cast]
lemma coe_restrictSA_apply (f : A₁ →ₚ[ℂ] A₂) (x : selfAdjoint A₁) :
    ↑(f.restrictSA x) = f ↑x := by
  simp [restrictSA]

section Complex

open Complex ComplexOrder ComplexConjugate

/-- A positive complex-linear functional induces a positive real-linear functional on
self-adjoint elements. -/
noncomputable def restrictSAC (f : A₁ →ₚ[ℂ] ℂ) : selfAdjoint A₁ →ₚ[ℝ] ℝ :=
  Complex.selfAdjointUPLM.toPositiveLinearMap.comp f.restrictSA

@[simp, norm_cast]
lemma coe_restrictSAC_apply (f : A₁ →ₚ[ℂ] ℂ) (x : selfAdjoint A₁) :
    (f.restrictSAC x : ℂ) = f (x : A₁) := by
  have : conj (f x) = f x := by
    rw [← star_def, ← isSelfAdjoint_iff]
    exact IsSelfAdjoint.map f isSelfAdjoint
  change (((f.restrictSA x : selfAdjoint ℂ) : ℂ).re : ℂ) = f (x : A₁)
  rw [coe_restrictSA_apply]
  exact conj_eq_iff_re.mp this

end Complex

end PositiveLinearMap

end SelfAdjoint

namespace ProbabilisticTheory

section SelfAdjoint

variable {A₁ A₂ : Type*}

namespace UnitalPositiveLinearMap

variable
    [Ring A₁] [PartialOrder A₁] [StarRing A₁]
    [Ring A₂] [PartialOrder A₂] [StarRing A₂]
    [SelfAdjointDecompose A₁]
    [Module ℂ A₁] [Module ℂ A₂]
    [StarModule ℂ A₁] [StarModule ℂ A₂]
    [StarOrderedRing A₂]

open selfAdjoint

variable (f : A₁ →ₚ₁[ℂ] A₂)

/-- A unital positive linear map induces a unital positive real-linear map on
self-adjoint elements. -/
noncomputable def restrictSA (f : A₁ →ₚ₁[ℂ] A₂) : selfAdjoint A₁ →ₚ₁[ℝ] selfAdjoint A₂ :=
  submoduleUPLM.comp <|
    (f.restrict val_one val_one (by simp_all [IsSelfAdjoint.map])).comp
      <| submoduleUPLMSymm ℝ

@[simp, norm_cast]
lemma coe_restrictSA_apply (f : A₁ →ₚ₁[ℂ] A₂) (x : selfAdjoint A₁) :
    ↑(f.restrictSA x) = f ↑x := by
  change f ↑((submoduleEquiv (R := ℝ) (A := A₁)).symm x) = f ↑x
  exact congrArg f (submoduleEquiv_symm_apply_coe x)

open Complex ComplexOrder ComplexConjugate

/-- A unital positive complex-linear functional induces a unital positive real-linear functional
on self-adjoint elements. -/
noncomputable def restrictSAC (f : A₁ →ₚ₁[ℂ] ℂ) : selfAdjoint A₁ →ₚ₁[ℝ] ℝ :=
  Complex.selfAdjointUPLM.comp f.restrictSA

@[simp, norm_cast]
lemma coe_restrictSAC_apply (f : A₁ →ₚ₁[ℂ] ℂ) (x : selfAdjoint A₁) :
    (f.restrictSAC x : ℂ) = f (x : A₁) := by
  have : conj (f x) = f x := by
    rw [← star_def, ← isSelfAdjoint_iff]
    exact IsSelfAdjoint.map f isSelfAdjoint
  change (((f.restrictSA x : selfAdjoint ℂ) : ℂ).re : ℂ) = f (x : A₁)
  rw [coe_restrictSA_apply]
  exact conj_eq_iff_re.mp this

end UnitalPositiveLinearMap

end SelfAdjoint

end ProbabilisticTheory
