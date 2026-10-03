/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Physlib.QuantumMechanics.Basic.SelfAdjoint

/-!

# Restriction of (unital) positive linear maps to submodules

We define the restriction of (unital) positive linear maps to submodules.

In particular, we treat the special case where the submodule consists of the self-adjoint elements.

## Main definitions

- `PositiveLinearMap.restrict`: The restriction of a positive linear map to a submodule
- `UnitalPositiveLinearMap.restrict`: The restriction of a unital positive linear map to a submodule

## TODO

- What are the most general assumptions that assure that positive linear maps preserve
the self-adjoint elements?

-/

@[expose] public section

section Restrict

variable {R S E₁ E₂ : Type*}
    [Semiring R] [Semiring S]
    [AddCommMonoid E₁] [AddCommMonoid E₂]
    [PartialOrder E₁] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] [Module S E₁] [Module S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R]

/-- The restriction of a poistive linear map to a submodule. -/
@[simps!]
def PositiveLinearMap.restrict (f : E₁ →ₚ[R] E₂) {F₁ : Submodule S E₁} {F₂ : Submodule S E₂}
    (h : ∀ ⦃x⦄, x ∈ F₁ → f x ∈ F₂) : F₁ →ₚ[S] F₂ where
  toLinearMap := (f.toLinearMap.restrictScalars S).restrict (by simpa)
  monotone' a b h := f.monotone (by simpa)

variable [One E₁] [One E₂]

/-- The restriction of a unital poistive linear map to a submodule. -/
@[simps!]
def UnitalPositiveLinearMap.restrict (f : E₁ →ₚ₁[R] E₂) {F₁ : Submodule S E₁} {F₂ : Submodule S E₂}
    [One F₁] [One F₂] (h₁ : ↑(1 : F₁) = (1 : E₁)) (h₂ : ↑(1 : F₂) = (1 : E₂))
    (h : ∀ ⦃x⦄, x ∈ F₁ → f x ∈ F₂) : F₁ →ₚ₁[S] F₂ where
  toPositiveLinearMap := f.toPositiveLinearMap.restrict h
  map_one' := by
    ext
    simp [h₁, h₂]

end Restrict

section SelfAdjoint

variable {A₁ A₂ : Type*}

namespace PositiveLinearMap

-- We will use `IsSelfAdjoint.map` to prove that positive linear maps preserve self-adjointness.
-- That theorem uses a `StarHomClass` instance for PLMs, which exists in Mathlib
-- under the assumptions below. The instance is defined at the end of the
-- `Mathlib.LinearAlgebra.Complex.Module` file.
variable
    [AddCommGroup A₁] [PartialOrder A₁] [StarAddMonoid A₁]
    [NonUnitalRing A₂] [PartialOrder A₂] [StarRing A₂]
    [SelfAdjointDecompose A₁]
    [Module ℂ A₁] [Module ℂ A₂]
    [StarModule ℂ A₁] [StarModule ℂ A₂]
    [StarOrderedRing A₂]

open selfAdjoint

/-- A positive linear map defines a positive linear map between self-adjoint elements -/
noncomputable def restrictSA (f : A₁ →ₚ[ℂ] A₂) : selfAdjoint A₁ →ₚ[ℝ] selfAdjoint A₂ :=
  submodulePLM.comp <| (f.restrict (by simp_all [IsSelfAdjoint.map])).comp <| submodulePLM_symm ℝ

@[simp, norm_cast]
theorem coe_restrictSA_apply (f : A₁ →ₚ[ℂ] A₂) (x : selfAdjoint A₁) :
    ↑(f.restrictSA x) = f ↑x := by
  simp [restrictSA]

section Complex

open Complex ComplexOrder ComplexConjugate

/-- A positive linear map into `ℂ` defines a positive linear map from the
self-adjoint elements to `ℝ` -/
noncomputable def restrictSAC (f : A₁ →ₚ[ℂ] ℂ) : selfAdjoint A₁ →ₚ[ℝ] ℝ :=
  Complex.selfAdjointUPLM.toPositiveLinearMap.comp f.restrictSA

@[simp, norm_cast]
theorem coe_restrictSAC_apply (f : A₁ →ₚ[ℂ] ℂ) (x : selfAdjoint A₁) :
    (f.restrictSAC x : ℂ) = f (x : A₁) := by
  have : conj (f x) = f x := by
    rw [← star_def, ← isSelfAdjoint_iff]
    exact IsSelfAdjoint.map isSelfAdjoint f
  simpa [restrictSAC] using (conj_eq_iff_re.mp this)

end Complex

end PositiveLinearMap

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

/-- A unital positive linear map defines a unital positive linear map between
self-adjoint elements -/
noncomputable def restrictSA (f : A₁ →ₚ₁[ℂ] A₂) : selfAdjoint A₁ →ₚ₁[ℝ] selfAdjoint A₂ :=
  submoduleUPLM.comp <|
    (f.restrict val_one val_one (by simp_all [IsSelfAdjoint.map])).comp
      <| submoduleUPLM_symm ℝ

@[simp, norm_cast]
theorem coe_restrictSA_apply (f : A₁ →ₚ₁[ℂ] A₂) (x : selfAdjoint A₁) :
    ↑(f.restrictSA x) = f ↑x := by
  simp [restrictSA]

open Complex ComplexOrder ComplexConjugate

/-- A unital positive linear map into `ℂ` defines a unital positive linear map from the
self-adjoint elements to `ℝ` -/
noncomputable def restrictSAC (f : A₁ →ₚ₁[ℂ] ℂ) : selfAdjoint A₁ →ₚ₁[ℝ] ℝ :=
  Complex.selfAdjointUPLM.comp f.restrictSA

@[simp, norm_cast]
theorem coe_restrictSAC_apply (f : A₁ →ₚ₁[ℂ] ℂ) (x : selfAdjoint A₁) :
    (f.restrictSAC x : ℂ) = f (x : A₁) := by
  have : conj (f x) = f x := by
    rw [← star_def, ← isSelfAdjoint_iff]
    exact IsSelfAdjoint.map isSelfAdjoint f
  simpa [restrictSAC] using (conj_eq_iff_re.mp this)

end UnitalPositiveLinearMap

end SelfAdjoint
