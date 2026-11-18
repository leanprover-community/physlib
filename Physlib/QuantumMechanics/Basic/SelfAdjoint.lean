/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Star.Module
public import Physlib.QuantumMechanics.Basic.PositiveLinearMap.Unital

/-!

# Some basic results on `selfAdjoint` elements

Mathlib provides a number of different ways to express the fact that an element
is self-adjoint.  Natural formulations that appear in different contexts are
`IsSelfAdjoint x` and `x ∈ selfAdjoint A`. There are also two ways to talk about
a module structure on the self-adjoint elements: A module instance on
`selfAdjoint A`, and `selfAdjoint.module R A: Submodule A`.

In this file, we collect basic lemmas to convert between these points of view.

-/

@[expose] public section

namespace selfAdjoint

@[simp]
theorem mem_selfAdjoint_iff_isSelfAdjoint {R : Type*} [AddGroup R] [StarAddMonoid R] (x : R) :
    x ∈ selfAdjoint R ↔ IsSelfAdjoint x := isSelfAdjoint_iff.trans selfAdjoint.mem_iff.symm

variable {R A : Type*} [Semiring R] [StarMul R] [TrivialStar R]
  [AddCommGroup A] [Module R A] [StarAddMonoid A] [StarModule R A]

@[simp]
theorem submodule_mem_iff {x : A} : (x ∈ submodule R A) ↔ (x ∈ selfAdjoint A) := by
  rfl

/-- The linear equivalence that forgets the `Submodule` structure on the self-adjoint elements. -/
@[simps!]
def submoduleEquiv : selfAdjoint.submodule R A ≃ₗ[R] selfAdjoint A where
  toFun x := ⟨x.val, submodule_mem_iff.mp x.prop⟩
  invFun x := ⟨x.val, submodule_mem_iff.mpr x.prop⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by ext; simp

variable [PartialOrder A]

/-- Forgetting the `Submodule` structure as a positive linear map. -/
@[simps!]
def submodulePLM : submodule R A →ₚ[R] selfAdjoint A :=
  { selfAdjoint.submoduleEquiv.toLinearMap with monotone' a b hab := by simpa }

variable (R) in
/-- Inverse of `submodulePLM`. (There is no `PositiveLinearEquivalence` type) -/
@[simps!]
def submodulePLM_symm : selfAdjoint A →ₚ[R] submodule R A:=
  { selfAdjoint.submoduleEquiv.symm.toLinearMap with monotone' a b hab := by simpa }

variable {R A : Type*} [Semiring R] [StarMul R] [TrivialStar R]
  [Ring A] [StarRing A] [Module R A] [StarModule R A]

instance : One (submodule R A) :=
  ⟨⟨1, .one _⟩⟩

@[simp] theorem val_one_submodule : ↑(1 : submodule R A) = (1 : A) := rfl
@[simp] theorem submoduleEquiv_one : ↑(submoduleEquiv (R := R) (A := A) 1) = 1 := rfl
@[simp] theorem submoduleEquiv_symm_one : ↑(submoduleEquiv (R := R) (A := A).symm 1) = 1 := rfl

variable [PartialOrder A]

/-- Forgetting the `Submodule` structure as a unital positive linear map. -/
@[simps!]
def submoduleUPLM : submodule R A →ₚ₁[R] selfAdjoint A :=
  { submoduleEquiv.toLinearMap with monotone' a b hab := by simpa, map_one' := by simp }

variable (R) in
/-- Inverse of `submoduleUPLM`. (There is no `UnitalPositiveLinearEquivalence` type) -/
@[simps!]
def submoduleUPLM_symm : selfAdjoint A →ₚ₁[R] submodule R A :=
  { submoduleEquiv.symm.toLinearMap with monotone' a b hab := by simpa, map_one' := by simp }

end selfAdjoint

open ComplexOrder

/-- The map from self-adjoint complex numbers to real numbers as a unital positive linear map. -/
@[simps!]
noncomputable def Complex.selfAdjointUPLM : selfAdjoint ℂ →ₚ₁[ℝ] ℝ where
  toLinearMap := Complex.selfAdjointEquiv.toLinearMap
  monotone' a b hab := by simp; gcongr
  map_one' := by simp
