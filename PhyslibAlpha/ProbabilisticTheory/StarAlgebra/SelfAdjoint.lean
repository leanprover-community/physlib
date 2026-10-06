/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Star.Module
public import PhyslibAlpha.ProbabilisticTheory.Channel.Basic

/-!

# Self-adjoint elements

Relating the predicate, subgroup and submodule descriptions of self-adjoint elements.

## i. Overview

Mathlib describes self-adjointness by the predicate `IsSelfAdjoint`, the additive subgroup
`selfAdjoint A` and a real submodule. This file relates these descriptions.

## ii. Key results

- `selfAdjoint.submoduleEquiv` : the subgroup and the submodule of self-adjoint elements agree.
- `selfAdjoint.submoduleUPLM` : the corresponding channel.

## iii. Table of contents

- A. Membership in the self-adjoint part
- B. Forgetting the submodule structure
- C. The unit and unital maps
- D. Self-adjoint complex numbers

## iv. References

* None.

-/

@[expose] public section

namespace selfAdjoint
open ProbabilisticTheory

/-! ## A. Membership in the self-adjoint part -/

@[simp]
lemma mem_selfAdjoint_iff_isSelfAdjoint {R : Type*} [AddGroup R] [StarAddMonoid R] (x : R) :
    x ∈ selfAdjoint R ↔ IsSelfAdjoint x := isSelfAdjoint_iff.trans selfAdjoint.mem_iff.symm

variable {R A : Type*} [Semiring R] [StarMul R] [TrivialStar R]
  [AddCommGroup A] [Module R A] [StarAddMonoid A] [StarModule R A]

@[simp]
lemma submodule_mem_iff {x : A} : (x ∈ submodule R A) ↔ (x ∈ selfAdjoint A) := by
  rfl

/-! ## B. Forgetting the submodule structure -/

/-- The linear equivalence that forgets the `Submodule` structure on self-adjoint elements. -/
@[simps!]
def submoduleEquiv : selfAdjoint.submodule R A ≃ₗ[R] selfAdjoint A where
  toFun x := ⟨x.val, submodule_mem_iff.mp x.prop⟩
  invFun x := ⟨x.val, submodule_mem_iff.mpr x.prop⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by ext; simp

variable [PartialOrder A]

/-- Forget the `Submodule` structure as a positive linear map. -/
@[simps!]
def submodulePLM : submodule R A →ₚ[R] selfAdjoint A :=
  { selfAdjoint.submoduleEquiv.toLinearMap with monotone' a b hab := by simpa }

variable (R) in
/-- Inverse of `submodulePLM`. (There is no `PositiveLinearEquivalence` type.) -/
@[simps!]
def submodulePLMSymm : selfAdjoint A →ₚ[R] submodule R A :=
  { selfAdjoint.submoduleEquiv.symm.toLinearMap with monotone' a b hab := by simpa }

/-! ## C. The unit and unital maps -/

variable {R A : Type*} [Semiring R] [StarMul R] [TrivialStar R]
  [Ring A] [StarRing A] [Module R A] [StarModule R A]

instance : One (submodule R A) :=
  ⟨⟨1, .one _⟩⟩

@[simp] lemma val_one_submodule : ↑(1 : submodule R A) = (1 : A) := rfl
@[simp] lemma submoduleEquiv_one : ↑(submoduleEquiv (R := R) (A := A) 1) = 1 := rfl
@[simp] lemma submoduleEquiv_symm_one : ↑(submoduleEquiv (R := R) (A := A).symm 1) = 1 := rfl

variable [PartialOrder A]

/-- Forget the `Submodule` structure as a unital positive linear map. -/
def submoduleUPLM : submodule R A →ₚ₁[R] selfAdjoint A :=
  { toPositiveLinearMap :=
      { submoduleEquiv.toLinearMap with monotone' a b hab := by simpa }
    map_one' := rfl }

variable (R) in
/-- Inverse of `submoduleUPLM`. (There is no `UnitalPositiveLinearEquivalence` type.) -/
def submoduleUPLMSymm : selfAdjoint A →ₚ₁[R] submodule R A :=
  { toPositiveLinearMap :=
      { submoduleEquiv.symm.toLinearMap with monotone' a b hab := by simpa }
    map_one' := rfl }

end selfAdjoint

/-! ## D. Self-adjoint complex numbers -/

namespace ProbabilisticTheory

open ComplexOrder

/-- The map from self-adjoint complex numbers to real numbers as a unital positive linear map. -/
@[simps!]
noncomputable def _root_.Complex.selfAdjointUPLM : selfAdjoint ℂ →ₚ₁[ℝ] ℝ where
  toPositiveLinearMap :=
    { toLinearMap := Complex.selfAdjointEquiv.toLinearMap
      monotone' a b hab := by simp; gcongr }
  map_one' := by
    change Complex.selfAdjointEquiv (1 : selfAdjoint ℂ) = 1
    simp

end ProbabilisticTheory
