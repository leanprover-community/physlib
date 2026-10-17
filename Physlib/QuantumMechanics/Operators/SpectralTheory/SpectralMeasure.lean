/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.VectorMeasure.Basic
/-!

# Spectral measures

## i. Overview

A spectral measure `μS` on a measurable space `α` is a σ-additive function `Set α → H →L[ℂ] H`
such that each set is mapped to a star projection on `H`, the empty set and non-measurable sets are
mapped to zero, and `univ` is mapped to the identity.
This is implemented as a structure extending `VectorMeasure α (H →L[ℂ] H)` with additional fields
constraining `μS A` to be a star projection for each set `A` and `μS univ = 1`.

For each `x : H` there is an associated measure `μₓ` given by `μₓ A = ‖μS A x‖² = ⟪x, μS A x⟫ ≤ 1`.

## ii. Key results

- `SpectralMeasure` : A star projection-valued measure.
- `comp_eq_of_inter` : For a spectral measure `μS` and measurable sets `A` and `B`,
    the composition `μS A ∘ μS B = μS (A ∩ B)`.

## iii. Table of contents

- A. Definition
- B. Composition

## iv. References

* None.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap
open MeasureTheory
open Set

instance (H : Type*) [SeminormedAddCommGroup H] [InnerProductSpace ℂ H] :
    HasUniqueDiv (H →L[ℂ] H) where
  nsmul_right_injective n hn := by
    refine Function.HasLeftInverse.injective ⟨fun f ↦ (n : ℂ)⁻¹ • f, fun x ↦ ?_⟩
    simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_ne_zero (R := ℂ), hn]

/-!
## A. Definition
-/

/-- A _spectral measure_ on a measurable space `α` is a σ-additive function `Set α → H →L[ℂ] H`
  such that each set is mapped to a star projection on `H`, the empty set and non-measurable sets
  are mapped to zero, and `univ` is mapped to the identity. -/
structure SpectralMeasure
    (α : Type*) [MeasurableSpace α]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends VectorMeasure α (H →L[ℂ] H) where
  isStarProjection' : ∀ A, IsStarProjection (measureOf' A)
  univ' : measureOf' univ = 1

namespace SpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μS : SpectralMeasure α H)

attribute [coe] toVectorMeasure

instance instCoeVectorMeasure : Coe (SpectralMeasure α H) (VectorMeasure α (H →L[ℂ] H)) :=
  ⟨toVectorMeasure⟩

instance instCoeFun : CoeFun (SpectralMeasure α H) fun _ ↦ Set α → H →L[ℂ] H :=
  ⟨fun μS ↦ ⇑μS.toVectorMeasure⟩

lemma isStarProjection (A : Set α) : IsStarProjection (μS A) := μS.isStarProjection' A

@[simp]
lemma univ : μS univ = 1 := μS.univ'

/-!
## B. Composition
-/

@[simp]
lemma comp_self (A : Set α) : μS A ∘L μS A = μS A := (μS.isStarProjection A).isIdempotentElem

lemma comp_of_disjoint
    {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μS A ∘L μS B = 0 := by
  suffices μS A ∘L μS (A ∪ B) = μS A by simp_all [μS.of_union]
  refine (IsStarProjection.sub_iff_mul_eq_left (μS.isStarProjection A)
    (μS.isStarProjection (A ∪ B))).mp ?_
  simpa [μS.of_union h hA hB] using μS.isStarProjection B

lemma comp_eq_of_inter {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μS A ∘L μS B = μS (A ∩ B) := by
  nth_rw 1 [← inter_union_sdiff B A, ← inter_union_sdiff A B]
  simp only [μS.of_union, hA.inter hB, hB.inter hA, hA.diff hB, hB.diff hA,
    disjoint_sdiff_inter.symm, add_comp, comp_add]
  rw [inter_comm B A, μS.comp_of_disjoint disjoint_sdiff_inter (hA.diff hB) (hA.inter hB),
    inter_comm A B, μS.comp_of_disjoint disjoint_sdiff_inter.symm (hB.inter hA) (hB.diff hA)]
  simp [μS.comp_of_disjoint disjoint_sdiff_sdiff (hA.diff hB) (hB.diff hA)]

lemma commute (A B : Set α) : Commute (μS A) (μS B) := by
  by_cases hAB : MeasurableSet A ∧ MeasurableSet B
  · simp [commute_iff_eq, mul_def, comp_eq_of_inter, hAB, inter_comm]
  · rcases not_and_or.mp hAB with hA | hB <;> simp [*]

end SpectralMeasure

end
