/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Convex

/-!

# Pure states

## i. Overview

Pure states are extreme points of the general convex state space. Equivalently, they cannot be
written as a genuine mixture of other states.

## ii. Key definitions and results

- `UnitalPositiveLinearMap.IsPure`
- `UnitalPositiveLinearMap.isPure_iff_binary_decompositions_trivial`
- `UnitalPositiveLinearMap.not_isPure_iff_nontrivial_binary_decomposition`

## iii. Table of contents

- A. Pure states
- B. Binary-decomposition characterizations

-/

@[expose] public section

open scoped ComplexOrder

namespace UnitalPositiveLinearMap

variable {A : Type*} [AddCommGroup A] [PartialOrder A] [IsOrderedAddMonoid A]
  [Module ℂ A] [One A]

/-! ## A. Pure states -/

/-- A pure state is an extreme point of the general state space. -/
def IsPure (ω : 𝓢[A]) : Prop :=
  ω.toLinearMap ∈ (stateSpace (A := A)).extremePoints ℝ

/-! ## B. Binary-decomposition characterizations -/

/-- A state is pure exactly when every genuine binary decomposition is trivial. -/
lemma isPure_iff_binary_decompositions_trivial (ω : 𝓢[A]) :
    IsPure ω ↔
      ∀ (φ ψ : 𝓢[A]) (t : unitInterval), t ≠ 0 → t ≠ 1 →
        mix φ ψ t = ω → φ = ω ∧ ψ = ω := by
  simp only [IsPure, mem_extremePoints]
  constructor
  · rintro ⟨-, hext⟩ φ ψ t ht₀ ht₁ hmix
    have hseg := (mem_openSegment_iff_exists_mix ω φ ψ).2 ⟨t, ht₀, ht₁, hmix⟩
    obtain ⟨hφ, hψ⟩ := hext φ.toLinearMap ⟨φ, rfl⟩ ψ.toLinearMap ⟨ψ, rfl⟩ hseg
    exact ⟨toLinearMap_injective hφ, toLinearMap_injective hψ⟩
  · intro h
    refine ⟨⟨ω, rfl⟩, ?_⟩
    rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩ hseg
    obtain ⟨t, ht₀, ht₁, hmix⟩ := (mem_openSegment_iff_exists_mix ω φ ψ).1 hseg
    obtain ⟨rfl, rfl⟩ := h φ ψ t ht₀ ht₁ hmix
    exact ⟨rfl, rfl⟩

/-- A genuine mixture equal to a pure state can only repeat that state at both endpoints. -/
lemma IsPure.eq_of_mix {ω φ ψ : 𝓢[A]} (hω : IsPure ω) (t : unitInterval)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) (hmix : mix φ ψ t = ω) :
    φ = ω ∧ ψ = ω :=
  (isPure_iff_binary_decompositions_trivial ω).mp hω φ ψ t ht₀ ht₁ hmix

/-- A state is mixed exactly when it has a genuine nontrivial binary decomposition. -/
lemma not_isPure_iff_nontrivial_binary_decomposition (ω : 𝓢[A]) :
    ¬ IsPure ω ↔
      ∃ (φ ψ : 𝓢[A]) (t : unitInterval), t ≠ 0 ∧ t ≠ 1 ∧
        mix φ ψ t = ω ∧ (φ ≠ ω ∨ ψ ≠ ω) := by
  rw [isPure_iff_binary_decompositions_trivial]
  push Not
  simp only [imp_iff_not_or]

end UnitalPositiveLinearMap
