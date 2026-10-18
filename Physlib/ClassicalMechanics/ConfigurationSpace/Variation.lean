/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Physlib.ClassicalMechanics.ConfigurationSpace.Basic
public import Physlib.SpaceAndTime.Time.Basic

/-!
# Variations of curves

Smooth variations of a curve in a configuration space fixing the endpoints.

## i. Overview

Variations probe the action of a Lagrangian system around a curve.

## ii. Key results

- `Variation` : smooth variations fixing the endpoints.

## iii. Table of contents

- A. Variations

## iv. References

* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
-/

@[expose] public section

namespace ClassicalMechanics

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : ConfigurationSpace I)

/-!
## A. Variations
-/

variable {M} in
/-- A smooth variation of `γ` on `[t₀, t₁]` fixing `γ t₀` and `γ t₁`. -/
@[ext]
structure Variation (γ : Time → M) (t₀ t₁ : Time) where
  /-- The smooth family of curves. -/
  toFun : C^∞⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), ℝ × Time; I, M⟯
  /-- Starts at `γ`. -/
  apply_zero : ∀ s ∈ Set.Icc 0 (t₁ -ᵥ t₀), toFun (0, s +ᵥ t₀) = γ (s +ᵥ t₀)
  /-- Fixes `γ t₀`. -/
  apply_left : ∀ s, toFun (s, t₀) = γ t₀
  /-- Fixes `γ t₁`. -/
  apply_right : ∀ s, toFun (s, t₁) = γ t₁

variable {I M} in
/-- A smooth curve admits the constant variation. -/
lemma Variation.nonempty {γ : Time → M} {t₀ t₁ : Time} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    Nonempty (Variation I γ t₀ t₁) :=
  ⟨⟨⟨fun p ↦ γ p.2, hγ.comp contMDiff_snd⟩, fun _ _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩⟩

end ClassicalMechanics
