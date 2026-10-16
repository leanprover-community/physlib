/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Physlib.ClassicalMechanics.ConfigurationSpace.Basic
public import Physlib.SpaceAndTime.Time.Derivatives

/-!
# Lagrangian systems

Lagrangians on `TM` and critical points of the action.

## i. Overview

The motions of a Lagrangian system are the critical points of its action.

## ii. Key results

- `Variation` : smooth variations fixing the endpoints.
- `LagrangianSystem` : smooth time-dependent Lagrangians on `TM`.
- `LagrangianSystem.action` : the action of a curve.
- `LagrangianSystem.IsCriticalPoint` : critical points of the action.

## iii. Table of contents

- A. Lagrangian systems

## iv. References

* V. I. Arnold, Mathematical Methods of Classical Mechanics. [ref: arnold_mechanics]
* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
-/

@[expose] public section

namespace ClassicalMechanics

open MeasureTheory
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : ConfigurationSpace I)

/-!
## A. Lagrangian systems
-/

variable {M} in
/-- A smooth variation of `γ` on `[t₀, t₁]` fixing `γ t₀` and `γ t₁`. -/
@[ext]
structure Variation (γ : Time → M) (t₀ t₁ : Time) where
  /-- The smooth family of curves. -/
  toFun : C^∞⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, Time), ℝ × Time; I, M⟯
  /-- Starts at `γ`. -/
  apply_zero : ∀ t ∈ Set.Icc t₀ t₁, toFun (0, t) = γ t
  /-- Fixes `γ t₀`. -/
  apply_left : ∀ s, toFun (s, t₀) = γ t₀
  /-- Fixes `γ t₁`. -/
  apply_right : ∀ s, toFun (s, t₁) = γ t₁

variable {I M} in
/-- A smooth curve admits the constant variation. -/
lemma Variation.nonempty {γ : Time → M} {t₀ t₁ : Time} (hγ : ContMDiff 𝓘(ℝ, Time) I ∞ γ) :
    Nonempty (Variation I γ t₀ t₁) :=
  ⟨⟨⟨fun p ↦ γ p.2, hγ.comp contMDiff_snd⟩, fun _ _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩⟩

/-- A smooth time-dependent Lagrangian on `TM`. -/
abbrev LagrangianSystem := C^∞⟮𝓘(ℝ, Time).prod I.tangent, Time × TangentBundle I M; ℝ⟯

namespace LagrangianSystem

/-- The Lagrangian system on a normed space `E` given by a smooth `L(t, q, q̇)`. -/
def ofNormedSpace (L : Time × E × E → ℝ) (hL : ContDiff ℝ ∞ L) :
    LagrangianSystem 𝓘(ℝ, E) ⟨E⟩ :=
  ⟨fun p ↦ L (p.1, p.2.1, p.2.2), hL.contMDiff.comp (contMDiff_fst.prodMk_space
    (contMDiff_tangentBundleModelSpaceHomeomorph.comp contMDiff_snd))⟩

variable {I M} (S : LagrangianSystem I M) {γ : Time → M} {t₀ t₁ : Time}

/-- The action `∫ L(t, γ, γ̇) dt` over `[t₀, t₁]`. -/
noncomputable def action (γ : Time → M) (t₀ t₁ : Time) : ℝ :=
  ∫ t in Set.Icc t₀ t₁, S (t, tangentMap 𝓘(ℝ, Time) I γ ⟨t, (1 : Time)⟩)

/-- `γ` is smooth and every variation has zero first variation of the action. -/
def IsCriticalPoint (γ : Time → M) (t₀ t₁ : Time) : Prop :=
  ContMDiff 𝓘(ℝ, Time) I ∞ γ ∧ ∀ h : Variation I γ t₀ t₁,
    HasDerivAt (fun s ↦ S.action (fun t ↦ h.toFun (s, t)) t₀ t₁) 0 0

/-- The action over an empty or one-point interval vanishes. -/
lemma action_eq_zero_of_le (h : t₁ ≤ t₀) : S.action γ t₀ t₁ = 0 := by
  simp [action, Measure.restrict_eq_zero.2 ((Set.subsingleton_Icc_of_ge h).measure_zero _)]

/-- Every smooth curve is critical over an empty or one-point interval. -/
lemma isCriticalPoint_of_le (hγ : ContMDiff 𝓘(ℝ, Time) I ∞ γ) (h : t₁ ≤ t₀) :
    S.IsCriticalPoint γ t₀ t₁ :=
  ⟨hγ, fun _ ↦ by simp [action_eq_zero_of_le _ h, hasDerivAt_const]⟩

end LagrangianSystem

end ClassicalMechanics
