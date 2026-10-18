/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Physlib.ClassicalMechanics.ConfigurationSpace.Variation
public import Physlib.SpaceAndTime.Time.Basic

/-!
# Lagrangian systems

Lagrangians on `TM` and critical points of the action.

## i. Overview

The motions of a Lagrangian system are the critical points of its action.

## ii. Key results

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

/-- A smooth time-dependent Lagrangian on `TM`, depending on first-order derivatives only. -/
abbrev LagrangianSystem := C^∞⟮𝓘(ℝ, ℝ).prod I.tangent, Time × TangentBundle I M; ℝ⟯

namespace LagrangianSystem

/-- The Lagrangian system on a normed space `E` given by a smooth `L(t, q, q̇)`. -/
def ofNormedSpace (L : Time × E × E → ℝ)
    (hL : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, ℝ) ∞ L) :
    LagrangianSystem 𝓘(ℝ, E) ⟨E⟩ :=
  ⟨fun p ↦ L (p.1, p.2.1, p.2.2), hL.comp (contMDiff_fst.prodMk
    (contMDiff_tangentBundleModelSpaceHomeomorph.comp contMDiff_snd))⟩

variable {I M} (S : LagrangianSystem I M) {γ : Time → M} {t₀ t₁ : Time}

/-- The action `∫ L(t, γ, γ̇) dt` over `[t₀, t₁]`. -/
noncomputable def action (γ : Time → M) (t₀ t₁ : Time) : ℝ :=
  ∫ s in Set.Icc 0 (t₁ -ᵥ t₀), S (s +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I γ ⟨s +ᵥ t₀, (1 : ℝ)⟩)

/-- `γ` is smooth and every variation has zero first variation of the action. -/
def IsCriticalPoint (γ : Time → M) (t₀ t₁ : Time) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ ∀ h : Variation I γ t₀ t₁,
    HasDerivAt (fun s ↦ S.action (fun t ↦ h.toFun (s, t)) t₀ t₁) 0 0

/-- The action over an empty or one-point interval vanishes. -/
lemma action_eq_zero_of_vsub_nonpos (h : t₁ -ᵥ t₀ ≤ 0) : S.action γ t₀ t₁ = 0 :=
  setIntegral_measure_zero _ ((Set.subsingleton_Icc_of_ge h).measure_zero _)

/-- Every smooth curve is critical over an empty or one-point interval. -/
lemma isCriticalPoint_of_vsub_nonpos (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (h : t₁ -ᵥ t₀ ≤ 0) :
    S.IsCriticalPoint γ t₀ t₁ :=
  ⟨hγ, fun _ ↦ by simp [action_eq_zero_of_vsub_nonpos _ h, hasDerivAt_const]⟩

end LagrangianSystem

end ClassicalMechanics
