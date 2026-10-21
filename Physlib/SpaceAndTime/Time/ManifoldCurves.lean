/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Physlib.SpaceAndTime.Time.Basic

/-!
# Curves in normed spaces over `Time`

A curve `Time → F` is smooth, or has a given derivative, iff its coordinate curve does.

## i. Overview

The charts of `Time` are translations, so the coordinate curve `τ ↦ γ (τ +ᵥ t₀)` needs no origin.

## ii. Key results

- `Time.contMDiff_iff_contDiff_vadd`: a curve is `C^n` iff its coordinate curve is
- `Time.mfderiv_eq_deriv_vadd`: the manifold derivative is the derivative of the coordinate curve
- `Time.tangentMap_eq_deriv_vadd`: the tangent map of a curve in coordinates

## iii. Table of contents

- A. Smoothness and differentiability of curves
- B. Derivatives of curves

## iv. References

* None.
-/

@[expose] public section

open scoped Manifold ContDiff
namespace Time

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-!
## A. Smoothness and differentiability of curves
-/

/-- Continuity of the coordinate curve at `0` gives continuity at `x`. -/
private lemma continuousAt_of_continuousAt_vadd {X : Type*} [TopologicalSpace X]
    {γ : Time → X} {x : Time} (h : ContinuousAt (fun τ : ℝ ↦ γ (τ +ᵥ x)) 0) : ContinuousAt γ x := by
  have h' : ContinuousAt (fun τ : ℝ ↦ γ (τ +ᵥ x)) (x -ᵥ x) := by simpa using h
  have hv : ContinuousAt (fun y : Time ↦ y -ᵥ x) x := continuousAt_id.vsub continuousAt_const
  simpa only [Function.comp_def, vsub_vadd] using
    (h'.comp_of_eq hv rfl :
      ContinuousAt ((fun τ : ℝ ↦ γ (τ +ᵥ x)) ∘ fun y : Time ↦ y -ᵥ x) x)

/-- A curve into a normed space is `C^n` at `x` iff its coordinate curve is `C^n` at `0`. -/
lemma contMDiffAt_iff_contDiffAt_vadd (γ : Time → F) (x : Time) (n : ℕ∞ω) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) n γ x ↔ ContDiffAt ℝ n (fun τ : ℝ ↦ γ (τ +ᵥ x)) 0 := by
  rw [contMDiffAt_iff]
  simpa [Function.comp_def, contDiffWithinAt_univ] using fun h ↦
    continuousAt_of_continuousAt_vadd h.continuousAt

/-- A curve into a normed space is differentiable at `x` iff its coordinate curve is at `0`. -/
lemma mdifferentiableAt_iff_differentiableAt_vadd (γ : Time → F) (x : Time) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ x ↔ DifferentiableAt ℝ (fun τ : ℝ ↦ γ (τ +ᵥ x)) 0 := by
  rw [mdifferentiableAt_iff]
  simpa [Function.comp_def, differentiableWithinAt_univ] using fun h ↦
    continuousAt_of_continuousAt_vadd h.continuousAt

/-- Shifting the base instant by `s` shifts the coordinate curve by `s`. -/
private lemma vadd_vadd_comp {X : Type*} (γ : Time → X) (t₀ : Time) (s : ℝ) :
    (fun τ : ℝ ↦ γ (τ +ᵥ (s +ᵥ t₀))) = fun τ ↦ (fun σ : ℝ ↦ γ (σ +ᵥ t₀)) (τ + s) := by
  ext τ; simp [add_vadd]

/-- A curve `γ : Time → F` into a normed space is `C^n` iff the coordinate curve
`τ ↦ γ (τ +ᵥ t₀)` is `C^n`. -/
lemma contMDiff_iff_contDiff_vadd (γ : Time → F) (t₀ : Time) (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) n γ ↔ ContDiff ℝ n (fun τ : ℝ ↦ γ (τ +ᵥ t₀)) := by
  rw [contDiff_iff_contDiffAt]
  refine ⟨fun h s ↦ ?_, fun h x ↦ ?_⟩
  · have h' : ContDiffAt ℝ n (fun τ : ℝ ↦ γ (τ +ᵥ (s +ᵥ t₀))) ((fun τ : ℝ ↦ τ - s) s) := by
      simpa [← contMDiffAt_iff_contDiffAt_vadd] using h _
    simpa [vadd_vadd_comp, Function.comp_def] using
      h'.comp s (f := fun τ : ℝ ↦ τ - s) (contDiffAt_id.sub contDiffAt_const)
  · rw [contMDiffAt_iff_contDiffAt_vadd, ← vsub_vadd x t₀, vadd_vadd_comp]
    exact ContDiffAt.comp (g := fun σ : ℝ ↦ γ (σ +ᵥ t₀)) 0 (by simpa using h _)
      (contDiffAt_id.add contDiffAt_const)

/-- A curve into a normed space is differentiable at `s +ᵥ t₀` iff its coordinate curve based
at `t₀` is differentiable at `s`. -/
lemma mdifferentiableAt_vadd_iff (γ : Time → F) (t₀ : Time) (s : ℝ) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ (s +ᵥ t₀) ↔
      DifferentiableAt ℝ (fun τ : ℝ ↦ γ (τ +ᵥ t₀)) s := by
  rw [mdifferentiableAt_iff_differentiableAt_vadd, vadd_vadd_comp]
  exact (differentiableAt_comp_add_const (f := fun σ : ℝ ↦ γ (σ +ᵥ t₀))).trans (by rw [zero_add])

/-!
## B. Derivatives of curves
-/

/-- A curve read in the extended chart at `x` is its coordinate curve based at `x`. -/
lemma writtenInExtChartAt_eq_vadd (γ : Time → F) (x : Time) :
    writtenInExtChartAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) x γ = fun τ : ℝ ↦ γ (τ +ᵥ x) := by
  ext τ; simp [writtenInExtChartAt]

/-- The manifold derivative of a curve into a normed space at `s +ᵥ t₀` applied to `1`
equals the ordinary derivative of the coordinate curve at `s`. -/
lemma mfderiv_eq_deriv_vadd (γ : Time → F) (t₀ : Time) (s : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ (s +ᵥ t₀) (1 : ℝ) = deriv (fun τ : ℝ ↦ γ (τ +ᵥ t₀)) s := by
  by_cases h : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ (s +ᵥ t₀)
  · simp only [mfderiv, h, ↓reduceIte, writtenInExtChartAt_eq_vadd, extChartAt_apply,
      ModelWithCorners.range_eq_univ, fderivWithin_univ]
    rw [vsub_self]
    change fderiv ℝ (fun τ : ℝ ↦ γ (τ +ᵥ (s +ᵥ t₀))) 0 1 = _
    rw [fderiv_apply_one_eq_deriv, vadd_vadd_comp]
    exact (deriv_comp_add_const (f := fun σ : ℝ ↦ γ (σ +ᵥ t₀)) s 0).trans (by rw [zero_add])
  · rw [mfderiv_zero_of_not_mdifferentiableAt h,
      deriv_zero_of_not_differentiableAt
        ((mdifferentiableAt_vadd_iff γ t₀ s).not.1 h)]
    rfl

/-- The tangent map of a curve into a normed space sends `⟨s +ᵥ t₀, 1⟩` to the point and
the ordinary derivative of the coordinate curve. -/
lemma tangentMap_eq_deriv_vadd (γ : Time → F) (t₀ : Time) (s : ℝ) :
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ ⟨s +ᵥ t₀, (1 : ℝ)⟩ =
      ⟨γ (s +ᵥ t₀), deriv (fun τ : ℝ ↦ γ (τ +ᵥ t₀)) s⟩ := by
  simp [tangentMap, mfderiv_eq_deriv_vadd γ t₀ s]
  rfl

end Time
