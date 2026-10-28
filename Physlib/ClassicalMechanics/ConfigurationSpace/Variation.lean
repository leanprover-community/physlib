/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Physlib.ClassicalMechanics.ConfigurationSpace.Basic
public import Physlib.SpaceAndTime.Time.ManifoldCurves

/-!
# Variations of curves

Smooth variations of a curve in a configuration space fixing the endpoints.

## i. Overview

Variations probe the action of a Lagrangian system around a curve.

## ii. Key results

- `Variation` : smooth variations fixing the endpoints.
- `Variation.contDiff_comp_vadd` : a variation of a curve in a normed space is smooth in
  coordinates.
- `Variation.exists_bump` : a bump function gives a variation of a curve in a normed space.

## iii. Table of contents

- A. Variations
- B. Variations in a normed space

## iv. References

* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
-/

@[expose] public section

namespace ClassicalMechanics

open Set
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

namespace Variation

variable {I M} in
/-- A smooth curve admits the constant variation. -/
lemma nonempty {γ : Time → M} {t₀ t₁ : Time} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    Nonempty (Variation I γ t₀ t₁) :=
  ⟨⟨⟨fun p ↦ γ p.2, hγ.comp contMDiff_snd⟩, fun _ _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩⟩

/-!
## B. Variations in a normed space
-/

/-- `(s, τ) ↦ h (s, τ +ᵥ t₀)` is smooth. -/
lemma contDiff_comp_vadd {γ : Time → E} {t₀ t₁ : Time}
    (h : Variation (M := ⟨E⟩) 𝓘(ℝ, E) γ t₀ t₁) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ h.toFun (p.1, p.2 +ᵥ t₀)) := by
  have key (f : ℝ × ℝ → E) (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ f) :
      ContDiff ℝ ∞ f := by
    rwa [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := ℝ),
      chartedSpaceSelf_prod (H := ℝ) (H' := ℝ), contMDiff_iff_contDiff] at hf
  exact key _ (h.toFun.contMDiff.comp
    (contMDiff_fst.prodMk ((Time.contMDiff_vadd t₀ ∞).comp contMDiff_snd)))

/-- For a smooth curve `γ`, smooth `ψ` supported in `(0, t₁ -ᵥ t₀)` and `w : E`, there exists a
variation `h` of `γ` with `h (s, τ +ᵥ t₀) = γ (τ +ᵥ t₀) + s • ψ τ • w`. -/
lemma exists_bump {γ : Time → E} {t₀ t₁ : Time} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ Ioo 0 (t₁ -ᵥ t₀)) (w : E) :
    ∃ h : Variation (M := ⟨E⟩) 𝓘(ℝ, E) γ t₀ t₁,
      ∀ s τ, h.toFun (s, τ +ᵥ t₀) = γ (τ +ᵥ t₀) + s • (ψ τ • w) := by
  have hψt : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : Time ↦ ψ (t -ᵥ t₀)) :=
    (Time.contMDiff_iff_contDiff_vadd _ t₀ ∞).2 (by simpa using hψ)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × Time ↦ γ p.2 + p.1 • (ψ (p.2 -ᵥ t₀) • w)) :=
    ContMDiff.add (hγ.comp contMDiff_snd)
      (contMDiff_fst.smul ((hψt.comp contMDiff_snd).smul contMDiff_const))
  have h0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hs h).1.false
  have hT : ψ (t₁ -ᵥ t₀) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hs h).2.false
  refine ⟨⟨⟨fun p ↦ γ p.2 + p.1 • (ψ (p.2 -ᵥ t₀) • w), hF⟩, fun s _ ↦ ?_, fun s ↦ ?_, fun s ↦ ?_⟩,
    fun s τ ↦ ?_⟩
  · simp
  · simp [h0]
  · simp only [Time.vsub_eq_val] at hT
    simp [hT]
  · simp

end Variation

end ClassicalMechanics
