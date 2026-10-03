/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.Line
/-!

# Half-plane surface in `Space 3`

The half-plane in `Space 3` with its measure, distribution and vanishing ambient volume.

## i. Overview

The half-plane is the coordinate plane in `Space 3` with nonnegative second
coordinate. It is the image of the domain `halfPlaneDomain` in `Space 2` under the coordinate
plane embedding `halfPlane`. Pushing forward the restricted volume gives the measure
`halfPlaneMeasure`, and integrating against it gives the distribution `halfPlaneDist`. The
half-plane lies in a proper linear subspace, so it has ambient volume zero.

## ii. Key results

- `halfPlaneDomain` : the domain of the half-plane inside `Space 2`.
- `halfPlane` : the coordinate plane embedding of `Space 2` into `Space 3`.
- `halfPlaneMeasure` : the measure corresponding to integration over the half-plane.
- `halfPlaneDist` : the distribution corresponding to integration over the half-plane.
- `volume_halfPlane_image_domain` : the half-plane has ambient volume zero.

## iii. Table of contents

- A. The definition of the half-plane surface
- B. The measure associated with the half-plane
- C. The distribution associated with the half-plane
- D. The half-plane has ambient volume zero

## iv. References

* None.

-/

@[expose] public section
open SchwartzMap NNReal
noncomputable section
open Physlib Distribution
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory Real

/-!

## A. The definition of the half-plane surface

-/

/-- The domain of the half-plane inside `Space 2`. -/
def halfPlaneDomain : Set (Space 2) := {x | 0 ≤ x (1 : Fin 2)}

/-- The coordinate plane embedding used for the half-plane surface in `Space 3`. -/
def halfPlane : Space 2 → Space 3 := fun x => (slice (2 : Fin 3)).symm (0, x)

lemma halfPlane_eq : halfPlane = (slice (2 : Fin 3)).symm ∘ (fun x : Space 2 => (0, x)) := rfl

lemma halfPlane_injective : Function.Injective halfPlane := by
  intro x y h
  have h' := congrArg (slice (2 : Fin 3)) h
  simp [halfPlane] at h'
  exact h'

@[fun_prop]
lemma halfPlane_continuous : Continuous halfPlane := by
  rw [halfPlane_eq]
  fun_prop

lemma halfPlane_measurableEmbedding : MeasurableEmbedding halfPlane :=
  Continuous.measurableEmbedding halfPlane_continuous halfPlane_injective

@[simp]
lemma norm_halfPlane (x : Space 2) : ‖halfPlane x‖ = ‖x‖ := by
  rw [halfPlane, norm_slice_symm_eq]
  simp

/-!

## B. The measure associated with the half-plane

-/

/-- The measure on `Space 3` corresponding to integration over a half-plane. -/
def halfPlaneMeasure : Measure (Space 3) :=
  MeasureTheory.Measure.map halfPlane (volume.restrict halfPlaneDomain)

instance halfPlaneMeasure_hasTemperateGrowth :
    halfPlaneMeasure.HasTemperateGrowth := by
  rw [halfPlaneMeasure]
  refine { exists_integrable := ?_ }
  obtain ⟨n, hn⟩ := MeasureTheory.Measure.HasTemperateGrowth.exists_integrable
    (μ := volume (α := Space 2))
  use n
  rw [MeasurableEmbedding.integrable_map_iff halfPlane_measurableEmbedding]
  convert! hn.restrict using 1
  ext x
  simp [norm_halfPlane]

instance halfPlaneMeasure_sFinite : SFinite halfPlaneMeasure := by
  rw [halfPlaneMeasure]
  exact Measure.instSFiniteMap (volume.restrict halfPlaneDomain) halfPlane

/-!

## C. The distribution associated with the half-plane

-/

/-- The distribution on `Space 3` corresponding to integration over a half-plane. -/
def halfPlaneDist : (Space 3) →d[ℝ] ℝ :=
  SchwartzMap.integralCLM ℝ halfPlaneMeasure

lemma halfPlaneDist_apply_eq_integral_halfPlaneMeasure (f : 𝓢(Space 3, ℝ)) :
    halfPlaneDist f = ∫ x, f x ∂halfPlaneMeasure := by
  rw [halfPlaneDist, SchwartzMap.integralCLM_apply]

lemma halfPlaneDist_apply_eq_integral_volume (f : 𝓢(Space 3, ℝ)) :
    halfPlaneDist f = ∫ x, f (halfPlane x) ∂(volume.restrict halfPlaneDomain) := by
  rw [halfPlaneDist_apply_eq_integral_halfPlaneMeasure, halfPlaneMeasure,
    MeasurableEmbedding.integral_map halfPlane_measurableEmbedding]

/-!

## D. The half-plane has ambient volume zero

-/

/-- The coordinate plane containing the half-plane in `Space 3`. -/
def halfPlaneSubmodule : Submodule ℝ (Space 3) where
  carrier := {x | x (2 : Fin 3) = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    rw [Set.mem_ofPred_eq] at hx hy ⊢
    rw [Space.add_apply, hx, hy, add_zero]
  smul_mem' c x hx := by
    rw [Set.mem_ofPred_eq] at hx ⊢
    rw [Space.smul_apply, hx, mul_zero]

lemma halfPlane_mem_halfPlaneSubmodule (x : Space 2) : halfPlane x ∈ halfPlaneSubmodule := by
  simp [halfPlaneSubmodule, halfPlane]

lemma halfPlane_image_domain_subset_halfPlaneSubmodule :
    halfPlane '' halfPlaneDomain ⊆ (halfPlaneSubmodule : Set (Space 3)) := by
  rintro x ⟨y, _, rfl⟩
  exact halfPlane_mem_halfPlaneSubmodule y

lemma halfPlaneSubmodule_ne_top : halfPlaneSubmodule ≠ ⊤ := by
  intro htop
  have hbasis : basis (2 : Fin 3) ∈ halfPlaneSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  simp [halfPlaneSubmodule] at hbasis

lemma volume_halfPlane_image_domain :
    volume (halfPlane '' halfPlaneDomain : Set (Space 3)) = 0 := by
  refine measure_mono_null halfPlane_image_domain_subset_halfPlaneSubmodule ?_
  rw [volume_eq_addHaar]
  exact MeasureTheory.Measure.addHaar_submodule
    (Space.basis.toBasis.addHaar : Measure (Space 3))
    halfPlaneSubmodule halfPlaneSubmodule_ne_top

end Space
