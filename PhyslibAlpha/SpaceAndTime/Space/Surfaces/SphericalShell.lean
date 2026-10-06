/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.SpaceAndTime.Space.ConstantSliceDist
public import Physlib.SpaceAndTime.Space.Norm.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-!

# Spherical surfaces on Space

The unit sphere in `Space d` with its measure and the distribution of integration over it.

## i. Overview

The spherical shell is the unit sphere `S^{d-1}` of `Space d`, included by `sphericalShell d`.
Pushing forward the sphere measure gives `sphericalShellMeasure d`, and integrating against it
gives the distribution `sphericalShellDist d`, which one can roughly think of as taking a test
function to its integral against a mass, charge or current distribution on the shell.

## ii. Key results

- `sphericalShell` : the inclusion of the unit sphere into `Space d`.
- `sphericalShellMeasure` : the measure corresponding to integration over the spherical shell.
- `sphericalShellDist` : the distribution corresponding to integration over the spherical shell.

## iii. Table of contents

- A. The definition of the spherical shell surface
- B. The measure associated with the spherical shell
- C. The distribution associated with the spherical shell

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

## A. The definition of the spherical shell surface

-/

/-- The inclusion into `Space d` of its unit sphere `S^{d-1}` (the subtype coercion `x ↦ x.1`). -/
def sphericalShell (d : ℕ) : Metric.sphere (0 : Space d) 1 → Space d := fun x => x.1

lemma sphericalShell_injective (d : ℕ) : Function.Injective (sphericalShell d) := by
  intro x y h
  simp [sphericalShell] at h
  grind

lemma sphericalShell_continuous (d : ℕ) : Continuous (sphericalShell d) := continuous_subtype_val

lemma sphericalShell_measurableEmbedding (d : ℕ) : MeasurableEmbedding (sphericalShell d) := by
  apply Continuous.measurableEmbedding
  · exact sphericalShell_continuous d
  · exact sphericalShell_injective d

@[simp]
lemma norm_sphericalShell (d : ℕ) (x : Metric.sphere (0 : Space d) 1) :
    ‖sphericalShell d x‖ = 1 := by
  simp [sphericalShell, Metric.sphere]

/-!

## B. The measure associated with the spherical shell

-/

/-- The measure on `Space d` corresponding to integration around a spherical shell. -/
def sphericalShellMeasure (d : ℕ) : Measure (Space d) :=
  MeasureTheory.Measure.map (sphericalShell d) (MeasureTheory.Measure.toSphere volume)

instance sphericalShellMeasure_hasTemperateGrowth (d : ℕ) :
    (sphericalShellMeasure d).HasTemperateGrowth := by
  rw [sphericalShellMeasure]
  refine { exists_integrable := ?_ }
  use 0
  simp

/-!

## C. The distribution associated with the spherical shell

-/

/-- The distribution associated with a spherical shell.
  One can roughly think of this distribution as the distribution which
  takes test functions `f (r)` to `∫ d³r f(r) ρ(r)` where `ρ(r)` is the
  mass, charge or current etc. distribution. -/
def sphericalShellDist (d : ℕ) : (Space d) →d[ℝ] ℝ  :=
  SchwartzMap.integralCLM ℝ (sphericalShellMeasure d)


lemma sphericalShellDist_apply_eq_integral_sphericalShellMeasure (d : ℕ) (f : 𝓢(Space d, ℝ)) :
    sphericalShellDist d f = ∫ x, f x ∂sphericalShellMeasure d := by
  rw [sphericalShellDist, SchwartzMap.integralCLM_apply]

lemma sphericalShellDist_apply_eq_integral_sphere_volume (d : ℕ) (f : 𝓢(Space d, ℝ)) :
    sphericalShellDist d f =
    ∫ x, f (sphericalShell d x) ∂(MeasureTheory.Measure.toSphere volume) := by
  rw [sphericalShellDist_apply_eq_integral_sphericalShellMeasure, sphericalShellMeasure,
   MeasurableEmbedding.integral_map (sphericalShell_measurableEmbedding d)]

end Space
