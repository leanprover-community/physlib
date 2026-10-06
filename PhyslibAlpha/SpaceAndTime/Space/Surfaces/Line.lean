/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module
public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.SphericalShell
public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
/-!

# Line surfaces in `Space d`

The coordinate line in `Space d` with its measure, distribution and vanishing ambient volume.

## i. Overview

The line surface is the coordinate line in `Space d`, the image of `ℝ` under the embedding
`line d`. Pushing forward the volume on `ℝ` gives the measure `lineMeasure d`, and integrating
against it gives the distribution `lineDist d`, roughly the integral of a test function against a
density concentrated on a line. For `2 ≤ d` the line lies in a proper linear subspace, so it has
ambient volume zero.

## ii. Key results

- `line` : the coordinate line embedded in `Space d`.
- `lineMeasure` : the measure corresponding to integration along the line.
- `lineDist` : the distribution corresponding to integration along the line.
- `lineSubmodule` : the linear subspace spanned by the line.
- `volume_line_range` : for `2 ≤ d` the line has ambient volume zero.

## iii. Table of contents

- A. The definition of the line surface
- B. The measure associated with the line
- C. The distribution associated with the line
- D. The line has ambient volume zero

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

## A. The definition of the line surface

-/

/-- The coordinate line embedded in `Space d`. -/
def line (d : ℕ) [NeZero d] : ℝ → Space d := fun r =>
  r • basis (0 : Fin d)

lemma line_eq_smul_basis (d : ℕ) [NeZero d] :
    line d = fun r => r • basis (0 : Fin d) := rfl

lemma line_injective (d : ℕ) [NeZero d] : Function.Injective (line d) := by
  intro x y h
  have h0 := congrArg (fun p : Space d => p (0 : Fin d)) h
  simpa [line] using h0

@[fun_prop]
lemma line_continuous (d : ℕ) [NeZero d] : Continuous (line d) := by
  rw [line_eq_smul_basis]
  fun_prop

lemma line_measurableEmbedding (d : ℕ) [NeZero d] : MeasurableEmbedding (line d) :=
  Continuous.measurableEmbedding (line_continuous d) (line_injective d)

@[simp]
lemma norm_line (d : ℕ) [NeZero d] (r : ℝ) : ‖line d r‖ = ‖r‖ := by
  rw [line, norm_smul]
  simp

/-!

## B. The measure associated with the line

-/

/-- The measure on `Space d` corresponding to integration along a coordinate line. -/
def lineMeasure (d : ℕ) [NeZero d] : Measure (Space d) :=
  MeasureTheory.Measure.map (line d) volume

instance lineMeasure_hasTemperateGrowth (d : ℕ) [NeZero d] :
    (lineMeasure d).HasTemperateGrowth := by
  rw [lineMeasure]
  refine { exists_integrable := ?_ }
  obtain ⟨r, hr⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := volume (α := ℝ))
  use r
  rw [MeasurableEmbedding.integrable_map_iff]
  · convert hr using 1
    ext x
    simp [norm_line]
  · exact line_measurableEmbedding d

/-!

## C. The distribution associated with the line

-/

/-- The distribution on `Space d` corresponding to integration along a coordinate line.
  One can roughly think of this distribution as taking a test function `f` to its integral against
  a mass, charge or current density concentrated on a line. -/
def lineDist (d : ℕ) [NeZero d] : (Space d) →d[ℝ] ℝ :=
  SchwartzMap.integralCLM ℝ (lineMeasure d)

lemma lineDist_apply_eq_integral_lineMeasure (d : ℕ) [NeZero d] (f : 𝓢(Space d, ℝ)) :
    lineDist d f = ∫ x, f x ∂lineMeasure d := by
  rw [lineDist, SchwartzMap.integralCLM_apply]

lemma lineDist_apply_eq_integral_volume (d : ℕ) [NeZero d] (f : 𝓢(Space d, ℝ)) :
    lineDist d f = ∫ r : ℝ, f (line d r) := by
  rw [lineDist_apply_eq_integral_lineMeasure, lineMeasure,
    MeasurableEmbedding.integral_map (line_measurableEmbedding d)]

/-!

## D. The line has ambient volume zero

-/

/-- The linear subspace spanned by the coordinate line in `Space d`. -/
def lineSubmodule (d : ℕ) [NeZero d] : Submodule ℝ (Space d) :=
  ℝ ∙ basis (0 : Fin d)

lemma line_mem_lineSubmodule (d : ℕ) [NeZero d] (r : ℝ) : line d r ∈ lineSubmodule d := by
  rw [line_eq_smul_basis]
  exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self (basis (0 : Fin d)))

lemma range_line_subset_lineSubmodule (d : ℕ) [NeZero d] :
    Set.range (line d) ⊆ (lineSubmodule d : Set (Space d)) := by
  rintro x ⟨r, rfl⟩
  exact line_mem_lineSubmodule d r

lemma lineSubmodule_ne_top (d : ℕ) [NeZero d] (hd : 2 ≤ d) : lineSubmodule d ≠ ⊤ := by
  intro htop
  have hbasis : basis (1 : Fin d) ∈ lineSubmodule d := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton.mp hbasis)
  have hcoord := congrArg (fun p : Space d => p (1 : Fin d)) hc
  have hd1 : d ≠ 1 := by omega
  simp [basis_apply, hd1] at hcoord

lemma volume_line_range (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    volume (Set.range (line d) : Set (Space d)) = 0 := by
  refine measure_mono_null (range_line_subset_lineSubmodule d) ?_
  rw [volume_eq_addHaar]
  exact MeasureTheory.Measure.addHaar_submodule
    (Space.basis.toBasis.addHaar : Measure (Space d))
    (lineSubmodule d) (lineSubmodule_ne_top d hd)

end Space
