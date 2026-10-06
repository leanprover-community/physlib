/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
/-!
# Time

`Time` represents instants with a fixed but arbitrary unit and orientation. It is an
affine space over `ℝ`: two instants determine a real-valued elapsed time, and adding
such a duration to an instant produces another instant. There is no distinguished zero.

The field `Time.val` is an implementation coordinate, not a frame-relative time
coordinate. A reference frame chooses its own time origin. Import
`Physlib.SpaceAndTime.Time.InnerProductSpace` to use the inner product space structure with the
implicit origin `Time.mk 0`, including addition of instants, norms, and derivatives.

-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

/-!
# A. The `Time` type
-/

/-- An instant in time with a given unit and orientation, but no distinguished origin. -/
@[ext]
structure Time where
  /-- The implementation coordinate associated with an instant. -/
  val : ℝ

namespace Time

lemma val_injective : Function.Injective val := fun _ _ h => Time.ext h

instance : Nonempty Time := ⟨⟨0⟩⟩

/-!
# B. The affine structure
-/

instance : VAdd ℝ Time where
  vadd dt t := ⟨dt + t.val⟩

@[simp]
lemma vadd_val (dt : ℝ) (t : Time) : (dt +ᵥ t).val = dt + t.val := rfl

instance : VSub ℝ Time where
  vsub t₁ t₂ := t₁.val - t₂.val

@[simp]
lemma vsub_eq_val (t₁ t₂ : Time) : t₁ -ᵥ t₂ = t₁.val - t₂.val := rfl

instance : AddTorsor ℝ Time where
  zero_vadd t := by ext; simp
  add_vadd dt₁ dt₂ t := by ext; simp [add_assoc]
  vsub_vadd' t₁ t₂ := by ext; simp
  vadd_vsub' dt t := by simp

/-!
# C. The metric and manifold structure
-/

instance : MetricSpace Time := metricSpaceOfNormedAddCommGroupOfAddTorsor ℝ Time

instance : NormedAddTorsor ℝ Time where
  dist_eq_norm' _ _ := rfl

instance : ChartedSpace ℝ Time :=
  let chartAt t := (Homeomorph.vaddConst t).symm.toOpenPartialHomeomorph
  { chartAt,
    atlas := Set.range chartAt,
    mem_chart_source := Set.mem_univ,
    chart_mem_atlas := by simp }

instance : IsManifold 𝓘(ℝ, ℝ) ω Time := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨_, rfl⟩ ⟨_, rfl⟩
  exact contDiff_id.add contDiff_const |>.sub contDiff_const |>.contDiffOn

end Time
