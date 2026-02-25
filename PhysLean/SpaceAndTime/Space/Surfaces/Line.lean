/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.ConstantSliceDist
/-!


-/
open SchwartzMap NNReal
noncomputable section
open Distribution
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory Real

/-!

## A. The definition of the line surface

-/

/-- The linear isometry corresponding the inclusion of the x-axis line into
  `Space d.succ`. -/
def line (d : ℕ) : Space 1 →ₗᵢ[ℝ] Space d.succ where
  toFun x := {
     val i :=
      match i with
      | 0 => x 0
      | ⟨Nat.succ i, h⟩ => 0}
  map_add' := by
    intro x y
    ext i
    simp only [Nat.succ_eq_add_one, Fin.isValue, add_apply]
    grind
  map_smul' := by
    intro c x
    ext i
    simp only [Nat.succ_eq_add_one, Fin.isValue, smul_apply, RingHom.id_apply]
    grind
  norm_map' := by
    intro x
    simp [Space.norm_eq]
    congr
    rw [Finset.sum_eq_single ⟨0, by simp⟩]
    · grind
    · grind

@[simp]
lemma line_apply_zero (d : ℕ) (x : Space 1) : line d x 0 = x 0 := by
  rfl

@[simp]
lemma line_apply_succ (d : ℕ) (x : Space 1) (i : Fin d) : line d x (Fin.succ i) = 0 := by
  rfl

@[simp]
lemma line_apply_succ' (d : ℕ) (x : Space 1) (i : ℕ) (h : i + 1 < d.succ) : line d x ⟨i + 1, h⟩ = 0 := by
  rfl

lemma line_eq_slice_symm (d : ℕ) (x : Space 1) : line d x = (slice 0).symm (x 0, 0) := by
  ext i
  match i with
  | ⟨0, h⟩ => simp
  | ⟨Nat.succ i, h⟩ =>
    simp [slice_symm_apply]
    rfl

lemma line_measurable (d : ℕ) : Measurable (line d) := by
  apply Continuous.measurable
  exact LinearIsometry.continuous (line d)

lemma line_injective (d : ℕ) : Function.Injective (line d) := by
  intro x y h
  ext i
  fin_cases i
  simp only [Fin.zero_eta, Fin.isValue]
  rw [← line_apply_zero, h]
  simp

lemma line_measurableEmbedding (d : ℕ) : MeasurableEmbedding (line d) := by
  apply Continuous.measurableEmbedding
  · exact LinearIsometry.continuous (line d)
  · exact line_injective d

/-!

## B. The measure associated with the line

-/

/-- The measure on `Space d.succ` corresponding to integration along the `x`-axis. -/
def lineMeasure (d : ℕ) : Measure (Space d.succ) := MeasureTheory.Measure.map (line d) (volume)

instance lineMeasure_hasTemperateGrowth (d : ℕ) : (lineMeasure d).HasTemperateGrowth := by
  simp [lineMeasure]
  refine { exists_integrable := ?_ }
  obtain ⟨n, hn⟩ := MeasureTheory.Measure.HasTemperateGrowth.exists_integrable
    (μ := volume (α := Space 1) )
  use n
  rw [MeasurableEmbedding.integrable_map_iff (line_measurableEmbedding d)]
  change Integrable ((fun x => (1 + ‖⇑(line d) x‖) ^ (- (n : ℝ)))) volume
  simpa using hn
/-!

## C. The distribution associated with the line

-/

/-- The distribution corresponding to integrating over a line.
  Physically, this is the distribution associated with, for example, lines of charges,
  or infinitely thin wires. -/
def lineDist (d : ℕ) : (Space d.succ) →d[ℝ] ℝ :=
  SchwartzMap.integralCLM ℝ (lineMeasure d)

lemma lineDist_apply (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    lineDist d f = ∫ x, f (line d x) ∂(volume (α := Space 1)) := by
  simp [lineDist, SchwartzMap.integralCLM, SchwartzMap.mkCLMtoNormedSpace, lineMeasure]
  rw [MeasurableEmbedding.integral_map (line_measurableEmbedding d)]

lemma lineDist_eq_constantSliceDist_diracDelta (d : ℕ) :
    lineDist d = constantSliceDist 0 (diracDelta ℝ 0) := by
  ext η
  simp only [Nat.succ_eq_add_one, lineDist_apply, line_eq_slice_symm, Fin.isValue,
    constantSliceDist_apply, diracDelta_apply, sliceSchwartz_apply]
  rw [integral_one_dim_eq_integral_real]
  rfl

end Space
