/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.SphericalShell
public import Physlib.SpaceAndTime.Space.Translations
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
/-!

## Ring surface in `Space 3`

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

## A. The definition of the ring surface

-/

/-- The embedding of the unit ring (a circle `S¹` in `Space 2`) into `Space 3`. -/
def ring : Metric.sphere (0 : Space 2) 1 → Space 3 := fun x =>
  (slice 2).symm (0, Space.sphericalShell 2 x)

lemma ring_eq : ring = (slice 2).symm ∘ (fun x => (0, sphericalShell 2 x)) := rfl

lemma ring_injective : Function.Injective ring := by
  intro x y h
  simp [ring] at h
  exact sphericalShell_injective _ h

@[fun_prop]
lemma ring_continuous : Continuous ring := by
  apply Continuous.comp
  · fun_prop
  · fun_prop

lemma ring_measurableEmbedding : MeasurableEmbedding ring :=
  Continuous.measurableEmbedding ring_continuous ring_injective


/-!

## B. The measure associated with the ring

-/

/-- The measure on `Space 3` corresponding to integration around a ring. -/
def ringMeasure : Measure (Space 3) :=
  MeasureTheory.Measure.map ring (MeasureTheory.Measure.toSphere volume)

instance ringMeasure_hasTemperateGrowth :
    ringMeasure.HasTemperateGrowth := by
  rw [ringMeasure]
  refine { exists_integrable := ?_ }
  use 0
  simp

instance ringMeasure_prod_volume_hasTemperateGrowth :
    (ringMeasure.prod (volume (α := Space))).HasTemperateGrowth := by
  infer_instance

instance ringMeasure_sFinite: SFinite ringMeasure := by
  rw [ringMeasure]
  exact Measure.instSFiniteMap volume.toSphere ring

instance ringMeasure_finite: IsFiniteMeasure ringMeasure := by
  rw [ringMeasure]
  exact Measure.isFiniteMeasure_map volume.toSphere ring

lemma integrable_ringMeasure_of_continuous (f : Space → ℝ) (hf : Continuous (f ∘ ring)) :
    Integrable f ringMeasure := by
  rw [ringMeasure]
  rw [MeasurableEmbedding.integrable_map_iff]
  · let f' : BoundedContinuousFunction (Metric.sphere (0 : Space 2) 1) ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨f ∘ ring, hf⟩
    exact BoundedContinuousFunction.integrable _ f'
  · exact ring_measurableEmbedding

lemma integrable_ringMeasure_of_continuous_euclid (f : Space → EuclideanSpace ℝ (Fin n))
    (hf : Continuous (f ∘ ring)) :
    Integrable f ringMeasure := by
  rw [ringMeasure]
  rw [MeasurableEmbedding.integrable_map_iff]
  · exact BoundedContinuousFunction.integrable _
      (BoundedContinuousFunction.mkOfCompact ⟨f ∘ ring, hf⟩)
  · exact ring_measurableEmbedding

lemma ringMeasure_prod_volume_map :
    (ringMeasure.prod (volume (α := Space))).map (fun x : Space × Space => (x.1, x.2 + x.1))
     = (ringMeasure.prod (volume (α := Space))) := by
  refine (MeasureTheory.MeasurePreserving.skew_product (f := id) (g := fun x => fun y => y + x)
    ?_ ?_ ?_).map_eq
  · exact MeasurePreserving.id ringMeasure
  · fun_prop
  · filter_upwards with x
    exact Measure.IsAddRightInvariant.map_add_right_eq_self (x)

@[simp]
lemma ringMeasure_univ : ringMeasure Set.univ = ENNReal.ofReal ((2 : ℝ) * π) := by
  rw [ringMeasure, Measure.map_apply]
  simp only [Set.preimage_univ, Measure.toSphere_apply_univ, finrank_eq_dim, Nat.cast_ofNat,
    volume_metricBall_two, Nat.ofNat_nonneg, ENNReal.ofReal_mul, ENNReal.ofReal_ofNat]
  · fun_prop
  · exact MeasurableSet.univ


/-!

## C. The distribution associated with the ring

-/

/-- The distribution on `Space 3` corresponding to integration around a ring. -/
def ringDist : (Space 3) →d[ℝ] ℝ  :=
  SchwartzMap.integralCLM ℝ ringMeasure

lemma ringDist_apply_eq_integral_ringMeasure (f : 𝓢(Space 3, ℝ)) :
    ringDist f = ∫ x, f x ∂ringMeasure := by
  rw [ringDist, SchwartzMap.integralCLM_apply]

lemma ringDist_eq_integral_delta (f : 𝓢(Space 3, ℝ)) :
    ringDist f = ∫ z, diracDelta ℝ z f ∂ringMeasure := by
  rw [ringDist_apply_eq_integral_ringMeasure]
  simp

end Space
