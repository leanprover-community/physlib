/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.CayleySpectralData.SpecTheorem

/-!
# The bounded self-adjoint spectral measure

The bounded normal construction naturally produces a measure on the complex spectrum.  For a
self-adjoint operator that spectrum is real, so pushing the measure forward along `Complex.re`
gives the real spectral measure consumed by the unbounded integral API.  This file records that
adapter independently of the Cayley transform.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace QuantumMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real spectral measure of a bounded self-adjoint operator, obtained from the genuine
bounded-normal spectral measure by the real-part map on the complex spectrum. -/
noncomputable def boundedSelfAdjointSpectralMeasure
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    QuantumMechanics.WOTSpectralMeasure ℝ H :=
  (cfcSpectralMeasure A hA.isStarNormal).map
    (fun z : spectrum ℂ A => z.1.re) (by fun_prop)

set_option maxHeartbeats 2000000 in
lemma boundedSelfAdjointSpectralMeasure_reconstruction
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x y : H) :
    (boundedSelfAdjointSpectralMeasure A hA).complexWeakIntegral
        (fun r : ℝ => (r : ℂ)) x y = ⟪y, A x⟫_ℂ := by
  let E := cfcSpectralMeasure A hA.isStarNormal
  let f : spectrum ℂ A → ℝ := fun z => z.1.re
  have hf : Measurable f := by fun_prop
  have hfinite : IsFiniteMeasure (E.scalarMeasure x y).variation := by
    rw [cfcSpectralMeasure_scalarMeasure]
    exact polarizedCfcScalarMeasure_isFiniteMeasure A hA.isStarNormal x y
  let := hfinite
  have hgi : (E.scalarMeasure x y).Integrable (fun z => ((f z : ℝ) : ℂ)) := by
    have hcont : Continuous (fun z : spectrum ℂ A => ((f z : ℝ) : ℂ)) := by
      fun_prop
    have hbdd : BddAbove ((fun z : ℂ => ‖z‖) '' (spectrum ℂ A)) :=
      (spectrum.isCompact A).bddAbove_image continuous_norm.continuousOn
    rcases hbdd with ⟨C, hC⟩
    apply MeasureTheory.Integrable.of_bound hcont.aestronglyMeasurable C
    filter_upwards [] with z
    calc
      ‖((f z : ℝ) : ℂ)‖ = |f z| := by simp
      _ = |z.1.re| := rfl
      _ ≤ ‖z.1‖ := Complex.abs_re_le_norm _
      _ ≤ C := hC ⟨z.1, z.property, rfl⟩
  have hmap := QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral_map
    (μS := E) f hf (fun r : ℝ => (r : ℂ)) x y
    Complex.continuous_ofReal.aestronglyMeasurable hgi
  change (E.map f hf).complexWeakIntegral (fun r : ℝ => (r : ℂ)) x y = _
  rw [hmap]
  have hreal : ((fun r : ℝ => (r : ℂ)) ∘ f) = (fun z : spectrum ℂ A => z.1) := by
    funext z
    exact (hA.mem_spectrum_eq_re z.property).symm
  rw [hreal]
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [cfcSpectralMeasure_scalarMeasure]
  exact polarizedCfcScalarMeasure_integral_spectrum_coe A hA.isStarNormal x y

/-- Every spectral projection of the real spectral measure of a bounded self-adjoint operator
commutes with any unitary intertwiner of that operator — the Schur's-lemma-facing form of
`cfcSpectralMeasure_commute_of_commute_unitary`.  Since `A` is self-adjoint, `Commute A T` alone
gives `Commute (star A) T` for free (`star A = A`), so no separate adjoint-commutation hypothesis
is needed. -/
lemma boundedSelfAdjointSpectralMeasure_commute_of_commute
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {T : H →L[ℂ] H} (hAT : Commute A T)
    (hTunit : T ∈ unitary (H →L[ℂ] H)) (E : Set ℝ) :
    boundedSelfAdjointSpectralMeasure A hA E * ContinuousLinearMapWOT.ofCLM T =
      ContinuousLinearMapWOT.ofCLM T * boundedSelfAdjointSpectralMeasure A hA E := by
  have hAT' : Commute (star A) T := by rwa [hA.star_eq]
  by_cases hE : MeasurableSet E
  · show (cfcSpectralMeasure A hA.isStarNormal).map (fun z : spectrum ℂ A => z.1.re) (by fun_prop) E
        * ContinuousLinearMapWOT.ofCLM T =
      ContinuousLinearMapWOT.ofCLM T *
        (cfcSpectralMeasure A hA.isStarNormal).map (fun z : spectrum ℂ A => z.1.re) (by fun_prop) E
    rw [(cfcSpectralMeasure A hA.isStarNormal).map_apply
      (fun z : spectrum ℂ A => z.1.re) (by fun_prop) hE]
    exact cfcSpectralMeasure_commute_of_commute_unitary A hA.isStarNormal hAT hAT' hTunit _
  · rw [(boundedSelfAdjointSpectralMeasure A hA).apply_eq_zero_of_not_measurableSet hE]
    simp

lemma exists_boundedSelfAdjointSpectralSupport
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    ∃ C : ℝ, HasBoundedSpectralSupport
      (boundedSelfAdjointSpectralMeasure A hA) C := by
  let E := cfcSpectralMeasure A hA.isStarNormal
  let f : spectrum ℂ A → ℝ := fun z => z.1.re
  have hbdd : BddAbove ((fun z : ℂ => ‖z‖) '' (spectrum ℂ A)) :=
    (spectrum.isCompact A).bddAbove_image continuous_norm.continuousOn
  rcases hbdd with ⟨B, hB⟩
  let C : ℝ := max 0 B
  refine ⟨C, le_max_left _ _, ?_⟩
  intro S hS hdisj
  have hpre : f ⁻¹' S = ∅ := by
    ext z
    constructor
    · intro hz
      have habs : |f z| ≤ C := by
        calc
          |f z| ≤ ‖z.1‖ := Complex.abs_re_le_norm _
          _ ≤ B := hB ⟨z.1, z.property, rfl⟩
          _ ≤ C := le_max_right _ _
      have hzIcc : f z ∈ Set.Icc (-C) C :=
        (abs_le.mp habs)
      exact (Set.disjoint_left.1 hdisj hz) hzIcc
    · simp
  change (E.map f (by fun_prop)) S = 0
  rw [E.map_apply f (by fun_prop) hS, hpre]
  simp

end QuantumMechanics

end
