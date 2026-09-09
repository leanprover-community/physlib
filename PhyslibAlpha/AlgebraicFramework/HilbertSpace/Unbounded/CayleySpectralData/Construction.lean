/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.UnitaryInfra.SpectralMeasure
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.SpectralIntegral.SpecTheorem
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Cayley.Certificate
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Bounded spectral data for a Cayley transform: construction

Builds the bounded normal spectral certificate for a Cayley unitary `cayleyBoundedOperator T` from
its continuous functional calculus, and specializes it to the case where `1` carries no spectral
mass, culminating in `cayleyRealSpectralMeasure`, the real spectral measure of the original
self-adjoint operator `T`. Continued in `CayleySpectralData/SpecTheorem.lean`, which assembles
this data into the self-adjoint spectral theorem itself.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped ComplexOrder CStarAlgebra InnerProductSpace
open QuantumMechanics.WOTSpectralMeasure

namespace QuantumMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- The real part of a spectral point of `U`, as a compactly supported continuous function on
`spectrum ℂ U`. -/
def spectrumRealPart (U : H →L[ℂ] H) :
    CompactlySupportedContinuousMap (spectrum ℂ U) ℝ :=
  ⟨⟨fun z => z.1.re, by fun_prop⟩,
    hasCompactSupport_def.mpr
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (subset_univ _))⟩

/-- The imaginary part of a spectral point of `U`, as a compactly supported continuous function
on `spectrum ℂ U`. -/
def spectrumImagPart (U : H →L[ℂ] H) :
    CompactlySupportedContinuousMap (spectrum ℂ U) ℝ :=
  ⟨⟨fun z => z.1.im, by fun_prop⟩,
    hasCompactSupport_def.mpr
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (subset_univ _))⟩

lemma cfcScalarMeasure_integral_spectrum_coe
    (U : H →L[ℂ] H) (hU : IsStarNormal U) (v : H) :
    ∫ z, (z.1 : ℂ) ∂cfcScalarMeasure U hU v =
      ((∫ z, spectrumRealPart U z ∂cfcScalarMeasure U hU v : ℝ) : ℂ) +
        Complex.I * ∫ z, spectrumImagPart U z ∂cfcScalarMeasure U hU v := by
  have hf : Integrable (fun z : spectrum ℂ U => (z.1 : ℂ))
      (cfcScalarMeasure U hU v) := by
    rw [← integrableOn_univ]
    exact continuous_subtype_val.continuousOn.integrableOn_compact isCompact_univ
  have hre : ∫ z, (z.1).re ∂cfcScalarMeasure U hU v =
      RCLike.re ⟪v, cfcRealOperator U hU (spectrumRealPart U) v⟫_ℂ := by
    simpa [spectrumRealPart] using
      cfcScalarMeasure_integral U hU v (spectrumRealPart U)
  have him : ∫ z, (z.1).im ∂cfcScalarMeasure U hU v =
      RCLike.re ⟪v, cfcRealOperator U hU (spectrumImagPart U) v⟫_ℂ := by
    simpa [spectrumImagPart] using
      cfcScalarMeasure_integral U hU v (spectrumImagPart U)
  rw [← integral_re_add_im hf]
  change ((∫ z, (z.1).re ∂cfcScalarMeasure U hU v : ℝ) : ℂ) +
      (∫ z, (z.1).im ∂cfcScalarMeasure U hU v : ℝ) * Complex.I =
    ((∫ z, (z.1).re ∂cfcScalarMeasure U hU v : ℝ) : ℂ) +
      Complex.I * ∫ z, (z.1).im ∂cfcScalarMeasure U hU v
  rw [hre, him]
  ring

lemma polarizedCfcScalarMeasure_integral_spectrum_coe
    (U : H →L[ℂ] H) (hU : IsStarNormal U) (x y : H) :
    ∫ᵛ z, (z.1 : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      polarizedCfcScalarMeasure (hU := hU) U x y] =
      ⟪y, U x⟫_ℂ := by
  let fC : spectrum ℂ U → ℂ := fun z => (z.1 : ℂ)
  have hfC : Continuous fC := by fun_prop
  have hplus : Integrable fC (cfcScalarMeasure U hU (x + y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  have hminus : Integrable fC (cfcScalarMeasure U hU (x - y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  have hip : Integrable fC
      (cfcScalarMeasure U hU (x + Complex.I • y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  have him : Integrable fC
      (cfcScalarMeasure U hU (x - Complex.I • y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  let μplus := cfcScalarMeasure U hU (x + y)
  let μminus := cfcScalarMeasure U hU (x - y)
  let νplus := cfcScalarMeasure U hU (x + Complex.I • y)
  let νminus := cfcScalarMeasure U hU (x - Complex.I • y)
  change ∫ᵛ z, fC z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      ((1 / 4 : ℝ) • (μplus.toSignedMeasure - μminus.toSignedMeasure)).toComplexMeasure
        ((1 / 4 : ℝ) • (νplus.toSignedMeasure - νminus.toSignedMeasure))] = _
  have hreal :
      (((1 / 4 : ℝ) • (μplus.toSignedMeasure - μminus.toSignedMeasure)).mapRange
        Complex.ofRealCLM.toAddMonoidHom Complex.ofRealCLM.continuous).Integrable fC := by
    rw [VectorMeasure.mapRange_smul, mapRange_sub_toSignedMeasure μplus μminus]
    exact (integrable_mapRange_ofReal_signedMeasure μplus fC hplus).sub_vectorMeasure
      (integrable_mapRange_ofReal_signedMeasure μminus fC hminus) |>.smul_vectorMeasure _
  have himag :
      (((1 / 4 : ℝ) • (νplus.toSignedMeasure - νminus.toSignedMeasure)).mapRange
        imaginaryOfRealCLM.toAddMonoidHom imaginaryOfRealCLM.continuous).Integrable fC := by
    rw [VectorMeasure.mapRange_smul, mapRange_sub_toSignedMeasure νplus νminus]
    exact (integrable_mapRange_imaginaryOfReal_signedMeasure νplus fC hip).sub_vectorMeasure
      (integrable_mapRange_imaginaryOfReal_signedMeasure νminus fC him) |>.smul_vectorMeasure _
  rw [integral_toComplexMeasure_eq_add_mapRange _ _ fC hreal himag]
  rw [integral_mapRange_ofReal_signedDifference μplus μminus (1 / 4 : ℝ) fC hplus hminus,
    integral_mapRange_imaginaryOfReal_signedDifference νplus νminus (1 / 4 : ℝ) fC hip him]
  have hJ (v : H) :
      ∫ z, (z.1 : ℂ) ∂cfcScalarMeasure U hU v =
        ((∫ z, spectrumRealPart U z ∂cfcScalarMeasure U hU v : ℝ) : ℂ) +
          Complex.I * ∫ z, spectrumImagPart U z ∂cfcScalarMeasure U hU v :=
    cfcScalarMeasure_integral_spectrum_coe U hU v
  rw [hJ, hJ, hJ, hJ]
  have hre := polarizedCfcRealIntegral_eq_inner U hU (spectrumRealPart U) x y
  have him' := polarizedCfcRealIntegral_eq_inner U hU (spectrumImagPart U) x y
  have hsplit :
      cfcRealOperator U hU (spectrumRealPart U) +
          (Complex.I : ℂ) • (cfcRealOperator U hU (spectrumImagPart U)) = U := by
    unfold cfcRealOperator
    rw [← map_smul, ← map_add]
    have hid :
        realToComplexContinuousMap U (spectrumRealPart U) +
            (Complex.I : ℂ) • realToComplexContinuousMap U (spectrumImagPart U) =
          (ContinuousMap.id ℂ).restrict (spectrum ℂ U) := by
      ext z
      change (z.1.re : ℂ) + Complex.I * z.1.im = z.1
      rw [mul_comm]
      exact Complex.re_add_im z.1
    calc
      cfcHom hU (realToComplexContinuousMap U (spectrumRealPart U) +
          Complex.I • realToComplexContinuousMap U (spectrumImagPart U)) =
          cfcHom hU ((ContinuousMap.id ℂ).restrict (spectrum ℂ U)) :=
        congrArg (fun f => cfcHom hU f) hid
      _ = U := cfcHom_id hU
  have hfinal :
      polarizedCfcRealIntegral U hU (spectrumRealPart U) x y +
          Complex.I * polarizedCfcRealIntegral U hU (spectrumImagPart U) x y =
        ⟪y, (cfcRealOperator U hU (spectrumRealPart U) +
          (Complex.I : ℂ) • (cfcRealOperator U hU (spectrumImagPart U))) x⟫_ℂ := by
    rw [hre, him']
    simp only [add_apply, smul_apply, inner_add_right, inner_smul_right]
  calc
    _ = polarizedCfcRealIntegral U hU (spectrumRealPart U) x y +
        Complex.I * polarizedCfcRealIntegral U hU (spectrumImagPart U) x y := by
      dsimp [polarizedCfcRealIntegral]
      ring
    _ = ⟪y, (cfcRealOperator U hU (spectrumRealPart U) +
        (Complex.I : ℂ) • cfcRealOperator U hU (spectrumImagPart U)) x⟫_ℂ := hfinal
    _ = ⟪y, U x⟫_ℂ := by rw [hsplit]

/-- The Cayley unitary of `T`, as a bounded continuous linear map. -/
def cayleyBoundedOperator (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) : H →L[ℂ] H :=
  (cayleyUnitary T hT).toLinearIsometry.toContinuousLinearMap

lemma cayleyBoundedOperator_apply (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    cayleyBoundedOperator T hT x = cayleyContinuousLinearMap T hT x := by
  rfl

lemma cayleyBoundedOperator_isStarNormal (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    IsStarNormal (cayleyBoundedOperator T hT) := by
  let u := cayleyUnitary T hT
  change IsStarNormal (u.toLinearIsometry.toContinuousLinearMap)
  rw [isStarNormal_iff]
  rw [show star u.toLinearIsometry.toContinuousLinearMap =
      u.symm.toLinearIsometry.toContinuousLinearMap by
        change star (u : H →L[ℂ] H) = (u.symm : H →L[ℂ] H)
        exact u.star_eq_symm]
  ext x
  simp [ContinuousLinearMap.mul_def]

lemma cayleyBoundedOperator_mem_unitary (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    cayleyBoundedOperator T hT ∈ unitary (H →L[ℂ] H) := by
  let u := cayleyUnitary T hT
  have hstar : star u.toLinearIsometry.toContinuousLinearMap =
      u.symm.toLinearIsometry.toContinuousLinearMap := by
    change star (u : H →L[ℂ] H) = (u.symm : H →L[ℂ] H)
    exact u.star_eq_symm
  rw [Unitary.mem_iff]
  constructor
  · change star u.toLinearIsometry.toContinuousLinearMap *
      u.toLinearIsometry.toContinuousLinearMap = 1
    rw [hstar]
    ext x
    simp [ContinuousLinearMap.mul_def]
  · change u.toLinearIsometry.toContinuousLinearMap *
      star u.toLinearIsometry.toContinuousLinearMap = 1
    rw [hstar]
    ext x
    simp [ContinuousLinearMap.mul_def]

/-- The pushforward of the Cayley unitary's continuous functional calculus spectral measure
along `spectrum ℂ U ↪ ℂ`. -/
noncomputable def cayleyBoundedSpectralMeasure (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    QuantumMechanics.WOTSpectralMeasure ℂ H :=
  let U := cayleyBoundedOperator T hT
  (cfcSpectralMeasure U (cayleyBoundedOperator_isStarNormal T hT)).map
    (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe

lemma cfcSpectralMeasure_reconstruction_coe
    (U : H →L[ℂ] H) (hU : IsStarNormal U) (x y : H) :
    (cfcSpectralMeasure U hU).complexWeakIntegral
        (fun z : spectrum ℂ U => (z.1 : ℂ)) x y = ⟪y, U x⟫_ℂ := by
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [cfcSpectralMeasure_scalarMeasure]
  exact polarizedCfcScalarMeasure_integral_spectrum_coe U hU x y

/-! ## The generic bounded-normal wrapper

The Riesz--Markov construction is carried out on the compact spectrum.  The public spectral
certificate should expose a measure on the ambient scalar field, since that is what the later
functional-calculus and Cayley APIs consume.  This wrapper performs exactly that harmless subtype
pushforward and does not impose any unitary or Cayley support hypothesis.
-/

lemma cfcSpectralMeasure_ambient_reconstruction
    (U : H →L[ℂ] H) (hU : IsStarNormal U) (x y : H) :
    ((cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe).complexWeakIntegral
        id x y = ⟪y, U x⟫_ℂ := by
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_map]
  rw [(MeasurableEmbedding.subtype_coe (spectrum.isClosed
      U).measurableSet).integral_map_vectorMeasure]
  change (cfcSpectralMeasure U hU).complexWeakIntegral
      (fun z : spectrum ℂ U => (z.1 : ℂ)) x y = ⟪y, U x⟫_ℂ
  exact cfcSpectralMeasure_reconstruction_coe U hU x y

/-- The generic bounded normal spectral certificate for `U`, from its continuous functional
calculus. -/
noncomputable def cfcBoundedNormalSpectralData
    (U : H →L[ℂ] H) (hU : IsStarNormal U) :
    QuantumMechanics.WOTSpectralMeasure.BoundedNormalSpectralData U where
  spectralMeasure := (cfcSpectralMeasure U hU).map
    (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe
  reconstruction := cfcSpectralMeasure_ambient_reconstruction U hU

/-! A unitary with no spectral mass at `1` is now the exact input expected by the Cayley inverse.
The only extra work is the support calculation: the normal PVM is pushed forward from the compact
spectrum, and the spectrum of a unitary lies on the unit circle. -/

/-- The bounded unitary spectral certificate for a unitary with no spectral mass at `1`. -/
noncomputable def cfcBoundedUnitarySpectralData
    (u : H ≃ₗᵢ[ℂ] H)
    (h1 : (1 : ℂ) ∉ spectrum ℂ (u : H →L[ℂ] H)) :
    QuantumMechanics.WOTSpectralMeasure.BoundedUnitarySpectralData u := by
  let hu : unitary (H →L[ℂ] H) :=
    (Unitary.linearIsometryEquiv (𝕜 := ℂ) (H := H)).symm u
  let U : H →L[ℂ] H := u
  have hU : IsStarNormal U := by
    exact isStarNormal_of_mem_unitary (by simpa [U, hu] using hu.property)
  let D := cfcBoundedNormalSpectralData U hU
  have hsub : spectrum ℂ U ⊆ Metric.sphere 0 1 := by
    simpa [U, hu] using (Unitary.spectrum_subset_circle hu)
  have hsupport : ∀ S : Set ℂ, MeasurableSet S →
      D.spectralMeasure S = D.spectralMeasure (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1}) := by
    intro S hS
    have hpre : (fun z : spectrum ℂ U => (z : ℂ)) ⁻¹' S =
        (fun z : spectrum ℂ U => (z : ℂ)) ⁻¹'
          (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1}) := by
      ext z
      constructor
      · intro hz
        have hzunit : (z : ℂ) ∈ Metric.sphere 0 1 := hsub z.property
        have hznorm : ‖(z : ℂ)‖ = 1 := by
          have := Metric.mem_sphere.mp hzunit
          simpa [dist_zero_right] using this
        have hznot : (z : ℂ) ≠ 1 := by
          intro hz1
          apply h1
          simpa [U, hz1] using z.property
        exact ⟨hz, hznorm, hznot⟩
      · intro hz
        exact hz.1
    change (cfcSpectralMeasure U hU).map
        (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe S =
      (cfcSpectralMeasure U hU).map
        (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe
          (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1})
    calc
      _ = (cfcSpectralMeasure U hU)
          ((fun z : spectrum ℂ U => (z : ℂ)) ⁻¹' S) :=
        (cfcSpectralMeasure U hU).map_apply
          (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe hS
      _ = (cfcSpectralMeasure U hU)
          ((fun z : spectrum ℂ U => (z : ℂ)) ⁻¹'
            (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1})) := congrArg _ hpre
      _ = _ := ((cfcSpectralMeasure U hU).map_apply
          (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe (hS.inter
            ((measurableSet_eq_fun measurable_norm measurable_const).inter
              (measurableSet_singleton (1 : ℂ)).compl))).symm
  exact {
    spectralMeasure := D.spectralMeasure
    support_away_one := hsupport
    reconstruction := D.reconstruction
  }

lemma cayleyBoundedSpectralMeasure_reconstruction
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x y : H) :
    (cayleyBoundedSpectralMeasure T hT).complexWeakIntegral id x y =
      ⟪y, cayleyBoundedOperator T hT x⟫_ℂ := by
  let U := cayleyBoundedOperator T hT
  let hU : IsStarNormal U := cayleyBoundedOperator_isStarNormal T hT
  change ((cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe).complexWeakIntegral
        id x y = _
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_map]
  rw [(MeasurableEmbedding.subtype_coe (spectrum.isClosed
      U).measurableSet).integral_map_vectorMeasure]
  change (cfcSpectralMeasure U hU).complexWeakIntegral
      (fun z : spectrum ℂ U => (z.1 : ℂ)) x y = ⟪y, U x⟫_ℂ
  exact cfcSpectralMeasure_reconstruction_coe U hU x y

set_option maxHeartbeats 1000000 in
lemma cayleyBoundedSpectralMeasure_scalarMeasure_isFinite
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x y : H) :
    IsFiniteMeasure
      ((cayleyBoundedSpectralMeasure T hT).scalarMeasure x y).variation := by
  let U := cayleyBoundedOperator T hT
  let hU : IsStarNormal U := cayleyBoundedOperator_isStarNormal T hT
  have hp : IsFiniteMeasure
      (polarizedCfcScalarMeasure (hU := hU) U x y).variation :=
    polarizedCfcScalarMeasure_isFiniteMeasure U hU x y
  let : IsFiniteMeasure
      (polarizedCfcScalarMeasure (hU := hU) U x y).variation := hp
  change IsFiniteMeasure
    (((cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe).scalarMeasure x y).variation
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_map]
  rw [cfcSpectralMeasure_scalarMeasure]
  infer_instance

lemma atom_eigenvector_of_reconstruction
    (E : QuantumMechanics.WOTSpectralMeasure ℂ H) (V : H →L[ℂ] H)
    (hrec : ∀ x y : H, E.complexWeakIntegral id x y = ⟪y, V x⟫_ℂ)
    {a : ℂ} (ha : MeasurableSet {a}) (x : H)
    (hfinite : ∀ y : H, IsFiniteMeasure (E.scalarMeasure x y).variation) :
    V (E {a} x) = a • E {a} x := by
  apply ext_inner_left ℂ
  intro y
  let : IsFiniteMeasure (E.scalarMeasure x y).variation := hfinite y
  let : IsFiniteMeasure ((E.scalarMeasure x y).restrict {a}).variation := by
    rw [MeasureTheory.VectorMeasure.variation_restrict ha]
    infer_instance
  have hμ : E.scalarMeasure (E {a} x) y = (E.scalarMeasure x y).restrict {a} := by
    apply MeasureTheory.VectorMeasure.ext
    intro S hS
    rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply,
      MeasureTheory.VectorMeasure.restrict_apply _ ha hS,
      QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
    change ⟪y, (E S * E {a}) x⟫_ℂ = _
    rw [E.comp_eq_of_inter hS ha]
  rw [← hrec (E {a} x) y]
  change (∫ᵛ z, id z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      E.scalarMeasure (E {a} x) y]) = _
  rw [hμ]
  change (∫ᵛ z in {a}, id z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      E.scalarMeasure x y]) = _
  have hid :
      (∫ᵛ z in {a}, id z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        E.scalarMeasure x y]) =
        ∫ᵛ _ in {a}, a ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
          E.scalarMeasure x y] := by
    apply VectorMeasure.integral_congr_ae
    rw [MeasureTheory.VectorMeasure.variation_restrict ha]
    filter_upwards [ae_restrict_mem ha] with z hz
    simpa [Set.mem_singleton_iff] using hz
  rw [hid]
  change (∫ᵛ _ : ℂ, a ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      (E.scalarMeasure x y).restrict {a}]) = _
  rw [VectorMeasure.integral_const]
  rw [MeasureTheory.VectorMeasure.restrict_apply_univ]
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
  simp [inner_smul_right]

lemma cayleyBoundedSpectralMeasure_support_unit_circle
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (S : Set ℂ) (hS : MeasurableSet S) :
    cayleyBoundedSpectralMeasure T hT S =
      cayleyBoundedSpectralMeasure T hT (S ∩ {z | ‖z‖ = 1}) := by
  let U := cayleyBoundedOperator T hT
  let hU : IsStarNormal U := cayleyBoundedOperator_isStarNormal T hT
  have hu : U ∈ unitary (H →L[ℂ] H) := cayleyBoundedOperator_mem_unitary T hT
  change (cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe S =
    (cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe (S ∩ {z | ‖z‖ = 1})
  change (cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe S =
    (cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe
        (S ∩ (fun z : ℂ => ‖z‖) ⁻¹' ({1} : Set ℝ))
  rw [(cfcSpectralMeasure U hU).map_apply
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe hS,
    (cfcSpectralMeasure U hU).map_apply
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe
      (hS.inter (((isClosed_singleton : IsClosed ({1} : Set ℝ)).preimage
        continuous_norm).measurableSet))]
  congr 1
  ext z
  constructor
  · intro hz
    refine ⟨hz, ?_⟩
    exact spectrum.norm_eq_one_of_unitary hu z.property
  · exact fun hz => hz.1

lemma cayleyBoundedOperator_one_eigenspace_eq_bot
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) {x : H}
    (hx : cayleyBoundedOperator T hT x = x) : x = 0 := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have heq : T - (-Complex.I) • 1 = T + Complex.I • 1 := by
    exact LinearPMap.ext rfl fun z hz hz' => by
      simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, neg_smul]
  have hker : (T + Complex.I • 1).toFun.ker = ⊥ := by
    rw [← heq]
    exact hres.1
  have hrange : (T + Complex.I • 1).toFun.range = ⊤ := by
    rw [← heq]
    exact hres.2.1
  have hinvdom : (T + Complex.I • 1).inverse.domain = ⊤ := by
    rw [LinearPMap.inverse_domain, hrange]
  let xi : (T + Complex.I • 1).inverse.domain :=
    ⟨x, by rw [hinvdom]; exact Submodule.mem_top⟩
  have hxi : (T + Complex.I • 1).inverse xi ∈ (T + Complex.I • 1).domain := by
    rw [← LinearPMap.inverse_range hker]
    exact LinearMap.mem_range_self _ xi
  let y : (T + Complex.I • 1).domain :=
    ⟨(T + Complex.I • 1).inverse xi, hxi⟩
  have hxrange : x ∈ (T + Complex.I • 1).toFun.range := by
    rw [hrange]
    exact Submodule.mem_top
  obtain ⟨x₀, hx₀⟩ := hxrange
  have hxy : (T + Complex.I • 1) x₀ = xi := by
    change (T + Complex.I • 1) x₀ = x
    exact hx₀
  have hinv₀ : (T + Complex.I • 1).inverse xi = x₀ :=
    LinearPMap.inverse_apply_eq hker hxy
  have hy : (T + Complex.I • 1) y = x := by
    have heq : y = x₀ := Subtype.ext hinv₀
    rw [heq]
    exact hx₀
  have hminus : (T - Complex.I • 1) y = x := by
    calc
      (T - Complex.I • 1) y = cayleyContinuousLinearMap T hT x := by
        symm
        exact cayleyContinuousLinearMap_apply_of_mem_range hT y x hy
      _ = cayleyBoundedOperator T hT x := by
        rw [cayleyBoundedOperator_apply]
      _ = x := hx
  have hdiff : (T + Complex.I • 1) y - (T - Complex.I • 1) y = 0 := by
    rw [hy, hminus]
    simp
  have hplusdom : (T + Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.add_domain]
  let yt : T.domain := ⟨(y : H), by rw [← hplusdom]; exact y.property⟩
  have hdiff' : (T yt + Complex.I • (y : H)) -
      (T yt - Complex.I • (y : H)) = 0 := by
    simpa [LinearPMap.add_apply, LinearPMap.sub_apply, LinearPMap.smul_apply] using hdiff
  have hy0 : (y : H) = 0 := by
    have hscalar : (2 * Complex.I) • (y : H) = 0 := by
      have heq : Complex.I • (y : H) = -(Complex.I • (y : H)) := by
        apply add_left_cancel (a := T yt)
        simpa [sub_eq_add_neg] using (sub_eq_zero.mp hdiff')
      calc
        (2 * Complex.I) • (y : H) = (Complex.I + Complex.I) • (y : H) := by module
        _ = Complex.I • (y : H) + Complex.I • (y : H) := by rw [add_smul]
        _ = Complex.I • (y : H) + -(Complex.I • (y : H)) :=
          congrArg (fun q => Complex.I • (y : H) + q) heq
        _ = 0 := add_neg_cancel _
    exact (smul_eq_zero.mp hscalar).resolve_left (by norm_num)
  calc
    x = (T + Complex.I • 1) y := hy.symm
    _ = 0 := by
      have hy' : y = 0 := Subtype.ext hy0
      rw [hy']
      simp

set_option maxHeartbeats 1000000

lemma cayleyBoundedSpectralMeasure_id_integrable
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x y : H) :
    ((cayleyBoundedSpectralMeasure T hT).scalarMeasure x y).Integrable id := by
  let E := cayleyBoundedSpectralMeasure T hT
  let C : Set ℂ := {z | ‖z‖ = 1}
  have hC : MeasurableSet C := by
    dsimp [C]
    exact measurableSet_eq_fun measurable_norm measurable_const
  have hfinite : IsFiniteMeasure (E.scalarMeasure x y).variation := by
    exact cayleyBoundedSpectralMeasure_scalarMeasure_isFinite T hT x y
  let := hfinite
  have hrestrict : E.scalarMeasure x y = (E.scalarMeasure x y).restrict C := by
    apply MeasureTheory.VectorMeasure.ext
    intro S hS
    rw [MeasureTheory.VectorMeasure.restrict_apply (E.scalarMeasure x y) hC hS]
    rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply,
      QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
    rw [cayleyBoundedSpectralMeasure_support_unit_circle T hT S hS]
  rw [hrestrict]
  change MeasureTheory.Integrable id ((E.scalarMeasure x y).restrict C).variation
  rw [MeasureTheory.VectorMeasure.variation_restrict hC]
  apply MeasureTheory.Integrable.of_bound measurable_id.aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem hC] with z hz
  calc
    ‖z‖ = 1 := hz
    _ ≤ 1 := le_rfl

lemma cayleyBoundedSpectralMeasure_singleton_one
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    cayleyBoundedSpectralMeasure T hT {1} = 0 := by
  let U := cayleyBoundedOperator T hT
  let hU : IsStarNormal U := cayleyBoundedOperator_isStarNormal T hT
  let E := cayleyBoundedSpectralMeasure T hT
  have hrec : ∀ x y : H, E.complexWeakIntegral id x y = ⟪y, U x⟫_ℂ := by
    intro x y
    exact cayleyBoundedSpectralMeasure_reconstruction T hT x y
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  have hfinite : ∀ y : H, IsFiniteMeasure (E.scalarMeasure x y).variation := by
    intro y
    have hp : IsFiniteMeasure
        (polarizedCfcScalarMeasure (hU := hU) U x y).variation := by
      unfold polarizedCfcScalarMeasure
      have hsub (a b : H) : IsFiniteMeasure
          (((1 / 4 : ℝ) • ((cfcScalarMeasure U hU a).toSignedMeasure -
            (cfcScalarMeasure U hU b).toSignedMeasure)).variation) := by
        let : IsFiniteMeasure (cfcScalarMeasure U hU a).toSignedMeasure.variation := by
          rw [Measure.variation_toSignedMeasure]
          infer_instance
        let : IsFiniteMeasure (cfcScalarMeasure U hU b).toSignedMeasure.variation := by
          rw [Measure.variation_toSignedMeasure]
          infer_instance
        apply isFiniteMeasure_of_le
          (cfcScalarMeasure U hU a + cfcScalarMeasure U hU b)
        rw [MeasureTheory.VectorMeasure.variation_smul]
        have hv : ((cfcScalarMeasure U hU a).toSignedMeasure -
            (cfcScalarMeasure U hU b).toSignedMeasure).variation ≤
            cfcScalarMeasure U hU a + cfcScalarMeasure U hU b := by
          simpa only [Measure.variation_toSignedMeasure] using
            (MeasureTheory.VectorMeasure.variation_sub_le
              (μ := (cfcScalarMeasure U hU a).toSignedMeasure)
              (ν := (cfcScalarMeasure U hU b).toSignedMeasure))
        calc
          ‖(1 / 4 : ℝ)‖₊ •
              ((cfcScalarMeasure U hU a).toSignedMeasure -
                (cfcScalarMeasure U hU b).toSignedMeasure).variation ≤
              (1 : ENNReal) • ((cfcScalarMeasure U hU a).toSignedMeasure -
                (cfcScalarMeasure U hU b).toSignedMeasure).variation := by
            change ((‖(1 / 4 : ℝ)‖₊ : NNReal) : ENNReal) •
                ((cfcScalarMeasure U hU a).toSignedMeasure -
                  (cfcScalarMeasure U hU b).toSignedMeasure).variation ≤
              (1 : ENNReal) • ((cfcScalarMeasure U hU a).toSignedMeasure -
                (cfcScalarMeasure U hU b).toSignedMeasure).variation
            gcongr
            norm_num
          _ ≤ (1 : ENNReal) • (cfcScalarMeasure U hU a + cfcScalarMeasure U hU b) := by
            simpa only [one_smul] using hv
          _ = cfcScalarMeasure U hU a + cfcScalarMeasure U hU b := by simp
      apply isFiniteMeasure_toComplexMeasure
    let : IsFiniteMeasure
        (polarizedCfcScalarMeasure (hU := hU) U x y).variation := hp
    change IsFiniteMeasure
      (((cfcSpectralMeasure U hU).map
        (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe).scalarMeasure x y).variation
    rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_map]
    rw [cfcSpectralMeasure_scalarMeasure]
    infer_instance
  have hAtom := atom_eigenvector_of_reconstruction (a := (1 : ℂ)) E U hrec
    (measurableSet_singleton (1 : ℂ)) x hfinite
  have hzero : E {1} x = 0 := by
    apply cayleyBoundedOperator_one_eigenspace_eq_bot T hT
    simpa using hAtom
  simpa [E] using congrArg (fun v : H => ⟪y, v⟫_ℂ) hzero

lemma cayleyBoundedSpectralMeasure_support_away_one
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (S : Set ℂ) (hS : MeasurableSet S) :
    cayleyBoundedSpectralMeasure T hT S =
      cayleyBoundedSpectralMeasure T hT (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1}) := by
  let E := cayleyBoundedSpectralMeasure T hT
  have hC : MeasurableSet ({z : ℂ | ‖z‖ = 1}) :=
    ((isClosed_singleton : IsClosed ({1} : Set ℝ)).preimage continuous_norm).measurableSet
  have h1 : MeasurableSet ({(1 : ℂ)} : Set ℂ) := measurableSet_singleton 1
  have hne : MeasurableSet ({z : ℂ | z ≠ 1}) := h1.compl
  have hA : MeasurableSet (S ∩ {z : ℂ | ‖z‖ = 1}) := hS.inter hC
  have hB : MeasurableSet (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ)) :=
    (hS.inter hC).inter h1
  have hB' : MeasurableSet (S ∩ {z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | z ≠ 1}) :=
    (hS.inter hC).inter hne
  have hunion :
      (S ∩ {z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | z ≠ 1}) ∪
          (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ)) =
        S ∩ {z : ℂ | ‖z‖ = 1} := by
    ext z
    by_cases hz : z = 1 <;> simp [hz]
  have hdisj : Disjoint
      (S ∩ {z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | z ≠ 1})
      (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ)) := by
    refine Set.disjoint_left.2 ?_
    intro z hz hz'
    exact hz.2 hz'.2
  have hzeroB : E (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ)) = 0 := by
    have hcomp := E.comp_eq_of_inter hB h1
    have hinter :
        (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ)) ∩ ({(1 : ℂ)} : Set ℂ) =
          S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ) := by
      ext z
      simp
    rw [hinter, cayleyBoundedSpectralMeasure_singleton_one T hT] at hcomp
    simpa using hcomp.symm
  calc
    E S = E (S ∩ {z : ℂ | ‖z‖ = 1}) :=
      cayleyBoundedSpectralMeasure_support_unit_circle T hT S hS
    _ = E ((S ∩ {z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | z ≠ 1}) ∪
        (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ))) := by rw [hunion]
    _ = E (S ∩ {z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | z ≠ 1}) +
        E (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ)) :=
      E.of_union hdisj hB' hB
    _ = E (S ∩ {z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | z ≠ 1}) := by
      rw [hzeroB]
      simp
    _ = E (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1}) := by
      congr 1
      ext z
      simp [and_left_comm, and_comm]

lemma cayleyInverse_mul_one_sub_of_unit_circle
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    (cayleyInverse z : ℂ) * (1 - z) = Complex.I * (1 + z) := by
  let x : ℝ := cayleyInverse z
  have hx : cayley x = z := by
    exact cayley_cayleyInverse hz hz1
  change (x : ℂ) * (1 - z) = Complex.I * (1 + z)
  rw [← hx]
  unfold cayley
  have hden : (x : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  field_simp [hden]
  ring

lemma cayley_domain_factorization
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x : T.domain) :
    ∃ v : H,
      (x : H) = v - cayleyBoundedOperator T hT v ∧
        T x = Complex.I • (v + cayleyBoundedOperator T hT v) := by
  let hplusdom : (T + Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.add_domain]
  let xp : (T + Complex.I • 1).domain :=
    ⟨(x : H), by rw [hplusdom]; exact x.property⟩
  let a : H := (T + Complex.I • 1) xp
  let v : H := (2 * Complex.I)⁻¹ • a
  have ha : cayleyBoundedOperator T hT a = (T - Complex.I • 1) xp := by
    rw [cayleyBoundedOperator_apply]
    exact cayleyContinuousLinearMap_apply_of_mem_range hT xp a rfl
  have h2i : (2 * Complex.I : ℂ) ≠ 0 := by norm_num
  have hxpinf : (xp : H) ∈ T.domain ⊓
      (Complex.I • (1 : H →ₗ.[ℂ] H)).domain := by
    rw [← LinearPMap.add_domain]
    exact xp.property
  have hxmem : (xp : H) ∈ T.domain ∧
      (xp : H) ∈ (Complex.I • (1 : H →ₗ.[ℂ] H)).domain := by
    exact ⟨hxpinf.1, hxpinf.2⟩
  have hxpT : (⟨(xp : H), hxmem.1⟩ : T.domain) = x := by
    apply Subtype.ext
    rfl
  have hxp_coe : (xp : H) = (x : H) := by
    rfl
  refine ⟨v, ?_, ?_⟩
  · dsimp [v, a]
    rw [map_smul, ha]
    field_simp [h2i]
    simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, hxpT,
      smul_add, smul_sub, smul_smul, div_eq_mul_inv, Complex.inv_I]
    field_simp [h2i]
    norm_num [Complex.I_sq, Complex.I_mul_I, pow_two]
    simp [hxp_coe]; module

  · dsimp [v, a]
    rw [map_smul, ha]
    field_simp [h2i]
    simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, hxpT,
      smul_add, smul_sub, smul_smul, div_eq_mul_inv, Complex.inv_I]
    field_simp [h2i]
    norm_num [Complex.I_sq, Complex.I_mul_I, pow_two]
    simp [hxp_coe]; module

/-! ### A bounded extension of the Cayley difference multiplier

The algebraic factor `1 - z` is bounded on the unit circle, which is the support of the
bounded Cayley spectral measure, but it is not bounded on all of `ℂ`.  The bounded integral
API quite correctly asks for a global bound.  We therefore use the zero extension outside the
closed unit disk; support reduction makes it equal to `1 - z` wherever the spectral measure
sees it.
-/

/-- `z ↦ 1 - z` on the unit circle, extended by zero elsewhere so it is globally bounded. -/
def cayleyDifferenceMultiplier (z : ℂ) : ℂ :=
  if ‖z‖ = 1 then 1 - z else 0

lemma cayleyDifferenceMultiplier_measurable :
    Measurable cayleyDifferenceMultiplier := by
  unfold cayleyDifferenceMultiplier
  exact Measurable.ite (measurableSet_eq_fun measurable_norm measurable_const)
    (measurable_const.sub measurable_id) measurable_const

lemma cayleyDifferenceMultiplier_bounded :
    ∃ C : ℝ, ∀ z : ℂ, ‖cayleyDifferenceMultiplier z‖ ≤ C := by
  refine ⟨2, fun z => ?_⟩
  by_cases hz : ‖z‖ = 1
  · simp [cayleyDifferenceMultiplier, hz]
    exact (norm_sub_le _ _).trans (by norm_num; linarith)
  · simp [cayleyDifferenceMultiplier, hz]

lemma cayleyDifferenceMultiplier_eq_one_sub_of_unit_circle {z : ℂ} (hz : ‖z‖ = 1) :
    cayleyDifferenceMultiplier z = 1 - z := by
  simp [cayleyDifferenceMultiplier, hz]

lemma boundedIntegral_cayleyDifferenceMultiplier_eq_sub
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    QuantumMechanics.WOTSpectralMeasure.boundedIntegral (cayleyBoundedSpectralMeasure T hT)
        cayleyDifferenceMultiplier cayleyDifferenceMultiplier_measurable
        cayleyDifferenceMultiplier_bounded =
      (1 : H →WOT[ℂ] H) -
        ContinuousLinearMapWOT.ofCLM (cayleyBoundedOperator T hT) := by
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  have hfinite := cayleyBoundedSpectralMeasure_scalarMeasure_isFinite T hT x y
  let ν := (cayleyBoundedSpectralMeasure T hT).scalarMeasure x y
  let A : Set ℂ := {z : ℂ | ‖z‖ = 1 ∧ z ≠ 1}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact (measurableSet_eq_fun measurable_norm measurable_const).inter
      (measurableSet_singleton (1 : ℂ)).compl
  have hνA : ν = ν.restrict {z : ℂ | ‖z‖ = 1 ∧ z ≠ 1} := by
    apply MeasureTheory.VectorMeasure.ext
    intro S hS
    rw [MeasureTheory.VectorMeasure.restrict_apply ν
      hA hS]
    change ⟪y, (cayleyBoundedSpectralMeasure T hT) S x⟫_ℂ =
      ⟪y, (cayleyBoundedSpectralMeasure T hT)
        (S ∩ {z : ℂ | ‖z‖ = 1 ∧ z ≠ 1}) x⟫_ℂ
    rw [cayleyBoundedSpectralMeasure_support_away_one T hT S hS]
  have hνA' : ν = ν.restrict A := by simpa [A] using hνA
  let := hfinite
  have hA_ae : ∀ᵐ z ∂ν.variation, ‖z‖ = 1 ∧ z ≠ 1 := by
    have hvar : ν.variation = (ν.restrict A).variation := congrArg
      MeasureTheory.VectorMeasure.variation hνA'
    rw [hvar, MeasureTheory.VectorMeasure.variation_restrict hA]
    exact ae_restrict_mem hA
  have hq_ae : cayleyDifferenceMultiplier =ᵐ[ν.variation]
      (fun z : ℂ => (1 : ℂ) - z) := by
    filter_upwards [hA_ae] with z hz
    exact cayleyDifferenceMultiplier_eq_one_sub_of_unit_circle hz.1
  have hconst : ν.Integrable (fun _ : ℂ => (1 : ℂ)) := by
    exact MeasureTheory.integrable_const (μ := ν.variation) (c := (1 : ℂ))
  have hfi : ν.Integrable id :=
    cayleyBoundedSpectralMeasure_id_integrable T hT x y
  have hq : ν.Integrable (fun z : ℂ => (1 : ℂ) - z) := hconst.sub hfi
  have hqbd : ν.Integrable cayleyDifferenceMultiplier := by
    exact hq.congr hq_ae.symm
  have hqint : ∫ᵛ z, cayleyDifferenceMultiplier z ∂[
      ContinuousLinearMap.lsmul ℝ ℂ; ν] =
      ∫ᵛ z, ((1 : ℂ) - z) ∂[
        ContinuousLinearMap.lsmul ℝ ℂ; ν] :=
    VectorMeasure.integral_congr_ae hq_ae
  have hsub : ∫ᵛ z, ((1 : ℂ) - z) ∂[
      ContinuousLinearMap.lsmul ℝ ℂ; ν] =
      ⟪y, x⟫_ℂ - ⟪y, cayleyBoundedOperator T hT x⟫_ℂ := by
    have hdiff : ν.Integrable (fun z : ℂ => (1 : ℂ) - z) := hq
    change ∫ᵛ z, ((fun _ : ℂ => (1 : ℂ)) z - id z) ∂[
      ContinuousLinearMap.lsmul ℝ ℂ; ν] = _
    rw [VectorMeasure.integral_fun_sub hconst hfi]
    rw [VectorMeasure.integral_const]
    rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
    rw [QuantumMechanics.WOTSpectralMeasure.univ]
    simp only [ContinuousLinearMap.lsmul_apply, one_smul]
    change ⟪y, x⟫_ℂ - (∫ᵛ z, id z ∂[
      ContinuousLinearMap.lsmul ℝ ℂ; ν]) = _
    rw [show (∫ᵛ z, id z ∂[
        ContinuousLinearMap.lsmul ℝ ℂ; ν]) =
        ⟪y, cayleyBoundedOperator T hT x⟫_ℂ by
      change (cayleyBoundedSpectralMeasure T hT).complexWeakIntegral id x y = _
      exact cayleyBoundedSpectralMeasure_reconstruction T hT x y]
  change ⟪y, QuantumMechanics.WOTSpectralMeasure.boundedIntegral
      (cayleyBoundedSpectralMeasure T hT)
      cayleyDifferenceMultiplier cayleyDifferenceMultiplier_measurable
      cayleyDifferenceMultiplier_bounded x⟫_ℂ = _
  rw [QuantumMechanics.WOTSpectralMeasure.boundedIntegral_inner
    (cayleyBoundedSpectralMeasure T hT) cayleyDifferenceMultiplier_measurable
    cayleyDifferenceMultiplier_bounded x y hfinite]
  rw [hqint, hsub]
  simp [inner_sub_right]

/-- The bounded unitary spectral certificate for `T`'s Cayley unitary. -/
noncomputable def cayleyBoundedUnitarySpectralData
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    QuantumMechanics.WOTSpectralMeasure.BoundedUnitarySpectralData
      (cayleyUnitary T hT) where
  spectralMeasure := cayleyBoundedSpectralMeasure T hT
  support_away_one := fun S hS => cayleyBoundedSpectralMeasure_support_away_one T hT S hS
  reconstruction := by
    intro x y
    simpa [cayleyUnitary_apply, cayleyBoundedOperator_apply] using
      cayleyBoundedSpectralMeasure_reconstruction T hT x y

/-- The real spectral measure of `T`, transported from its Cayley unitary's bounded unitary
spectral data. -/
noncomputable def cayleyRealSpectralMeasure
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    QuantumMechanics.WOTSpectralMeasure ℝ H :=
  (cayleyBoundedUnitarySpectralData T hT).realSpectralMeasure

lemma cayleyMap_cayleyRealSpectralMeasure
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    QuantumMechanics.WOTSpectralMeasure.cayleyMap (cayleyRealSpectralMeasure T hT) =
      cayleyBoundedSpectralMeasure T hT := by
  exact (cayleyBoundedUnitarySpectralData T hT).cayleyMap_realSpectralMeasure

end QuantumMechanics

end
