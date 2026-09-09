/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.CayleySpectralData.Construction
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.SelfAdjointSpectralTheorem

/-!
# Bounded spectral data for a Cayley transform: the self-adjoint spectral theorem

Continues `CayleySpectralData/Construction.lean`: transports its bounded spectral certificate back
through the Cayley transform to `cayleyRealSpectralMeasure`, proves the resulting measure is a
weak spectral resolution of the original self-adjoint operator, and assembles
`unboundedSpectralTheorem` — the public unbounded spectral theorem for a self-adjoint `LinearPMap`
— together with its essentially-self-adjoint variant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped ComplexOrder CStarAlgebra InnerProductSpace
open QuantumMechanics.WOTSpectralMeasure

namespace QuantumMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cayleyRealSpectralMeasure_mem_domain
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x : T.domain) :
    (x : H) ∈ spectralSquareMomentDomain
      (cayleyRealSpectralMeasure T hT) := by
  let E := cayleyBoundedSpectralMeasure T hT
  let q := cayleyDifferenceMultiplier
  obtain ⟨v, hx, _⟩ := cayley_domain_factorization T hT x
  have hqv : QuantumMechanics.WOTSpectralMeasure.boundedIntegral E q
      cayleyDifferenceMultiplier_measurable cayleyDifferenceMultiplier_bounded v =
      v - cayleyBoundedOperator T hT v := by
    have h := congrArg (fun A : H →WOT[ℂ] H => A v)
      (boundedIntegral_cayleyDifferenceMultiplier_eq_sub T hT)
    simpa [E, q] using h
  have hxeq : (x : H) = QuantumMechanics.WOTSpectralMeasure.boundedIntegral E q
      cayleyDifferenceMultiplier_measurable cayleyDifferenceMultiplier_bounded v :=
    hx.trans hqv.symm
  have hdiag : E.diagonalMeasure ((x : H)) =
      Measure.withDensity (E.diagonalMeasure v)
        (fun z => ENNReal.ofReal (‖q z‖ ^ 2)) := by
    rw [hxeq]
    exact QuantumMechanics.WOTSpectralMeasure.diagonalMeasure_boundedIntegral_eq_withDensity E
      cayleyDifferenceMultiplier_measurable cayleyDifferenceMultiplier_bounded v
  let A : Set ℂ := {z : ℂ | ‖z‖ = 1 ∧ z ≠ 1}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact (measurableSet_eq_fun measurable_norm measurable_const).inter
      (measurableSet_singleton (1 : ℂ)).compl
  have hdiagA : E.diagonalMeasure v = (E.diagonalMeasure v).restrict A := by
    apply Measure.ext
    intro S hS
    rw [MeasureTheory.Measure.restrict_apply hS]
    rw [E.diagonalMeasure_apply_eq_norm_sq v S hS,
      E.diagonalMeasure_apply_eq_norm_sq v (S ∩ A) (hS.inter hA)]
    have hs := cayleyBoundedSpectralMeasure_support_away_one T hT S hS
    have hvec : (E S) v = (E (S ∩ A)) v := by
      simpa [A] using congrArg (fun P : H →WOT[ℂ] H => P v) hs
    rw [hvec]
  have hA_ae : ∀ᵐ z ∂E.diagonalMeasure v, z ∈ A := by
    rw [hdiagA]
    exact ae_restrict_mem hA
  have hbase : Integrable (fun z : ℂ => (cayleyInverse z) ^ 2)
      (E.diagonalMeasure ((x : H))) := by
    rw [hdiag]
    let d : ℂ → ENNReal := fun z => ENNReal.ofReal (‖q z‖ ^ 2)
    have hd : Measurable d := ENNReal.continuous_ofReal.measurable.comp
      (cayleyDifferenceMultiplier_measurable.norm.pow_const 2)
    have hd_top : ∀ᵐ z ∂E.diagonalMeasure v, d z < (⊤ : ENNReal) := by
      filter_upwards [] with z
      exact (lt_top_iff_ne_top).2 (ENNReal.ofReal_ne_top)
    apply (integrable_withDensity_iff_integrable_smul₀' hd.aemeasurable hd_top).2
    have hmeas : AEStronglyMeasurable (fun z : ℂ =>
        (d z).toReal • (cayleyInverse z) ^ 2) (E.diagonalMeasure v) := by
      change AEStronglyMeasurable
        ((fun z : ℂ => (d z).toReal) * (fun z : ℂ => (cayleyInverse z) ^ 2))
        (E.diagonalMeasure v)
      exact hd.ennreal_toReal.aestronglyMeasurable.mul
        (measurable_cayleyInverse.pow_const 2).aestronglyMeasurable
    apply Integrable.of_bound hmeas 4
    filter_upwards [hA_ae] with z hz
    have hzid := cayleyInverse_mul_one_sub_of_unit_circle hz.1 hz.2
    have hqz : q z = 1 - z := cayleyDifferenceMultiplier_eq_one_sub_of_unit_circle hz.1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (cayleyInverse z))]
    rw [show d z = ENNReal.ofReal (‖1 - z‖ ^ 2) by
      dsimp [d]
      rw [hqz],
      ENNReal.toReal_ofReal (sq_nonneg ‖1 - z‖)]
    have hprod : ‖(cayleyInverse z : ℂ) * (1 - z)‖ ≤ 2 := by
      rw [hzid]
      calc
        ‖Complex.I * (1 + z)‖ = ‖1 + z‖ := by rw [norm_mul]; simp
        _ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
        _ = 2 := by rw [hz.1]; norm_num
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hprod
    have hprod_nonneg : 0 ≤ |cayleyInverse z| * ‖1 - z‖ :=
      mul_nonneg (abs_nonneg _) (norm_nonneg _)
    have hsq := (sq_le_sq₀ hprod_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr hprod
    calc
      ‖1 - z‖ ^ 2 * cayleyInverse z ^ 2 =
          (|cayleyInverse z| * ‖1 - z‖) ^ 2 := by
            rw [mul_pow, sq_abs]
            ring
      _ ≤ 2 ^ 2 := hsq
      _ = 4 := by norm_num
  rw [mem_spectralSquareMomentDomain_iff]
  rw [show (cayleyRealSpectralMeasure T hT).diagonalMeasure (x : H) =
      Measure.map cayleyInverse (E.diagonalMeasure (x : H)) by
    change (E.map cayleyInverse measurable_cayleyInverse).diagonalMeasure (x : H) = _
    exact E.diagonalMeasure_map cayleyInverse measurable_cayleyInverse (x : H)]
  apply (integrable_map_measure
    ((measurable_id.pow_const 2).aestronglyMeasurable)
    measurable_cayleyInverse.aemeasurable).2
  simpa [Function.comp_def] using hbase

/-! ### Restriction identities for PVM scalar measures

These identities are independent of the Cayley transform.  They express the elementary fact
that testing a projection-valued measure after applying one of its projections restricts the
corresponding scalar measure.  They are the bookkeeping lemmas needed when a bounded spectral
moment is localized to a measurable spectral set.
-/

lemma WOTSpectralMeasure.scalarMeasure_proj_left_restrict
    {α : Type*} [MeasurableSpace α]
    (μ : QuantumMechanics.WOTSpectralMeasure α H) {S : Set α} (hS : MeasurableSet S)
    (x y : H) :
    μ.scalarMeasure (μ S x) y = (μ.scalarMeasure x y).restrict S := by
  apply MeasureTheory.VectorMeasure.ext
  intro A hA
  change μ.scalarMeasure (μ S x) y A = (μ.scalarMeasure x y).restrict S A
  rw [MeasureTheory.VectorMeasure.restrict_apply (μ.scalarMeasure x y) hS hA]
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply,
    QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
  change ⟪y, (μ A * μ S) x⟫_ℂ = _
  rw [μ.comp_eq_of_inter hA hS]

lemma WOTSpectralMeasure.scalarMeasure_proj_right_restrict
    {α : Type*} [MeasurableSpace α]
    (μ : QuantumMechanics.WOTSpectralMeasure α H) {S : Set α} (hS : MeasurableSet S)
    (x y : H) :
    μ.scalarMeasure x (μ S y) = (μ.scalarMeasure x y).restrict S := by
  apply MeasureTheory.VectorMeasure.ext
  intro A hA
  change μ.scalarMeasure x (μ S y) A = (μ.scalarMeasure x y).restrict S A
  rw [MeasureTheory.VectorMeasure.restrict_apply (μ.scalarMeasure x y) hS hA]
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply,
    QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
  calc
    ⟪μ S y, μ A x⟫_ℂ = ⟪y, μ S (μ A x)⟫_ℂ := by
      change ⟪ContinuousLinearMapWOT.toCLM (μ S) y, μ A x⟫_ℂ =
        ⟪y, ContinuousLinearMapWOT.toCLM (μ S) (μ A x)⟫_ℂ
      have hstar : star (ContinuousLinearMapWOT.toCLM (μ S)) =
          ContinuousLinearMapWOT.toCLM (μ S) :=
        congrArg ContinuousLinearMapWOT.toCLM (μ.isStarProjection S).isSelfAdjoint
      have hstar' : ContinuousLinearMap.adjoint (ContinuousLinearMapWOT.toCLM (μ S)) =
          ContinuousLinearMapWOT.toCLM (μ S) := by
        rw [← ContinuousLinearMap.star_eq_adjoint]
        exact hstar
      calc
        ⟪ContinuousLinearMapWOT.toCLM (μ S) y, μ A x⟫_ℂ =
            ⟪ContinuousLinearMap.adjoint (ContinuousLinearMapWOT.toCLM (μ S)) y,
              μ A x⟫_ℂ := by rw [hstar']
        _ = ⟪y, ContinuousLinearMapWOT.toCLM (μ S) (μ A x)⟫_ℂ :=
          ContinuousLinearMap.adjoint_inner_left (ContinuousLinearMapWOT.toCLM (μ S))
            (μ A x) y
    _ = ⟪y, (μ S * μ A) x⟫_ℂ := rfl
    _ = ⟪y, μ (S ∩ A) x⟫_ℂ := by
      rw [μ.comp_eq_of_inter hS hA]
    _ = ⟪y, μ (A ∩ S) x⟫_ℂ := by rw [inter_comm]
    _ = _ := rfl

@[nolint unusedArguments]
lemma WOTSpectralMeasure.complexWeakIntegral_proj_left
    {α : Type*} [MeasurableSpace α]
    (μ : QuantumMechanics.WOTSpectralMeasure α H) {S : Set α} (hS : MeasurableSet S)
    (g : α → ℂ) (x y : H)
    (_hgi : (μ.scalarMeasure x y).Integrable g) :
    μ.complexWeakIntegral g (μ S x) y =
      ∫ᵛ z, Set.indicator S g z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μ.scalarMeasure x y] := by
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [WOTSpectralMeasure.scalarMeasure_proj_left_restrict μ hS]
  exact (MeasureTheory.VectorMeasure.integral_indicator
    (μ := μ.scalarMeasure x y) (f := g) hS).symm

@[nolint unusedArguments]
lemma WOTSpectralMeasure.complexWeakIntegral_proj_right
    {α : Type*} [MeasurableSpace α]
    (μ : QuantumMechanics.WOTSpectralMeasure α H) {S : Set α} (hS : MeasurableSet S)
    (g : α → ℂ) (x y : H)
    (_hgi : (μ.scalarMeasure x y).Integrable g) :
    μ.complexWeakIntegral g x (μ S y) =
      ∫ᵛ z, Set.indicator S g z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μ.scalarMeasure x y] := by
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [WOTSpectralMeasure.scalarMeasure_proj_right_restrict μ hS]
  exact (MeasureTheory.VectorMeasure.integral_indicator
    (μ := μ.scalarMeasure x y) (f := g) hS).symm

lemma WOTSpectralMeasure.reconstruction_commutes_projection
    {α : Type*} [MeasurableSpace α]
    (μ : QuantumMechanics.WOTSpectralMeasure α H) (U : H →L[ℂ] H)
    (f : α → ℂ)
    (hrec : ∀ x y, μ.complexWeakIntegral f x y = ⟪y, U x⟫_ℂ)
    (hfi : ∀ x y, (μ.scalarMeasure x y).Integrable f)
    {S : Set α} (hS : MeasurableSet S) :
    μ S * ContinuousLinearMapWOT.ofCLM U =
      ContinuousLinearMapWOT.ofCLM U * μ S := by
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  have hstar : star (ContinuousLinearMapWOT.toCLM (μ S)) =
      ContinuousLinearMapWOT.toCLM (μ S) :=
    congrArg ContinuousLinearMapWOT.toCLM (μ.isStarProjection S).isSelfAdjoint
  have hstar' : ContinuousLinearMap.adjoint (ContinuousLinearMapWOT.toCLM (μ S)) =
      ContinuousLinearMapWOT.toCLM (μ S) := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hstar
  have hproj : ⟪y, μ S (U x)⟫_ℂ = ⟪μ S y, U x⟫_ℂ := by
    change ⟪y, ContinuousLinearMapWOT.toCLM (μ S) (U x)⟫_ℂ =
      ⟪ContinuousLinearMapWOT.toCLM (μ S) y, U x⟫_ℂ
    calc
      ⟪y, ContinuousLinearMapWOT.toCLM (μ S) (U x)⟫_ℂ =
          ⟪y, ContinuousLinearMap.adjoint (ContinuousLinearMapWOT.toCLM (μ S))
            (U x)⟫_ℂ := by rw [hstar']
      _ = ⟪ContinuousLinearMapWOT.toCLM (μ S) y, U x⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_right
          (ContinuousLinearMapWOT.toCLM (μ S)) y (U x)
  calc
    ⟪y, (μ S * ContinuousLinearMapWOT.ofCLM U) x⟫_ℂ =
        ⟪y, μ S (U x)⟫_ℂ := rfl
    _ = ⟪μ S y, U x⟫_ℂ := hproj
    _ = μ.complexWeakIntegral f x (μ S y) := (hrec x (μ S y)).symm
    _ = ∫ᵛ z, Set.indicator S f z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μ.scalarMeasure x y] := by
      exact WOTSpectralMeasure.complexWeakIntegral_proj_right μ hS f x y (hfi x y)
    _ = μ.complexWeakIntegral f (μ S x) y := by
      symm
      exact WOTSpectralMeasure.complexWeakIntegral_proj_left μ hS f x y (hfi x y)
    _ = ⟪y, U (μ S x)⟫_ℂ := hrec (μ S x) y
    _ = ⟪y, (ContinuousLinearMapWOT.ofCLM U * μ S) x⟫_ℂ := rfl

lemma WOTSpectralMeasure.complexWeakIntegral_one_sub
    (μ : QuantumMechanics.WOTSpectralMeasure ℂ H) (U : H →L[ℂ] H)
    (hrec : ∀ x y, μ.complexWeakIntegral id x y = ⟪y, U x⟫_ℂ)
    (hfi : ∀ x y, (μ.scalarMeasure x y).Integrable id)
    (hfinite : ∀ x y, IsFiniteMeasure (μ.scalarMeasure x y).variation) (x y : H) :
    μ.complexWeakIntegral (fun z => (1 : ℂ) - z) x y =
      ⟪y, x - U x⟫_ℂ := by
  let := hfinite x y
  have hconst : (μ.scalarMeasure x y).Integrable (fun _ : ℂ => (1 : ℂ)) := by
    change Integrable (fun _ : ℂ => (1 : ℂ)) (μ.scalarMeasure x y).variation
    exact MeasureTheory.integrable_const (μ := (μ.scalarMeasure x y).variation) (c := (1 : ℂ))
  have hsub : (μ.scalarMeasure x y).Integrable (fun z => (1 : ℂ) - z) := by
    exact hconst.sub (hfi x y)
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  have hfun : (fun z : ℂ => (1 : ℂ) - z) = (fun _ : ℂ => (1 : ℂ)) - id := by
    funext z
    simp
  rw [hfun]
  rw [VectorMeasure.integral_sub (μ := μ.scalarMeasure x y)
    (B := ContinuousLinearMap.lsmul ℝ ℂ) hconst (hfi x y)]
  rw [VectorMeasure.integral_const]
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
  simp only [μ.univ, ContinuousLinearMap.lsmul_apply, one_smul]
  have hid : (∫ᵛ z, id z ∂[ContinuousLinearMap.lsmul ℝ ℂ;
      μ.scalarMeasure x y]) = ⟪y, U x⟫_ℂ := by
    change μ.complexWeakIntegral id x y = _
    exact hrec x y
  rw [hid]
  change ⟪y, x⟫_ℂ - ⟪y, U x⟫_ℂ = _
  rw [inner_sub_right]

lemma WOTSpectralMeasure.scalarMeasure_domain_factorization
    (μ : QuantumMechanics.WOTSpectralMeasure ℂ H) (U : H →L[ℂ] H)
    (hrec : ∀ x y, μ.complexWeakIntegral id x y = ⟪y, U x⟫_ℂ)
    (hfi : ∀ x y, (μ.scalarMeasure x y).Integrable id)
    (hfinite : ∀ x y, IsFiniteMeasure (μ.scalarMeasure x y).variation)
    (hcomm : ∀ {S : Set ℂ}, MeasurableSet S →
      μ S * ContinuousLinearMapWOT.ofCLM U =
        ContinuousLinearMapWOT.ofCLM U * μ S)
    (x v y : H) (hx : x = v - U v) {S : Set ℂ} (hS : MeasurableSet S) :
    μ.scalarMeasure x y S =
      μ.complexWeakIntegral (fun z => (1 : ℂ) - z) (μ S v) y := by
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply, hx, map_sub]
  have hcommv := congrArg (fun A : H →WOT[ℂ] H => A v) (hcomm hS)
  change μ S (U v) = U (μ S v) at hcommv
  rw [hcommv]
  exact (WOTSpectralMeasure.complexWeakIntegral_one_sub μ U hrec hfi hfinite
    (μ S v) y).symm

/-! ### Complex vector-measure density transport

The scalar measures of a complex PVM are complex vector measures, rather than positive
measures.  This is the reusable density-integral theorem needed by the inverse Cayley step.
-/

set_option maxHeartbeats 3000000 in
lemma VectorMeasure.integral_real_withDensity_mul
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.VectorMeasure α ℂ)
    {q : α → ℂ} (hq : μ.Integrable q) {g : α → ℝ}
    (hg : (μ.withDensity q (ContinuousLinearMap.mul ℝ ℂ)).Integrable g)
    (hvar0 : (μ.withDensity q (ContinuousLinearMap.mul ℝ ℂ)).variation =
      μ.variation.withDensity (fun x => ‖q x‖ₑ)) :
    ∫ᵛ x, g x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ);
        μ.withDensity q (ContinuousLinearMap.mul ℝ ℂ)] =
      ∫ᵛ x, (g x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := by
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  have hmul : B = ContinuousLinearMap.lsmul ℝ ℂ := by
    ext z w
    simp [B, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hvar :
      (μ.withDensity q B).variation = μ.variation.withDensity (fun x => ‖q x‖ₑ) := by
    simpa [B] using hvar0
  have hq_lt : ∀ᵐ x ∂μ.variation, ‖q x‖ₑ < ⊤ := by
    filter_upwards with x
    exact (lt_top_iff_ne_top).2 enorm_ne_top
  have bridge : ∀ {f : α → ℝ},
      (μ.withDensity q B).Integrable f →
        Integrable (fun x => (f x : ℂ) * q x) μ.variation := by
    intro f hf
    have hfd : Integrable f (μ.variation.withDensity (fun x => ‖q x‖ₑ)) := by
      change Integrable f (μ.withDensity q B).variation at hf
      rw [hvar] at hf
      exact hf
    have hweighted : Integrable
        (fun x => (‖q x‖ₑ).toReal • f x) μ.variation :=
      (integrable_withDensity_iff_integrable_smul₀'
        hq.aestronglyMeasurable.enorm hq_lt).1 hfd
    have hmeas : AEStronglyMeasurable (fun x => (f x : ℂ) * q x) μ.variation := by
      have hqmeas : AEStronglyMeasurable q μ.variation := hq.aestronglyMeasurable
      have hnormmeas : AEStronglyMeasurable (fun x => ‖q x‖) μ.variation :=
        hqmeas.norm
      let u : α → ℂ := fun x => (‖q x‖ : ℝ)⁻¹ • q x
      have hu : AEStronglyMeasurable u μ.variation :=
        hnormmeas.inv₀.smul hqmeas
      have haux' : AEStronglyMeasurable
          (fun x => ((‖q x‖ₑ).toReal • f x : ℂ) * u x) μ.variation := by
        convert (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
          hweighted.aestronglyMeasurable).mul hu using 1
        funext x; simp [Complex.ofRealCLM_apply, smul_eq_mul]
      have haux := haux'
      apply haux.congr
      filter_upwards with x
      by_cases hqx : q x = 0
      · simp [u, hqx]
      · dsimp [u]
        rw [show (‖q x‖ₑ).toReal = ‖q x‖ by simp [enorm_eq_nnnorm]]
        have hn : (‖q x‖ : ℂ) ≠ 0 := by
          exact_mod_cast (norm_ne_zero_iff.mpr hqx)
        calc
          (‖q x‖ : ℂ) * (f x : ℂ) * (((‖q x‖⁻¹ : ℝ) : ℂ) * q x) =
              (‖q x‖ : ℂ) * (f x : ℂ) * ((‖q x‖ : ℂ)⁻¹ * q x) := by
                rw [Complex.ofReal_inv]
          _ =
              (f x : ℂ) * ((‖q x‖ : ℂ) * (‖q x‖ : ℂ)⁻¹) * q x := by ring
          _ = (f x : ℂ) * q x := by
            rw [mul_inv_cancel₀ hn, mul_one]
    apply hweighted.norm.mono' hmeas
    filter_upwards with x
    rw [norm_mul, Complex.norm_real]
    simp [enorm_eq_nnnorm, mul_comm]
  apply hg.induction (P := fun f =>
    ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ.withDensity q B] =
      ∫ᵛ x, (f x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ])
  · intro c s hs hfinite
    change (μ.withDensity q B).variation s < ⊤ at hfinite
    have hfinite' : IsFiniteMeasure ((μ.withDensity q B).variation.restrict s) := by
      exact MeasureTheory.isFiniteMeasure_restrict.mpr hfinite.ne
    let := hfinite'
    rw [VectorMeasure.integral_indicator_const c hs]
    have hfun : (fun x => ((s.indicator (fun _ => c) x : ℝ) : ℂ) * q x) =
        s.indicator (fun x => (c : ℂ) * q x) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hfun, MeasureTheory.VectorMeasure.withDensity_apply hq, hmul]
    rw [VectorMeasure.integral_indicator (μ := μ)
      (B := ContinuousLinearMap.lsmul ℝ ℂ) (f := fun x => (c : ℂ) * q x) hs]
    change (c : ℂ) • (∫ᵛ x, q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ.restrict s]) =
      ∫ᵛ x, (c : ℝ) • q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ.restrict s]
    rw [VectorMeasure.integral_fun_smul]
    simp [smul_eq_mul]
  · intro f k _ hf hk hfP hkP
    have hfk := bridge hf
    have hkk := bridge hk
    change (∫ᵛ x, f x + k x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ);
      μ.withDensity q B]) = _
    rw [VectorMeasure.integral_fun_add (μ := μ.withDensity q B) hf hk]
    have hfunadd : (fun x => ((f + k) x : ℂ) * q x) =
        (fun x => ((f x : ℂ) + (k x : ℂ)) * q x) := by
      funext x
      simp [Pi.add_apply]
    rw [hfunadd]
    have hfunadd' :
        (fun x => ((f x : ℂ) + (k x : ℂ)) * q x) =
          (fun x => (f x : ℂ) * q x + (k x : ℂ) * q x) := by
      funext x
      rw [add_mul]
    rw [hfunadd']
    rw [VectorMeasure.integral_fun_add (μ := μ) hfk hkk, hfP, hkP]
  · apply isClosed_eq
    · exact MeasureTheory.VectorMeasure.continuous_integral
    · have hLip : LipschitzWith 1
          (fun y : (Lp ℝ 1 ((μ.withDensity q B).variation)) =>
            ∫ᵛ x, (y x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ]) := by
        rw [lipschitzWith_iff_dist_le_mul]
        intro f k
        have hf := bridge (by
          simpa [B] using (L1.integrable_coeFn f))
        have hk := bridge (by
          simpa [B] using (L1.integrable_coeFn k))
        have hdist := MeasureTheory.VectorMeasure.dist_integral_le_lintegral_edist
          (μ := μ) (B := ContinuousLinearMap.lsmul ℝ ℂ) hf hk
        calc
          dist (∫ᵛ x, (f x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ])
              (∫ᵛ x, (k x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ]) ≤
              ‖ContinuousLinearMap.lsmul ℝ ℂ‖ *
                (∫⁻ x, edist ((f x : ℂ) * q x) ((k x : ℂ) * q x) ∂μ.variation).toReal := hdist
          _ = (1 : ℝ) * dist f k := by
            have hlin :
                (∫⁻ x, edist ((f x : ℂ) * q x) ((k x : ℂ) * q x) ∂μ.variation) =
                  ∫⁻ x, ‖f x - k x‖ₑ ∂(μ.variation.withDensity
                    (fun x => ‖q x‖ₑ)) := by
              rw [lintegral_withDensity_eq_lintegral_mul₀'
                hq.aestronglyMeasurable.enorm]
              · apply lintegral_congr_ae
                filter_upwards with x
                rw [edist_dist, dist_eq_norm, ← sub_mul]
                rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _),
                  ofReal_norm, ofReal_norm]
                have hnorm : ‖(f x : ℂ) - (k x : ℂ)‖ₑ = ‖f x - k x‖ₑ := by
                  rw [← Complex.ofReal_sub]
                  simp only [enorm_eq_nnnorm]
                  apply congrArg ENNReal.ofNNReal
                  apply NNReal.eq
                  simp only [coe_nnnorm, Complex.norm_real]
                rw [hnorm]
                simp [enorm_eq_nnnorm, mul_comm]
              · rw [← hvar]
                exact (Lp.aestronglyMeasurable f).sub
                  (Lp.aestronglyMeasurable k) |>.enorm
            rw [hlin, ← hvar]
            rw [← eLpNorm_one_eq_lintegral_enorm]
            have he : eLpNorm (fun x => f x - k x) 1 (μ.withDensity q B).variation =
                eLpNorm (⇑(f - k)) 1 (μ.withDensity q B).variation :=
              eLpNorm_congr_ae (Lp.coeFn_sub f k).symm
            rw [he, Lp.dist_def]
            rw [eLpNorm_congr_ae (Lp.coeFn_sub f k)]
            simp
      exact hLip.continuous
  · intro f k hfk hf hfP
    have hfk' : f =ᵐ[μ.variation.withDensity (fun x => ‖q x‖ₑ)] k := by
      change f =ᵐ[(μ.withDensity q B).variation] k at hfk
      rw [hvar] at hfk
      exact hfk
    have hfkq : (fun x => (f x : ℂ) * q x) =ᵐ[μ.variation]
        (fun x => (k x : ℂ) * q x) := by
      have hqae := (ae_withDensity_iff' hq.aestronglyMeasurable.enorm).1 hfk'
      filter_upwards [hqae] with x hx
      by_cases hqx : q x = 0
      · simp [hqx]
      · rw [hx (by simp [hqx])]
    calc
      ∫ᵛ x, k x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ);
          μ.withDensity q B] =
          ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ);
            μ.withDensity q B] :=
        (VectorMeasure.integral_congr_ae (μ := μ.withDensity q B) hfk).symm
      _ = ∫ᵛ x, (f x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := hfP
      _ = ∫ᵛ x, (k x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] :=
        VectorMeasure.integral_congr_ae (μ := μ) hfkq

lemma WOTSpectralMeasure.scalarMeasure_eq_withDensity_one_sub
    (μ : QuantumMechanics.WOTSpectralMeasure ℂ H) (U : H →L[ℂ] H)
    (hrec : ∀ x y, μ.complexWeakIntegral id x y = ⟪y, U x⟫_ℂ)
    (hfi : ∀ x y, (μ.scalarMeasure x y).Integrable id)
    (hfinite : ∀ x y, IsFiniteMeasure (μ.scalarMeasure x y).variation)
    (hcomm : ∀ {S : Set ℂ}, MeasurableSet S →
      μ S * ContinuousLinearMapWOT.ofCLM U =
        ContinuousLinearMapWOT.ofCLM U * μ S)
    (x v y : H) (hx : x = v - U v) :
    μ.scalarMeasure x y =
      (μ.scalarMeasure v y).withDensity (fun z => (1 : ℂ) - z)
        (ContinuousLinearMap.mul ℝ ℂ) := by
  let ν := μ.scalarMeasure v y
  let := hfinite v y
  have hconst : ν.Integrable (fun _ : ℂ => (1 : ℂ)) := by
    change Integrable (fun _ : ℂ => (1 : ℂ)) ν.variation
    exact MeasureTheory.integrable_const (μ := ν.variation) (c := (1 : ℂ))
  have hq : ν.Integrable (fun z => (1 : ℂ) - z) := by
    exact hconst.sub (hfi v y)
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  rw [WOTSpectralMeasure.scalarMeasure_domain_factorization μ U hrec hfi hfinite hcomm
    x v y hx hS]
  rw [MeasureTheory.VectorMeasure.withDensity_apply hq]
  rw [← MeasureTheory.VectorMeasure.integral_indicator hS]
  have hB : ContinuousLinearMap.mul ℝ ℂ = ContinuousLinearMap.lsmul ℝ ℂ := by
    ext z w
    simp [ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [hB]
  exact WOTSpectralMeasure.complexWeakIntegral_proj_left μ hS
    (fun z => (1 : ℂ) - z) v y hq

lemma cayleyBoundedSpectralMeasure_commutes_operator
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T)
    {S : Set ℂ} (hS : MeasurableSet S) :
    cayleyBoundedSpectralMeasure T hT S *
        ContinuousLinearMapWOT.ofCLM (cayleyBoundedOperator T hT) =
      ContinuousLinearMapWOT.ofCLM (cayleyBoundedOperator T hT) *
        cayleyBoundedSpectralMeasure T hT S := by
  apply WOTSpectralMeasure.reconstruction_commutes_projection
    (cayleyBoundedSpectralMeasure T hT)
    (cayleyBoundedOperator T hT) id
  · intro x y
    exact cayleyBoundedSpectralMeasure_reconstruction T hT x y
  · intro x y
    exact cayleyBoundedSpectralMeasure_id_integrable T hT x y
  · exact hS

lemma cayleyBoundedSpectralMeasure_inverse_moment
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    ∀ x : T.domain, ∀ y : H,
      ((cayleyBoundedSpectralMeasure T hT).scalarMeasure (x : H) y).Integrable
          cayleyInverse ∧
        ⟪y, T x⟫_ℂ =
          (cayleyBoundedSpectralMeasure T hT).weakIntegral
            cayleyInverse (x : H) y := by
  intro x y
  let E := cayleyBoundedSpectralMeasure T hT
  let U := cayleyBoundedOperator T hT
  obtain ⟨v, hx, hTx⟩ := cayley_domain_factorization T hT x
  let ν := E.scalarMeasure v y
  let q : ℂ → ℂ := fun z => (1 : ℂ) - z
  have hfinite : IsFiniteMeasure ν.variation := by
    exact cayleyBoundedSpectralMeasure_scalarMeasure_isFinite T hT v y
  let := hfinite
  have hfi : ν.Integrable id := by
    exact cayleyBoundedSpectralMeasure_id_integrable T hT v y
  have hconst : ν.Integrable (fun _ : ℂ => (1 : ℂ)) := by
    change Integrable (fun _ : ℂ => (1 : ℂ)) ν.variation
    exact MeasureTheory.integrable_const (μ := ν.variation) (c := (1 : ℂ))
  have hq : ν.Integrable q := by
    exact hconst.sub hfi
  have hq_ae : AEMeasurable (fun z => ‖q z‖ₑ) ν.variation :=
    hq.aestronglyMeasurable.enorm
  have hq_lt : ∀ᵐ z ∂ν.variation, ‖q z‖ₑ < ⊤ := by
    filter_upwards with z
    exact (lt_top_iff_ne_top).2 (show ‖q z‖ₑ ≠ ⊤ from enorm_ne_top)
  have hvar : (ν.withDensity q (ContinuousLinearMap.mul ℝ ℂ)).variation =
      ν.variation.withDensity (fun z => ‖q z‖ₑ) := by
    rw [MeasureTheory.VectorMeasure.variation_withDensity hq]
    rw [MeasureTheory.VectorMeasure.variation_transpose_eq _ _]
    · simp [ContinuousLinearMap.mul_apply', nnnorm_mul]
    · intro a b
      simp [ContinuousLinearMap.mul_apply', nnnorm_mul]
  let A : Set ℂ := {z | ‖z‖ = 1 ∧ z ≠ 1}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact (measurableSet_eq_fun measurable_norm measurable_const).inter
      (measurableSet_singleton (1 : ℂ)).compl
  have hνA : ν = ν.restrict A := by
    apply MeasureTheory.VectorMeasure.ext
    intro S hS
    rw [MeasureTheory.VectorMeasure.restrict_apply ν hA hS]
    change ⟪y, E S v⟫_ℂ = ⟪y, E (S ∩ A) v⟫_ℂ
    rw [cayleyBoundedSpectralMeasure_support_away_one T hT S hS]
  have hA_ae : ∀ᵐ z ∂ν.variation, z ∈ A := by
    rw [hνA, MeasureTheory.VectorMeasure.variation_restrict hA]
    exact ae_restrict_mem hA
  have hprod : Integrable (fun z => (cayleyInverse z : ℂ) * q z) ν.variation := by
    have hmeas : AEStronglyMeasurable
        (fun z => (cayleyInverse z : ℂ) * q z) ν.variation := by
      have hqmeas : AEStronglyMeasurable q ν.variation := hq.aestronglyMeasurable
      exact (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
        measurable_cayleyInverse.aestronglyMeasurable).mul hqmeas
    apply Integrable.of_bound hmeas 2
    filter_upwards [hA_ae] with z hz
    have hzid := cayleyInverse_mul_one_sub_of_unit_circle hz.1 hz.2
    calc
      ‖(cayleyInverse z : ℂ) * q z‖ = ‖Complex.I * (1 + z)‖ := by
        rw [show q z = 1 - z by rfl, hzid]
      _ = ‖1 + z‖ := by rw [norm_mul]; simp
      _ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
      _ = 2 := by rw [hz.1]; norm_num
  have hweighted : (ν.withDensity q (ContinuousLinearMap.mul ℝ ℂ)).Integrable
      cayleyInverse := by
    change Integrable cayleyInverse
      (ν.withDensity q (ContinuousLinearMap.mul ℝ ℂ)).variation
    rw [hvar]
    apply (integrable_withDensity_iff_integrable_smul₀' hq_ae hq_lt).2
    have habs : Integrable
        (fun z => ‖(cayleyInverse z : ℂ) * q z‖) ν.variation := hprod.norm
    have habs' : Integrable
        (fun z => ‖q z‖ * |cayleyInverse z|) ν.variation := by
      apply habs.congr
      filter_upwards with z
      simp [Complex.norm_real, Real.norm_eq_abs, mul_comm]
    have hsign : Integrable
        (fun z => ‖q z‖ * cayleyInverse z) ν.variation := by
      apply habs'.congr'
        ((hq.aestronglyMeasurable.norm.mul
          measurable_cayleyInverse.aestronglyMeasurable))
      filter_upwards with z
      simp
    apply hsign.congr
    filter_upwards with z
    simp [toReal_enorm, smul_eq_mul]
  have hmeasure : E.scalarMeasure (x : H) y =
      ν.withDensity q (ContinuousLinearMap.mul ℝ ℂ) := by
    exact WOTSpectralMeasure.scalarMeasure_eq_withDensity_one_sub E U
      (fun a b => cayleyBoundedSpectralMeasure_reconstruction T hT a b)
      (fun a b => cayleyBoundedSpectralMeasure_id_integrable T hT a b)
      (fun a b => cayleyBoundedSpectralMeasure_scalarMeasure_isFinite T hT a b)
      (fun {S} hS => cayleyBoundedSpectralMeasure_commutes_operator T hT hS)
      (x : H) v y hx
  constructor
  · rw [hmeasure]
    exact hweighted
  · have hden := VectorMeasure.integral_real_withDensity_mul ν hq hweighted hvar
    have hbase : ∫ᵛ z, (cayleyInverse z : ℂ) * q z ∂[
        ContinuousLinearMap.lsmul ℝ ℂ; ν] =
        Complex.I * (∫ᵛ z, (1 + z) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ; ν]) := by
      have hplus : ν.Integrable (fun z => (1 : ℂ) + z) := hconst.add hfi
      have hpoint : (fun z => (cayleyInverse z : ℂ) * q z) =ᵐ[ν.variation]
          (fun z => Complex.I * ((1 : ℂ) + z)) := by
        rw [hνA, MeasureTheory.VectorMeasure.variation_restrict hA]
        filter_upwards [ae_restrict_mem hA] with z hz
        exact cayleyInverse_mul_one_sub_of_unit_circle hz.1 hz.2
      rw [VectorMeasure.integral_congr_ae hpoint]
      have hcomp :
          ContinuousLinearMap.lsmul ℝ ℂ ∘L ContinuousLinearMap.lsmul ℝ ℂ Complex.I =
            (ContinuousLinearMap.compL ℝ ℂ ℂ ℂ
              (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) ∘L
              ContinuousLinearMap.lsmul ℝ ℂ := by
        ext c w
        simp [ContinuousLinearMap.compL_apply, ContinuousLinearMap.lsmul_apply,
          smul_eq_mul]
        ring
      calc
        ∫ᵛ x, Complex.I * (1 + x) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ; ν] =
            ∫ᵛ x, (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) (1 + x) ∂[
              ContinuousLinearMap.lsmul ℝ ℂ; ν] := by rfl
        _ = ∫ᵛ x, (1 + x) ∂[
            (ContinuousLinearMap.lsmul ℝ ℂ) ∘L
              (ContinuousLinearMap.lsmul ℝ ℂ Complex.I); ν] :=
          VectorMeasure.integral_continuousLinearMap_comp hplus
        _ = ∫ᵛ x, (1 + x) ∂[
            (ContinuousLinearMap.compL ℝ ℂ ℂ ℂ
              (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) ∘L
              ContinuousLinearMap.lsmul ℝ ℂ; ν] := by rw [hcomp]
        _ = Complex.I * (∫ᵛ x, (1 + x) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ; ν]) :=
          (VectorMeasure.continuousLinearMap_apply_integral
            (C := ContinuousLinearMap.lsmul ℝ ℂ Complex.I) hplus).symm
    unfold QuantumMechanics.WOTSpectralMeasure.weakIntegral
    rw [hmeasure, hden, hbase]
    have hplus : ∫ᵛ z, (1 + z) ∂[
        ContinuousLinearMap.lsmul ℝ ℂ; ν] = ⟪y, v + U v⟫_ℂ := by
      have hplus' : ν.Integrable (fun z => (1 : ℂ) + z) := hconst.add hfi
      have hfun : (fun z : ℂ => (1 : ℂ) + z) =
          (fun _ : ℂ => (1 : ℂ)) + id := by
        funext z
        simp
      rw [hfun]
      change (∫ᵛ z, (1 : ℂ) + id z ∂[
        ContinuousLinearMap.lsmul ℝ ℂ; ν]) = _
      rw [VectorMeasure.integral_fun_add hconst hfi]
      rw [VectorMeasure.integral_const]
      rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
      rw [QuantumMechanics.WOTSpectralMeasure.univ]
      simp only [ContinuousLinearMap.lsmul_apply, one_smul]
      have hid : (∫ᵛ z, id z ∂[ContinuousLinearMap.lsmul ℝ ℂ; ν]) =
          ⟪y, U v⟫_ℂ := by
        change E.complexWeakIntegral id v y = _
        exact cayleyBoundedSpectralMeasure_reconstruction T hT v y
      rw [hid]
      change ⟪y, v⟫_ℂ + ⟪y, U v⟫_ℂ = _
      rw [inner_add_right]
    rw [hplus, hTx, inner_smul_right]

/-! ### The inverse-moment transport lemma

The bounded spectral reconstruction supplies the Cayley moment `z`.  The genuinely unbounded
step is the inverse-Cayley moment on the operator domain.  The following theorem isolates the
measure-transport part of that step: once the inverse moment is established on the bounded
Cayley measure, it is transported automatically to the real spectral measure.  This keeps the
analytic domain argument separate from the bookkeeping for mapped vector measures.
-/

lemma cayleyRealSpectralMeasure_isWeakSpectralResolution_of_inverse_moment
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T)
    (hinv : ∀ x : T.domain, ∀ y : H,
      ((cayleyBoundedSpectralMeasure T hT).scalarMeasure (x : H) y).Integrable cayleyInverse ∧
        ⟪y, T x⟫_ℂ =
          (cayleyBoundedSpectralMeasure T hT).weakIntegral cayleyInverse (x : H) y) :
    IsWeakSpectralResolution T (cayleyRealSpectralMeasure T hT) := by
  intro x
  refine ⟨?_, ?_⟩
  · intro y
    have hmap := hinv x y |>.1
    change ((cayleyBoundedSpectralMeasure T hT).map cayleyInverse
      measurable_cayleyInverse).scalarMeasure (x : H) y |>.Integrable id
    rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_map]
    exact VectorMeasure.Integrable.map measurable_id.aestronglyMeasurable hmap
  · intro y
    have hmap := hinv x y |>.1
    have htransport :
        (cayleyRealSpectralMeasure T hT).weakIntegral id (x : H) y =
          (cayleyBoundedSpectralMeasure T hT).weakIntegral
            (id ∘ cayleyInverse) (x : H) y := by
      change ((cayleyBoundedSpectralMeasure T hT).map cayleyInverse
        measurable_cayleyInverse).weakIntegral id (x : H) y = _
      exact QuantumMechanics.WOTSpectralMeasure.weakIntegral_map
        (μS := cayleyBoundedSpectralMeasure T hT) cayleyInverse
        measurable_cayleyInverse id (x : H) y
        measurable_id.aestronglyMeasurable hmap
    rw [htransport]
    simpa [Function.comp_def] using (hinv x y).2

lemma cayleyRealSpectralMeasure_isWeakSpectralResolution
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    IsWeakSpectralResolution T (cayleyRealSpectralMeasure T hT) := by
  apply cayleyRealSpectralMeasure_isWeakSpectralResolution_of_inverse_moment T hT
  exact cayleyBoundedSpectralMeasure_inverse_moment T hT

theorem cayleySelfAdjointSpectralTheorem
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    SelfAdjointSpectralTheorem T (cayleyRealSpectralMeasure T hT) where
  isSelfAdjoint := hT
  reconstruction := cayleyRealSpectralMeasure_isWeakSpectralResolution T hT

lemma cayleyRealSpectralMeasure_le_maximal
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    T ≤ QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
      (cayleyRealSpectralMeasure T hT) := by
  let E := cayleyRealSpectralMeasure T hT
  let M := QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral E
  have hres := cayleyRealSpectralMeasure_isWeakSpectralResolution T hT
  refine ⟨?_, ?_⟩
  · intro x hx
    change x ∈ spectralSquareMomentDomain E
    exact cayleyRealSpectralMeasure_mem_domain T hT (⟨x, hx⟩ : T.domain)
  · intro x z hxz
    have hxM : (x : H) ∈ M.domain := by
      change (x : H) ∈ spectralSquareMomentDomain E
      exact cayleyRealSpectralMeasure_mem_domain T hT x
    let z₀ : M.domain := ⟨(x : H), hxM⟩
    have hz : z = z₀ := by
      apply Subtype.ext
      exact hxz.symm
    apply ext_inner_left ℂ
    intro y
    have hfi : (E.scalarMeasure (x : H) y).Integrable id := (hres x).1 y
    have hweak :=
      QuantumMechanics.WOTSpectralMeasure.truncationIntegral_inner_tendsto_weakIntegral
        E (x : H) y hfi
    have hcomplex : Filter.Tendsto
        (fun n : ℕ => ∫ᵛ r, QuantumMechanics.WOTSpectralMeasure.truncationFunction n r ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); E.scalarMeasure (x : H) y])
        Filter.atTop (𝓝 (E.weakIntegral id (x : H) y)) := by
      apply hweak.congr'
      filter_upwards [] with n
      have htrunc : (E.scalarMeasure (x : H) y).Integrable
          (QuantumMechanics.WOTSpectralMeasure.realTruncationFunction n) := by
        rcases QuantumMechanics.WOTSpectralMeasure.realTruncationFunction_bounded n with ⟨C, hC⟩
        let := QuantumMechanics.WOTSpectralMeasure.scalarMeasure_isFiniteVariation E (x : H) y
        apply Integrable.of_bound
          (QuantumMechanics.WOTSpectralMeasure.realTruncationFunction_measurable
              n).aestronglyMeasurable C
        filter_upwards [] with r
        simpa [Real.norm_eq_abs] using hC r
      have hreal := QuantumMechanics.WOTSpectralMeasure.integral_real_eq_complex
        (E.scalarMeasure (x : H) y) htrunc
      have hfun : (fun r => QuantumMechanics.WOTSpectralMeasure.truncationFunction n r) =
          (fun r => Complex.ofRealCLM
            (QuantumMechanics.WOTSpectralMeasure.realTruncationFunction n r)) := by
        funext r
        simpa [Complex.ofRealCLM_apply] using congrFun
          (QuantumMechanics.WOTSpectralMeasure.realTruncationFunction_complex_eq n).symm r
      calc
        ∫ᵛ r, QuantumMechanics.WOTSpectralMeasure.realTruncationFunction n r ∂[
            ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); E.scalarMeasure (x : H) y] =
            ∫ᵛ r, Complex.ofRealCLM
              (QuantumMechanics.WOTSpectralMeasure.realTruncationFunction n r) ∂[
                ContinuousLinearMap.lsmul ℝ ℂ; E.scalarMeasure (x : H) y] :=
          hreal
        _ = ∫ᵛ r, QuantumMechanics.WOTSpectralMeasure.truncationFunction n r ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); E.scalarMeasure (x : H) y] :=
          congrArg (fun f : ℝ → ℂ => ∫ᵛ r, f r ∂[
            ContinuousLinearMap.lsmul ℝ ℂ; E.scalarMeasure (x : H) y]) hfun.symm
    have hmax :=
      QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_weak_truncation_reconstruction
        E (x : H) hxM y
    have hinner : ⟪y, M z₀⟫_ℂ = E.weakIntegral id (x : H) y :=
      tendsto_nhds_unique hmax hcomplex
    calc
      ⟪y, T x⟫_ℂ = E.weakIntegral id (x : H) y := (hres x).2 y
      _ = ⟪y, M z₀⟫_ℂ := hinner.symm
      _ = ⟪y, M z⟫_ℂ := by rw [hz]

theorem cayleyRealSpectralMeasure_eq_maximal
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    maximalSpectralIntegral
        (cayleyRealSpectralMeasure T hT) = T := by
  exact maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution
      T hT
      (cayleyRealSpectralMeasure_isWeakSpectralResolution T hT)
      (fun x => cayleyRealSpectralMeasure_mem_domain T hT x)

theorem cayleyDomainAwareSelfAdjointSpectralTheorem
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    DomainAwareSelfAdjointSpectralTheorem T (cayleyRealSpectralMeasure T hT) := by
  exact domainAwareSelfAdjointSpectralTheorem_of_isWeakSpectralResolution
      T hT
      (cayleyRealSpectralMeasure_isWeakSpectralResolution T hT)
      (fun x => cayleyRealSpectralMeasure_mem_domain T hT x)

/-- The public unbounded spectral theorem for a self-adjoint `LinearPMap`.

The Cayley transform is an implementation detail of the construction: the result exposes the
real spectral measure and the exact square-moment domain through the standard
`DomainAwareSelfAdjointSpectralTheorem` interface.  Clients that already have a self-adjoint
operator should use this facade rather than depending on the Cayley-side names. -/
theorem unboundedSpectralTheorem
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    DomainAwareSelfAdjointSpectralTheorem T (cayleyRealSpectralMeasure T hT) := by
  exact cayleyDomainAwareSelfAdjointSpectralTheorem T hT

/-- The public Cayley-based theorem starting from an essentially self-adjoint core.

The operator supplied to the spectral API is the canonical graph closure.  Thus the implication
`essential self-adjointness → self-adjoint closure → exact unbounded spectral theorem` is visible
in one declaration, while the returned certificate still exposes the closure domain and the
square-moment domain equality separately. -/
theorem unboundedSpectralTheorem_of_essentiallySelfAdjoint
    (T : H →ₗ.[ℂ] H) (hT : LinearPMap.IsEssentiallySelfAdjoint T) :
    DomainAwareSelfAdjointSpectralTheorem T.closure
      (cayleyRealSpectralMeasure T.closure hT) := by
  exact cayleyDomainAwareSelfAdjointSpectralTheorem T.closure hT

end QuantumMechanics

end
