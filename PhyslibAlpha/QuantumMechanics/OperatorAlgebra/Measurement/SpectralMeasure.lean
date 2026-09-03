/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.States.Basic
public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.Observables.Basic
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!

# The probability measure of an observable in a state

A state `ω` and an observable `a` together fix a probability measure `μ_{ω,a}` on `ℝ`: the one
against which integrating `f` gives `ω(f(a))`, so it's what you integrate against for `a`'s
expectation, variance, or any other statistic in the preparation `ω`. `μ_{ω,a}` is supported on
`a`'s spectrum and is the unique measure with this property.

Restricting `Re ∘ ω` to the continuous functional calculus of `a` turns `ω, a` into one positive,
normalized functional on `C(σ_ℝ(a), ℝ)` — exactly the input to Riesz–Markov–Kakutani, which
Mathlib already supplies. Pushing the result forward along `σ_ℝ(a) ↪ ℝ` gives `μ_{ω,a}`.

-/

@[expose] public section

open MeasureTheory CompactlySupportedContinuousMap
open scoped CompactlySupported ComplexOrder

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- `f ↦ Re ω(f(a))`: positive since `ω` is a state and `f(a) ≥ 0` for `f ≥ 0`; real-valued for
free since `f(a)` is self-adjoint. -/
noncomputable def spectralFunctional (ω : State A) (a : Observable A) :
    C(spectrum ℝ (a : A), ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => (ω (cfcHom a.property f) : ℂ).re
      map_add' := fun f g => by simp
      map_smul' := fun c f => by simp }
    (fun f hf => by
      have hnn : (0 : A) ≤ cfcHom a.property f := by
        have := cfcHom_mono a.property (f := (0 : C(spectrum ℝ (a : A), ℝ))) (g := f) hf
        simpa using this
      exact (Complex.le_def.mp (ω.toPositiveLinearMap.map_nonneg hnn)).1)

/-- `spectralFunctional` on compactly supported functions (all functions, since the spectrum is
compact), as `RealRMK.rieszMeasure` requires. -/
noncomputable def spectralFunctionalCc (ω : State A) (a : Observable A) :
    C_c(spectrum ℝ (a : A), ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => spectralFunctional ω a f.toContinuousMap
      map_add' := fun f g => by
        show spectralFunctional ω a (f + g).toContinuousMap = _
        rw [show (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap from rfl, map_add]
      map_smul' := fun c f => by
        show spectralFunctional ω a (c • f).toContinuousMap = _
        rw [show (c • f).toContinuousMap = c • f.toContinuousMap from rfl]
        exact (spectralFunctional ω a).toLinearMap.map_smul c f.toContinuousMap }
    (fun f hf => (spectralFunctional ω a).map_nonneg hf)

/-- `spectralMeasure` on the spectrum itself; `realSpectralMeasure` below places it inside `ℝ`. -/
noncomputable def spectralMeasure (ω : State A) (a : Observable A) :
    Measure (spectrum ℝ (a : A)) :=
  RealRMK.rieszMeasure (spectralFunctionalCc ω a)

instance spectralMeasure_isFiniteMeasure (ω : State A) (a : Observable A) :
    IsFiniteMeasure (spectralMeasure ω a) := by
  unfold spectralMeasure; infer_instance

lemma spectralFunctional_one (ω : State A) (a : Observable A) :
    spectralFunctional ω a 1 = 1 := by
  show (ω (cfcHom a.property (1 : C(spectrum ℝ (a : A), ℝ))) : ℂ).re = 1
  rw [map_one, show ω (1 : A) = 1 from ω.map_one']
  rfl

/-- Total mass one, matching `ω(1) = 1`. -/
instance spectralMeasure_isProbabilityMeasure (ω : State A) (a : Observable A) :
    IsProbabilityMeasure (spectralMeasure ω a) := by
  rw [isProbabilityMeasure_iff_real, ← spectralFunctional_one ω a]
  have hg : (spectralFunctionalCc ω a) (continuousMapEquiv 1) = spectralFunctional ω a 1 := rfl
  rw [← hg, ← RealRMK.integral_rieszMeasure (spectralFunctionalCc ω a) (continuousMapEquiv 1)]
  simp [spectralMeasure, measureReal_def]

/-- `∫ f dμ = ω(f(a))` on the spectrum. -/
lemma spectralMeasure_integral (ω : State A) (a : Observable A)
    (f : C(spectrum ℝ (a : A), ℝ)) :
    ω (cfcHom a.property f) = ((∫ x, f x ∂(spectralMeasure ω a) : ℝ) : ℂ) := by
  have hself : IsSelfAdjoint (cfcHom a.property f) := cfcHom_predicate a.property f
  have hreal := State.state_is_real_on_selfAdjoint ω hself
  have hint : (∫ x, f x ∂(spectralMeasure ω a)) = spectralFunctional ω a f := by
    show (∫ x, (continuousMapEquiv f : spectrum ℝ (a : A) → ℝ) x ∂(spectralMeasure ω a)) = _
    exact RealRMK.integral_rieszMeasure (spectralFunctionalCc ω a) (continuousMapEquiv f)
  rw [hint]
  show _ = ((ω (cfcHom a.property f) : ℂ).re : ℂ)
  apply Complex.ext
  · simp
  · simpa using hreal

/-- The probability measure `μ_{ω,a}` on `ℝ`: `spectralMeasure` pushed forward along the inclusion
of the spectrum into `ℝ`. Integrating `f` against it gives `ω(f(a))`
(`realSpectralMeasure_integral`), so this is what to integrate against for `a`'s expectation,
variance, or any other statistic in the state `ω`. -/
noncomputable def realSpectralMeasure (ω : State A) (a : Observable A) : Measure ℝ :=
  Measure.map Subtype.val (spectralMeasure ω a)

instance realSpectralMeasure_isProbabilityMeasure (ω : State A) (a : Observable A) :
    IsProbabilityMeasure (realSpectralMeasure ω a) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

/-- `μ_{ω,a}` is concentrated on `a`'s spectrum. -/
lemma realSpectralMeasure_compl_spectrum (ω : State A) (a : Observable A) :
    realSpectralMeasure ω a (spectrum ℝ (a : A))ᶜ = 0 := by
  have hmeas : MeasurableSet (spectrum ℝ (a : A))ᶜ :=
    (spectrum.isClosed (a : A)).measurableSet.compl
  show Measure.map Subtype.val (spectralMeasure ω a) (spectrum ℝ (a : A))ᶜ = 0
  rw [Measure.map_apply measurable_subtype_coe hmeas]
  convert measure_empty (μ := spectralMeasure ω a)
  ext x
  simp

/-- `∫ f dμ_{ω,a} = ω(f(a))`, for any `f` continuous on the spectrum of `a`. -/
lemma realSpectralMeasure_integral (ω : State A) (a : Observable A) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (a : A))) :
    ω (cfc f (a : A)) = ((∫ y, f y ∂(realSpectralMeasure ω a) : ℝ) : ℂ) := by
  have hemb : MeasurableEmbedding (Subtype.val : spectrum ℝ (a : A) → ℝ) :=
    MeasurableEmbedding.subtype_coe (spectrum.isClosed (a : A)).measurableSet
  have hmap : (∫ y, f y ∂(realSpectralMeasure ω a)) =
      (∫ x, f (x : ℝ) ∂(spectralMeasure ω a)) :=
    hemb.integral_map f
  rw [hmap]
  have heq : cfc f (a : A) =
      cfcHom a.property (⟨fun x => f x, hf.domRestrict⟩ : C(spectrum ℝ (a : A), ℝ)) :=
    cfc_apply f (a : A) a.property hf
  rw [heq]
  exact spectralMeasure_integral ω a ⟨fun x => f x, hf.domRestrict⟩

/-- Every continuous function on the spectrum extends to one on `ℝ`, continuous on the spectrum. -/
lemma exists_continuousOn_extend (a : Observable A) (g : C(spectrum ℝ (a : A), ℝ)) :
    ∃ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (a : A)) ∧
      ∀ x : spectrum ℝ (a : A), f (x : ℝ) = g x := by
  classical
  refine ⟨fun y => if h : y ∈ spectrum ℝ (a : A) then g ⟨y, h⟩ else 0, ?_, fun x => by simp⟩
  rw [continuousOn_iff_continuous_domRestrict]
  convert g.continuous using 1
  ext x
  simp

/-- If a measure `μ` on `ℝ` reproduces `ω(f(a))` for every continuous `f`, then pulling `μ` back
to the spectrum integrates every continuous test
function there exactly as `spectralMeasure ω a` does. -/
lemma comap_integral_eq (ω : State A) (a : Observable A) (μ : Measure ℝ)
    (hrep : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (a : A)) →
      ω (cfc f (a : A)) = ((∫ y, f y ∂μ : ℝ) : ℂ))
    (hcomap_map :
      Measure.map Subtype.val (μ.comap (Subtype.val : spectrum ℝ (a : A) → ℝ)) = μ)
    (g : C(spectrum ℝ (a : A), ℝ)) :
    (∫ x, g x ∂(μ.comap (Subtype.val : spectrum ℝ (a : A) → ℝ))) =
      ∫ x, g x ∂(spectralMeasure ω a) := by
  have hemb : MeasurableEmbedding (Subtype.val : spectrum ℝ (a : A) → ℝ) :=
    MeasurableEmbedding.subtype_coe (spectrum.isClosed (a : A)).measurableSet
  obtain ⟨f, hf, hfg⟩ := exists_continuousOn_extend a g
  have hfy : (∫ y, f y ∂μ) =
      ∫ x, f (x : ℝ) ∂(μ.comap (Subtype.val : spectrum ℝ (a : A) → ℝ)) := by
    conv_lhs => rw [← hcomap_map]
    exact hemb.integral_map f
  have hfg' : (∫ x, f (x : ℝ) ∂(μ.comap (Subtype.val : spectrum ℝ (a : A) → ℝ))) =
      ∫ x, g x ∂(μ.comap (Subtype.val : spectrum ℝ (a : A) → ℝ)) :=
    integral_congr_ae (Filter.Eventually.of_forall hfg)
  have hleft := hrep f hf
  rw [hfy, hfg'] at hleft
  have hright := spectralMeasure_integral ω a g
  have hgeq : cfc f (a : A) = cfcHom a.property g := by
    have heq : cfc f (a : A) =
        cfcHom a.property (⟨fun x => f x, hf.domRestrict⟩ : C(spectrum ℝ (a : A), ℝ)) :=
      cfc_apply f (a : A) a.property hf
    rw [heq]
    congr 1
    ext x
    exact hfg x
  rw [hgeq] at hleft
  exact (Complex.ofReal_injective (hright.symm.trans hleft)).symm

/-- `μ_{ω,a}` is the only probability measure on `ℝ`, concentrated on `a`'s spectrum, with
`∫ f dμ = ω(f(a))`: any other measure with these two properties already is `μ_{ω,a}`. -/
lemma realSpectralMeasure_unique (ω : State A) (a : Observable A) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hsupp : μ (spectrum ℝ (a : A))ᶜ = 0)
    (hrep : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (a : A)) →
      ω (cfc f (a : A)) = ((∫ y, f y ∂μ : ℝ) : ℂ)) :
    μ = realSpectralMeasure ω a := by
  have hmeas : MeasurableSet (spectrum ℝ (a : A)) := (spectrum.isClosed (a : A)).measurableSet
  have hemb : MeasurableEmbedding (Subtype.val : spectrum ℝ (a : A) → ℝ) :=
    MeasurableEmbedding.subtype_coe hmeas
  have hcomap_map :
      Measure.map Subtype.val (μ.comap (Subtype.val : spectrum ℝ (a : A) → ℝ)) = μ := by
    rw [map_comap_subtype_coe hmeas]
    exact Measure.restrict_eq_self_of_ae_mem hsupp
  have hfin : IsFiniteMeasure (μ.comap (Subtype.val : spectrum ℝ (a : A) → ℝ)) := by
    constructor
    rw [hemb.comap_apply, Set.image_univ, Subtype.range_coe]
    exact measure_lt_top μ _
  have hreg : (μ.comap (Subtype.val : spectrum ℝ (a : A) → ℝ)).Regular := by infer_instance
  have hintCc : ∀ h : C_c(spectrum ℝ (a : A), ℝ),
      (∫ x, h x ∂(μ.comap (Subtype.val : spectrum ℝ (a : A) → ℝ))) =
        ∫ x, h x ∂(spectralMeasure ω a) :=
    fun h => comap_integral_eq ω a μ hrep hcomap_map h.toContinuousMap
  have hres := MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported hintCc
  rw [← hcomap_map, hres]
  rfl

end OperatorAlgebra
