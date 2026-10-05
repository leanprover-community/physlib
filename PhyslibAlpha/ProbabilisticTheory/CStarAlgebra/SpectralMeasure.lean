/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Observable
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.OrderUnit
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.SharpEffect
public import PhyslibAlpha.ProbabilisticTheory.Measurement.Binary
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Algebra.Indicator

/-!

# The distribution of an observable

The outcome distribution of an observable in a state, and the measurement of an isolated eigenvalue.

## i. Overview

A state `ω` and an observable `a` determine a probability measure `μ_{ω,a}` on `ℝ`, the distribution
of the outcomes of measuring `a` in `ω`. It is the unique probability measure on the spectrum of `a`
with `ω(f(a)) = ∫ f dμ_{ω,a}` for continuous `f`, given by the Riesz–Markov–Kakutani theorem. At an
isolated point `x` of the spectrum the spectral projection gives a two-outcome measurement "does `a`
take the value `x`?", whose probability of `true` is `μ_{ω,a}({x})`.

## ii. Key results

- `realSpectralMeasure` : the distribution `μ_{ω,a}`.
- `realSpectralMeasure_integral` : `ω(f(a)) = ∫ f dμ_{ω,a}`.
- `realSpectralMeasure_unique` : the distribution is unique.
- `eigenMeasurement` : the measurement of an isolated eigenvalue.
- `eigenMeasurement_true` : its outcome probability is `μ_{ω,a}({x})`.

## iii. Table of contents

- A. Measuring an isolated eigenvalue

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open MeasureTheory CompactlySupportedContinuousMap
open scoped CompactlySupported ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The positive functional `f ↦ ω(f(a))` on continuous functions on the spectrum of `a`. -/
noncomputable def spectralFunctional (ω : 𝓢[ℂ, A]) (a : Observable A) :
    C(spectrum ℝ (a : A), ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => ω.onObservables ⟨cfcHom a.property f, cfcHom_predicate a.property f⟩
      map_add' := fun f g => by
        have heq : (⟨cfcHom a.property (f + g), cfcHom_predicate a.property (f + g)⟩ :
            Observable A) = ⟨cfcHom a.property f, cfcHom_predicate a.property f⟩ +
              ⟨cfcHom a.property g, cfcHom_predicate a.property g⟩ := by
          apply Subtype.ext; simp
        rw [heq, map_add]
      map_smul' := fun c f => by
        have heq : (⟨cfcHom a.property (c • f), cfcHom_predicate a.property (c • f)⟩ :
            Observable A) = c • ⟨cfcHom a.property f, cfcHom_predicate a.property f⟩ := by
          apply Subtype.ext; simp
        rw [heq, map_smul]; rfl }
    (fun f hf => by
      have hnn : (0 : A) ≤ cfcHom a.property f := by
        have := cfcHom_mono a.property (f := (0 : C(spectrum ℝ (a : A), ℝ))) (g := f) hf
        simpa using this
      exact ω.onObservables.map_nonneg hnn)

/-- `spectralFunctional` on compactly supported functions. -/
noncomputable def spectralFunctionalCc (ω : 𝓢[ℂ, A]) (a : Observable A) :
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
noncomputable def spectralMeasure (ω : 𝓢[ℂ, A]) (a : Observable A) :
    Measure (spectrum ℝ (a : A)) :=
  RealRMK.rieszMeasure (spectralFunctionalCc ω a)

instance spectralMeasure_isFiniteMeasure (ω : 𝓢[ℂ, A]) (a : Observable A) :
    IsFiniteMeasure (spectralMeasure ω a) := by
  unfold spectralMeasure; infer_instance

lemma spectralFunctional_one (ω : 𝓢[ℂ, A]) (a : Observable A) :
    spectralFunctional ω a 1 = 1 := by
  show ω.onObservables ⟨cfcHom a.property (1 : C(spectrum ℝ (a : A), ℝ)),
    cfcHom_predicate a.property 1⟩ = 1
  have heq : (⟨cfcHom a.property (1 : C(spectrum ℝ (a : A), ℝ)), cfcHom_predicate a.property 1⟩ :
      Observable A) = 1 := by
    apply Subtype.ext; simp
  rw [heq, map_one]

/-- Total mass one, matching `ω(1) = 1`. -/
instance spectralMeasure_isProbabilityMeasure (ω : 𝓢[ℂ, A]) (a : Observable A) :
    IsProbabilityMeasure (spectralMeasure ω a) := by
  rw [isProbabilityMeasure_iff_real, ← spectralFunctional_one ω a]
  have hg : (spectralFunctionalCc ω a) (continuousMapEquiv 1) = spectralFunctional ω a 1 := rfl
  rw [← hg, ← RealRMK.integral_rieszMeasure (spectralFunctionalCc ω a) (continuousMapEquiv 1)]
  simp [spectralMeasure, measureReal_def]

/-- `∫ f dμ = ω(f(a))` on the spectrum. -/
lemma spectralMeasure_integral (ω : 𝓢[ℂ, A]) (a : Observable A)
    (f : C(spectrum ℝ (a : A), ℝ)) :
    ω.onObservables ⟨cfcHom a.property f, cfcHom_predicate a.property f⟩ =
      ∫ x, f x ∂(spectralMeasure ω a) := by
  show (spectralFunctional ω a) f = _
  show (spectralFunctional ω a) f =
      ∫ x, (continuousMapEquiv f : spectrum ℝ (a : A) → ℝ) x ∂(spectralMeasure ω a)
  exact (RealRMK.integral_rieszMeasure (spectralFunctionalCc ω a) (continuousMapEquiv f)).symm

/-- **The distribution of `a` in `ω`**, the probability measure `μ_{ω,a}` on `ℝ` with `ω(f(a)) = ∫ f
dμ_{ω,a}`. -/
noncomputable def realSpectralMeasure (ω : 𝓢[ℂ, A]) (a : Observable A) : Measure ℝ :=
  Measure.map Subtype.val (spectralMeasure ω a)

instance realSpectralMeasure_isProbabilityMeasure (ω : 𝓢[ℂ, A]) (a : Observable A) :
    IsProbabilityMeasure (realSpectralMeasure ω a) :=
  (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr inferInstance

/-- `μ_{ω,a}` is concentrated on `a`'s spectrum. -/
lemma realSpectralMeasure_compl_spectrum (ω : 𝓢[ℂ, A]) (a : Observable A) :
    realSpectralMeasure ω a (spectrum ℝ (a : A))ᶜ = 0 := by
  have hmeas : MeasurableSet (spectrum ℝ (a : A))ᶜ :=
    (spectrum.isClosed (a : A)).measurableSet.compl
  show Measure.map Subtype.val (spectralMeasure ω a) (spectrum ℝ (a : A))ᶜ = 0
  rw [Measure.map_apply measurable_subtype_coe hmeas]
  convert measure_empty (μ := spectralMeasure ω a)
  ext x
  simp

/-- `∫ f dμ_{ω,a} = ω(f(a))`, for any `f` continuous on the spectrum of `a`. -/
lemma realSpectralMeasure_integral (ω : 𝓢[ℂ, A]) (a : Observable A) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (a : A))) :
    ω.onObservables ⟨cfc f (a : A), cfc_predicate f (a : A)⟩ =
      ∫ y, f y ∂(realSpectralMeasure ω a) := by
  have hemb : MeasurableEmbedding (Subtype.val : spectrum ℝ (a : A) → ℝ) :=
    MeasurableEmbedding.subtype_coe (spectrum.isClosed (a : A)).measurableSet
  have hmap : (∫ y, f y ∂(realSpectralMeasure ω a)) =
      (∫ x, f (x : ℝ) ∂(spectralMeasure ω a)) :=
    hemb.integral_map f
  rw [hmap]
  have heq : (⟨cfc f (a : A), cfc_predicate f (a : A)⟩ : Observable A) =
      ⟨cfcHom a.property (⟨fun x => f x, hf.domRestrict⟩ : C(spectrum ℝ (a : A), ℝ)),
        cfcHom_predicate a.property _⟩ := by
    apply Subtype.ext
    exact cfc_apply f (a : A) a.property hf
  rw [heq]
  exact spectralMeasure_integral ω a ⟨fun x => f x, hf.domRestrict⟩

omit [PartialOrder A] [StarOrderedRing A] in
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
lemma comap_integral_eq (ω : 𝓢[ℂ, A]) (a : Observable A) (μ : Measure ℝ)
    (hrep : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (a : A)) →
      ω.onObservables ⟨cfc f (a : A), cfc_predicate f (a : A)⟩ = ((∫ y, f y ∂μ : ℝ)))
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
  have hgeq : (⟨cfc f (a : A), cfc_predicate f (a : A)⟩ : Observable A) =
      ⟨cfcHom a.property g, cfcHom_predicate a.property g⟩ := by
    apply Subtype.ext
    show cfc f (a : A) = cfcHom a.property g
    have heq : cfc f (a : A) =
        cfcHom a.property (⟨fun x => f x, hf.domRestrict⟩ : C(spectrum ℝ (a : A), ℝ)) :=
      cfc_apply f (a : A) a.property hf
    rw [heq]
    congr 1
    ext x
    exact hfg x
  rw [hgeq] at hleft
  exact hleft.symm.trans hright

/-- `μ_{ω,a}` is the only probability measure on `ℝ`, concentrated on `a`'s spectrum, with
`∫ f dμ = ω(f(a))`: any other measure with these two properties already is `μ_{ω,a}`. -/
lemma realSpectralMeasure_unique (ω : 𝓢[ℂ, A]) (a : Observable A) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hsupp : μ (spectrum ℝ (a : A))ᶜ = 0)
    (hrep : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (a : A)) →
      ω.onObservables ⟨cfc f (a : A), cfc_predicate f (a : A)⟩ = ((∫ y, f y ∂μ : ℝ))) :
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

/-!

## A. Measuring an isolated eigenvalue

At an isolated point `x` of the spectrum of `a`, an eigenvalue separated from the rest of the
spectrum, the indicator of `{x}` is continuous on the spectrum, so the continuous functional
calculus gives the spectral projection `eigenEffect`. Its two-outcome measurement asks whether `a`
takes the value `x`, and the probability of `true` in `ω` is `μ_{ω,a}({x})`. Spectral projections of
arbitrary Borel sets need the Borel functional calculus.
-/

/-- The indicator function of an isolated point `x` of `a`'s spectrum, as a continuous function on
the spectrum: continuous because `{x}` is clopen (`IsClopen.continuous_indicator`). -/
noncomputable def eigenIndicator (a : Observable A) {x : spectrum ℝ (a : A)}
    (hx : IsClopen ({x} : Set (spectrum ℝ (a : A)))) : C(spectrum ℝ (a : A), ℝ) :=
  ⟨Set.indicator {x} 1, hx.continuous_indicator continuous_const⟩

omit [PartialOrder A] [StarOrderedRing A] in
@[simp]
lemma eigenIndicator_apply (a : Observable A) {x : spectrum ℝ (a : A)}
    (hx : IsClopen ({x} : Set (spectrum ℝ (a : A)))) (y : spectrum ℝ (a : A)) :
    eigenIndicator a hx y = Set.indicator {x} 1 y := rfl

/-- The spectral projection of `a` at an isolated point `x` of its spectrum. -/
noncomputable def eigenEffect (a : Observable A) {x : spectrum ℝ (a : A)}
    (hx : IsClopen ({x} : Set (spectrum ℝ (a : A)))) : Effect (Observable A) :=
  ⟨⟨cfcHom a.property (eigenIndicator a hx), cfcHom_predicate a.property (eigenIndicator a hx)⟩,
    by
      have h0 : (0 : C(spectrum ℝ (a : A), ℝ)) ≤ eigenIndicator a hx :=
        ContinuousMap.le_def.mpr fun y => by
          simp only [ContinuousMap.zero_apply, eigenIndicator_apply, Set.indicator_apply,
            Pi.one_apply]
          split <;> norm_num
      have h1 : eigenIndicator a hx ≤ (1 : C(spectrum ℝ (a : A), ℝ)) :=
        ContinuousMap.le_def.mpr fun y => by
          simp only [ContinuousMap.one_apply, eigenIndicator_apply, Set.indicator_apply,
            Pi.one_apply]
          split <;> norm_num
      refine ⟨?_, ?_⟩
      · show (0 : A) ≤ cfcHom a.property (eigenIndicator a hx)
        have := cfcHom_mono a.property h0
        simpa using this
      · show cfcHom a.property (eigenIndicator a hx) ≤ (1 : A)
        have := cfcHom_mono a.property h1
        simpa using this⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma eigenIndicator_mul_self (a : Observable A) {x : spectrum ℝ (a : A)}
    (hx : IsClopen ({x} : Set (spectrum ℝ (a : A)))) :
    eigenIndicator a hx * eigenIndicator a hx = eigenIndicator a hx := by
  ext y
  simp only [ContinuousMap.mul_apply, eigenIndicator_apply, Set.indicator_apply, Pi.one_apply]
  split <;> ring

/-- `eigenEffect` is idempotent: `cfcHom` is an algebra homomorphism, and the indicator function
`eigenIndicator a hx` is already idempotent under pointwise multiplication. -/
lemma isIdempotentElem_eigenEffect (a : Observable A) {x : spectrum ℝ (a : A)}
    (hx : IsClopen ({x} : Set (spectrum ℝ (a : A)))) :
    IsIdempotentElem (((eigenEffect a hx : Effect (Observable A)) : Observable A) : A) := by
  show cfcHom a.property (eigenIndicator a hx) * cfcHom a.property (eigenIndicator a hx) =
      cfcHom a.property (eigenIndicator a hx)
  rw [← map_mul, eigenIndicator_mul_self]

/-- The spectral projection at an isolated point is sharp. -/
lemma isSharp_eigenEffect (a : Observable A) {x : spectrum ℝ (a : A)}
    (hx : IsClopen ({x} : Set (spectrum ℝ (a : A)))) :
    Effect.IsSharp (eigenEffect a hx) :=
  (isIdempotentElem_eigenEffect a hx).isSharp

/-- The two-outcome measurement "does `a` read out the isolated spectral point `x`, or not?" -/
noncomputable def eigenMeasurement (a : Observable A) {x : spectrum ℝ (a : A)}
    (hx : IsClopen ({x} : Set (spectrum ℝ (a : A)))) : Measurement Bool (Observable A) :=
  Effect.binaryMeasurement (eigenEffect a hx)

/-- The probability that `eigenMeasurement` reads out `x` in `ω` is `μ_{ω,a}({x})`: the Born rule
of the two-outcome measurement "does `a` read out `x`?" agrees with the probability measure built
from `a`'s continuous functional calculus. -/
lemma eigenMeasurement_true (ω : 𝓢[ℂ, A]) (a : Observable A)
    {x : spectrum ℝ (a : A)} (hx : IsClopen ({x} : Set (spectrum ℝ (a : A))))
    (h : MeasurableSet {true}) :
    ω.onObservables (eigenMeasurement a hx {true} h : Observable A) =
      (realSpectralMeasure ω a).real ({(x : ℝ)} : Set ℝ) := by
  rw [eigenMeasurement, Effect.binaryMeasurement_true]
  have hmeas : MeasurableSet ({(x : ℝ)} : Set ℝ) := measurableSet_singleton _
  rw [show ((eigenEffect a hx : Effect (Observable A)) : Observable A) =
      ⟨cfcHom a.property (eigenIndicator a hx), cfcHom_predicate a.property (eigenIndicator a hx)⟩
      from rfl,
    spectralMeasure_integral ω a (eigenIndicator a hx),
    show realSpectralMeasure ω a = Measure.map Subtype.val (spectralMeasure ω a) from rfl,
    map_measureReal_apply measurable_subtype_coe hmeas]
  have hpre : (Subtype.val : spectrum ℝ (a : A) → ℝ) ⁻¹' ({(x : ℝ)} : Set ℝ) = {x} := by
    ext y; simp [Subtype.ext_iff]
  rw [hpre]
  simp only [eigenIndicator_apply]
  exact integral_indicator_one (measurableSet_singleton x)

end ProbabilisticTheory
