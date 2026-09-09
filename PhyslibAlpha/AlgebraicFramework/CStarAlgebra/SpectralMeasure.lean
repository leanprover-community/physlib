/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Observable
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.OrderUnit
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.SharpEffect
public import PhyslibAlpha.AlgebraicFramework.Measurement.Basic
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Algebra.Indicator

/-!

# The probability measure of an observable in a state

A state `ω` and an observable `a` together fix a probability measure `μ_{ω,a}` on `ℝ`: the one
against which integrating `f` gives `ω(f(a))`, so it's what you integrate against for `a`'s
expectation, variance, or any other statistic in the preparation `ω`. `μ_{ω,a}` is supported on
`a`'s spectrum and is the unique measure with this property.

Restricting `ω` to the observables of the continuous functional calculus of `a`
(`UnitalPositiveLinearMap.onObservables`, `Observable.lean`) turns `ω, a` into one positive,
normalized functional on `C(σ_ℝ(a), ℝ)` — exactly the input to Riesz–Markov–Kakutani, which
Mathlib already supplies. Pushing the result forward along `σ_ℝ(a) ↪ ℝ` gives `μ_{ω,a}`.

This is the concrete payoff of the whole measurement layer built on top of `OrderUnit/`
(`OVERVIEW.md` §9): `μ_{ω,a}` *is* the outcome distribution of measuring the single observable `a`
in the preparation `ω`. The "Connection to the abstract measurement layer" section below makes
this precise at every isolated point of `a`'s spectrum — a genuine eigenvalue with a spectral
gap — where CFC already supplies the spectral projection needed to state it as a bona fide
`Measurement`, matching `Measurement.outcomeDistribution` (`Measurement/Basic.lean`) exactly.
Doing this at every Borel set at once, recovering `μ_{ω,a}` as a full
`EffectValuedMeasure ℝ (selfAdjoint A)` (a PVM), would need a projection for every Borel set —
the measurable functional calculus underlying the spectral theorem — which this codebase does not
yet have; only continuous functional calculus (`cfc`, `cfcHom`) is available, and that reaches
exactly the clopen (isolated-point) subsets of the spectrum and no further.

## Main definitions

- `spectralMeasure`, `realSpectralMeasure` : `μ_{ω,a}`, first on `a`'s spectrum, then on `ℝ`.
- `realSpectralMeasure_integral` : `ω(f(a)) = ∫ f dμ_{ω,a}`.
- `realSpectralMeasure_unique` : `μ_{ω,a}` is the only probability measure on `ℝ`, concentrated on
  `a`'s spectrum, reproducing `ω(f(a))` this way.
- `eigenEffect`, `eigenMeasurement` : the two-outcome measurement "does `a` read out `x`?" at an
  isolated spectral point `x`, and `eigenMeasurement_outcomeDistribution_true` : its outcome
  distribution in `ω` matches `μ_{ω,a}({x})`.

-/

@[expose] public section

open MeasureTheory CompactlySupportedContinuousMap
open scoped CompactlySupported ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `f ↦ ω.onObservables (f(a))`: positive since `ω` is a state and `f(a) ≥ 0` for `f ≥ 0`;
already real-valued, with no detour through `Re` needed, since `onObservables` is a state on the
observables directly (`Observable.lean`). -/
noncomputable def spectralFunctional (ω : 𝓢[A]) (a : Observable A) :
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

/-- `spectralFunctional` on compactly supported functions (all functions, since the spectrum is
compact), as `RealRMK.rieszMeasure` requires. -/
noncomputable def spectralFunctionalCc (ω : 𝓢[A]) (a : Observable A) :
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
noncomputable def spectralMeasure (ω : 𝓢[A]) (a : Observable A) :
    Measure (spectrum ℝ (a : A)) :=
  RealRMK.rieszMeasure (spectralFunctionalCc ω a)

instance spectralMeasure_isFiniteMeasure (ω : 𝓢[A]) (a : Observable A) :
    IsFiniteMeasure (spectralMeasure ω a) := by
  unfold spectralMeasure; infer_instance

lemma spectralFunctional_one (ω : 𝓢[A]) (a : Observable A) :
    spectralFunctional ω a 1 = 1 := by
  show ω.onObservables ⟨cfcHom a.property (1 : C(spectrum ℝ (a : A), ℝ)),
    cfcHom_predicate a.property 1⟩ = 1
  have heq : (⟨cfcHom a.property (1 : C(spectrum ℝ (a : A), ℝ)), cfcHom_predicate a.property 1⟩ :
      Observable A) = 1 := by
    apply Subtype.ext; simp
  rw [heq, map_one]

/-- Total mass one, matching `ω(1) = 1`. -/
instance spectralMeasure_isProbabilityMeasure (ω : 𝓢[A]) (a : Observable A) :
    IsProbabilityMeasure (spectralMeasure ω a) := by
  rw [isProbabilityMeasure_iff_real, ← spectralFunctional_one ω a]
  have hg : (spectralFunctionalCc ω a) (continuousMapEquiv 1) = spectralFunctional ω a 1 := rfl
  rw [← hg, ← RealRMK.integral_rieszMeasure (spectralFunctionalCc ω a) (continuousMapEquiv 1)]
  simp [spectralMeasure, measureReal_def]

/-- `∫ f dμ = ω(f(a))` on the spectrum. -/
lemma spectralMeasure_integral (ω : 𝓢[A]) (a : Observable A)
    (f : C(spectrum ℝ (a : A), ℝ)) :
    ω.onObservables ⟨cfcHom a.property f, cfcHom_predicate a.property f⟩ =
      ∫ x, f x ∂(spectralMeasure ω a) := by
  show (spectralFunctional ω a) f = _
  show (spectralFunctional ω a) f =
      ∫ x, (continuousMapEquiv f : spectrum ℝ (a : A) → ℝ) x ∂(spectralMeasure ω a)
  exact (RealRMK.integral_rieszMeasure (spectralFunctionalCc ω a) (continuousMapEquiv f)).symm

/-- The probability measure `μ_{ω,a}` on `ℝ`: `spectralMeasure` pushed forward along the inclusion
of the spectrum into `ℝ`. Integrating `f` against it gives `ω(f(a))`
(`realSpectralMeasure_integral`), so this is what to integrate against for `a`'s expectation,
variance, or any other statistic in the state `ω`. -/
noncomputable def realSpectralMeasure (ω : 𝓢[A]) (a : Observable A) : Measure ℝ :=
  Measure.map Subtype.val (spectralMeasure ω a)

instance realSpectralMeasure_isProbabilityMeasure (ω : 𝓢[A]) (a : Observable A) :
    IsProbabilityMeasure (realSpectralMeasure ω a) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

/-- `μ_{ω,a}` is concentrated on `a`'s spectrum. -/
lemma realSpectralMeasure_compl_spectrum (ω : 𝓢[A]) (a : Observable A) :
    realSpectralMeasure ω a (spectrum ℝ (a : A))ᶜ = 0 := by
  have hmeas : MeasurableSet (spectrum ℝ (a : A))ᶜ :=
    (spectrum.isClosed (a : A)).measurableSet.compl
  show Measure.map Subtype.val (spectralMeasure ω a) (spectrum ℝ (a : A))ᶜ = 0
  rw [Measure.map_apply measurable_subtype_coe hmeas]
  convert measure_empty (μ := spectralMeasure ω a)
  ext x
  simp

/-- `∫ f dμ_{ω,a} = ω(f(a))`, for any `f` continuous on the spectrum of `a`. -/
lemma realSpectralMeasure_integral (ω : 𝓢[A]) (a : Observable A) (f : ℝ → ℝ)
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
lemma comap_integral_eq (ω : 𝓢[A]) (a : Observable A) (μ : Measure ℝ)
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
lemma realSpectralMeasure_unique (ω : 𝓢[A]) (a : Observable A) (μ : Measure ℝ)
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

## Connection to the abstract measurement layer

An isolated point `x` of `a`'s spectrum — one for which `{x}` is clopen in the subspace topology,
i.e. a genuine eigenvalue with a spectral gap around it — is exactly where continuous functional
calculus already reaches: the indicator function of `{x}` is continuous there (clopen sets have
continuous indicators, `IsClopen.continuous_indicator`), so CFC turns it into an honest spectral
projection `eigenEffect`. Pairing that projection with its complement is a two-outcome
`Measurement` (`Measurement/Basic.lean`) — "does `a` read out `x`, or not?" — and its outcome
distribution in `ω` is exactly `μ_{ω,a}` evaluated at `{x}` and its complement
(`eigenMeasurement_outcomeDistribution_true`): the abstract POVM layer's Born rule and the
concrete spectral measure built above agree at every point either can see.

What is not attempted: doing this simultaneously at every Borel subset of the spectrum, so that
`x ↦ eigenEffect` extends to a full projection-valued `EffectValuedMeasure ℝ (selfAdjoint A)`
agreeing with `realSpectralMeasure` on every Borel set (not just clopen singletons), needs a
projection for every Borel set — the *measurable* functional calculus underlying the spectral
theorem for self-adjoint operators. That is a substantially larger piece of infrastructure than
continuous functional calculus, and this codebase does not have it yet.
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

/-- The spectral projection at an isolated point `x` of `a`'s spectrum: `cfc` applied to the
(continuous, since `{x}` is clopen) indicator function of `{x}`. Idempotent, hence sharp
(`IsIdempotentElem.isSharp`) — a genuine projection in the operator-algebraic sense. -/
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

/-- `eigenEffect` is sharp: a genuine projection, not merely an effect. -/
lemma isSharp_eigenEffect (a : Observable A) {x : spectrum ℝ (a : A)}
    (hx : IsClopen ({x} : Set (spectrum ℝ (a : A)))) :
    Effect.IsSharp (eigenEffect a hx) :=
  (isIdempotentElem_eigenEffect a hx).isSharp

/-- The two-outcome measurement "does `a` read out the isolated spectral point `x`, or not?" -/
noncomputable def eigenMeasurement (a : Observable A) {x : spectrum ℝ (a : A)}
    (hx : IsClopen ({x} : Set (spectrum ℝ (a : A)))) : Measurement (Observable A) Bool where
  outcomes := Finset.univ
  effects := fun b => if b then eigenEffect a hx else Effect.complement (eigenEffect a hx)
  sum_eq_one := by
    show ∑ b : Bool,
        ((if b then eigenEffect a hx else Effect.complement (eigenEffect a hx) :
          Effect (Observable A)) : Observable A) = 1
    rw [Fintype.sum_bool]
    show ((eigenEffect a hx : Effect (Observable A)) : Observable A) +
        ((Effect.complement (eigenEffect a hx) : Effect (Observable A)) : Observable A) = 1
    have : ((Effect.complement (eigenEffect a hx) : Effect (Observable A)) : Observable A) =
        1 - ((eigenEffect a hx : Effect (Observable A)) : Observable A) := rfl
    rw [this]
    abel

/-- The outcome distribution of `eigenMeasurement` in `ω` matches `μ_{ω,a}` at `{x}`: the
abstract Born rule of the two-outcome measurement "does `a` read out `x`?" agrees with the
concrete probability measure built from `a`'s continuous functional calculus. -/
theorem eigenMeasurement_outcomeDistribution_true (ω : 𝓢[A]) (a : Observable A)
    {x : spectrum ℝ (a : A)} (hx : IsClopen ({x} : Set (spectrum ℝ (a : A)))) :
    (eigenMeasurement a hx).outcomeDistribution ω.onObservables ⟨true, Finset.mem_univ true⟩ =
      (realSpectralMeasure ω a).real ({(x : ℝ)} : Set ℝ) := by
  rw [Measurement.outcomeDistribution_apply]
  show ω.onObservables (eigenEffect a hx : Observable A) = _
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
