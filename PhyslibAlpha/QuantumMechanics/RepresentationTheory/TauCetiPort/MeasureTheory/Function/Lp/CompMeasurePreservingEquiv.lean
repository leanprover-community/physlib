/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# `L^p` isometric equivalences from an almost-everywhere inverse pair

Mathlib turns a measure-preserving map `f : α → β` into a linear isometry
`MeasureTheory.Lp.compMeasurePreservingₗᵢ : Lp E p μb →ₗᵢ[𝕜] Lp E p μ`, but stops there: there is
no constructor producing a `LinearIsometryEquiv`. Transporting structure between `L²` spaces —
a Hilbert basis, an orthonormal family, a spectral decomposition — needs the equivalence, since
`HilbertBasis.mapₗᵢ` and its relatives consume `≃ₗᵢ` rather than `→ₗᵢ`.

A change of variables rarely supplies a `MeasurableEquiv`. The maps that arise in practice are
inverse to each other only *almost everywhere*: `Real.cos` and `Real.arccos` are mutually inverse
on `[-1, 1]` and on `(0, π]`, not on all of `ℝ`. This file therefore takes a convenient sufficient
hypothesis — a pair of measure-preserving maps that compose to the identity almost everywhere in
one direction — and builds the isometric equivalence from it. One direction is enough: both
precompositions are linear isometries, hence injective, and an injective map with a one-sided
inverse has that inverse on both sides.

## Main declarations

* `MeasureTheory.Lp.compMeasurePreservingₗᵢ_apply` is the application lemma for Mathlib's
  linear isometry. Mathlib's `@[simps!]` generates only `compMeasurePreservingₗᵢ_apply_coe`,
  which unfolds one level too far to rewrite with.
* `MeasureTheory.Lp.compMeasurePreservingₗᵢEquiv` upgrades that linear isometry to a
  `LinearIsometryEquiv` given a one-sided almost-everywhere inverse partner.
* `MeasureTheory.Lp.coeFn_compMeasurePreservingₗᵢEquiv` and
  `MeasureTheory.Lp.coeFn_compMeasurePreservingₗᵢEquiv_symm` identify the equivalence and its
  inverse with precomposition by `f` and by `g` respectively.
* `MeasureTheory.Lp.compMeasurePreserving_toLp` identifies precomposition on the `Lp` class of a
  continuous function with ordinary composition of continuous maps.

This construction generalizes the by-hand equivalence
`TauCeti.chebyshevCosineL2Equiv`
(`TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Cosine/Transfer.lean`), which builds
exactly this `≃ₗᵢ` for the specific `Real.cos` / `Real.arccos` pair via `ofLinearIsometry` with a
separately constructed inverse; the proof plan here is drawn from it.
-/

public section

open scoped ENNReal

namespace MeasureTheory
namespace Lp

/-- The application lemma for `MeasureTheory.Lp.compMeasurePreservingₗᵢ`.

Mathlib marks that definition `@[simps!]`, which generates `compMeasurePreservingₗᵢ_apply_coe`
— an equation about the underlying `AEEqFun`, one unfolding past the point where a rewrite is
usable. This states the map itself. -/
@[simp]
theorem compMeasurePreservingₗᵢ_apply {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E] {f : α → β}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (x : Lp E p μb) :
    compMeasurePreservingₗᵢ 𝕜 f hf x = compMeasurePreserving f hf x :=
  rfl

/-- If `f` and `g` are measure-preserving and `f ∘ g` is the identity almost everywhere, then
precomposing by `g` undoes precomposing by `f`. -/
theorem compMeasurePreserving_comp_apply_of_ae_id {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α} (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μb) :
    compMeasurePreserving g hg (compMeasurePreserving f hf x) = x := by
  rw [← compMeasurePreserving_comp_apply (E := E) (p := p) x hf hg]
  refine Subtype.ext ?_
  rw [compMeasurePreserving_val,
    AEEqFun.compMeasurePreserving_congr _ _ measurable_id hfg,
    AEEqFun.compMeasurePreserving_id]

/-- Precomposition of the `Lp` class of a continuous function by a measure-preserving continuous
map is the `Lp` class of the composite continuous function. -/
@[simp]
theorem compMeasurePreserving_toLp {α β E : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] [TopologicalSpace β] [CompactSpace β] [MeasurableSpace β]
    [BorelSpace β] [NormedAddCommGroup E] [SecondCountableTopologyEither α E]
    [SecondCountableTopologyEither β E] {μ : Measure α} {μb : Measure β} [IsFiniteMeasure μ]
    [IsFiniteMeasure μb] {p : ℝ≥0∞} [Fact (1 ≤ p)] (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] (F : C(β, E)) (φ : C(α, β)) (hφ : MeasurePreserving φ μ μb) :
    compMeasurePreserving φ hφ (ContinuousMap.toLp p μb 𝕜 F) =
      ContinuousMap.toLp p μ 𝕜 (F.comp φ) := by
  refine Lp.ext ((coeFn_compMeasurePreserving _ hφ).trans ?_)
  exact (hφ.quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := p) μb F)).trans
      (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := p) μ (F.comp φ)).symm

/-- **The `L^p` isometric equivalence induced by an almost-everywhere inverse pair of
measure-preserving maps.**

`f` and `g` are each measure-preserving and `f ∘ g` is the identity almost everywhere;
precomposition by `f` is then an isometric isomorphism `Lp E p μb ≃ₗᵢ[𝕜] Lp E p μ`, with inverse
precomposition by `g`.

Only the one composition identity is needed. It makes precomposition by `g` a retraction of
precomposition by `f`, and precomposition by `g` is a linear isometry, hence injective, so that
retraction is already a two-sided inverse. The symmetric hypothesis `g ∘ f =ᵐ[μ] id` is therefore
not required as an argument.

The almost-everywhere hypothesis is what makes this usable for a change of variables: `Real.cos`
and `Real.arccos` satisfy it without forming a `MeasurableEquiv`. -/
noncomputable def compMeasurePreservingₗᵢEquiv {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ) (hfg : f ∘ g =ᵐ[μb] id) :
    Lp E p μb ≃ₗᵢ[𝕜] Lp E p μ :=
  LinearIsometryEquiv.ofLinearIsometry (compMeasurePreservingₗᵢ 𝕜 f hf)
    (compMeasurePreservingₗ 𝕜 g hg)
    (LinearMap.ext fun x => (compMeasurePreservingₗᵢ 𝕜 g hg).injective
      (compMeasurePreserving_comp_apply_of_ae_id (E := E) (p := p) hf hg hfg
        (compMeasurePreserving g hg x)))
    (LinearMap.ext fun x => compMeasurePreserving_comp_apply_of_ae_id (E := E) (p := p) hf hg hfg x)

@[simp]
theorem compMeasurePreservingₗᵢEquiv_apply {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μb) :
    compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg x = compMeasurePreserving f hf x := by
  rw [compMeasurePreservingₗᵢEquiv, LinearIsometryEquiv.coe_ofLinearIsometry,
    compMeasurePreservingₗᵢ_apply]

@[simp]
theorem compMeasurePreservingₗᵢEquiv_symm_apply {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μ) :
    (compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg).symm x = compMeasurePreserving g hg x := by
  rw [compMeasurePreservingₗᵢEquiv, LinearIsometryEquiv.coe_ofLinearIsometry_symm]
  rfl

/-- The equivalence is almost everywhere precomposition by `f`. -/
theorem coeFn_compMeasurePreservingₗᵢEquiv {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μb) :
    ⇑(compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg x) =ᵐ[μ] ⇑x ∘ f := by
  simpa using coeFn_compMeasurePreserving (E := E) (p := p) x hf

/-- The inverse equivalence is almost everywhere precomposition by `g`. -/
theorem coeFn_compMeasurePreservingₗᵢEquiv_symm {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μ) :
    ⇑((compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg).symm x) =ᵐ[μb] ⇑x ∘ g := by
  simpa using coeFn_compMeasurePreserving (E := E) (p := p) x hg

end Lp
end MeasureTheory
