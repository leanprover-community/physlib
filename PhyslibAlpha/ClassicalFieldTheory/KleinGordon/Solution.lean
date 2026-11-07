/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.DistributionSources

/-!

# Klein–Gordon fields and causal propagation

A disturbance of a relativistic field spreads inside the light cone. This file states how the
Klein–Gordon equation describes this, for massless and massive fields in every spatial dimension.

## i. Overview

Time and space are measured in units with the speed of light equal to one. For a source `f` of
compact support the file solves `(∂ₜ² - Δ + m²) u = f` on `SpaceTime d`. The mass parameter `m`
is any real number. The source and the solution are smooth fields with values in a normed space.
Sources may also be distributions of compact support.

The retarded solution is supported in the causal future of the source. The advanced solution is
supported in the causal past. Their difference is the causal propagator. It solves the equation
without source. Every homogeneous solution with spacelike compact support arises this way.

## ii. Key results

- `existsUnique_retarded` : a compact source has exactly one solution with support in the causal
  future of the source.
- `exact_sequence` : compact sources, the equation of motion and the causal propagator form an
  exact sequence.
- `solutionsEquivQuotient` : spacelike compact solutions are the compact sources modulo the
  equation of motion.
- `retardedDistribution_unique` : the same uniqueness for distributional sources.
- `pointSource_solves` and `pointSource_reciprocity` : the point source solves the equation with a
  delta source, and the retarded kernel seen from `p` is the advanced solution at `p`.

## iii. Table of contents

- A. The problem
- B. The Fourier picture
- C. Smooth sources
- D. Distributional sources
- E. Tempered slices
- F. Not proved here

## iv. References

None.

## A. The problem

Given a source `f` of compact support, find a field `u` with `(∂ₜ² - Δ + m²) u = f`. The operator
is `operator m`. A source is a smooth field of compact support, `TestField d F`. A distributional
source is a compactly supported distribution, `compactDistributions`. A solution is a smooth
field, `smoothFields d F`, or a distribution, `DistributionField d V`.

## B. The Fourier picture

Transform in space. Put `f̂(s, ξ) = ∫ e^(-2πi x·ξ) f(s, x) dx` and `ω(ξ) = √(4π²‖ξ‖² + m²)`.
Each Fourier mode obeys the forced oscillator equation `û'' + ω² û = f̂`. Its solutions use the
kernel `sin(ω r) / ω`. This is `sincPropagator ω`. It equals `r` at `ω = 0`.

* The retarded solution is `û(t, ξ) = ∫_{s ≤ t} sin(ω (t - s)) / ω · f̂(s, ξ) ds`.
  Every cause comes before its effect.
* The advanced solution is `û(t, ξ) = ∫_{s ≥ t} sin(ω (s - t)) / ω · f̂(s, ξ) ds`.
  Every effect comes before its cause.
* The difference is the causal propagator `E`. It is
  `û(t, ξ) = ∫ sin(ω (t - s)) / ω · f̂(s, ξ) ds` over all times.

## C. Smooth sources

The results `retarded_solves`, `retarded_support` and `retarded_formula` describe the retarded
solution. The same results hold for the advanced solution. The causal propagator `E` solves the
equation without source and is supported in the causal future and past of the source. The sequence
`0 → D → D → Sol → 0` is exact. `D` is the space of compact sources. The first map is the
operator. The second map is `E`. `Sol` is the space of homogeneous solutions with spacelike
compact support.

## D. Distributional sources

Compactly supported distributions have retarded and advanced solutions with the same properties.
The point source at `p` is the retarded solution of a delta distribution. Reciprocity holds. The
retarded kernel seen from `p` and tested on `φ` is the advanced solution of `φ` at `p`.

## E. Tempered slices

At each time the solution is a tempered distribution in space. `fourier_sineEvolution` gives its
Fourier transform. `retarded_slice_pairing` gives its pairing with Schwartz functions.

## F. Not proved here

The Fourier transform in time and space, the convolution form `u = K * f` and closed expressions
for the kernel `K` in a given dimension are not proved here.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap Distributions FourierTransform
open Minkowski CausalRelation LocalOperator Distribution KleinGordon.Spacetime TimeSlice
    TopologicalSpace MeasureTheory
universe u

namespace KleinGordon.Solution

section SmoothSources

variable {d : ℕ} (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (m : ℝ)

/-- The retarded solution of `operator m u = f`. -/
abbrev retarded : TestField d F →ₗ[ℝ] smoothFields d F := retardedMap F m

/-- The advanced solution of `operator m u = f`. -/
abbrev advanced : TestField d F →ₗ[ℝ] smoothFields d F := advancedMap F m

variable {F m}

/-- Smooth fields form an additive group, needed to form the quotient. -/
local instance : AddCommGroup (smoothFields d F) := (smoothFields d F).addCommGroup

/-- The retarded solution solves the equation. -/
lemma retarded_solves (f : TestField d F) : operator m (retarded F m f) = f :=
  retardedMap_solves F m f

/-- The advanced solution solves the equation. -/
lemma advanced_solves (f : TestField d F) : operator m (advanced F m f) = f :=
  advancedMap_solves F m f

/-- The retarded solution vanishes outside the causal future of the source. -/
lemma retarded_support (f : TestField d F) :
    tsupport (retarded F m f : SpaceTime d → F) ⊆
      (causalRelation d).causalFuture (tsupport (f : SpaceTime d → F)) :=
  (retardedGreenOperator F m).support f

/-- The advanced solution vanishes outside the causal past of the source. -/
lemma advanced_support (f : TestField d F) :
    tsupport (advanced F m f : SpaceTime d → F) ⊆
      (causalRelation d).causalPast (tsupport (f : SpaceTime d → F)) :=
  (advancedGreenOperator F m).support f

/-- The retarded solution in time and space coordinates. At time `t` and position `x` it adds
the sine evolution of the source slice at every earlier time `s`. -/
lemma retarded_formula (f : TestField d F) (p : SpaceTime d) :
    (retarded F m f : SpaceTime d → F) p = ∫ s in Set.Iic (coordinates d p).1,
      sineEvolution F ((coordinates d p).1 - s) (m ^ 2)
        (slice F (sourceEquiv F (testFieldEquiv F f)) s) (coordinates d p).2 :=
  KleinGordon.solution_eq_integral F _ (sq_nonneg m) _ _

/-- The advanced solution in time and space coordinates. It adds the sine evolution of the
source slice at every later time. -/
lemma advanced_formula (f : TestField d F) (p : SpaceTime d) :
    (advanced F m f : SpaceTime d → F) p = ∫ s in Set.Ioi (coordinates d p).1,
      sineEvolution F (s - (coordinates d p).1) (m ^ 2)
        (slice F (sourceEquiv F (testFieldEquiv F f)) s) (coordinates d p).2 :=
  KleinGordon.advancedSolution_eq_integral F _ (sq_nonneg m) _ _

variable (F m) in
/-- The causal propagator `E`: the retarded minus the advanced solution. -/
abbrev propagator : TestField d F →ₗ[ℝ] smoothFields d F := (greenOperators F m).causalPropagator

/-- The causal propagator is the retarded minus the advanced solution. -/
lemma propagator_eq (f : TestField d F) :
    propagator F m f = retarded F m f - advanced F m f := rfl

/-- The causal propagator solves the equation without source. -/
lemma propagator_solves (f : TestField d F) : operator m (propagator F m f) = 0 :=
  (greenOperators F m).causalPropagator_solves f

/-- The causal propagator is supported in the causal future and past of the source. -/
lemma propagator_support (f : TestField d F) :
    tsupport (propagator F m f : SpaceTime d → F) ⊆
      (causalRelation d).causalHull (tsupport (f : SpaceTime d → F)) :=
  (greenOperators F m).causalPropagator_support f

/-- The causal propagator kills every source that is an equation of motion. -/
lemma propagator_operator (f : TestField d F) :
    propagator F m (compactOperator (equation m) f) = 0 :=
  (greenOperators F m).causalPropagator_comp_operator f

/-- A source has exactly one solution with support in the causal future of the source. -/
lemma existsUnique_retarded (f : TestField d F) :
    ∃! u : smoothFields d F, operator m u = f ∧
      tsupport (u : SpaceTime d → F) ⊆
        (causalRelation d).causalFuture (tsupport (f : SpaceTime d → F)) :=
  existsUnique_retardedSolution F m f

/-- Compact sources, the equation of motion and the retarded minus advanced solution form an
exact sequence ending in the spacelike compact fields. -/
lemma exact_sequence :
    let P := equation (d := d) (V := F) m
    Function.Injective P.compactOperator ∧
      Function.Exact P.compactOperator (greenOperators F m).toSpacelikeCompact ∧
      Function.Exact (greenOperators F m).toSpacelikeCompact
        (P.spacelikeCompactOperator (causalRelation d)) ∧
      Function.Surjective (P.spacelikeCompactOperator (causalRelation d)) :=
  causalGreen_exactSequence F m

/-- Spacelike compact solutions are the compact sources modulo the equation of motion. -/
def solutionsEquivQuotient :
    let P := equation (d := d) (V := F) m
    P.spacelikeCompactSolution (causalRelation d) ≃ₗ[ℝ]
      (P.compactSources ⧸ LinearMap.range P.compactOperator) :=
  solutionSpaceEquivQuotient F m

end SmoothSources

section DistributionSources

variable {d : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (m : ℝ)

/-- The retarded solution for a compactly supported distribution. -/
abbrev retardedDistribution (T : compactDistributions (SpaceTime d) V) : DistributionField d V :=
  retardedCompactResponse m T

/-- The advanced solution for a compactly supported distribution. -/
abbrev advancedDistribution (T : compactDistributions (SpaceTime d) V) : DistributionField d V :=
  advancedCompactResponse m T

variable {m}

/-- The retarded solution of a distribution solves the equation. -/
lemma retardedDistribution_solves (T : compactDistributions (SpaceTime d) V) :
    distributionOperator m (retardedDistribution m T) = T :=
  retardedCompactResponse_solves m T

/-- The advanced solution of a distribution solves the equation. -/
lemma advancedDistribution_solves (T : compactDistributions (SpaceTime d) V) :
    distributionOperator m (advancedDistribution m T) = T :=
  advancedCompactResponse_solves m T

/-- The retarded solution vanishes outside the causal future of the support of the source. -/
lemma retardedDistribution_support (T : compactDistributions (SpaceTime d) V) :
    IsVanishingOn (retardedDistribution m T)
      ((causalRelation d).causalFuture (compactDistributionBound T))ᶜ :=
  retardedCompactResponse_vanishes m T

/-- The advanced solution vanishes outside the causal past of the support of the source. -/
lemma advancedDistribution_support (T : compactDistributions (SpaceTime d) V) :
    IsVanishingOn (advancedDistribution m T)
      ((causalRelation d).causalPast (compactDistributionBound T))ᶜ :=
  advancedCompactResponse_vanishes m T

/-- A distribution solution supported in the causal future of a compact set is the retarded
solution. -/
lemma retardedDistribution_unique (T : compactDistributions (SpaceTime d) V)
    (u : DistributionField d V) {K : Set (SpaceTime d)} (hK : IsCompact K)
    (hu : IsVanishingOn u ((causalRelation d).causalFuture K)ᶜ)
    (hT : distributionOperator m u = T) : u = retardedDistribution m T :=
  retardedCompactResponse_unique m T u K hK hu hT

/-- Solving and then applying the operator returns the source. -/
lemma retardedDistribution_inverse (T : compactDistributions (SpaceTime d) V) :
    retardedDistribution m (compactDistributionOperator m T) = T :=
  retardedCompactResponse_operator m T

/-- The point source at `p`: the retarded solution of a delta distribution. -/
abbrev pointSource (p : SpaceTime d) := retardedPointSource m p

/-- The point source solves the equation with the delta distribution at `p` as source. -/
lemma pointSource_solves (p : SpaceTime d) :
    distributionOperator m (pointSource (m := m) p) = Distribution.delta p :=
  distributionOperator_retardedPointSource m p

/-- The point source vanishes outside the causal future of `p`. -/
lemma pointSource_support (p : SpaceTime d) :
    IsVanishingOn (pointSource (m := m) p) ((causalRelation d).causalFuture {p})ᶜ :=
  retardedPointSource_vanishes m p

/-- Reciprocity. The retarded kernel seen from `p` and tested on `f` is the advanced solution for
`f`, evaluated at `p`. -/
lemma pointSource_reciprocity (p : SpaceTime d) (f : TestField d ℝ) :
    pointSource (m := m) p (testFieldEquiv ℝ f) =
      ((realAdvancedGreenOperator m).toLinearMap f : SpaceTime d → ℝ) p :=
  realAdvancedEvaluation_apply m p f

/-- The point source at `p` applied to a test function `φ`. It integrates the sine evolution of
the delta distribution at the position of `p` against the slices of `φ` over later times. -/
lemma pointSource_apply (p : SpaceTime d) (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    pointSource (m := m) p φ =
      (∫ s in Set.Ioi (coordinates d p).1,
        KleinGordon.sineEvolutionTempered ℂ (s - (coordinates d p).1) (m ^ 2)
          (TemperedDistribution.delta (coordinates d p).2)
          (slice ℂ (sourceEquiv ℂ (_root_.TestFunction.postcompCLM Complex.ofRealCLM φ)) s)).re :=
  retardedPointSource_apply m p φ

end DistributionSources

section Tempered

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (F : Type u) [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F] (f : 𝓓((⊤ : Opens (ℝ × E)), F))

/-- In Fourier space the sine evolution multiplies by `sin(ω r) / ω`. -/
lemma fourier_sineEvolution {μ : ℝ} (hμ : 0 ≤ μ) (r : ℝ) (g : 𝓢(E, F)) (ξ : E) :
    𝓕 (sineEvolution F r μ g) ξ = (Real.sincPropagator r (dispersion μ ξ) : ℂ) • 𝓕 g ξ := by
  simp only [sineEvolution, SchwartzMap.fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq]
  exact SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_multiplier r hμ) _ ξ

/-- At time `t` the retarded solution is a tempered distribution in space. Tested against a
Schwartz function it is the integral over earlier times `s` of the sine evolution of the source
slice at time `s`. -/
lemma retarded_slice_pairing {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) (g : 𝓢(E, ℂ)) :
    (solutionSlice F f hμ t : 𝓢'(E, F)) g =
      ∫ s in Set.Iic t, sineEvolutionTempered F (t - s) μ (slice F f s : 𝓢'(E, F)) g :=
  solutionSlice_pairing F f hμ t g

end Tempered

end KleinGordon.Solution
