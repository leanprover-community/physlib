/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.PureState
public import PhyslibAlpha.Mathematics.Convex.Choquet.BoundaryRepresentation
public import PhyslibAlpha.Mathematics.MeasureTheory.IntegrationFunctional
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Classical systems: unique decomposition into pure states

## i. Overview

A system is classical when every state is a mixture of pure states in exactly one way. A die is the
basic example. Its pure states are the six outcomes. Every state is a probability vector, and the
state fixes the probabilities.

Geometrically, the states of a die form a simplex: the convex hull of six affinely independent
points. The weights of a state are its barycentric coordinates. In infinite dimensions there can be
infinitely many pure states, and the weights become a probability measure on the pure states. We
call this measure a pure decomposition. The state space is a simplex when every state has exactly
one pure decomposition. It is a Bauer simplex when moreover the pure states form a closed set.

A qubit is not classical. The maximally mixed state is an equal mixture of spin up and spin down,
but also of spin left and spin right.

On a simplex, measures on the pure states are the same as positive functionals on the observables,
and this identification respects the order.

## ii. Key results

- `UnitalPositiveLinearMap.HasPureDecomposition` states that a state is a mixture of pure states.
- `UnitalPositiveLinearMap.HasUniquePureDecomposition` states that it is so in exactly one way.
- `IsSimplexStateSpace E` states that every state has exactly one pure decomposition.
- `IsBauerSimplexStateSpace E` states in addition that the pure states form a closed set.
- `PureState.toPositive` turns a measure on the pure states into a positive functional.

## iii. Table of contents

- A. Pure decompositions and simplices
- B. Measures on the pure states as positive functionals
- C. Simplices identify functionals with measures

-/

@[expose] public section

namespace ProbabilisticTheory

open StateSpace

open MeasureTheory PureState
open scoped ENNReal

/-!

## A. Pure decompositions and simplices

-/

section Archimedean

variable (E : Type*) [ArchimedeanOrderUnitSpace E]

namespace UnitalPositiveLinearMap

variable {E}

/-- The state `ω` decomposes into pure states: some regular probability measure on the pure states
represents it. -/
def HasPureDecomposition (ω : 𝓢[ℝ, E]) : Prop :=
  Choquet.HasBoundaryDecomposition (fun f (φ : 𝓢[ℝ, E]) => φ f)
    (fun φ : PureState E => toState φ.1) ω

/-- The state `ω` decomposes uniquely into pure states: exactly one regular probability measure on
the pure states represents it. -/
def HasUniquePureDecomposition (ω : 𝓢[ℝ, E]) : Prop :=
  Choquet.HasUniqueBoundaryDecomposition (fun f (φ : 𝓢[ℝ, E]) => φ f)
    (fun φ : PureState E => toState φ.1) ω

end UnitalPositiveLinearMap

/-- The state space of `E` is a simplex: every state is a unique mixture of pure states, given by
a regular probability measure on the pure states. In finite dimension this is the convex hull of
affinely independent pure states, every state having unique barycentric coordinates. -/
def IsSimplexStateSpace : Prop :=
  Choquet.IsSimplexRepresentation (fun f (φ : 𝓢[ℝ, E]) => φ f)
    (fun φ : PureState E => toState φ.1)

/-- The state space of `E` is a Bauer simplex: a simplex whose pure states form a closed, hence
compact, set. -/
def IsBauerSimplexStateSpace : Prop :=
  IsSimplexStateSpace E ∧ IsClosed {ω : stateSpace E | (toState ω).IsPure}

end Archimedean

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-!

## B. Measures on the pure states as positive functionals

-/

namespace PureState

lemma integrable (μ : Measure (PureState E)) [IsFiniteMeasure μ] (f : E) :
    Integrable (fun ω : PureState E => toState ω.1 f) μ :=
  .of_bound (evalPure f).continuous.aestronglyMeasurable (ArchimedeanOrderUnitSpace.orderUnitNorm f)
    (.of_forall fun _ => UnitalPositiveLinearMap.abs_apply_le_orderUnitNorm _ f)

/-- Integration of the observables against a finite measure on the pure states. -/
noncomputable def toPositive (μ : Measure (PureState E)) [IsFiniteMeasure μ] : E →ₚ[ℝ] ℝ :=
  .mk₀ ⟨⟨fun f => ∫ ω, toState ω.1 f ∂μ, fun f g => by
      simp only [map_add]
      exact integral_add (integrable μ f) (integrable μ g)⟩, fun c f => by
      simp only [map_smul, smul_eq_mul, RingHom.id_apply]
      exact integral_const_mul c _⟩
    fun _ hf => integral_nonneg fun _ => map_nonneg _ hf

@[simp] lemma toPositive_apply (μ : Measure (PureState E)) [IsFiniteMeasure μ] (f : E) :
    toPositive μ f = ∫ ω, toState ω.1 f ∂μ := rfl

lemma toPositive_add (μ ν : Measure (PureState E)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    toPositive (μ + ν) = toPositive μ + toPositive ν :=
  PositiveLinearMap.ext fun f => integral_add_measure (integrable μ f) (integrable ν f)

lemma toPositive_mono {μ ν : Measure (PureState E)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ ≤ ν) : toPositive μ ≤ toPositive ν := fun f hf =>
  integral_mono_measure h (.of_forall fun _ => map_nonneg _ hf) (integrable ν f)

lemma toPositive_one (μ : Measure (PureState E)) [IsFiniteMeasure μ] :
    toPositive μ 1 = μ.real Set.univ := by
  simp

lemma measure_univ_eq_of_toPositive_eq {μ ν : Measure (PureState E)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : toPositive μ = toPositive ν) : μ Set.univ = ν Set.univ := by
  have := congrArg (· 1) hμν
  simp only [toPositive_one, measureReal_def] at this
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

lemma toPositive_smul_eq {μ ν : Measure (PureState E)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : ℝ≥0∞} [IsFiniteMeasure (c • μ)] [IsFiniteMeasure (c • ν)]
    (hμν : toPositive μ = toPositive ν) : toPositive (c • μ) = toPositive (c • ν) :=
  PositiveLinearMap.ext fun f => by
    have hf := congrArg (· f) hμν
    simp only [toPositive_apply] at hf
    rw [toPositive_apply, toPositive_apply, integral_smul_measure, integral_smul_measure, hf]

end PureState

/-!

## C. Simplices identify functionals with measures

-/

section Simplex

variable (h : IsSimplexStateSpace E)
include h

/-- Every positive functional is integration against a finite regular measure on the pure
states. -/
lemma exists_toPositive_eq (α : E →ₚ[ℝ] ℝ) :
    ∃ (μ : Measure (PureState E)) (_ : IsFiniteMeasure μ), μ.Regular ∧ toPositive μ = α := by
  rcases (map_nonneg α OrderUnitSpace.one_nonneg).eq_or_lt with h0 | h0
  · refine ⟨0, inferInstance, inferInstance, PositiveLinearMap.ext fun f => ?_⟩
    simpa using (UnitalPositiveLinearMap.apply_eq_zero_of_apply_one_eq_zero h0.symm f).symm
  obtain ⟨μ, ⟨hreg, hprob, hint⟩, -⟩ := h (UnitalPositiveLinearMap.normalize α h0)
  have := hprob
  refine ⟨(α 1).toNNReal • μ, inferInstance, inferInstance, PositiveLinearMap.ext fun f => ?_⟩
  rw [toPositive_apply, integral_smul_nnreal_measure, hint, NNReal.smul_def,
    Real.coe_toNNReal _ h0.le]
  change α 1 * UnitalPositiveLinearMap.normalize α h0 f = α f
  rw [UnitalPositiveLinearMap.normalize_apply, mul_inv_cancel_left₀ h0.ne']

/-- Regular probability measures on the pure states with the same integrals are equal. -/
lemma eq_of_toPositive_eq_of_isProbabilityMeasure {μ ν : Measure (PureState E)} [μ.Regular]
    [ν.Regular] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : toPositive μ = toPositive ν) : μ = ν := by
  have hpos : 0 < toPositive μ 1 := by simp
  obtain ⟨_, -, huniq⟩ := h (UnitalPositiveLinearMap.normalize (toPositive μ) hpos)
  have hrep (κ : Measure (PureState E)) [IsProbabilityMeasure κ] (hκ : toPositive κ = toPositive μ)
      (f : E) :
      ∫ ω, toState ω.1 f ∂κ = UnitalPositiveLinearMap.normalize (toPositive μ) hpos f := by
    simp [← hκ]
  exact (huniq μ ⟨inferInstance, inferInstance, hrep μ rfl⟩).trans
    (huniq ν ⟨inferInstance, inferInstance, hrep ν hμν.symm⟩).symm

/-- Finite regular measures on the pure states with the same integrals are equal. -/
lemma eq_of_toPositive_eq {μ ν : Measure (PureState E)} [μ.Regular] [ν.Regular]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : toPositive μ = toPositive ν) : μ = ν := by
  have hmass := measure_univ_eq_of_toPositive_eq hμν
  rcases eq_or_ne (μ Set.univ) 0 with h0 | h0
  · rw [Measure.measure_univ_eq_zero.1 h0, Measure.measure_univ_eq_zero.1 (hmass.symm.trans h0)]
  set c := (μ Set.univ)⁻¹
  have hc : c ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top _ _)
  have hc1 : c * μ Set.univ = 1 := ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)
  have : IsProbabilityMeasure (c • μ) := ⟨by simp [hc1]⟩
  have : IsProbabilityMeasure (c • ν) := ⟨by simp [← hmass, hc1]⟩
  have : (c • μ).Regular := Measure.Regular.smul hc
  have : (c • ν).Regular := Measure.Regular.smul hc
  have e := eq_of_toPositive_eq_of_isProbabilityMeasure h (toPositive_smul_eq (c := c) hμν)
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul] using congrArg (c⁻¹ • ·) e

/-- Unique decomposition makes the order on positive functionals that of measures. -/
lemma le_of_toPositive_le {μ θ : Measure (PureState E)} [μ.Regular] [θ.Regular]
    [IsFiniteMeasure μ] [IsFiniteMeasure θ] (hle : toPositive μ ≤ toPositive θ) : μ ≤ θ := by
  obtain ⟨ρ, hρf, hρ, hρθ⟩ := exists_toPositive_eq h (PositiveLinearMap.subOfLE _ _ hle)
  have := hρ
  rw [← eq_of_toPositive_eq h (μ := μ + ρ) (ν := θ)
    (by rw [toPositive_add, hρθ, PositiveLinearMap.add_subOfLE])]
  exact Measure.le_add_right le_rfl

end Simplex

end ProbabilisticTheory
