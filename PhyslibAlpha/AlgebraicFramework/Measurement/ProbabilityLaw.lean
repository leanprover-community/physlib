/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Measurement.MeasurableOutcome
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Order.MonotoneConvergence

/-!

# Probability laws of effect-valued measurements

A real-valued effect measure is exactly a probability measure: its values lie in `[0, 1]`, and
its order-theoretic countable additivity becomes `ENNReal` countable additivity after applying
`ENNReal.ofReal`.  Consequently, scalarizing a POVM by a normal state produces an ordinary
probability law.

## Main definitions

- `EffectValuedMeasure.toMeasure`
- `EffectValuedMeasure.toProbabilityMeasure`
- `EffectValuedMeasure.probabilityLaw`

-/

@[expose] public section

open MeasureTheory

variable {Ω C : Type*} [MeasurableSpace Ω]

namespace EffectValuedMeasure

/-- The ordinary measure represented by a real-valued effect-valued measure. -/
noncomputable def toMeasure (ν : EffectValuedMeasure Ω ℝ) : Measure Ω :=
  Measure.ofMeasurable
    (fun s hs => ENNReal.ofReal (ν s hs : ℝ))
    (by simp)
    (by
      intro s hsm hs
      let a : ℕ → ℝ := fun n => (ν (s n) (hsm n) : ℝ)
      let p : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, a n
      have ha : ∀ n, 0 ≤ a n := fun n => (ν (s n) (hsm n)).2.1
      have hpmono : Monotone p := fun _ _ hNM =>
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNM)
          (fun i _ _ => ha i)
      have hlub : IsLUB (Set.range p) (ν (⋃ n, s n) (MeasurableSet.iUnion hsm) : ℝ) := by
        simpa [p, a] using ν.countably_additive s hsm hs
      have hreal : Filter.Tendsto p Filter.atTop
          (nhds (ν (⋃ n, s n) (MeasurableSet.iUnion hsm) : ℝ)) :=
        tendsto_atTop_isLUB hpmono hlub
      have henn : Filter.Tendsto (fun N => ENNReal.ofReal (p N)) Filter.atTop
          (nhds (ENNReal.ofReal (ν (⋃ n, s n) (MeasurableSet.iUnion hsm) : ℝ))) :=
        ENNReal.tendsto_ofReal hreal
      have hpartial : (fun N => ENNReal.ofReal (p N)) =
          fun N => ∑ n ∈ Finset.range N, ENNReal.ofReal (a n) := by
        funext N
        exact ENNReal.ofReal_sum_of_nonneg fun i _ => ha i
      rw [hpartial] at henn
      exact tendsto_nhds_unique henn (ENNReal.tendsto_nat_tsum fun n => ENNReal.ofReal (a n)))

@[simp]
lemma toMeasure_apply (ν : EffectValuedMeasure Ω ℝ) (s : Set Ω) (hs : MeasurableSet s) :
    ν.toMeasure s = ENNReal.ofReal (ν s hs : ℝ) :=
  Measure.ofMeasurable_apply _ hs

/-- Every real-valued effect-valued measure has total mass one. -/
instance (ν : EffectValuedMeasure Ω ℝ) : IsProbabilityMeasure ν.toMeasure where
  measure_univ := by simp [toMeasure_apply]

/-- A real-valued effect-valued measure bundled as an ordinary probability measure. -/
noncomputable def toProbabilityMeasure (ν : EffectValuedMeasure Ω ℝ) : ProbabilityMeasure Ω :=
  ⟨ν.toMeasure, inferInstance⟩

variable [AddCommGroup C] [PartialOrder C] [IsOrderedAddMonoid C] [Module ℝ C]
  [PosSMulMono ℝ C] [One C] [IsOrderUnit C]

/-- The probability distribution obtained by measuring `μ` in the normal state `ω`. -/
noncomputable def probabilityLaw (μ : EffectValuedMeasure Ω C) (ω : 𝓢[ℝ, C]) (hω : ω.IsNormal) :
    ProbabilityMeasure Ω := (μ.scalarize ω hω).toProbabilityMeasure

omit [PosSMulMono ℝ C] in
@[simp]
lemma probabilityLaw_apply (μ : EffectValuedMeasure Ω C) (ω : 𝓢[ℝ, C]) (hω : ω.IsNormal)
    (s : Set Ω) (hs : MeasurableSet s) :
    (μ.probabilityLaw ω hω : Measure Ω) s = ENNReal.ofReal (ω (μ s hs : C)) := by
  change (μ.scalarize ω hω).toMeasure s = ENNReal.ofReal (ω (μ s hs : C))
  rw [toMeasure_apply _ s hs, coe_scalarize_apply]

end EffectValuedMeasure
