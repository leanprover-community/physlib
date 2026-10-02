/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.MeasureTheory.BoundedMeasurable
public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.Lattice
public import PhyslibAlpha.ProbabilisticTheory.Measurement.EffectValuedMeasure

/-!
# Observables of a sample space

## i. Overview

The observables of a sample space `Ω` are the bounded measurable functions on `Ω`, ordered
pointwise, with the constant function `1` as order unit. They form a classical system whose
observables are even a lattice. For a mechanical system, `Ω` is its phase space; for a measurement,
`Ω` is its set of outcomes. Asking whether the outcome lies in a measurable set `A` is the effect
`1_A`; these effects form the effect-valued measure of the outcome.

## ii. Key results

- `BoundedMeasurable Ω` is an order-unit lattice.
- `BoundedMeasurable.indicatorEffect` : the effect testing whether the outcome lies in a set.
- `BoundedMeasurable.outcomeMeasurement` : the effect-valued measure of the outcome.

## iii. Table of contents

- A. The order-unit space
- B. Indicator effects

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. The order-unit space

-/

end ProbabilisticTheory

namespace BoundedMeasurable
open ProbabilisticTheory

variable {Ω : Type*} [MeasurableSpace Ω]

instance : OrderUnitSpace (BoundedMeasurable Ω) where
  one_nonneg := le_def.2 fun _ => by simp
  exists_nsmul_one_le f := by
    obtain ⟨C, hC⟩ := f.exists_bound
    exact ⟨⌈C⌉₊, le_def.2 fun x => by
      simpa using (le_abs_self _).trans ((hC x).trans (Nat.le_ceil C))⟩

instance : ArchimedeanOrderUnitSpace (BoundedMeasurable Ω) where
  le_zero_of_forall_pos_smul_one_le f h := le_def.2 fun x =>
    le_of_forall_pos_le_add fun ε hε => by simpa using le_def.1 (h ε hε) x

instance : OrderUnitLattice (BoundedMeasurable Ω) :=
  { (inferInstance : ArchimedeanOrderUnitSpace (BoundedMeasurable Ω)),
    (inferInstance : Lattice (BoundedMeasurable Ω)) with }

end BoundedMeasurable

namespace BoundedMeasurable
open ProbabilisticTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-!

## B. Indicator effects

-/

/-- The effect testing whether the outcome lies in `s`. -/
noncomputable def indicatorEffect (s : Set Ω) (hs : MeasurableSet s) :
    Effect (BoundedMeasurable Ω) :=
  ⟨indicator s hs, indicator_nonneg s hs, indicator_le_one s hs⟩

@[simp] lemma coe_indicatorEffect (s : Set Ω) (hs : MeasurableSet s) :
    (indicatorEffect s hs : BoundedMeasurable Ω) = indicator s hs := rfl

/-- The effect-valued measure of the outcome: the set `A` is the effect `1_A`. -/
noncomputable def outcomeMeasurement : EffectValuedMeasure Ω (BoundedMeasurable Ω) where
  toFun := indicatorEffect
  map_empty' := Subtype.ext (ext fun x => by simp)
  map_univ' := Subtype.ext (ext fun x => by simp)
  countably_additive' _ hs hd := isLUB_sum_indicator hs hd

end BoundedMeasurable

