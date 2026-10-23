/-
Copyright (c) 2026 brent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: brent
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!

# Monotonicity of finite product measures

Finite product measures `MeasureTheory.Measure.pi` are monotone in each of their factors.

## i. Overview

Mathlib constructs the finite product `Measure.pi μ` of a family of measures `μ i`, but does
not (yet) record that it is monotone in the family. This file proves that if `μ i ≤ ν i` for
every `i`, then `Measure.pi μ ≤ Measure.pi ν`. No `SigmaFinite` assumption is needed, since the
proof goes through the outer measure `MeasureTheory.OuterMeasure.pi` from which `Measure.pi` is
built.

## ii. Key results

- `MeasureTheory.Measure.pi_mono` : the finite product of measures is monotone in the family.

## iii. Table of contents

- A. Monotonicity of the product measure

## iv. References

* None.

-/

@[expose] public section

namespace MeasureTheory.Measure

/-!

## A. Monotonicity of the product measure

-/

/-- The finite product measure `Measure.pi μ` is monotone in the family of measures `μ`:
if `μ i ≤ ν i` for every `i`, then `Measure.pi μ ≤ Measure.pi ν`. -/
lemma pi_mono {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {μ ν : (i : ι) → Measure (α i)} (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.pi, toMeasure_apply _ _ hs, Measure.pi, toMeasure_apply _ _ hs]
  suffices OuterMeasure.pi (fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) from this s
  refine OuterMeasure.le_pi.2 fun t _ => ?_
  exact (OuterMeasure.pi_pi_le _ t).trans <|
    Finset.prod_le_prod fun i _ => (Measure.le_iff'.1 (h i)) (t i)

end MeasureTheory.Measure
