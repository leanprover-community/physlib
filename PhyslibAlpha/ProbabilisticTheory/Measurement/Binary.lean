/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Measurement.Finite
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Binary measurements

## i. Overview

Every effect of an Archimedean system defines a yes/no measurement: the outcome `true` has the
effect itself, the outcome `false` its complement.

## ii. Key results

- `Effect.binaryMeasurement` : the binary measurement associated to an effect.

## iii. Table of contents

- A. Binary measurements

-/

@[expose] public section

namespace ProbabilisticTheory

namespace Effect

variable {E : Type*} [OrderUnitSpace E]

/-! ## A. Binary measurements -/

/-- The effect of each outcome of the binary measurement of `e`: `e` for `true`, its complement
for `false`. -/
def binaryAtom (e : Effect E) (b : Bool) : Effect E :=
  if b then e else complement e

lemma sum_binaryAtom (e : Effect E) : ∑ b, (binaryAtom e b : E) = 1 := by
  simp [binaryAtom, complement]

variable {F : Type*} [ArchimedeanOrderUnitSpace F]

/-- The two-outcome measurement whose `true` effect is `e` and whose `false` effect is `1 - e`. -/
noncomputable def binaryMeasurement (e : Effect F) : Measurement Bool F :=
  Measurement.ofAtoms (binaryAtom e) (sum_binaryAtom e)

@[simp]
lemma binaryMeasurement_true (e : Effect F) (h : MeasurableSet {true}) :
    binaryMeasurement e {true} h = e :=
  Subtype.ext (Measurement.coe_ofAtoms_singleton _ _ _ h)

@[simp]
lemma binaryMeasurement_false (e : Effect F) (h : MeasurableSet {false}) :
    binaryMeasurement e {false} h = complement e :=
  Subtype.ext (Measurement.coe_ofAtoms_singleton _ _ _ h)

end Effect

end ProbabilisticTheory
