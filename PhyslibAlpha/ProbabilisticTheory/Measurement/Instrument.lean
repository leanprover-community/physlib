/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Measurement.Finite
public import PhyslibAlpha.ProbabilisticTheory.Channel.Operation

/-!

# Instruments

Finite-outcome instruments, their induced measurements and post-measurement states.

## i. Overview

An instrument with finitely many outcomes describes both the outcome probabilities and the state
after the measurement. It is a family of operations, one per outcome, whose values on the unit sum
to `1`. Forgetting the post-measurement state gives a measurement, and conditioning a state on an
outcome of nonzero probability gives the post-measurement state.

## ii. Key results

- `Instrument` : finite-outcome instruments.
- `Instrument.measurement` : the underlying measurement.
- `Instrument.conditionalState` : the post-measurement state.

## iii. Table of contents

- A. Instruments
- B. The induced measurement
- C. Conditional states

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

variable {E ι : Type*} [ArchimedeanOrderUnitSpace E] [Fintype ι]

/-! ## A. Instruments -/

/-- A finite-outcome instrument: an operation for each outcome, whose images of the certain event
exhaust it. The instrument loses no probability overall, even though a single operation may. -/
structure Instrument (E : Type*) [OrderUnitSpace E] (ι : Type*) [Fintype ι] where
  /-- The operation associated to each possible outcome. -/
  op : ι → Operation E
  /-- The outcome probabilities exhaust the certain event. -/
  sum_op_one_eq_one : ∑ i, (op i : E → E) 1 = 1

namespace Instrument

/-! ## B. The induced measurement -/

section Measurement

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The measurement an instrument induces: only the outcome probabilities remain, given by each
operation's image of the certain event. -/
noncomputable def measurement (𝓘 : Instrument E ι) : Measurement ι E :=
  Measurement.ofAtoms (fun i => Operation.outcomeEffect (𝓘.op i)) 𝓘.sum_op_one_eq_one

/-- The effect of an outcome is the value of its operation on the unit. -/
lemma coe_measurement_effects (𝓘 : Instrument E ι) (i : ι) :
    ((𝓘.measurement {i} (measurableSet_singleton i) : Effect E) : E) =
      (𝓘.op i : E → E) 1 :=
  Measurement.coe_ofAtoms_singleton _ _ i _

end Measurement

/-! ## C. Conditional states -/

/-- The post-measurement (conditional) state after outcome `i`, given a prior state `ω` for which
that outcome has nonzero probability: apply the operation, then renormalize by the outcome's
probability, so the certain event is again sent to `1`. -/
noncomputable def conditionalState (𝓘 : Instrument E ι) (i : ι) (ω : 𝓢[ℝ, E])
    (hpos : 0 < ω ((𝓘.op i : E → E) 1)) : 𝓢[ℝ, E] :=
  (𝓘.op i).condition ω hpos

@[simp]
lemma conditionalState_apply (𝓘 : Instrument E ι) (i : ι) (ω : 𝓢[ℝ, E])
    (hpos : 0 < ω ((𝓘.op i : E → E) 1)) (a : E) :
    𝓘.conditionalState i ω hpos a =
      (ω ((𝓘.op i : E → E) 1))⁻¹ * ω ((𝓘.op i : E → E) a) :=
  Operation.condition_apply _ _ _ _

/-- A normal instrument operation sends a normal input state to a normal conditional state,
whenever its outcome has nonzero probability. -/
lemma conditionalState_isNormal (𝓘 : Instrument E ι) (i : ι) (ω : 𝓢[ℝ, E])
    (hpos : 0 < ω ((𝓘.op i : E → E) 1)) (hOp : (𝓘.op i).IsNormal) (hω : ω.IsNormal) :
    (𝓘.conditionalState i ω hpos).IsNormal :=
  Operation.condition_isNormal (𝓘.op i) ω hpos hOp hω

end Instrument

end ProbabilisticTheory
