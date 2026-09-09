/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Measurement.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Operation

/-!

# Instruments

A finite-outcome instrument retains more than a measurement: not just the outcome probabilities,
but the transformed, post-measurement system too. It is a finite family of operations (one per
outcome, `Instrument.op`) whose images of the certain event sum to exactly `1` — the instrument as
a whole loses no probability, even though each individual operation may.

Forgetting the post-measurement state and keeping only the outcome probabilities recovers a
`Measurement` (`Instrument.measurement`); pairing a prior state with an outcome, when that outcome
has nonzero probability, gives the conditional (post-measurement, renormalized) state
(`Instrument.conditionalState`).

## Main definitions

- `Instrument E ι`
- `Instrument.measurement`
- `Instrument.conditionalState`

-/

@[expose] public section

variable {E ι : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsOrderUnit E]

/-- A finite-outcome instrument: an operation for each outcome in the finite set `outcomes`,
whose images of the certain event exhaust it — the instrument loses no probability overall, even
though a single operation may. As with `Measurement`, `ι` itself need not be finite. -/
structure Instrument (E : Type*) [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
    [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsOrderUnit E] (ι : Type*) where
  /-- The finitely many outcomes this instrument can actually produce. -/
  outcomes : Finset ι
  /-- The operation associated to each possible outcome. -/
  op : ι → Operation E
  /-- The outcome probabilities exhaust the certain event. -/
  sum_op_one_eq_one : ∑ i ∈ outcomes, (op i : E → E) 1 = 1

namespace Instrument

/-- The measurement an instrument induces: only the outcome probabilities remain, given by each
operation's image of the certain event. -/
def measurement (𝓘 : Instrument E ι) : Measurement E ι where
  outcomes := 𝓘.outcomes
  effects i := Operation.outcomeEffect (𝓘.op i)
  sum_eq_one := 𝓘.sum_op_one_eq_one

@[simp]
lemma coe_measurement_effects (𝓘 : Instrument E ι) (i : ι) :
    ((𝓘.measurement.effects i : Effect E) : E) = (𝓘.op i : E → E) 1 :=
  rfl

/-- The post-measurement (conditional) state after outcome `i`, given a prior state `ω` for which
that outcome has nonzero probability: apply the operation, then renormalize by the outcome's
probability, so the certain event is again sent to `1`. -/
noncomputable def conditionalState (𝓘 : Instrument E ι) (i : ι) (ω : 𝓢[ℝ, E])
    (hpos : 0 < ω ((𝓘.op i : E → E) 1)) : 𝓢[ℝ, E] :=
  UnitalPositiveLinearMap.ofLinearMap
    ((ω ((𝓘.op i : E → E) 1))⁻¹ • (ω.toLinearMap.comp (𝓘.op i).1.toLinearMap))
    (fun x hx => by
      have : (0:ℝ) ≤ (ω ((𝓘.op i : E → E) 1))⁻¹ * ω ((𝓘.op i : E → E) x) :=
        mul_nonneg (inv_nonneg.mpr hpos.le) (ω.map_nonneg ((𝓘.op i).map_nonneg hx))
      simpa [LinearMap.smul_apply, smul_eq_mul] using this)
    (by simp [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hpos.ne'])

@[simp]
lemma conditionalState_apply (𝓘 : Instrument E ι) (i : ι) (ω : 𝓢[ℝ, E])
    (hpos : 0 < ω ((𝓘.op i : E → E) 1)) (a : E) :
    𝓘.conditionalState i ω hpos a =
      (ω ((𝓘.op i : E → E) 1))⁻¹ * ω ((𝓘.op i : E → E) a) :=
  rfl

end Instrument
