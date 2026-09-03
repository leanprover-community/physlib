/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Basic.OrderUnit.Effect.EffectValuedMeasure

/-!

# POVMs

`EffectValuedMeasure Ω E` already *is* a positive-operator-valued measure, once `E` is the
self-adjoint part of an operator algebra: `POVM` is just the physics-literature name for it, kept
here for discoverability alongside `PVM.lean`.

## Main definitions

- `POVM`

-/

@[expose] public section

/-- A positive-operator-valued measure: the physics name for `EffectValuedMeasure`. -/
abbrev POVM (Ω E : Type*) [MeasurableSpace Ω] [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [One E] [IsOrderUnit E] := EffectValuedMeasure Ω E
