/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Effect.Basic
public import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!

# Operations

## i. Overview

An operation on `E` is a positive linear endomorphism that is not required to be unital: unlike a
channel (`Channel/Basic.lean`), it can lose "probability mass" — the way a single, non-selective
outcome of a measurement transforms a state without necessarily preserving its normalization.
What keeps it physical rather than an arbitrary positive map is that it never *gains* mass either:
`op 1 ≤ 1`. A channel is exactly an operation with `op 1 = 1` (`Channel/Basic.lean`'s
`UnitalPositiveLinearMap`); a finite family of operations whose images of `1` sum to exactly `1`
is an instrument (`Measurement/Instrument.lean`).

## ii. Key definitions and results

- `Operation E`
- `Operation.outcomeEffect`

## iii. Table of contents

- A. Operations
- B. Outcome effects

-/

@[expose] public section

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [Module ℝ E] [One E]

/-! ## A. Operations -/

/-- An operation on `E`: a positive linear endomorphism that never sends the certain event above
itself. -/
def Operation (E : Type*) [AddCommGroup E] [PartialOrder E] [Module ℝ E] [One E] :=
  {op : E →ₚ[ℝ] E // op 1 ≤ 1}

namespace Operation

/-- Regard an operation as its underlying positive linear map. -/
instance : CoeFun (Operation E) (fun _ => E → E) := ⟨fun op => op.1⟩

@[ext]
lemma ext {op₁ op₂ : Operation E} (h : ∀ x, op₁ x = op₂ x) : op₁ = op₂ :=
  Subtype.ext (PositiveLinearMap.ext h)

/-- An operation never sends a possible outcome to something negative. -/
lemma map_nonneg (op : Operation E) {x : E} (hx : 0 ≤ x) : 0 ≤ op x :=
  op.1.map_nonneg hx

/-- An operation never sends the certain event above itself. -/
lemma apply_one_le_one (op : Operation E) : op 1 ≤ 1 :=
  op.2

variable [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E]

/-! ## B. Outcome effects -/

/-- The image of the certain event under an operation, as an effect: the probability of the
operation actually "firing" in a given state. -/
def outcomeEffect (op : Operation E) : Effect E :=
  ⟨op 1, op.map_nonneg IsOrderUnit.one_nonneg, op.apply_one_le_one⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
@[simp]
lemma coe_outcomeEffect (op : Operation E) : (outcomeEffect op : E) = op 1 := rfl

end Operation
