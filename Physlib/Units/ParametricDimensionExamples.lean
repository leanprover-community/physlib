/-
Copyright (c) 2026 Nicolas Rouquette. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
module

public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Physlib.Units.Dimension
public import Physlib.Units.WithDim.Basic  -- shake: keep (used in `example` only)
/-!

# Examples: parametric dimensions and comparing dimensioned quantities

`Dimension B` is parameterised by a basis `B` of base dimensions. This module
illustrates two consequences.

## Comparing a length with a velocity times a time

A recurring question is how to compare a quantity of dimension `length` with a
product of a quantity of dimension `length / time` and a quantity of dimension
`time`. In the fixed-tuple representation of `LTMCTDimensionBase`, reducible exponent
arithmetic makes this concrete cancellation a definitional equality:

* `(L𝓭 / T𝓭) * T𝓭 = L𝓭` is closed by `rfl`.
* `WithDim ((L𝓭 / T𝓭) * T𝓭) ℝ` and `WithDim L𝓭 ℝ` are therefore definitionally
  equal types.

Consequently a bare `x = v * t` is well-typed for these concrete dimensions. For a
representation where the same cancellation holds only propositionally, `WithDim.cast`
bridges the two dimension-indexed types.

## A non-standard basis

Because `Dimension` is parametric, the same dimensional algebra and `cast`-based
comparison are available over any represented basis, not just the physical
`LTMCTDimensionBase`. The unit-scaling layer (`LTMCTUnitChoices`, `dimScale`) is not
needed for either the algebra or the comparison, so neither is referenced here.

This module is illustrative and should not be imported by other modules.

-/

@[expose] public section

open Dimension

namespace ParametricDimensionExamples

/-- The concrete dimension equality `(length / time) · time = length` holds by
definitional equality. -/
example : (L𝓭 / T𝓭) * T𝓭 = L𝓭 := rfl

/-- The two concrete `WithDim` types are definitionally equal, so multiplication has
the required result type without a cast. -/
example (v : WithDim (L𝓭 / T𝓭) ℝ) (t : WithDim T𝓭 ℝ) : WithDim L𝓭 ℝ :=
  v * t

/-- The end-to-end comparison: a length equals a velocity times a time directly. -/
example (x : WithDim L𝓭 ℝ) (v : WithDim (L𝓭 / T𝓭) ℝ) (t : WithDim T𝓭 ℝ) : Prop :=
  x = v * t

/-- Two half-powers of length multiply definitionally to length. The unannotated exponent also
regresses the default away from natural-number division. -/
example : (L𝓭 ^ (1 / 2)) * (L𝓭 ^ (1 / 2)) = L𝓭 := rfl

/-- Reducible dimension powers also cancel for non-half fractional exponents. -/
example : (L𝓭 ^ (2 / 3 : Exponent)) * (L𝓭 ^ (1 / 3 : Exponent)) = L𝓭 := rfl

/-- Quantities carrying half-powers of length multiply directly to a length. -/
example (a b : WithDim (L𝓭 ^ (1 / 2)) ℝ) : WithDim L𝓭 ℝ :=
  a * b

/-!
## The same comparison over a non-standard basis

A basis with two base dimensions of its own — `bit` and `symbol` — that
`LTMCTDimensionBase` does not have. Nothing in the standard units system is involved.
-/

/-- A basis of information-theoretic base dimensions. -/
inductive Info
  /-- The information base dimension (bits). -/
  | bit
  /-- The symbol base dimension. -/
  | symbol

instance : DimensionBasis Info := DimensionBasis.pi _

/-- The `bit` base dimension. -/
def bitDim : Dimension Info := Dimension.ofFunction fun | .bit => 1 | .symbol => 0

/-- The `symbol` base dimension. -/
def symbolDim : Dimension Info := Dimension.ofFunction fun | .bit => 0 | .symbol => 1

/-- Cancellation works identically over the non-standard basis. -/
example : (bitDim / symbolDim) * symbolDim = bitDim := by ext; simp

/-- And so does the `cast`-based comparison: an information content equals an
information rate (`bit / symbol`) times a number of symbols. -/
example (x : WithDim bitDim ℝ) (r : WithDim (bitDim / symbolDim) ℝ)
    (n : WithDim symbolDim ℝ) : Prop :=
  x = (r * n).cast

end ParametricDimensionExamples
