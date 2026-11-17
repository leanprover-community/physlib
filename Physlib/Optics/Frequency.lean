/-
Copyright (c) 2026 Samyak Rai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samyak Rai
-/
module

public import Physlib.Units.WithDim.Basic
/-!

# Frequency

In this module we define the type `Frequency`, corresponding to the frequency of a wave
carrying the dimension of inverse time.

## i. Overview

The type `Frequency` is `WithDim T𝓭⁻¹ ℝ≥0`, i.e., a nonnegative real number tagged with
the dimension of inverse time.

## ii. Key results

- `Frequency` : The type of frequencies of waves.

## iii. Table of contents

- A. The Frequency type

## iv. References

- https://en.wikipedia.org/wiki/Frequency
- https://en.wikipedia.org/wiki/Wavelength

-/

@[expose] public section

open Dimension
open scoped NNReal

/-!

## A. The Frequency type

-/

/-- The type `Frequency` represents the measure of of how often sinusodial components
 of a wave repeat per unit time, i.e. a nonnegative real number carrying the dimension
 of inverse time, in a given (but arbitrary) set of units. -/
abbrev Frequency : Type := WithDim T𝓭⁻¹ ℝ≥0
