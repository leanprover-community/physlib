/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.NNReal.Defs
/-!

# Boltzmann constant

The Boltzmann constant is a constant `kB` of dimension `m² kg s⁻² K⁻¹`, that is
`Energy/Temperature`. It is named after Ludwig Boltzmann.

In this module give the value of the Boltzmann constant.

-/
open NNReal

namespace Constants

/-- The Boltzmann constant in units of `m ^ 2 kg s ^ (-2) K ^ (-1)`.
  As long as one does not use the underlying value of this quantity,
  then it can be used as Boltzmann's constant in an arbitrary set of units. -/
def kBAx : {p : ℝ | 0 < p} := ⟨1.380649e-23, by norm_num⟩

/-- The Boltzmann constant in a given but arbitrary set of units.
  Boltzman's constant has dimension equivalent to `Energy/Temperature`. -/
noncomputable def kB : ℝ := kBAx.1

/-- The Boltzmann constant is positive. -/
lemma kB_pos : 0 < kB := kBAx.2

/-- The Boltzmann constant is non-negative. -/
lemma kB_nonneg : 0 ≤ kB := le_of_lt kBAx.2

/-- The Boltzmann constant is not equal to zero. -/
lemma kB_ne_zero : kB ≠ 0 := by
  linarith [kB_pos]

end Constants
